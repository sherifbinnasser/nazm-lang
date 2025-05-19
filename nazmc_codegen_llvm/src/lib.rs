mod fns;
mod operand;
mod rvalue;
mod stm;
mod types;
mod util;

use fns::*;
use nazmc_nir_interpreter::InterpreterData;
use operand::*;
use rvalue::*;
use std::{
    cell::{Cell, RefCell},
    cmp::max,
    collections::HashMap,
};
use stm::*;
use types::*;
use util::*;

use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::PassBuilderOptions,
    targets::{
        CodeModel, InitializationConfig, RelocMode, Target, TargetData, TargetMachine, TargetTriple,
    },
    types::{
        AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType,
        IntType, PointerType, StructType,
    },
    values::{
        AnyValue, AnyValueEnum, BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue,
        GlobalValue, InstructionOpcode, PointerValue,
    },
    AddressSpace, FloatPredicate, IntPredicate,
};

pub use inkwell::OptimizationLevel;
use nazmc_data_pool::*;
use nazmc_nir::*;
use typed_index_collections::{TiSlice, TiVec};

pub struct LLVMCodeGen<'ctx, 'nir> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    machine: TargetMachine,
    nir: NIR<'nir>,
    interpreter_data: InterpreterData,
    llvm_fns: TiVec<FnKey, FunctionValue<'ctx>>,
    llvm_str_pool: TiVec<StrKey, GlobalValue<'ctx>>,
    llvm_str_slices_pool: TiVec<StrKey, PointerValue<'ctx>>,
    llvm_statics: TiVec<StaticKey, PointerValue<'ctx>>,
    llvm_consts: HashMap<ConstKey, PointerValue<'ctx>>,
    llvm_temps_counter: Cell<usize>,
    ret_ptr: Cell<Option<PointerValue<'ctx>>>,
    llvm_temps: RefCell<Vec<String>>,
    fn_ptr_types: RefCell<HashMap<FnPtrTypeKey, FnPtrLayout<'ctx>>>,
    structs_layouts: RefCell<HashMap<StructKey, TypeLayout<'ctx>>>,
    tuples_layouts: RefCell<HashMap<TupleTypeKey, TypeLayout<'ctx>>>,
    basic_blocks: RefCell<HashMap<BasicBlockKey, BasicBlock<'ctx>>>,
    args: RefCell<HashMap<ArgKey, PointerValue<'ctx>>>,
    locals: RefCell<HashMap<BindingKey, PointerValue<'ctx>>>,
    temps: RefCell<HashMap<TempKey, AnyValueEnum<'ctx>>>,
}

#[derive(Debug, Clone, Copy)]
enum ArgLayout {
    RetPtr,
    ByvalPtr,
    IntStruct,
    BinaryStruct,
    Regular,
    Skipped,
}

struct FnPtrLayout<'ctx> {
    fn_type: FunctionType<'ctx>,
    attributes: Vec<(AttributeLoc, Attribute)>,
    args_layout: Vec<ArgLayout>,
}

struct TypeLayout<'ctx> {
    struct_ty: StructType<'ctx>,
    size: u32,
    align: u32,
    fields: Vec<FieldLayout>,
}

struct FieldLayout {
    offset: u32,
}

enum FlatFieldClass {
    Int(u32),
    Float(u32),
}

impl FlatFieldClass {
    pub(crate) fn to_llvm_type(self, context: &Context) -> BasicTypeEnum {
        match self {
            Self::Int(bytes) => context
                .custom_width_int_type((bytes as u32) * 8)
                .as_basic_type_enum(),
            Self::Float(4) => context.f32_type().as_basic_type_enum(),
            Self::Float(_) => context.f64_type().as_basic_type_enum(),
        }
    }

    pub(crate) fn is_float(self) -> bool {
        matches!(self, Self::Float(_))
    }
}

impl<'ctx, 'nir> LLVMCodeGen<'ctx, 'nir> {
    pub fn new_ctx() -> Context {
        let target_config = InitializationConfig::default();

        Target::initialize_native(&target_config)
            .expect("Failed to initialize native machine target!");

        Target::initialize_all(&target_config);

        Context::create()
    }

    pub fn new(
        context: &'ctx Context,
        nir: NIR<'nir>,
        interpreter_data: InterpreterData,
        name: &str,
        target: Option<&str>,
        opt_lvl: OptimizationLevel,
    ) -> Self {
        let triple = match target {
            None => TargetMachine::get_default_triple(),
            Some(target_str) => TargetTriple::create(target_str),
        };

        let target =
            Target::from_triple(&triple).expect("Unknown target: please specify a target ");

        let machine = target
            .create_target_machine(
                &triple,
                "generic",
                "",
                opt_lvl,
                RelocMode::Default,
                CodeModel::Default,
            )
            .unwrap();

        let module = context.create_module(name);
        module.set_triple(&triple);
        module.set_data_layout(&machine.get_target_data().get_data_layout());

        let builder = context.create_builder();

        Self {
            context: &context,
            module,
            builder,
            machine,
            interpreter_data,
            llvm_fns: TiVec::with_capacity(nir.fns.len()),
            llvm_str_pool: TiVec::with_capacity(nir.str_pool.len()),
            llvm_str_slices_pool: TiVec::with_capacity(nir.str_pool.len()),
            llvm_statics: TiVec::with_capacity(nir.statics.len()),
            llvm_consts: HashMap::with_capacity(nir.consts.len()),
            llvm_temps_counter: Cell::new(0),
            ret_ptr: Default::default(),
            llvm_temps: RefCell::new(Vec::new()),
            fn_ptr_types: RefCell::new(HashMap::with_capacity(nir.fn_ptr_types.len())),
            structs_layouts: RefCell::new(HashMap::with_capacity(nir.structs.len())),
            tuples_layouts: RefCell::new(HashMap::with_capacity(nir.tuple_types.len())),
            basic_blocks: Default::default(),
            args: Default::default(),
            locals: Default::default(),
            temps: Default::default(),
            nir,
        }
    }

    pub fn lower(&mut self) {
        // lower_string_consts will take the ownership of str_pool
        // So lower functions signatures first as extern functions may have string consts link names
        self.lower_fns_signatures();
        self.lower_string_consts();
        self.lower_consts();
        self.lower_fns_bodies();
    }

    pub fn optimize_module(&self, opt_level: OptimizationLevel) {
        // Configure PassBuilderOptions
        let pbo = PassBuilderOptions::create();
        pbo.set_loop_vectorization(true);
        pbo.set_loop_unrolling(true);
        pbo.set_verify_each(true);
        pbo.set_debug_logging(false);

        // Map optimization level to passes string
        let passes = match opt_level {
            OptimizationLevel::None => "default<O0>",
            OptimizationLevel::Less => "default<O1>",
            OptimizationLevel::Default => "default<O2>",
            OptimizationLevel::Aggressive => "default<O3>",
        };

        // Run passes on the module
        let _ = self
            .module
            .run_passes(passes, &self.machine, pbo)
            .map_err(|e| {
                eprintln!("Optimization failed: {}", e.to_string());
            });
    }

    pub fn print_ir(&self) {
        let _ = self
            .module
            .print_to_file(&format!("{}.ll", self.module.get_name().to_str().unwrap()));
    }

    fn lower_string_consts(&mut self) {
        let strs = std::mem::take(&mut self.nir.str_pool);

        for (str_key, _str) in strs.into_iter_enumerated() {
            let str_len = self.isize_type().const_int(_str.len() as u64, false);
            let const_str = self.context.const_string(&_str.into_bytes(), true);
            let global =
                self.module
                    .add_global(const_str.get_type(), None, &format!(".str{}", str_key.0));
            global.set_initializer(&const_str);
            global.set_constant(true);
            global.set_unnamed_addr(true);
            global.set_linkage(Linkage::Private);
            global.set_alignment(1);
            self.llvm_str_pool.push(global);

            let slice = self
                .context
                .const_struct(&[global.as_pointer_value().into(), str_len.into()], false);

            let global_slice = self.module.add_global(
                self.slice_type(),
                None,
                &format!(".str_slice{}", str_key.0),
            );
            global_slice.set_initializer(&slice);
            global_slice.set_constant(true);
            global_slice.set_unnamed_addr(true);
            global_slice.set_linkage(Linkage::Private);

            self.llvm_str_slices_pool
                .push(global_slice.as_pointer_value());
        }
    }

    fn lower_consts(&mut self) {
        for i in 0..self.nir.consts.len() as u32 {
            self.lower_const(ConstKey(i));
        }
    }

    fn lower_const(&mut self, const_key: ConstKey) -> PointerValue {
        if let Some(ptr) = self.llvm_consts.get(&const_key) {
            return ptr.clone();
        }

        let typ = self.nir.consts[&const_key].typ;
        let llvm_typ = self.lower_type(typ);
        let global_const = self.module.add_global(
            any_type_enum_to_basic_type_enum(llvm_typ),
            None,
            &format!("CONST{}", const_key.0),
        );

        let value = self.lower_bytes(self.nir.consts[&const_key].value, typ, llvm_typ);

        global_const.set_initializer(&value);
        global_const.set_constant(true);
        global_const.set_unnamed_addr(true);
        global_const.set_linkage(Linkage::Private);
        let global_const = global_const.as_pointer_value();
        self.llvm_consts.insert(const_key, global_const);
        global_const
    }

    fn get_interpreter_type_size(&self, type_key: TypeKey) -> u32 {
        match self.nir.types[type_key] {
            Type::Unit => 0,
            Type::I | Type::U | Type::MutPtr(_) | Type::Ptr(_) | Type::FnPtr(_) => {
                std::mem::size_of::<usize>() as u32
            }
            Type::I1 | Type::U1 | Type::Bool => 1,
            Type::I2 | Type::U2 => 2,
            Type::I4 | Type::U4 | Type::F4 | Type::Char => 4,
            Type::I8 | Type::U8 | Type::F8 => 8,
            Type::Slice(_) | Type::MutSlice(_) => 2 * std::mem::size_of::<usize>() as u32,
            Type::Struct(struct_key) => self.interpreter_data.structs_layouts[&struct_key].size,
            Type::Tuple(tuple_type_key) => {
                self.interpreter_data.tuples_layouts[&tuple_type_key].size
            }
            Type::Array(array_type_key) => {
                let ArrayType {
                    underlying_typ,
                    size,
                } = self.nir.array_types[array_type_key];
                self.get_interpreter_type_size(underlying_typ) * size
            }
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }

    fn lower_bytes(
        &mut self,
        value_ptr: PtrKey,
        typ: TypeKey,
        llvm_typ: AnyTypeEnum<'ctx>,
    ) -> BasicValueEnum {
        use nazmc_nir_interpreter::bytes::*;

        let size = self.get_interpreter_type_size(typ);
        let value = self
            .interpreter_data
            .memory
            .get_bytes_at(value_ptr, size as usize);

        macro_rules! to_int {
            ($method: ident) => {
                llvm_typ
                    .into_int_type()
                    .const_int($method(value).unwrap() as u64, false)
                    .as_basic_value_enum()
            };
        }

        macro_rules! to_float {
            ($method: ident) => {
                llvm_typ
                    .into_float_type()
                    .const_float($method(value).unwrap() as f64)
                    .as_basic_value_enum()
            };
        }

        match self.nir.types[typ] {
            Type::Bool => to_int!(to_bool),
            Type::Char => to_int!(to_char),
            Type::I => to_int!(to_isize),
            Type::I1 => to_int!(to_i8),
            Type::I2 => to_int!(to_i16),
            Type::I4 => to_int!(to_i32),
            Type::I8 => to_int!(to_i64),
            Type::U => to_int!(to_usize),
            Type::U1 => to_int!(to_u8),
            Type::U2 => to_int!(to_u16),
            Type::U4 => to_int!(to_u32),
            Type::U8 => to_int!(to_u64),
            Type::F4 => to_float!(to_f32),
            Type::F8 => to_float!(to_f64),
            Type::Unit => self
                .context
                .i64_type()
                .const_int(0, false)
                .as_basic_value_enum(),
            Type::FnPtr(fn_ptr_type_key) => {
                let fn_key = to_fn_key(value).unwrap();
                self.llvm_fns[fn_key]
                    .as_global_value()
                    .as_pointer_value()
                    .as_basic_value_enum()
            }
            Type::Ptr(type_key) | Type::MutPtr(type_key) => todo!(),
            Type::Struct(struct_key) => todo!(),
            Type::Slice(type_key) | Type::MutSlice(type_key) => todo!(),
            Type::Array(array_type_key) => todo!(),
            Type::Tuple(tuple_type_key) => todo!(),
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }

    // fn lower_rc_value(&mut self, value: RcValue, typ: AnyTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
    //     match &*value.borrow() {
    //         Value::Unit => self
    //             .context
    //             .i64_type()
    //             .const_int(0, false)
    //             .as_basic_value_enum(),
    //         Value::Int(int) => typ
    //             .into_int_type()
    //             .const_int(*int as u64, false)
    //             .as_basic_value_enum(),
    //         Value::UInt(int) => typ
    //             .into_int_type()
    //             .const_int(*int, false)
    //             .as_basic_value_enum(),
    //         Value::Float(float) => typ
    //             .into_float_type()
    //             .const_float(*float as f64)
    //             .as_basic_value_enum(),
    //         Value::Bool(b) => typ
    //             .into_int_type() // i8
    //             .const_int(*b as u64, false)
    //             .as_basic_value_enum(),
    //         Value::Char(c) => typ
    //             .into_int_type() // i32
    //             .const_int(*c as u64, false)
    //             .as_basic_value_enum(),
    //         Value::FnPtr(fn_key) => self.llvm_fns[*fn_key]
    //             .as_global_value()
    //             .as_pointer_value()
    //             .as_basic_value_enum(),
    //         Value::Ptr(rc_value) => {
    //             if let Some(str_key) = self.nir.interpreter_str_pool.get(rc_value) {
    //                 // Prepare GEP indices
    //                 let i32_type = self.context.i32_type();
    //                 let zero = i32_type.const_zero();
    //                 let two = i32_type.const_int(2, false);
    //                 let str_ptr = self.llvm_str_pool[*str_key];
    //                 let str_typ = any_type_enum_to_basic_type_enum(str_ptr.get_value_type());
    //                 unsafe { str_ptr.as_pointer_value().const_gep(str_typ, &[zero, two]) }
    //             } else {
    //                 todo!()
    //             }
    //             .as_basic_value_enum()
    //         }
    //         Value::Agg(vec) => match typ {
    //             AnyTypeEnum::ArrayType(array_type) => {
    //                 let underlying_typ = array_type.get_element_type().as_any_type_enum();
    //                 let values_iter = vec
    //                     .iter()
    //                     .map(|val| self.lower_rc_value(val.clone(), underlying_typ));

    //                 macro_rules! map {
    //                     ($id: ident, $typ: expr) => {
    //                         $typ.const_array(&values_iter.map(|val| val.$id()).collect::<Vec<_>>())
    //                     };
    //                 }

    //                 match underlying_typ {
    //                     AnyTypeEnum::ArrayType(typ) => map!(into_array_value, typ),
    //                     AnyTypeEnum::FloatType(typ) => map!(into_float_value, typ),
    //                     AnyTypeEnum::IntType(typ) => map!(into_int_value, typ),
    //                     AnyTypeEnum::PointerType(typ) => map!(into_pointer_value, typ),
    //                     AnyTypeEnum::StructType(typ) => map!(into_struct_value, typ),
    //                     AnyTypeEnum::FunctionType(typ) => map!(
    //                         into_pointer_value,
    //                         typ.get_context().ptr_type(AddressSpace::default())
    //                     ),
    //                     _ => unreachable!(),
    //                 }
    //                 .as_basic_value_enum()
    //             }
    //             AnyTypeEnum::StructType(struct_type) => {
    //                 let mut fields = Vec::with_capacity(vec.len());
    //                 for (rc_value, typ) in vec.iter().zip(struct_type.get_field_types_iter()) {
    //                     fields.push(self.lower_rc_value(rc_value.clone(), typ.as_any_type_enum()));
    //                 }
    //                 struct_type
    //                     .const_named_struct(&fields)
    //                     .as_basic_value_enum()
    //             }
    //             _ => unreachable!(),
    //         },
    //     }
    // }

    fn get_id(&self, id: IdKey) -> &str {
        &self.nir.id_pool[id]
    }

    fn fmt_pkg_name(&self, pkg_key: PkgKey) -> String {
        self.nir.pkgs_names[pkg_key]
            .iter()
            .map(|id| self.get_id(*id))
            .collect::<Vec<_>>()
            .join("::")
    }

    fn fmt_item_name(&self, item_info: ItemInfo) -> String {
        let pkg = self.fmt_pkg_name(self.nir.files_to_pkgs[item_info.file_key]);
        let name = &self.nir.id_pool[item_info.id_key];
        if pkg.is_empty() {
            name.to_owned()
        } else {
            format!("{}::{}", pkg, name)
        }
    }

    fn new_llvm_temp(&self) -> String {
        let llvm_temps_counter = self.llvm_temps_counter.get();
        if llvm_temps_counter == self.llvm_temps.borrow().len() {
            self.llvm_temps
                .borrow_mut()
                .push(format!("llvm_tmp{}", llvm_temps_counter));
        }
        self.llvm_temps_counter.set(llvm_temps_counter + 1);
        let temps = self.llvm_temps.borrow();
        temps[llvm_temps_counter].clone()
    }
}
