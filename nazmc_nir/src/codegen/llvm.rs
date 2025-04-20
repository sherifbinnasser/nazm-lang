use std::{
    cell::{Cell, RefCell},
    cmp::max,
};

use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    passes::PassBuilderOptions,
    targets::{
        CodeModel, InitializationConfig, RelocMode, Target, TargetData, TargetMachine, TargetTriple,
    },
    types::{
        AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType,
        IntType, PointerType, StructType,
    },
    values::{
        AnyValue, AnyValueEnum, BasicMetadataValueEnum, BasicValueEnum, FunctionValue,
        InstructionOpcode, PointerValue,
    },
    AddressSpace, FloatPredicate, IntPredicate,
};

use crate::*;

pub use inkwell::OptimizationLevel;

pub struct LLVMCodeGen<'ctx, 'nir> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    machine: TargetMachine,
    nir: NIR<'nir>,
    llvm_fns: TiVec<FnKey, FunctionValue<'ctx>>,
    llvm_str_pool: TiVec<StrKey, PointerValue<'ctx>>,
    llvm_statics: TiVec<StaticKey, PointerValue<'ctx>>,
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

pub(crate) fn flatten_type(
    target_data: &TargetData,
    typ: BasicTypeEnum,
    align: u32,
) -> (FlatFieldClass, FlatFieldClass) {
    let mut a = 0;
    let mut a_float = true;
    let mut b = 0;
    let mut b_float = true;

    fn flatten_inner(
        target_data: &TargetData,
        typ: BasicTypeEnum,
        a: &mut u32,
        a_float: &mut bool,
        b: &mut u32,
        b_float: &mut bool,
    ) {
        match typ {
            BasicTypeEnum::StructType(t) => {
                for field in t.get_field_types() {
                    flatten_inner(target_data, field, a, a_float, b, b_float);
                }
            }
            BasicTypeEnum::ArrayType(t) => {
                let elem_type = t.get_element_type();
                let len = t.size_of().unwrap().get_zero_extended_constant().unwrap();
                for _ in 0..len {
                    flatten_inner(target_data, elem_type, a, a_float, b, b_float);
                }
            }
            BasicTypeEnum::FloatType(t) => {
                let size = target_data.get_abi_size(&t) as u32;
                if *a + size <= 8 {
                    *a += size;
                } else {
                    *b += size;
                }
            }
            BasicTypeEnum::IntType(t) => {
                let size = target_data.get_abi_size(&t) as u32;
                if *a + size <= 8 {
                    *a += size;
                    *a_float = false;
                } else {
                    *b += size;
                    *b_float = false;
                }
            }
            BasicTypeEnum::PointerType(t) => {
                let size = target_data.get_abi_size(&t) as u32;
                if *a + size <= 8 {
                    *a += size;
                    *a_float = false;
                } else {
                    *b += size;
                    *b_float = false;
                }
            }
            BasicTypeEnum::VectorType(_) => todo!(),
        }
    }

    flatten_inner(target_data, typ, &mut a, &mut a_float, &mut b, &mut b_float);

    // Apply alignment
    a = max(a, align);
    b = max(b, align);

    (
        if a_float && a > 0 {
            FlatFieldClass::Float(a)
        } else {
            FlatFieldClass::Int(a)
        },
        if b_float && b > 0 {
            FlatFieldClass::Float(b)
        } else {
            FlatFieldClass::Int(b)
        },
    )
}

fn ptr_type_from_fn_type(fn_type: FunctionType) -> PointerType {
    fn_type.get_context().ptr_type(AddressSpace::default())
}

fn any_value_as_basic_value(any_value: AnyValueEnum) -> Option<BasicValueEnum> {
    match any_value {
        AnyValueEnum::ArrayValue(value) => Some(BasicValueEnum::ArrayValue(value)),
        AnyValueEnum::IntValue(value) => Some(BasicValueEnum::IntValue(value)),
        AnyValueEnum::FloatValue(value) => Some(BasicValueEnum::FloatValue(value)),
        AnyValueEnum::PointerValue(value) => Some(BasicValueEnum::PointerValue(value)),
        AnyValueEnum::StructValue(value) => Some(BasicValueEnum::StructValue(value)),
        AnyValueEnum::VectorValue(value) => Some(BasicValueEnum::VectorValue(value)),
        AnyValueEnum::FunctionValue(value) => Some(BasicValueEnum::PointerValue(
            value.as_global_value().as_pointer_value(),
        )),
        _ => None,
    }
}

fn any_value_as_basic_metadata_value(any_value: AnyValueEnum) -> BasicMetadataValueEnum {
    match any_value {
        AnyValueEnum::ArrayValue(value) => BasicMetadataValueEnum::ArrayValue(value),
        AnyValueEnum::IntValue(value) => BasicMetadataValueEnum::IntValue(value),
        AnyValueEnum::FloatValue(value) => BasicMetadataValueEnum::FloatValue(value),
        AnyValueEnum::PointerValue(value) => BasicMetadataValueEnum::PointerValue(value),
        AnyValueEnum::StructValue(value) => BasicMetadataValueEnum::StructValue(value),
        AnyValueEnum::VectorValue(value) => BasicMetadataValueEnum::VectorValue(value),
        AnyValueEnum::FunctionValue(value) => {
            BasicMetadataValueEnum::PointerValue(value.as_global_value().as_pointer_value())
        }
        _ => unreachable!(),
    }
}

fn any_type_enum_to_basic_metadata_type_enum(ty: AnyTypeEnum) -> BasicMetadataTypeEnum {
    match ty {
        AnyTypeEnum::ArrayType(array_type) => BasicMetadataTypeEnum::ArrayType(array_type),
        AnyTypeEnum::FloatType(float_type) => BasicMetadataTypeEnum::FloatType(float_type),
        AnyTypeEnum::IntType(int_type) => BasicMetadataTypeEnum::IntType(int_type),
        AnyTypeEnum::PointerType(pointer_type) => BasicMetadataTypeEnum::PointerType(pointer_type),
        AnyTypeEnum::StructType(struct_type) => BasicMetadataTypeEnum::StructType(struct_type),
        AnyTypeEnum::VectorType(vector_type) => BasicMetadataTypeEnum::VectorType(vector_type),
        AnyTypeEnum::FunctionType(fn_type) => {
            BasicMetadataTypeEnum::PointerType(ptr_type_from_fn_type(fn_type))
        }
        AnyTypeEnum::VoidType(_) => {
            unreachable!()
        }
    }
}

fn any_type_enum_to_basic_type_enum(ty: AnyTypeEnum) -> BasicTypeEnum {
    match ty {
        AnyTypeEnum::ArrayType(array_type) => array_type.as_basic_type_enum(),
        AnyTypeEnum::FloatType(float_type) => float_type.as_basic_type_enum(),
        AnyTypeEnum::IntType(int_type) => int_type.as_basic_type_enum(),
        AnyTypeEnum::PointerType(pointer_type) => pointer_type.as_basic_type_enum(),
        AnyTypeEnum::StructType(struct_type) => struct_type.as_basic_type_enum(),
        AnyTypeEnum::VectorType(vector_type) => vector_type.as_basic_type_enum(),
        AnyTypeEnum::FunctionType(fn_type) => ptr_type_from_fn_type(fn_type).as_basic_type_enum(),
        AnyTypeEnum::VoidType(_) => {
            unreachable!()
        }
    }
}

fn fn_type_from_any_type_enum<'a>(
    ty: AnyTypeEnum<'a>,
    param_types: &[BasicMetadataTypeEnum<'a>],
    is_var_args: bool,
) -> FunctionType<'a> {
    match ty {
        AnyTypeEnum::FloatType(float_type) => float_type.fn_type(param_types, is_var_args),
        AnyTypeEnum::IntType(int_type) => int_type.fn_type(param_types, is_var_args),
        AnyTypeEnum::VoidType(void_type) => void_type.fn_type(param_types, is_var_args),
        AnyTypeEnum::ArrayType(array_type) => array_type.fn_type(param_types, is_var_args),
        AnyTypeEnum::PointerType(ptr_type) => ptr_type.fn_type(param_types, is_var_args),
        AnyTypeEnum::FunctionType(fn_type) => {
            ptr_type_from_fn_type(fn_type).fn_type(param_types, is_var_args)
        }
        AnyTypeEnum::StructType(struct_type) => struct_type.fn_type(param_types, is_var_args),
        AnyTypeEnum::VectorType(vector_type) => todo!(),
    }
}

fn array_type_from_any_type_enum(ty: AnyTypeEnum, size: u32) -> inkwell::types::ArrayType {
    match ty {
        AnyTypeEnum::ArrayType(array_type) => array_type.array_type(size),
        AnyTypeEnum::FloatType(float_type) => float_type.array_type(size),
        AnyTypeEnum::IntType(int_type) => int_type.array_type(size),
        AnyTypeEnum::StructType(struct_type) => struct_type.array_type(size),
        AnyTypeEnum::VectorType(vector_type) => vector_type.array_type(size),
        AnyTypeEnum::PointerType(ptr_type) => ptr_type.array_type(size),
        AnyTypeEnum::FunctionType(fn_type) => fn_type
            .get_context()
            .ptr_type(AddressSpace::default())
            .array_type(size),
        AnyTypeEnum::VoidType(void_type) => unreachable!(),
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
            llvm_fns: TiVec::with_capacity(nir.fns.len()),
            llvm_str_pool: TiVec::with_capacity(nir.str_pool.len()),
            llvm_statics: TiVec::with_capacity(nir.statics.len()),
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
        self.lower_string_consts();
        self.lower_fns_signatures();
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
            let const_str = self.context.const_string(&_str.into_bytes(), true);
            let global =
                self.module
                    .add_global(const_str.get_type(), None, &format!(".str{}", str_key.0));
            self.llvm_str_pool.push(global.as_pointer_value());
        }
    }

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

    fn ptr_type(&self) -> PointerType<'ctx> {
        self.context.ptr_type(AddressSpace::default())
    }

    fn isize_type(&self) -> IntType<'ctx> {
        self.context
            .ptr_sized_int_type(&self.machine.get_target_data(), None)
    }

    fn get_type_size(&self, type_key: TypeKey) -> u32 {
        match self.nir.types[type_key] {
            Type::Unit => 0,
            Type::I | Type::U | Type::MutPtr(_) | Type::Ptr(_) | Type::FnPtr(_) => {
                self.machine.get_target_data().get_pointer_byte_size(None)
            }
            Type::I1 | Type::U1 | Type::Bool => 1,
            Type::I2 | Type::U2 => 2,
            Type::I4 | Type::U4 | Type::F4 | Type::Char => 4,
            Type::I8 | Type::U8 | Type::F8 => 8,
            Type::Slice(_) | Type::MutSlice(_) => {
                2 * self.machine.get_target_data().get_pointer_byte_size(None)
            }
            Type::Struct(struct_key) => self.structs_layouts.borrow()[&struct_key].size,
            Type::Tuple(tuple_type_key) => self.tuples_layouts.borrow()[&tuple_type_key].size,
            Type::Array(array_type_key) => {
                let ArrayType {
                    underlying_typ,
                    size,
                } = self.nir.array_types[array_type_key];
                self.get_type_size(underlying_typ) * size
            }
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }

    fn get_type_align(&self, type_key: TypeKey) -> u32 {
        match self.nir.types[type_key] {
            Type::I1 | Type::U1 | Type::Unit | Type::Bool => 1,
            Type::I2 | Type::U2 => 2,
            Type::I4 | Type::U4 | Type::F4 | Type::Char => 4,
            Type::I8 | Type::U8 | Type::F8 => 8,
            Type::I
            | Type::U
            | Type::MutPtr(_)
            | Type::Ptr(_)
            | Type::FnPtr(_)
            | Type::Slice(_)
            | Type::MutSlice(_) => self.machine.get_target_data().get_pointer_byte_size(None),
            Type::Struct(struct_key) => self.structs_layouts.borrow()[&struct_key].align,
            Type::Tuple(tuple_type_key) => self.tuples_layouts.borrow()[&tuple_type_key].align,
            Type::Array(array_type_key) => {
                let ArrayType {
                    underlying_typ,
                    size: _,
                } = self.nir.array_types[array_type_key];
                self.get_type_align(underlying_typ)
            }
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }

    fn lower_type(&self, type_key: TypeKey) -> AnyTypeEnum<'ctx> {
        match self.nir.types[type_key] {
            Type::Unit => self.context.void_type().as_any_type_enum(),
            Type::I | Type::U => self.isize_type().as_any_type_enum(),
            Type::Bool | Type::I1 | Type::U1 => self.context.i8_type().as_any_type_enum(),
            Type::I2 | Type::U2 => self.context.i16_type().as_any_type_enum(),
            Type::Char | Type::I4 | Type::U4 => self.context.i32_type().as_any_type_enum(),
            Type::I8 | Type::U8 => self.context.i64_type().as_any_type_enum(),
            Type::F4 => self.context.f32_type().as_any_type_enum(),
            Type::F8 => self.context.f64_type().as_any_type_enum(),
            Type::Struct(struct_key) => self.lower_struct_type(struct_key).as_any_type_enum(),
            Type::Ptr(_) | Type::MutPtr(_) => self.ptr_type().as_any_type_enum(),
            Type::FnPtr(fn_ptr_ty_key) => self.lower_fn_ptr_type(fn_ptr_ty_key).as_any_type_enum(),
            Type::Tuple(tuple_type_key) => self.lower_tuple_type(tuple_type_key).as_any_type_enum(),
            Type::Array(array_type_key) => self.lower_array_type(array_type_key).as_any_type_enum(),
            Type::Slice(_) | Type::MutSlice(_) => self
                .context
                .struct_type(
                    &[
                        self.ptr_type().into(),
                        self.context
                            .ptr_sized_int_type(&self.machine.get_target_data(), None)
                            .into(),
                    ],
                    false,
                )
                .as_any_type_enum(),
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }

    fn is_agg_type(&self, type_key: TypeKey) -> bool {
        matches!(
            self.nir.types[type_key],
            Type::Struct(_)
                | Type::Slice(_)
                | Type::MutSlice(_)
                | Type::Array(_)
                | Type::Tuple(_)
                | Type::Lambda(_)
        )
    }

    fn is_sret_or_byval_type(&self, type_key: TypeKey) -> bool {
        self.is_agg_type(type_key) && self.get_type_size(type_key) > 16
    }

    fn lower_param_type(&self, type_key: TypeKey) -> (AnyTypeEnum<'ctx>, ArgLayout) {
        let typ = self.lower_type(type_key);
        let size = self.get_type_size(type_key);
        if !self.is_agg_type(type_key) {
            (typ, ArgLayout::Regular)
        } else if size == 0 {
            (
                self.context.void_type().as_any_type_enum(),
                ArgLayout::Skipped,
            )
        } else if size <= 8 {
            (
                AnyTypeEnum::IntType(self.context.custom_width_int_type(size * 8)),
                ArgLayout::IntStruct,
            )
        } else if size <= 16 {
            let align = self.get_type_align(type_key);
            let (class1, class2) = flatten_type(
                &self.machine.get_target_data(),
                any_type_enum_to_basic_type_enum(typ),
                align,
            );
            let (class1, class2) = (
                class1.to_llvm_type(&self.context),
                class2.to_llvm_type(&self.context),
            );
            let struct_type = self
                .context
                .struct_type(&[class1.into(), class2.into()], false);
            (
                AnyTypeEnum::StructType(struct_type),
                ArgLayout::BinaryStruct,
            )
        } else {
            (
                AnyTypeEnum::PointerType(self.ptr_type()),
                ArgLayout::ByvalPtr,
            )
        }
    }

    fn lower_fn_ptr_type(&self, fn_ptr_ty_key: FnPtrTypeKey) -> FunctionType<'ctx> {
        if let Some(fn_ty) = self.fn_ptr_types.borrow().get(&fn_ptr_ty_key) {
            return fn_ty.fn_type;
        }

        let params_len = self.nir.fn_ptr_types[fn_ptr_ty_key].params_types.len();
        let return_type = self.nir.fn_ptr_types[fn_ptr_ty_key].return_type;
        let (mut llvm_return_ty, return_arg_layout) = self.lower_param_type(return_type);

        let mut params_types;
        let mut args_layout;
        let mut attributes = Vec::new();

        if let ArgLayout::ByvalPtr = return_arg_layout {
            params_types = Vec::with_capacity(params_len + 1);
            args_layout = Vec::with_capacity(params_len + 1);
            params_types.push(any_type_enum_to_basic_metadata_type_enum(llvm_return_ty));
            args_layout.push(ArgLayout::RetPtr);
            llvm_return_ty = AnyTypeEnum::VoidType(self.context.void_type());
            let noalias_id = Attribute::get_named_enum_kind_id("noalias");
            let sret_id = Attribute::get_named_enum_kind_id("sret");
            let noalias = self.context.create_enum_attribute(noalias_id, 0);
            let sret = self
                .context
                .create_type_attribute(sret_id, self.lower_type(return_type));
            attributes.push((AttributeLoc::Param(0), noalias));
            attributes.push((AttributeLoc::Param(0), sret));
        } else {
            params_types = Vec::with_capacity(params_len);
            args_layout = Vec::with_capacity(params_len);
        }

        for &ty in &self.nir.fn_ptr_types[fn_ptr_ty_key].params_types {
            let (llvm_ty, arg_layout) = self.lower_param_type(ty);

            args_layout.push(arg_layout);

            match arg_layout {
                ArgLayout::RetPtr => unreachable!(),
                ArgLayout::IntStruct | ArgLayout::BinaryStruct => {}
                ArgLayout::ByvalPtr => {
                    let kind_id = Attribute::get_named_enum_kind_id("byval");
                    let byval = self
                        .context
                        .create_type_attribute(kind_id, self.lower_type(ty));
                    attributes.push((AttributeLoc::Param(params_types.len() as u32), byval));

                    let noundef_id = Attribute::get_named_enum_kind_id("noundef");
                    let byval = self.context.create_enum_attribute(noundef_id, 0);
                    attributes.push((AttributeLoc::Param(params_types.len() as u32), byval));
                }
                ArgLayout::Regular => {
                    let noundef_id = Attribute::get_named_enum_kind_id("noundef");
                    let byval = self.context.create_enum_attribute(noundef_id, 0);
                    attributes.push((AttributeLoc::Param(params_types.len() as u32), byval));
                }
                ArgLayout::Skipped => {
                    // Skip ZSTs and void params
                    continue;
                }
            }

            let llvm_ty = any_type_enum_to_basic_metadata_type_enum(llvm_ty);
            params_types.push(llvm_ty);
        }

        let fn_type = fn_type_from_any_type_enum(llvm_return_ty, &params_types, false);
        self.fn_ptr_types.borrow_mut().insert(
            fn_ptr_ty_key,
            FnPtrLayout {
                fn_type,
                attributes,
                args_layout,
            },
        );
        fn_type
    }

    fn lower_struct_type(&self, struct_key: StructKey) -> StructType<'ctx> {
        if let Some(TypeLayout { struct_ty, .. }) = self.structs_layouts.borrow().get(&struct_key) {
            return *struct_ty;
        }

        let _struct = &self.nir.structs[struct_key];
        let field_types = _struct
            .fields
            .iter()
            .map(|field| {
                let any_ty_enum = self.lower_type(field.typ);
                any_type_enum_to_basic_type_enum(any_ty_enum)
            })
            .collect::<Vec<_>>();

        let name = self.fmt_item_name(_struct.info);
        let struct_ty = self.context.opaque_struct_type(&name);
        struct_ty.set_body(&field_types, false);

        let mut fields = Vec::with_capacity(field_types.len());
        for i in 0..field_types.len() as u32 {
            let offset = self
                .machine
                .get_target_data()
                .offset_of_element(&struct_ty, i)
                .unwrap() as u32;
            fields.push(FieldLayout { offset });
        }

        let size = self.machine.get_target_data().get_store_size(&struct_ty) as u32;

        let align = self.machine.get_target_data().get_abi_alignment(&struct_ty);

        let struct_layout = TypeLayout {
            struct_ty,
            size,
            align,
            fields,
        };

        self.structs_layouts
            .borrow_mut()
            .insert(struct_key, struct_layout);

        struct_ty
    }

    fn lower_tuple_type(&self, tuple_type_key: TupleTypeKey) -> StructType<'ctx> {
        if let Some(TypeLayout { struct_ty, .. }) =
            self.tuples_layouts.borrow().get(&tuple_type_key)
        {
            return *struct_ty;
        }

        let tuple_type = &self.nir.tuple_types[tuple_type_key];

        let field_types = tuple_type
            .types
            .iter()
            .map(|&field_ty| {
                let any_ty_enum = self.lower_type(field_ty);
                any_type_enum_to_basic_type_enum(any_ty_enum)
            })
            .collect::<Vec<_>>();

        let struct_ty = self.context.struct_type(&field_types, false);

        let mut fields = Vec::with_capacity(field_types.len());
        for i in 0..field_types.len() as u32 {
            let offset = self
                .machine
                .get_target_data()
                .offset_of_element(&struct_ty, i)
                .unwrap() as u32;
            fields.push(FieldLayout { offset });
        }

        let size = self.machine.get_target_data().get_store_size(&struct_ty) as u32;

        let align = self.machine.get_target_data().get_abi_alignment(&struct_ty);

        let struct_layout = TypeLayout {
            struct_ty,
            size,
            align,
            fields,
        };

        self.tuples_layouts
            .borrow_mut()
            .insert(tuple_type_key, struct_layout);

        struct_ty
    }

    fn lower_array_type(&self, array_type_key: ArrayTypeKey) -> inkwell::types::ArrayType<'ctx> {
        let ArrayType {
            underlying_typ,
            size,
        } = self.nir.array_types[array_type_key];
        let underlying_ty = self.lower_type(underlying_typ);
        array_type_from_any_type_enum(underlying_ty, size)
    }

    fn lower_fns_signatures(&mut self) {
        for _fn in self.nir.fns.iter() {
            let name = if _fn.info.id_key == IdKey::MAIN
                && self.nir.files_to_pkgs[_fn.info.file_key] == PkgKey::TOP
            {
                format!("main")
            } else {
                self.fmt_item_name(_fn.info)
            };

            let Type::FnPtr(fn_ptr_type) = self.nir.types[_fn.fn_ptr_type] else {
                unreachable!()
            };
            let fn_type = self.lower_fn_ptr_type(fn_ptr_type);
            let llvm_fn = self.module.add_function(&name, fn_type, None);

            for &(attr_loc, attr_kind) in &self.fn_ptr_types.borrow()[&fn_ptr_type].attributes {
                llvm_fn.add_attribute(attr_loc, attr_kind);
            }

            self.llvm_fns.push(llvm_fn);
        }
    }

    fn lower_fns_bodies(&self) {
        for (fn_key, _fn) in self.nir.fns.iter_enumerated() {
            self.llvm_temps_counter.set(0);
            self.basic_blocks.borrow_mut().clear();
            self.args.borrow_mut().clear();
            self.locals.borrow_mut().clear();
            self.temps.borrow_mut().clear();

            let cfg = &_fn.cfg;
            let llvm_fn = self.llvm_fns[fn_key];
            let entry_bb = self.context.append_basic_block(llvm_fn, "entry");

            // Append all basic blocks
            for &bb_key in cfg.basic_blocks.keys() {
                if bb_key == BasicBlockKey::START_BASIC_BLOCK {
                    self.basic_blocks.borrow_mut().insert(bb_key, entry_bb);
                } else if bb_key != BasicBlockKey::END_BASIC_BLOCK {
                    let llvm_bb = self
                        .context
                        .append_basic_block(llvm_fn, &format!("bb{}", bb_key.0));
                    self.basic_blocks.borrow_mut().insert(bb_key, llvm_bb);
                }
            }

            self.builder.position_at_end(entry_bb);
            self.lower_ret_ptr_and_args(fn_key, _fn);
            self.lower_locals(&cfg.bindings);
            // Position may be set to first arg store instruction, so move it to the end
            self.builder.position_at_end(entry_bb);
            self.lower_block_jmp(&cfg.basic_blocks[&BasicBlockKey::START_BASIC_BLOCK], cfg);

            // Lower basic blocks
            for (&bb_key, bb) in &cfg.basic_blocks {
                if bb_key == BasicBlockKey::START_BASIC_BLOCK
                    || bb_key == BasicBlockKey::END_BASIC_BLOCK
                {
                    continue;
                }
                self.builder
                    .position_at_end(self.basic_blocks.borrow()[&bb_key]);

                for stm in &bb.stms {
                    self.lower_stm(stm, cfg)
                }

                self.lower_block_jmp(bb, cfg);
            }
        }
    }

    fn lower_ret_ptr_and_args(&self, fn_key: FnKey, _fn: &Fn) {
        let entry_bb = self.builder.get_insert_block().unwrap();

        let Type::FnPtr(fn_ptr_type_key) = self.nir.types[_fn.fn_ptr_type] else {
            unreachable!()
        };

        let fn_type = self.fn_ptr_types.borrow()[&fn_ptr_type_key].fn_type;
        let fn_value = self.llvm_fns[fn_key];

        let args_layout = &self.fn_ptr_types.borrow()[&fn_ptr_type_key].args_layout;
        let has_ret_ptr = matches!(args_layout.first(), Some(ArgLayout::RetPtr));
        let mut args_layout_iter = args_layout.iter().enumerate();
        let mut llvm_params_types_iter = fn_type.get_param_types().into_iter().enumerate();
        let mut first_store = None;

        let ret_ptr = if let Some(return_type) = fn_type.get_return_type() {
            // No need for array allocation is it will be lowered either to a pointer or a struct
            Some(self.builder.build_alloca(return_type, "ret_ptr").unwrap())
        } else if has_ret_ptr {
            args_layout_iter = args_layout[1..].iter().enumerate();
            llvm_params_types_iter.next();
            Some(fn_value.get_first_param().unwrap().into_pointer_value())
        } else {
            None
        };

        self.ret_ptr.set(ret_ptr);

        for (i, arg_layout) in args_layout_iter {
            match arg_layout {
                ArgLayout::Regular => {
                    let arg_key = ArgKey::from(i);
                    let (llvm_idx, llvm_ty) = llvm_params_types_iter.next().unwrap();

                    let arg_ptr = self
                        .builder
                        .build_alloca(llvm_ty, &format!("arg{}", i))
                        .unwrap();

                    self.args.borrow_mut().insert(arg_key, arg_ptr);
                    self.builder.position_at_end(entry_bb);
                    let _ = self
                        .builder
                        .build_store(arg_ptr, fn_value.get_nth_param(llvm_idx as u32).unwrap());

                    if first_store.is_none() {
                        first_store = entry_bb.get_last_instruction();
                    }

                    self.builder.position_before(&first_store.unwrap());
                }
                ArgLayout::IntStruct | ArgLayout::BinaryStruct => {
                    let arg_key = ArgKey::from(i);
                    let (llvm_idx, llvm_lowered_ty) = llvm_params_types_iter.next().unwrap();
                    let nir_ty = _fn.args[arg_key].typ;
                    let llvm_ty = any_type_enum_to_basic_type_enum(self.lower_type(nir_ty));
                    let dest_align = self.get_type_align(nir_ty);
                    let src_align = self
                        .machine
                        .get_target_data()
                        .get_abi_alignment(&llvm_lowered_ty);
                    let ty_size = self
                        .context
                        .i64_type()
                        .const_int(self.get_type_size(nir_ty) as u64, false);

                    let arg_ptr = self
                        .builder
                        .build_alloca(llvm_ty, &format!("arg{}", i))
                        .unwrap();

                    self.args.borrow_mut().insert(arg_key, arg_ptr);

                    let lowered_arg_ptr = self
                        .builder
                        .build_alloca(llvm_lowered_ty, &format!("lowered_arg{}", i))
                        .unwrap();

                    self.builder.position_at_end(entry_bb);

                    let _ = self.builder.build_store(
                        lowered_arg_ptr,
                        fn_value.get_nth_param(llvm_idx as u32).unwrap(),
                    );

                    if first_store.is_none() {
                        first_store = entry_bb.get_last_instruction();
                    }

                    let _ = self.builder.build_memcpy(
                        arg_ptr,
                        dest_align,
                        lowered_arg_ptr,
                        src_align,
                        ty_size,
                    );

                    self.builder.position_before(&first_store.unwrap());
                }
                ArgLayout::ByvalPtr => {
                    let arg_key = ArgKey::from(i);
                    let (llvm_idx, _) = llvm_params_types_iter.next().unwrap();
                    let arg_ptr = fn_value
                        .get_nth_param(llvm_idx as u32)
                        .unwrap()
                        .into_pointer_value();
                    self.args.borrow_mut().insert(arg_key, arg_ptr);
                }
                ArgLayout::RetPtr | ArgLayout::Skipped => {}
            }
        }

        if let Some(first_store) = first_store {
            // This will allocate locals after top allocas
            self.builder.position_before(&first_store);
        }
    }

    fn lower_locals(&self, bindings: &TiSlice<BindingKey, Binding>) {
        for (key, binding) in bindings.iter_enumerated() {
            let llvm_ty = self.lower_type(binding.typ);
            let name = format!("loc{}", key.0);
            let ptr_value = match llvm_ty {
                AnyTypeEnum::ArrayType(array_type) => self.builder.build_array_alloca(
                    array_type.get_element_type(),
                    self.context
                        .i64_type()
                        .const_int(array_type.len() as u64, false),
                    &name,
                ),
                AnyTypeEnum::FloatType(float_type) => self.builder.build_alloca(float_type, &name),
                AnyTypeEnum::IntType(int_type) => self.builder.build_alloca(int_type, &name),
                AnyTypeEnum::PointerType(ptr_type) => self.builder.build_alloca(ptr_type, &name),
                AnyTypeEnum::StructType(struct_ty) => self.builder.build_alloca(struct_ty, &name),
                AnyTypeEnum::FunctionType(function_type) => self
                    .builder
                    .build_alloca(ptr_type_from_fn_type(function_type), &name),
                AnyTypeEnum::VectorType(vector_type) => todo!(),
                AnyTypeEnum::VoidType(void_type) => continue,
            }
            .unwrap();
            self.locals.borrow_mut().insert(key, ptr_value);
        }
    }

    fn lower_block_jmp(&self, bb: &crate::BasicBlock, cfg: &CFG) {
        if let Some(branch_key) = bb.conditional_goto {
            let branch = &cfg.branches[&branch_key];
            let BranchKind::If(operand) = branch.kind else {
                unreachable!()
            };
            let else_branch = &cfg.branches[&bb.goto.unwrap()];

            if branch.to == BasicBlockKey::END_BASIC_BLOCK
                || else_branch.to == BasicBlockKey::END_BASIC_BLOCK
            {
                self.check_or_add_void_return();
                return;
            }

            let condition = self.lower_operand(&operand, &cfg).into_int_value();

            let then_bb = self.basic_blocks.borrow()[&branch.to];
            let else_bb = self.basic_blocks.borrow()[&else_branch.to];

            let _ = self
                .builder
                .build_conditional_branch(condition, then_bb, else_bb);
        } else {
            let branch = &cfg.branches[&bb.goto.unwrap()];
            if branch.to == BasicBlockKey::END_BASIC_BLOCK {
                self.check_or_add_void_return();
                return;
            }
            let _ = self
                .builder
                .build_unconditional_branch(self.basic_blocks.borrow()[&branch.to]);
        }
    }

    fn check_or_add_void_return(&self) {
        // If there is no return, it should return void
        let last_instr = self
            .builder
            .get_insert_block()
            .and_then(|block| block.get_last_instruction());

        let is_return = last_instr
            .map(|instr| instr.get_opcode() == InstructionOpcode::Return)
            .unwrap_or(false);

        if !is_return {
            let _ = self.builder.build_return(None);
        }
    }

    fn lower_stm(&self, stm: &Stm, cfg: &CFG) {
        match stm {
            Stm::Assign { lhs: _, rhs, typ } if self.get_type_size(*typ) == 0 => {
                let RValue::Call { on, args } = rhs else {
                    return;
                };

                self.lower_call_rvalue(on, &args, cfg);
            }
            Stm::Assign { lhs, rhs, typ } if self.is_agg_type(*typ) => {
                self.lower_assign_stm_agg_typ(*lhs, rhs, *typ, cfg)
            }
            Stm::Assign { lhs, rhs, typ: _ } => self.lower_assign_stm(*lhs, rhs, cfg),
            Stm::Phi { lhs, cases, typ } => {
                let LValueKind::Temp(temp_key) = cfg.lvalues[*lhs].kind else {
                    unreachable!()
                };
                let any_type = self.lower_type(*typ);
                let basic_type = any_type_enum_to_basic_type_enum(any_type);
                let phi = self
                    .builder
                    .build_phi(basic_type, &format!("tmp{}", temp_key.0))
                    .unwrap();
                for (bb_key, op_kind) in cases {
                    let bb = self.basic_blocks.borrow()[&bb_key];
                    let op = self.lower_operand_kind(*op_kind, cfg);
                    let op = any_value_as_basic_value(op).unwrap();
                    phi.add_incoming(&[(&op, bb)])
                }
            }
            Stm::Return { rvalue: _, typ } if self.get_type_size(*typ) == 0 => {
                let _ = self.builder.build_return(None);
            }
            Stm::Return { rvalue, typ } if self.is_agg_type(*typ) => {
                let ret_ptr = self.ret_ptr.get().unwrap();
                self.lower_rvalue_agg_type(ret_ptr, rvalue, *typ, cfg);
                let size = self.get_type_size(*typ);
                if size > 16 {
                    return;
                }

                let llvm_lowered_ty =
                    any_type_enum_to_basic_type_enum(self.lower_param_type(*typ).0);

                let dest_align = self
                    .machine
                    .get_target_data()
                    .get_abi_alignment(&llvm_lowered_ty);
                let src_align = self.get_type_align(*typ);
                let ty_size = self.context.i64_type().const_int(size as u64, false);

                let abi_ret_ptr = self.builder.build_alloca(llvm_lowered_ty, "").unwrap();
                let _ =
                    self.builder
                        .build_memcpy(abi_ret_ptr, dest_align, ret_ptr, src_align, ty_size);
                let value = self
                    .builder
                    .build_load(llvm_lowered_ty, abi_ret_ptr, "")
                    .unwrap();
                let _ = self.builder.build_return(Some(&value));
            }
            Stm::Return { rvalue, typ: _ } => {
                let rvalue = self.lower_rvalue(rvalue, &self.new_llvm_temp(), cfg);
                let _ = self
                    .builder
                    .build_return(Some(&any_value_as_basic_value(rvalue).unwrap()));
            }
            Stm::Drop(lvalue_key) => todo!(),
        }
    }

    fn lower_assign_stm_agg_typ(&self, lhs: LValueKey, rhs: &RValue, typ: TypeKey, cfg: &CFG) {
        let ptr = if let LValueKind::Temp(temp_key) = cfg.lvalues[lhs].kind {
            let llvm_ty = self.lower_type(typ);
            let name = format!("tmp{}", temp_key.0);

            let temp_ptr = if let AnyTypeEnum::ArrayType(array_ty) = llvm_ty {
                let len = self
                    .context
                    .i64_type()
                    .const_int(array_ty.len() as u64, false);
                self.builder
                    .build_array_alloca(array_ty, len, &name)
                    .unwrap()
            } else {
                self.builder
                    .build_alloca(any_type_enum_to_basic_type_enum(llvm_ty), &name)
                    .unwrap()
            };
            let temp = temp_ptr.as_any_value_enum();
            self.temps.borrow_mut().insert(temp_key, temp);
            temp_ptr
        } else {
            self.lower_lvalue_to_ptr(lhs, cfg)
        };

        self.lower_rvalue_agg_type(ptr, rhs, typ, cfg)
    }

    fn lower_assign_stm(&self, lhs: LValueKey, rhs: &RValue, cfg: &CFG) {
        if let LValueKind::Temp(temp_key) = cfg.lvalues[lhs].kind {
            let name = format!("tmp{}", temp_key.0);
            let temp = self.lower_rvalue(rhs, &name, cfg);
            self.temps.borrow_mut().insert(temp_key, temp);
        } else {
            let lvalue = self.lower_lvalue_to_ptr(lhs, cfg);
            let rvalue = self.lower_rvalue(rhs, &self.new_llvm_temp(), cfg);
            let rvalue = any_value_as_basic_value(rvalue).unwrap();
            let _ = self.builder.build_store(lvalue, rvalue);
        }
    }

    #[inline]
    fn lower_operand(&self, operand: &Operand, cfg: &CFG) -> AnyValueEnum<'ctx> {
        self.lower_operand_kind(operand.kind, cfg)
    }

    fn lower_operand_kind(&self, kind: OperandKind, cfg: &CFG) -> AnyValueEnum<'ctx> {
        match kind {
            OperandKind::LValue(lvalue_key) => self.lower_lvalue(lvalue_key, cfg),
            OperandKind::Const(Const::Unit) => unreachable!(),
            OperandKind::Const(Const::I(n)) => {
                AnyValueEnum::IntValue(self.isize_type().const_int(n as u64, true))
            }
            OperandKind::Const(Const::I1(n)) => {
                AnyValueEnum::IntValue(self.context.i8_type().const_int(n as u64, true))
            }
            OperandKind::Const(Const::I2(n)) => {
                AnyValueEnum::IntValue(self.context.i16_type().const_int(n as u64, true))
            }
            OperandKind::Const(Const::I4(n)) => {
                AnyValueEnum::IntValue(self.context.i32_type().const_int(n as u64, true))
            }
            OperandKind::Const(Const::I8(n)) => {
                AnyValueEnum::IntValue(self.context.i64_type().const_int(n as u64, true))
            }
            OperandKind::Const(Const::U(n)) => {
                AnyValueEnum::IntValue(self.isize_type().const_int(n as u64, false))
            }
            OperandKind::Const(Const::U1(n)) => {
                AnyValueEnum::IntValue(self.context.i8_type().const_int(n as u64, false))
            }
            OperandKind::Const(Const::U2(n)) => {
                AnyValueEnum::IntValue(self.context.i16_type().const_int(n as u64, false))
            }
            OperandKind::Const(Const::U4(n)) => {
                AnyValueEnum::IntValue(self.context.i32_type().const_int(n as u64, false))
            }
            OperandKind::Const(Const::U8(n)) => {
                AnyValueEnum::IntValue(self.context.i64_type().const_int(n as u64, false))
            }
            OperandKind::Const(Const::Bool(n)) => {
                AnyValueEnum::IntValue(self.context.i8_type().const_int(n as u64, false))
            }
            OperandKind::Const(Const::Char(n)) => {
                AnyValueEnum::IntValue(self.context.i32_type().const_int(n as u64, false))
            }
            OperandKind::Const(Const::F4(n)) => {
                AnyValueEnum::FloatValue(self.context.f32_type().const_float(n as f64))
            }
            OperandKind::Const(Const::F8(n)) => {
                AnyValueEnum::FloatValue(self.context.f64_type().const_float(n as f64))
            }
            OperandKind::Const(Const::Str(str_key)) => {
                AnyValueEnum::PointerValue(self.llvm_str_pool[str_key])
            }
            OperandKind::Const(Const::Fn(fn_key)) => {
                AnyValueEnum::FunctionValue(self.llvm_fns[fn_key])
            }
        }
    }

    fn lower_rvalue_agg_type(
        &self,
        dest_ptr: PointerValue<'ctx>,
        rvalue: &RValue,
        typ: TypeKey,
        cfg: &CFG,
    ) {
        let align = self.get_type_align(typ);
        let size = self
            .context
            .i64_type()
            .const_int(self.get_type_size(typ) as u64, false);
        match rvalue {
            RValue::Use(Operand {
                kind: OperandKind::LValue(src),
                ..
            }) => {
                let src_ptr = self.lower_lvalue_to_ptr(*src, cfg);
                let _ = self
                    .builder
                    .build_memcpy(dest_ptr, align, src_ptr, align, size);
            }
            RValue::Call { on, args } => self.lower_call_rvalue_agg_type(dest_ptr, on, &args, cfg),
            RValue::ArrayRepeated { repeated, size } => {
                struct OperandIter<'a> {
                    repeated: &'a Operand,
                    count: u32,
                    size: u32,
                }
                impl<'a> Iterator for OperandIter<'a> {
                    type Item = &'a Operand;

                    fn next(&mut self) -> Option<Self::Item> {
                        if self.count < self.size - 1 {
                            self.count += 1;
                            Some(self.repeated)
                        } else {
                            None
                        }
                    }
                }
                let iter = OperandIter {
                    repeated,
                    size: *size,
                    count: 0,
                };
                self.lower_array_rvalue(dest_ptr, typ, repeated.typ, iter, cfg)
            }
            // Size is not zero, as it called from assign stm on non zero type
            // So it has at least one element
            RValue::ArrayElements(elements) => {
                self.lower_array_rvalue(dest_ptr, typ, elements[0].typ, elements.iter(), cfg)
            }
            RValue::Tuple(types) => {
                let Type::Tuple(tuple_type_key) = self.nir.types[typ] else {
                    unreachable!()
                };
                let struct_ty = self.tuples_layouts.borrow()[&tuple_type_key].struct_ty;
                self.lower_struct_rvalue(
                    dest_ptr,
                    struct_ty,
                    types.iter().enumerate().map(|(i, &t)| (i as u32, t)),
                    cfg,
                )
            }
            RValue::Struct { struct_key, fields } => {
                let struct_ty = self.structs_layouts.borrow()[struct_key].struct_ty;
                self.lower_struct_rvalue(
                    dest_ptr,
                    struct_ty,
                    fields.iter().map(|(i, t)| (*i, *t)),
                    cfg,
                )
            }
            _ => unreachable!(),
        };
    }

    fn lower_rvalue(&self, rvalue: &RValue, name: &str, cfg: &CFG) -> AnyValueEnum<'ctx> {
        match rvalue {
            RValue::Use(operand) => self.lower_operand(operand, cfg),
            RValue::Ref(lvalue_key) | RValue::RefMut(lvalue_key) => self
                .lower_lvalue_to_ptr(*lvalue_key, cfg)
                .as_any_value_enum(),
            RValue::Cast { val, to } => todo!(),
            RValue::BinOp { op, lhs, rhs } => self.lower_bin_op_rvalue(*op, lhs, rhs, name, cfg),
            RValue::UnaryOp { op, operand } => self.lower_unary_op_rvalue(*op, operand, name, cfg),
            RValue::Call { on, args } => self.lower_call_rvalue(on, &args, cfg),
            _ => unreachable!(),
        }
    }

    fn lower_array_rvalue<'a>(
        &self,
        dest_ptr: PointerValue,
        array_type_key: TypeKey,
        element_type_key: TypeKey,
        elements: impl Iterator<Item = &'a Operand>,
        cfg: &CFG,
    ) {
        let llvm_array_ty = self.lower_type(array_type_key);

        if self.is_agg_type(element_type_key) {
            let align = self.get_type_align(element_type_key);
            let size = self.get_type_size(element_type_key);
            let ty_size = self.context.i64_type().const_int(size as u64, false);

            for (i, element) in elements.enumerate() {
                let element_ptr = unsafe {
                    self.builder
                        .build_gep(
                            any_type_enum_to_basic_type_enum(llvm_array_ty),
                            dest_ptr,
                            &[self.context.i64_type().const_int(i as u64, false)],
                            "",
                        )
                        .unwrap()
                };

                let OperandKind::LValue(field_lvalue) = element.kind else {
                    unreachable!()
                };

                let src_ptr = self.lower_lvalue_to_ptr(field_lvalue, cfg);

                let _ = self
                    .builder
                    .build_memcpy(element_ptr, align, src_ptr, align, ty_size);
            }
        } else {
            for (i, element) in elements.enumerate() {
                let element_ptr = unsafe {
                    self.builder
                        .build_gep(
                            any_type_enum_to_basic_type_enum(llvm_array_ty),
                            dest_ptr,
                            &[self.context.i64_type().const_int(i as u64, false)],
                            "",
                        )
                        .unwrap()
                };

                let element = any_value_as_basic_value(self.lower_operand(element, cfg)).unwrap();

                let _ = self.builder.build_store(element_ptr, element);
            }
        }
    }

    fn lower_struct_rvalue<'a>(
        &self,
        dest_ptr: PointerValue,
        struct_ty: StructType,
        fields: impl Iterator<Item = (u32, Operand)>,
        cfg: &CFG,
    ) {
        for (i, field) in fields {
            let size = self.get_type_size(field.typ);

            if size == 0 {
                continue;
            }

            let field_ptr = self
                .builder
                .build_struct_gep(struct_ty.as_basic_type_enum(), dest_ptr, i, "")
                .unwrap();

            if self.is_agg_type(field.typ) {
                let align = self.get_type_align(field.typ);

                let OperandKind::LValue(field_lvalue) = field.kind else {
                    unreachable!()
                };

                let src_ptr = self.lower_lvalue_to_ptr(field_lvalue, cfg);

                let _ = self.builder.build_memcpy(
                    field_ptr,
                    align,
                    src_ptr,
                    align,
                    self.context.i64_type().const_int(size as u64, false),
                );
            } else {
                let llvm_field = any_value_as_basic_value(self.lower_operand(&field, cfg)).unwrap();
                let _ = self.builder.build_store(field_ptr, llvm_field);
            }
        }
    }

    fn lower_call_rvalue_agg_type(
        &self,
        dest_ptr: PointerValue<'ctx>,
        on: &Operand,
        args: &[Operand],
        cfg: &CFG,
    ) {
        let llvm_on = self.lower_operand(on, cfg);

        let Type::FnPtr(fn_ptr_type_key) = self.nir.types[on.typ] else {
            unreachable!()
        };

        let fn_type = self.fn_ptr_types.borrow()[&fn_ptr_type_key].fn_type;
        let args_layout = &self.fn_ptr_types.borrow()[&fn_ptr_type_key].args_layout;
        let has_ret_ptr = matches!(args_layout.first(), Some(ArgLayout::RetPtr));
        let mut args_layout_iter = args_layout.iter().enumerate();
        let mut llvm_params_types_iter = fn_type.get_param_types().into_iter().enumerate();
        let mut llvm_args;
        if has_ret_ptr {
            llvm_params_types_iter.next();
            args_layout_iter = args_layout[1..].iter().enumerate();
            llvm_args = Vec::with_capacity(args.len() + 1);
            llvm_args.push(BasicMetadataValueEnum::PointerValue(dest_ptr));
        } else {
            llvm_args = Vec::with_capacity(args.len());
        }

        let call_site_value = self.lower_call_args(
            llvm_on,
            fn_ptr_type_key,
            fn_type,
            args,
            llvm_args,
            args_layout_iter,
            llvm_params_types_iter,
            cfg,
        );

        if has_ret_ptr {
            return;
        }

        let llvm_return_type = fn_type.get_return_type().unwrap();

        let abi_ptr = self.builder.build_alloca(llvm_return_type, "").unwrap();

        let _ = self
            .builder
            .build_store(abi_ptr, any_value_as_basic_value(call_site_value).unwrap());

        let nir_return_type = self.nir.fn_ptr_types[fn_ptr_type_key].return_type;
        let dest_align = self.get_type_align(nir_return_type);
        let src_align = self
            .machine
            .get_target_data()
            .get_abi_alignment(&llvm_return_type);
        let ty_size = self
            .context
            .i64_type()
            .const_int(self.get_type_size(nir_return_type) as u64, false);

        let _ = self
            .builder
            .build_memcpy(dest_ptr, dest_align, abi_ptr, src_align, ty_size);
    }

    fn lower_bin_op_rvalue(
        &self,
        op: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        name: &str,
        cfg: &CFG,
    ) -> AnyValueEnum<'ctx> {
        let builder = &self.builder;

        let llvm_lhs = self.lower_operand(lhs, cfg);

        if let AnyValueEnum::FloatValue(lhs) = llvm_lhs {
            let rhs = self.lower_operand(rhs, cfg).into_float_value();

            macro_rules! build_cmp {
                ($build_op: ident) => {
                    builder
                        .build_float_compare(FloatPredicate::$build_op, lhs, rhs, name)
                        .unwrap()
                        .as_any_value_enum()
                };
            }

            macro_rules! build {
                ($build_method: ident) => {
                    builder
                        .$build_method(lhs, rhs, name)
                        .unwrap()
                        .as_any_value_enum()
                };
            }

            return match op {
                BinOp::EqualEqual => build_cmp!(OEQ),
                BinOp::NotEqual => build_cmp!(ONE),
                BinOp::GE => build_cmp!(OGE),
                BinOp::GT => build_cmp!(OGT),
                BinOp::LE => build_cmp!(OLE),
                BinOp::LT => build_cmp!(OLT),
                BinOp::Plus => build!(build_float_add),
                BinOp::Minus => build!(build_float_sub),
                BinOp::Times => build!(build_float_mul),
                BinOp::Div => build!(build_float_div),
                BinOp::Mod => build!(build_float_rem),
                _ => unreachable!(),
            };
        }

        let is_unsigned = matches!(
            self.nir.types[lhs.typ],
            Type::U | Type::U1 | Type::U2 | Type::U4 | Type::U8
        );

        let lhs = llvm_lhs.into_int_value();
        let rhs = self.lower_operand(rhs, cfg).into_int_value();

        macro_rules! build_cmp {
            ($build_op: ident) => {
                builder
                    .build_int_compare(IntPredicate::$build_op, lhs, rhs, name)
                    .unwrap()
                    .as_any_value_enum()
            };
        }

        macro_rules! build {
            ($build_method: ident) => {
                builder
                    .$build_method(lhs, rhs, name)
                    .unwrap()
                    .as_any_value_enum()
            };
        }

        match op {
            BinOp::EqualEqual => build_cmp!(EQ),
            BinOp::NotEqual => build_cmp!(NE),
            BinOp::GE if is_unsigned => build_cmp!(UGE),
            BinOp::GT if is_unsigned => build_cmp!(UGT),
            BinOp::LE if is_unsigned => build_cmp!(ULE),
            BinOp::LT if is_unsigned => build_cmp!(ULT),
            BinOp::GE => build_cmp!(SGE),
            BinOp::GT => build_cmp!(SGT),
            BinOp::LE => build_cmp!(SLE),
            BinOp::LT => build_cmp!(SLT),
            BinOp::Shr => builder
                .build_right_shift(lhs, rhs, false, name)
                .unwrap()
                .as_any_value_enum(),
            BinOp::Shl => build!(build_left_shift),
            BinOp::BOr => build!(build_or),
            BinOp::Xor => build!(build_xor),
            BinOp::BAnd => build!(build_and),
            BinOp::Plus => build!(build_int_add),
            BinOp::Minus => build!(build_int_sub),
            BinOp::Times => build!(build_int_mul),
            BinOp::Div if is_unsigned => build!(build_int_unsigned_div),
            BinOp::Mod if is_unsigned => build!(build_int_unsigned_rem),
            BinOp::Div => build!(build_int_signed_div),
            BinOp::Mod => build!(build_int_signed_rem),
        }
    }

    fn lower_unary_op_rvalue(
        &self,
        op: UnaryOp,
        operand: &Operand,
        name: &str,
        cfg: &CFG,
    ) -> AnyValueEnum<'ctx> {
        match op {
            UnaryOp::LNot => {
                let lhs = self.lower_operand(operand, cfg).into_int_value();
                let rhs = lhs.get_type().const_int(1, false);
                self.builder
                    .build_xor(lhs, rhs, name)
                    .unwrap()
                    .as_any_value_enum()
            }
            UnaryOp::BNot => {
                let operand = self.lower_operand(operand, cfg).into_int_value();
                self.builder
                    .build_not(operand, name)
                    .unwrap()
                    .as_any_value_enum()
            }
            UnaryOp::Minus => {
                if let AnyValueEnum::FloatValue(operand) = self.lower_operand(operand, cfg) {
                    self.builder
                        .build_float_neg(operand, name)
                        .unwrap()
                        .as_any_value_enum()
                } else if let AnyValueEnum::IntValue(operand) = self.lower_operand(operand, cfg) {
                    self.builder
                        .build_int_neg(operand, name)
                        .unwrap()
                        .as_any_value_enum()
                } else {
                    unreachable!()
                }
            }
        }
    }

    fn lower_call_rvalue(&self, on: &Operand, args: &[Operand], cfg: &CFG) -> AnyValueEnum<'ctx> {
        let llvm_on = self.lower_operand(on, cfg);

        let Type::FnPtr(fn_ptr_type_key) = self.nir.types[on.typ] else {
            unreachable!()
        };

        let fn_type = self.fn_ptr_types.borrow()[&fn_ptr_type_key].fn_type;
        let args_layout = &self.fn_ptr_types.borrow()[&fn_ptr_type_key].args_layout;
        let args_layout_iter = args_layout.iter().enumerate();
        let llvm_params_types_iter = fn_type.get_param_types().into_iter().enumerate();
        let llvm_args = Vec::with_capacity(args.len());

        self.lower_call_args(
            llvm_on,
            fn_ptr_type_key,
            fn_type,
            args,
            llvm_args,
            args_layout_iter,
            llvm_params_types_iter,
            cfg,
        )
    }

    fn lower_call_args<'a>(
        &self,
        llvm_on: AnyValueEnum<'ctx>,
        fn_ptr_type_key: FnPtrTypeKey,
        fn_type: FunctionType<'ctx>,
        args: &[Operand],
        mut llvm_args: Vec<BasicMetadataValueEnum<'ctx>>,
        args_layout_iter: impl Iterator<Item = (usize, &'a ArgLayout)>,
        mut llvm_params_types_iter: impl Iterator<Item = (usize, BasicTypeEnum<'ctx>)>,
        cfg: &CFG,
    ) -> AnyValueEnum<'ctx> {
        for (i, arg_layout) in args_layout_iter {
            match arg_layout {
                ArgLayout::RetPtr => unreachable!(),
                ArgLayout::ByvalPtr | ArgLayout::IntStruct | ArgLayout::BinaryStruct => {
                    let (_, llvm_lowered_ty) = llvm_params_types_iter.next().unwrap();
                    let Operand {
                        kind: OperandKind::LValue(arg_lvalue),
                        typ: arg_typ,
                    } = args[i]
                    else {
                        unreachable!()
                    };

                    let arg_ptr = self.lower_lvalue_to_ptr(arg_lvalue, cfg);

                    let dest_align = self.get_type_align(arg_typ);
                    let src_align = self
                        .machine
                        .get_target_data()
                        .get_abi_alignment(&llvm_lowered_ty);
                    let ty_size = self
                        .context
                        .i64_type()
                        .const_int(self.get_type_size(arg_typ) as u64, false);

                    let abi_ptr = self.builder.build_alloca(llvm_lowered_ty, "").unwrap();

                    let _ = self
                        .builder
                        .build_memcpy(abi_ptr, dest_align, arg_ptr, src_align, ty_size);

                    let llvm_arg = if let ArgLayout::ByvalPtr = arg_layout {
                        abi_ptr.into()
                    } else {
                        self.builder
                            .build_load(llvm_lowered_ty, abi_ptr, "")
                            .unwrap()
                            .into()
                    };

                    llvm_args.push(llvm_arg);
                }
                ArgLayout::Regular => {
                    llvm_params_types_iter.next();
                    let arg = self.lower_operand(&args[i], cfg);
                    llvm_args.push(any_value_as_basic_metadata_value(arg));
                }
                ArgLayout::Skipped => {}
            }
        }

        let call_site_value = if let AnyValueEnum::FunctionValue(fn_value) = llvm_on {
            self.builder.build_direct_call(fn_value, &llvm_args, "")
        } else if let AnyValueEnum::PointerValue(fn_ptr_value) = llvm_on {
            self.builder
                .build_indirect_call(fn_type, fn_ptr_value, &llvm_args, "")
        } else {
            unreachable!()
        }
        .unwrap();

        for &(attr_loc, attr_kind) in &self.fn_ptr_types.borrow()[&fn_ptr_type_key].attributes {
            call_site_value.add_attribute(attr_loc, attr_kind);
        }

        call_site_value.as_any_value_enum()
    }

    fn lower_lvalue(&self, lvalue_key: LValueKey, cfg: &CFG) -> AnyValueEnum<'ctx> {
        let type_key = cfg.lvalues[lvalue_key].typ;
        if let LValueKind::Temp(temp_key) = cfg.lvalues[lvalue_key].kind {
            self.temps.borrow()[&temp_key]
        } else {
            let llvm_ptr = self.lower_lvalue_to_ptr(lvalue_key, cfg);
            self.add_load_instr(type_key, llvm_ptr)
        }
    }

    fn lower_lvalue_to_ptr(&self, lvalue_key: LValueKey, cfg: &CFG) -> PointerValue<'ctx> {
        match cfg.lvalues[lvalue_key].kind {
            LValueKind::Binding(binding_key) => self.locals.borrow()[&binding_key],
            LValueKind::Static(static_key) => self.llvm_statics[static_key],
            LValueKind::Arg(arg_key) => self.args.borrow()[&arg_key],
            LValueKind::Temp(temp_key) => self.temps.borrow()[&temp_key].into_pointer_value(),
            LValueKind::Deref(lvalue_key) | LValueKind::MutDeref(lvalue_key) => {
                // For dereference, we already have the pointer, just use it
                self.lower_lvalue(lvalue_key, cfg).into_pointer_value()
            }
            LValueKind::Field { on, idx }
            | LValueKind::MutField { on, idx }
            | LValueKind::TupleIdx { on, idx }
            | LValueKind::MutTupleIdx { on, idx } => {
                let type_key = cfg.lvalues[on].typ;
                let struct_ty = self.lower_type(type_key).into_struct_type();
                let llvm_on_ptr = self.lower_lvalue_to_ptr(on, cfg);
                let name = self.new_llvm_temp();
                let llvm_ptr = self
                    .builder
                    .build_struct_gep(struct_ty, llvm_on_ptr, idx, &name)
                    .unwrap();
                llvm_ptr
            }
            LValueKind::ArrayIdx { on, idx } | LValueKind::MutArrayIdx { on, idx } => {
                let array_ptr = self.lower_lvalue_to_ptr(on, cfg);
                let array_type_key = cfg.lvalues[on].typ;
                let llvm_array_ty = self.lower_type(array_type_key);
                let index = self.lower_lvalue(idx, cfg).into_int_value();
                unsafe {
                    self.builder
                        .build_gep(
                            any_type_enum_to_basic_type_enum(llvm_array_ty),
                            array_ptr,
                            &[index],
                            &self.new_llvm_temp(),
                        )
                        .unwrap()
                }
            }
            LValueKind::ArrayConstIdx { on, idx } | LValueKind::MutArrayConstIdx { on, idx } => {
                let array_ptr = self.lower_lvalue_to_ptr(on, cfg);
                let array_type_key = cfg.lvalues[on].typ;
                let llvm_array_ty = self.lower_type(array_type_key);
                unsafe {
                    self.builder
                        .build_gep(
                            any_type_enum_to_basic_type_enum(llvm_array_ty),
                            array_ptr,
                            &[self.context.i64_type().const_int(idx as u64, false)],
                            &self.new_llvm_temp(),
                        )
                        .unwrap()
                }
            }
        }
    }

    fn add_load_instr(
        &self,
        type_key: TypeKey,
        llvm_ptr: PointerValue<'ctx>,
    ) -> AnyValueEnum<'ctx> {
        let llvm_type = any_type_enum_to_basic_type_enum(self.lower_type(type_key));
        let pointee_name = self.new_llvm_temp();
        let pointee = self
            .builder
            .build_load(llvm_type, llvm_ptr, &pointee_name)
            .unwrap();
        pointee.as_any_value_enum()
    }
}
