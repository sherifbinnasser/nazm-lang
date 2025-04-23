mod fns;
mod operand;
mod rvalue;
mod stm;
mod types;
mod util;

use fns::*;
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
        // lower_string_consts will take the ownership of str_pool
        // So lower functions signatures first as extern functions may have string consts link names
        self.lower_fns_signatures();
        self.lower_string_consts();
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

            let global_slice = self.module.add_global(
                self.slice_type(),
                None,
                &format!(".str_slice{}", str_key.0),
            );
            let slice = self
                .context
                .const_struct(&[global.as_pointer_value().into(), str_len.into()], false);
            global_slice.set_initializer(&slice);

            self.llvm_str_pool.push(global_slice.as_pointer_value());
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
}
