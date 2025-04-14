use std::{
    cell::{Cell, Ref, RefCell},
    cmp::max,
};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    targets::{
        CodeModel, InitializationConfig, RelocMode, Target, TargetData, TargetMachine, TargetTriple,
    },
    types::{
        AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, IntType,
        StructType,
    },
    values::{AnyValue, AnyValueEnum, FunctionValue, InstructionOpcode, PointerValue},
    AddressSpace,
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
    llvm_temps: RefCell<Vec<String>>,
    fn_ptr_types: RefCell<HashMap<FnPtrTypeKey, FunctionType<'ctx>>>,
    structs_layouts: RefCell<HashMap<StructKey, TypeLayout<'ctx>>>,
    tuples_layouts: RefCell<HashMap<TupleTypeKey, TypeLayout<'ctx>>>,
    basic_blocks: RefCell<HashMap<BasicBlockKey, BasicBlock<'ctx>>>,
    locals: RefCell<HashMap<BindingKey, PointerValue<'ctx>>>,
    temps: RefCell<HashMap<TempKey, AnyValueEnum<'ctx>>>,
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

fn any_type_enum_to_basic_metadata_type_enum(ty: AnyTypeEnum) -> BasicMetadataTypeEnum {
    match ty {
        AnyTypeEnum::ArrayType(array_type) => BasicMetadataTypeEnum::ArrayType(array_type),
        AnyTypeEnum::FloatType(float_type) => BasicMetadataTypeEnum::FloatType(float_type),
        AnyTypeEnum::IntType(int_type) => BasicMetadataTypeEnum::IntType(int_type),
        AnyTypeEnum::PointerType(pointer_type) => BasicMetadataTypeEnum::PointerType(pointer_type),
        AnyTypeEnum::StructType(struct_type) => BasicMetadataTypeEnum::StructType(struct_type),
        AnyTypeEnum::VectorType(vector_type) => BasicMetadataTypeEnum::VectorType(vector_type),
        AnyTypeEnum::FunctionType(_) | AnyTypeEnum::VoidType(_) => {
            unreachable!()
        }
    }
}

fn any_type_enum_to_basic_type_enum(ty: AnyTypeEnum) -> BasicTypeEnum {
    match ty {
        AnyTypeEnum::ArrayType(array_type) => BasicTypeEnum::ArrayType(array_type),
        AnyTypeEnum::FloatType(float_type) => BasicTypeEnum::FloatType(float_type),
        AnyTypeEnum::IntType(int_type) => BasicTypeEnum::IntType(int_type),
        AnyTypeEnum::PointerType(pointer_type) => BasicTypeEnum::PointerType(pointer_type),
        AnyTypeEnum::StructType(struct_type) => BasicTypeEnum::StructType(struct_type),
        AnyTypeEnum::VectorType(vector_type) => BasicTypeEnum::VectorType(vector_type),
        AnyTypeEnum::FunctionType(_) | AnyTypeEnum::VoidType(_) => {
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
        AnyTypeEnum::FunctionType(function_type) => todo!(),
        AnyTypeEnum::StructType(struct_type) => todo!(),
        AnyTypeEnum::VectorType(vector_type) => todo!(),
    }
}

fn array_type_from_any_type_enum(ty: AnyTypeEnum, size: u32) -> inkwell::types::ArrayType {
    match ty {
        AnyTypeEnum::ArrayType(array_type) => array_type.array_type(size),
        AnyTypeEnum::FloatType(float_type) => float_type.array_type(size),
        AnyTypeEnum::IntType(int_type) => int_type.array_type(size),
        AnyTypeEnum::StructType(struct_type) => struct_type.array_type(size),
        AnyTypeEnum::PointerType(ptr_type) => ptr_type.array_type(size),
        AnyTypeEnum::FunctionType(function_type) => todo!(),
        AnyTypeEnum::VectorType(vector_type) => todo!(),
        AnyTypeEnum::VoidType(void_type) => todo!(),
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
            llvm_temps: RefCell::new(Vec::new()),
            fn_ptr_types: RefCell::new(HashMap::with_capacity(nir.fn_ptr_types.len())),
            structs_layouts: RefCell::new(HashMap::with_capacity(nir.structs.len())),
            tuples_layouts: RefCell::new(HashMap::with_capacity(nir.tuple_types.len())),
            basic_blocks: Default::default(),
            locals: Default::default(),
            temps: Default::default(),
            nir,
        }
    }

    pub fn lower(&mut self) {
        self.lower_string_consts();
        self.lower_fns_signatures();
        self.lower_fns_bodies();
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

    fn new_llvm_temp(&self) -> Ref<String> {
        let llvm_temps_counter = self.llvm_temps_counter.get();
        if llvm_temps_counter == self.llvm_temps.borrow().len() {
            self.llvm_temps
                .borrow_mut()
                .push(format!("llvm_tmp{}", llvm_temps_counter));
        }
        self.llvm_temps_counter.set(llvm_temps_counter + 1);
        let temps = self.llvm_temps.borrow();
        Ref::map(temps, |temps| &temps[llvm_temps_counter])
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
            Type::Unit => AnyTypeEnum::VoidType(self.context.void_type()),
            Type::I | Type::U => AnyTypeEnum::IntType(self.isize_type()),
            Type::Bool | Type::I1 | Type::U1 => AnyTypeEnum::IntType(self.context.i8_type()),
            Type::I2 | Type::U2 => AnyTypeEnum::IntType(self.context.i16_type()),
            Type::Char | Type::I4 | Type::U4 => AnyTypeEnum::IntType(self.context.i32_type()),
            Type::I8 | Type::U8 => AnyTypeEnum::IntType(self.context.i64_type()),
            Type::F4 => AnyTypeEnum::FloatType(self.context.f32_type()),
            Type::F8 => AnyTypeEnum::FloatType(self.context.f64_type()),
            Type::Struct(struct_key) => AnyTypeEnum::StructType(self.lower_struct_type(struct_key)),
            Type::Ptr(_) | Type::MutPtr(_) => {
                AnyTypeEnum::PointerType(self.context.ptr_type(AddressSpace::default()))
            }
            Type::FnPtr(fn_ptr_ty_key) => {
                AnyTypeEnum::FunctionType(self.lower_fn_ptr_type(fn_ptr_ty_key))
            }
            Type::Tuple(tuple_type_key) => {
                AnyTypeEnum::StructType(self.lower_tuple_type(tuple_type_key))
            }
            Type::Array(array_type_key) => {
                AnyTypeEnum::ArrayType(self.lower_array_type(array_type_key))
            }
            Type::Slice(_) | Type::MutSlice(_) => AnyTypeEnum::StructType(
                self.context.struct_type(
                    &[
                        self.context.ptr_type(AddressSpace::default()).into(),
                        self.context
                            .ptr_sized_int_type(&self.machine.get_target_data(), None)
                            .into(),
                    ],
                    false,
                ),
            ),
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }

    fn lower_fn_ptr_type(&self, fn_ptr_ty_key: FnPtrTypeKey) -> FunctionType<'ctx> {
        if let Some(fn_ty) = self.fn_ptr_types.borrow().get(&fn_ptr_ty_key) {
            return *fn_ty;
        }

        let params_len = self.nir.fn_ptr_types[fn_ptr_ty_key].params_types.len();
        let return_type = self.nir.fn_ptr_types[fn_ptr_ty_key].return_type;
        let mut llvm_return_ty = self.lower_type(return_type);

        let mut params_types = Vec::new();

        match self.nir.types[return_type] {
            Type::Struct(struct_key) => {
                let size = self.structs_layouts.borrow()[&struct_key].size;

                llvm_return_ty = if size <= 8 {
                    AnyTypeEnum::IntType(self.context.custom_width_int_type(size * 8))
                } else if size <= 16 {
                    let align = self.structs_layouts.borrow()[&struct_key].align;
                    let (class1, class2) = flatten_type(
                        &self.machine.get_target_data(),
                        any_type_enum_to_basic_type_enum(llvm_return_ty),
                        align,
                    );
                    let (class1, class2) = (
                        class1.to_llvm_type(&self.context),
                        class2.to_llvm_type(&self.context),
                    );
                    let struct_type = self
                        .context
                        .struct_type(&[class1.into(), class2.into()], false);
                    AnyTypeEnum::StructType(struct_type)
                } else {
                    params_types = Vec::with_capacity(params_len + 1);
                    let ptr_ty = self.context.ptr_type(AddressSpace::default());
                    params_types.push(BasicMetadataTypeEnum::PointerType(ptr_ty));
                    AnyTypeEnum::VoidType(self.context.void_type())
                };
            }
            Type::Slice(type_key) => todo!(),
            Type::MutSlice(type_key) => todo!(),
            Type::Array(array_type_key) => todo!(),
            Type::Tuple(tuple_type_key) => todo!(),
            Type::Lambda(lambda_type_key) => todo!(),
            _ => {
                params_types = Vec::with_capacity(params_len);
            }
        }

        for &ty in &self.nir.fn_ptr_types[fn_ptr_ty_key].params_types {
            let ty = any_type_enum_to_basic_metadata_type_enum(self.lower_type(ty));
            params_types.push(ty);
        }

        fn_type_from_any_type_enum(llvm_return_ty, &params_types, false)
    }

    fn lower_struct_type(&self, struct_key: StructKey) -> StructType<'ctx> {
        if let Some(TypeLayout { struct_ty, .. }) = self.structs_layouts.borrow().get(&struct_key) {
            return *struct_ty;
        }

        let _struct = &self.nir.structs[struct_key];
        let field_types = _struct
            .fields_order
            .iter()
            .map(|field_id| {
                let any_ty_enum = self.lower_type(_struct.fields_types[field_id]);
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
            let AnyTypeEnum::FunctionType(fn_type) = self.lower_type(_fn.fn_ptr_type) else {
                unreachable!()
            };
            let llvm_fn = self.module.add_function(&name, fn_type, None);
            self.llvm_fns.push(llvm_fn);
        }
    }

    fn lower_fns_bodies(&self) {
        for (fn_key, _fn) in self.nir.fns.iter_enumerated() {
            let cfg = &_fn.cfg;
            let llvm_fn = self.llvm_fns[fn_key];
            self.llvm_temps_counter.set(0);
            let entry_bb = self.context.append_basic_block(llvm_fn, "entry");

            self.lower_temps(&cfg.temps);

            // Append all basic blocks
            self.basic_blocks.borrow_mut().clear();
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

            // Lower basic blocks
            for (&bb_key, bb) in &cfg.basic_blocks {
                if bb_key == BasicBlockKey::START_BASIC_BLOCK {
                    self.builder.position_at_end(entry_bb);
                    self.lower_locals(&cfg.bindings);
                    self.lower_block_jmp(bb, cfg);
                    continue;
                } else if bb_key == BasicBlockKey::END_BASIC_BLOCK {
                    continue;
                }
                self.builder
                    .position_at_end(self.basic_blocks.borrow()[&bb_key]);
            }
        }
    }

    fn lower_temps(&self, temps: &TiSlice<TempKey, Temp>) {
        self.temps.borrow_mut().clear();
        for (key, temp) in temps.iter_enumerated() {
            let typ = self.lower_type(temp.typ);
        }
    }

    fn lower_locals(&self, bindings: &TiSlice<BindingKey, Binding>) {
        self.locals.borrow_mut().clear();
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
                AnyTypeEnum::FunctionType(function_type) => todo!(),
                AnyTypeEnum::VectorType(vector_type) => todo!(),
                AnyTypeEnum::VoidType(void_type) => todo!(),
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

            let AnyValueEnum::IntValue(condition) = self.lower_operand(&operand, &cfg) else {
                unreachable!("Bools should be lowered to i8 values")
            };

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

    #[inline]
    fn lower_operand(&self, operand: &Operand, cfg: &CFG) -> AnyValueEnum {
        self.lower_operand_kind(operand.kind, cfg)
    }

    fn lower_operand_kind(&self, kind: OperandKind, cfg: &CFG) -> AnyValueEnum {
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

    fn lower_lvalue(&self, lvalue_key: LValueKey, cfg: &CFG) -> AnyValueEnum<'ctx> {
        let type_key = cfg.lvalues[lvalue_key].typ;
        if let LValueKind::Arg(arg_key) = cfg.lvalues[lvalue_key].kind {
            todo!()
        } else if let LValueKind::Temp(temp_key) = cfg.lvalues[lvalue_key].kind {
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
            LValueKind::Arg(arg_key) => todo!(),
            LValueKind::Deref(lvalue_key) | LValueKind::MutDeref(lvalue_key) => {
                // For dereference, we already have the pointer, just use it
                let AnyValueEnum::PointerValue(llvm_ptr) = self.lower_lvalue(lvalue_key, cfg)
                else {
                    unreachable!()
                };
                llvm_ptr
            }
            LValueKind::Field { on, field_id } | LValueKind::MutField { on, field_id } => {
                todo!()
            }
            LValueKind::TupleIdx { on, idx } | LValueKind::MutTupleIdx { on, idx } => {
                let type_key = cfg.lvalues[lvalue_key].typ;
                let AnyTypeEnum::StructType(pointee_ty) = self.lower_type(type_key) else {
                    unreachable!()
                };
                let pointee_name = self.new_llvm_temp();
                let llvm_on_ptr = self.lower_lvalue_to_ptr(on, cfg);
                let llvm_ptr = self
                    .builder
                    .build_struct_gep(pointee_ty, llvm_on_ptr, idx, &pointee_name)
                    .unwrap();
                llvm_ptr
            }
            LValueKind::ArrayIdx { on, idx } | LValueKind::MutArrayIdx { on, idx } => todo!(),
            LValueKind::ArrayConstIdx { on, idx } | LValueKind::MutArrayConstIdx { on, idx } => {
                todo!()
            }
            LValueKind::Temp(temp_key) => {
                unreachable!("Temps don't have pointers to them, use lower_lvalue() instead")
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
