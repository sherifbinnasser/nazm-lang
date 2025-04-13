use std::cell::RefCell;

use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple},
    types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicTypeEnum, FunctionType, StructType},
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
    fn_ptr_types: RefCell<HashMap<FnPtrTypeKey, FunctionType<'ctx>>>,
    structs_layouts: RefCell<HashMap<StructKey, TypeLayout<'ctx>>>,
    tuples_layouts: RefCell<HashMap<TupleTypeKey, TypeLayout<'ctx>>>,
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
            fn_ptr_types: RefCell::new(HashMap::with_capacity(nir.fn_ptr_types.len())),
            structs_layouts: RefCell::new(HashMap::with_capacity(nir.structs.len())),
            tuples_layouts: RefCell::new(HashMap::with_capacity(nir.tuple_types.len())),
            nir,
        }
    }

    pub fn lower(&self) {
        self.lower_fns();
        self.module
            .print_to_file(&format!("{}.ll", self.module.get_name().to_str().unwrap()));
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

    fn lower_type(&self, type_key: TypeKey) -> AnyTypeEnum<'ctx> {
        match self.nir.types[type_key] {
            Type::Unit => AnyTypeEnum::VoidType(self.context.void_type()),
            Type::I | Type::U => AnyTypeEnum::IntType(
                self.context
                    .ptr_sized_int_type(&self.machine.get_target_data(), None),
            ),
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
            return fn_ty.clone();
        }

        let params_len = self.nir.fn_ptr_types[fn_ptr_ty_key].params_types.len();
        let return_type = self.nir.fn_ptr_types[fn_ptr_ty_key].return_type;
        let mut llvm_return_ty = self.lower_type(return_type);

        let mut params_types = Vec::new();

        match self.nir.types[return_type] {
            Type::Struct(struct_key) => {
                let TypeLayout { size, .. } = &self.structs_layouts.borrow()[&struct_key];

                if *size > 16 {
                    params_types = Vec::with_capacity(params_len + 1);
                    let ptr_ty = self.context.ptr_type(AddressSpace::default());
                    params_types.push(BasicMetadataTypeEnum::PointerType(ptr_ty));
                    llvm_return_ty = AnyTypeEnum::VoidType(self.context.void_type());
                } else if *size > 8 {
                } else {
                }
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
            return struct_ty.clone();
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
            struct_ty: struct_ty.clone(),
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
            return struct_ty.clone();
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
            struct_ty: struct_ty.clone(),
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

    fn lower_fns(&self) {
        // Lower fns signatures
        for (fn_key, _fn) in self.nir.fns.iter_enumerated() {
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

            self.module.add_function(&name, fn_type, None);
        }
    }
}
