use std::cell::RefCell;

use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    targets::TargetData,
    types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicTypeEnum, FunctionType},
    AddressSpace,
};

use crate::*;

pub struct LLVMCodeGen<'ctx> {
    context: Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    target_data: TargetData,
    nir: NIR<'ctx>,
    structs_layouts: RefCell<HashMap<StructKey, TypeLayout>>,
}

struct TypeLayout {
    name: String,
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

impl<'ctx> LLVMCodeGen<'ctx> {
    fn fn_type_from_any_type_enum<'a>(
        &self,
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

    fn lower_type(&self, type_key: TypeKey) -> AnyTypeEnum {
        match self.nir.types[type_key] {
            Type::Unit => AnyTypeEnum::VoidType(self.context.void_type()),
            Type::I | Type::U => AnyTypeEnum::IntType(self.context.i64_type()), // TODO
            Type::Bool | Type::I1 | Type::U1 => AnyTypeEnum::IntType(self.context.i8_type()),
            Type::I2 | Type::U2 => AnyTypeEnum::IntType(self.context.i16_type()),
            Type::Char | Type::I4 | Type::U4 => AnyTypeEnum::IntType(self.context.i32_type()),
            Type::I8 | Type::U8 => AnyTypeEnum::IntType(self.context.i64_type()),
            Type::F4 => AnyTypeEnum::FloatType(self.context.f32_type()),
            Type::F8 => AnyTypeEnum::FloatType(self.context.f64_type()),
            Type::Ptr(_) | Type::MutPtr(_) => {
                AnyTypeEnum::PointerType(self.context.ptr_type(AddressSpace::default()))
            }
            Type::FnPtr(fn_ptr_ty_key) => {
                let return_type = self.nir.fn_ptr_types[fn_ptr_ty_key].return_type;
                let params_types = self.nir.fn_ptr_types[fn_ptr_ty_key]
                    .params_types
                    .iter()
                    .map(|ty| any_type_enum_to_basic_metadata_type_enum(self.lower_type(*ty)))
                    .collect::<Vec<_>>();
                let llvm_return_ty = self.lower_type(return_type);
                let fn_ty = self.fn_type_from_any_type_enum(llvm_return_ty, &params_types, false);
                AnyTypeEnum::FunctionType(fn_ty)
            }
            Type::Struct(struct_key) => {
                if let Some(TypeLayout { name, .. }) =
                    self.structs_layouts.borrow().get(&struct_key)
                {
                    let struct_type = self.context.get_struct_type(&name).unwrap();
                    return AnyTypeEnum::StructType(struct_type);
                }

                let _struct = &self.nir.structs[struct_key];
                let field_types = _struct
                    .fields_order
                    .clone()
                    .iter()
                    .map(|field_id| {
                        let any_ty_enum = self.lower_type(_struct.fields_types[field_id]);
                        any_type_enum_to_basic_type_enum(any_ty_enum)
                    })
                    .collect::<Vec<_>>();
                let name = self.fmt_item_name(_struct.info);
                let struct_type = self.context.opaque_struct_type(&name);
                struct_type.set_body(&field_types, false);

                let mut fields = Vec::with_capacity(field_types.len());
                for i in 0..field_types.len() as u32 {
                    let offset =
                        self.target_data.offset_of_element(&struct_type, i).unwrap() as u32;
                    fields.push(FieldLayout { offset });
                }

                let size = self.target_data.get_store_size(&struct_type) as u32;
                let align = self.target_data.get_abi_alignment(&struct_type);

                let struct_layout = TypeLayout {
                    name,
                    size,
                    align,
                    fields,
                };

                self.structs_layouts
                    .borrow_mut()
                    .insert(struct_key, struct_layout);

                AnyTypeEnum::StructType(struct_type)
            }
            Type::Tuple(tuple_type_key) => todo!(),
            Type::Slice(type_key) => todo!(),
            Type::MutSlice(type_key) => todo!(),
            Type::Array(array_type_key) => todo!(),
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }
    fn lower_fns(&self) {}
}
