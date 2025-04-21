use crate::*;

pub(crate) fn ptr_type_from_fn_type(fn_type: FunctionType) -> PointerType {
    fn_type.get_context().ptr_type(AddressSpace::default())
}

pub(crate) fn any_value_as_basic_value(any_value: AnyValueEnum) -> Option<BasicValueEnum> {
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

pub(crate) fn any_value_as_basic_metadata_value(any_value: AnyValueEnum) -> BasicMetadataValueEnum {
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

pub(crate) fn any_type_enum_to_basic_metadata_type_enum(ty: AnyTypeEnum) -> BasicMetadataTypeEnum {
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

pub(crate) fn any_type_enum_to_basic_type_enum(ty: AnyTypeEnum) -> BasicTypeEnum {
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

pub(crate) fn fn_type_from_any_type_enum<'a>(
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

pub(crate) fn array_type_from_any_type_enum(
    ty: AnyTypeEnum,
    size: u32,
) -> inkwell::types::ArrayType {
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
