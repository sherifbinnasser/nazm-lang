use crate::*;

impl<'ctx, 'nir> LLVMCodeGen<'ctx, 'nir> {
    pub(crate) fn ptr_type(&self) -> PointerType<'ctx> {
        self.context.ptr_type(AddressSpace::default())
    }

    pub(crate) fn isize_type(&self) -> IntType<'ctx> {
        self.context
            .ptr_sized_int_type(&self.machine.get_target_data(), None)
    }

    pub(crate) fn slice_type(&self) -> StructType<'ctx> {
        self.context
            .struct_type(&[self.ptr_type().into(), self.isize_type().into()], false)
    }

    pub(crate) fn get_type_size(&self, type_key: TypeKey) -> u32 {
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

    pub(crate) fn get_type_align(&self, type_key: TypeKey) -> u32 {
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

    pub(crate) fn lower_type(&self, type_key: TypeKey) -> AnyTypeEnum<'ctx> {
        match self.nir.types[type_key] {
            Type::Unit => self.context.void_type().as_any_type_enum(),
            Type::I | Type::U => self.isize_type().as_any_type_enum(),
            Type::Bool | Type::I1 | Type::U1 => self.context.i8_type().as_any_type_enum(),
            Type::I2 | Type::U2 => self.context.i16_type().as_any_type_enum(),
            Type::Char | Type::I4 | Type::U4 => self.context.i32_type().as_any_type_enum(),
            Type::I8 | Type::U8 => self.context.i64_type().as_any_type_enum(),
            Type::F4 => self.context.f32_type().as_any_type_enum(),
            Type::F8 => self.context.f64_type().as_any_type_enum(),
            Type::Ptr(_) | Type::MutPtr(_) => self.ptr_type().as_any_type_enum(),
            Type::Struct(struct_key) => self.lower_struct_type(struct_key).as_any_type_enum(),
            Type::FnPtr(fn_ptr_ty_key) => self.lower_fn_ptr_type(fn_ptr_ty_key).as_any_type_enum(),
            Type::Tuple(tuple_type_key) => self.lower_tuple_type(tuple_type_key).as_any_type_enum(),
            Type::Array(array_type_key) => self.lower_array_type(array_type_key).as_any_type_enum(),
            Type::Slice(_) | Type::MutSlice(_) => self.slice_type().as_any_type_enum(),
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }

    pub(crate) fn is_agg_type(&self, type_key: TypeKey) -> bool {
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

    pub(crate) fn is_sret_or_byval_type(&self, type_key: TypeKey) -> bool {
        self.is_agg_type(type_key) && self.get_type_size(type_key) > 16
    }

    pub(crate) fn lower_param_type(&self, type_key: TypeKey) -> (AnyTypeEnum<'ctx>, ArgLayout) {
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

    pub(crate) fn lower_fn_params_types<'a>(
        &self,
        types_iter: impl Iterator<Item = &'a TypeKey>,
        args_layout: &mut Vec<ArgLayout>,
        params_types: &mut Vec<BasicMetadataTypeEnum<'ctx>>,
        attributes: &mut Vec<(AttributeLoc, Attribute)>,
    ) {
        for &ty in types_iter {
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
    }

    pub(crate) fn lower_fn_ptr_type(&self, fn_ptr_ty_key: FnPtrTypeKey) -> FunctionType<'ctx> {
        if let Some(fn_ty) = self.fn_ptr_types.borrow().get(&fn_ptr_ty_key) {
            return fn_ty.fn_type;
        }

        let params_len = self.nir.fn_ptr_types[fn_ptr_ty_key].params_types.len();
        let is_vararg = self.nir.fn_ptr_types[fn_ptr_ty_key].is_vararg;
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

        self.lower_fn_params_types(
            self.nir.fn_ptr_types[fn_ptr_ty_key].params_types.iter(),
            &mut args_layout,
            &mut params_types,
            &mut attributes,
        );

        let fn_type = fn_type_from_any_type_enum(llvm_return_ty, &params_types, is_vararg);
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

    pub(crate) fn lower_struct_type(&self, struct_key: StructKey) -> StructType<'ctx> {
        if let Some(TypeLayout { struct_ty, .. }) = self.structs_layouts.borrow().get(&struct_key) {
            return *struct_ty;
        }

        let _struct = &self.nir.structs[&struct_key];
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

    pub(crate) fn lower_tuple_type(&self, tuple_type_key: TupleTypeKey) -> StructType<'ctx> {
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

    pub(crate) fn lower_array_type(
        &self,
        array_type_key: ArrayTypeKey,
    ) -> inkwell::types::ArrayType<'ctx> {
        let ArrayType {
            underlying_typ,
            size,
        } = self.nir.array_types[array_type_key];
        let underlying_ty = self.lower_type(underlying_typ);
        array_type_from_any_type_enum(underlying_ty, size)
    }
}
