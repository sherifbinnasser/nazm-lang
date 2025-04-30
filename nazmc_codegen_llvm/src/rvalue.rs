use crate::*;

impl<'ctx, 'nir> LLVMCodeGen<'ctx, 'nir> {
    pub(crate) fn lower_rvalue_agg_type(
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
            RValue::Str(str_key) => {
                let src_ptr = self.llvm_str_pool[*str_key];
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

    pub(crate) fn lower_rvalue(
        &self,
        rvalue: &RValue,
        name: &str,
        cfg: &CFG,
    ) -> AnyValueEnum<'ctx> {
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

    pub(crate) fn lower_array_rvalue<'a>(
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
                let zero_index = self.context.i64_type().const_int(0, false);
                let index = self.context.i64_type().const_int(i as u64, false);

                let element_ptr = unsafe {
                    self.builder
                        .build_gep(
                            any_type_enum_to_basic_type_enum(llvm_array_ty),
                            dest_ptr,
                            &[zero_index, index],
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
                let zero_index = self.context.i64_type().const_int(0, false);
                let index = self.context.i64_type().const_int(i as u64, false);

                let element_ptr = unsafe {
                    self.builder
                        .build_gep(
                            any_type_enum_to_basic_type_enum(llvm_array_ty),
                            dest_ptr,
                            &[zero_index, index],
                            "",
                        )
                        .unwrap()
                };

                let element = any_value_as_basic_value(self.lower_operand(element, cfg)).unwrap();

                let _ = self.builder.build_store(element_ptr, element);
            }
        }
    }

    pub(crate) fn lower_struct_rvalue<'a>(
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

    pub(crate) fn lower_call_rvalue_agg_type(
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
        let mut args_layout_iter = args_layout.iter().copied().enumerate();
        let mut llvm_params_types_iter = fn_type.get_param_types().into_iter();
        let mut llvm_args;
        if has_ret_ptr {
            llvm_params_types_iter.next();
            args_layout_iter = args_layout[1..].iter().copied().enumerate();
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
            args_layout.len(),
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

    pub(crate) fn lower_bin_op_rvalue(
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
        } else if let AnyValueEnum::PointerValue(lhs) = llvm_lhs {
            let rhs = self.lower_operand(rhs, cfg);

            if let AnyValueEnum::IntValue(rhs) = rhs {
                let rhs = if let BinOp::Minus = op {
                    builder.build_int_neg(rhs, "").unwrap()
                } else {
                    rhs
                };

                return unsafe {
                    builder
                        .build_gep(self.ptr_type(), lhs, &[rhs], name)
                        .unwrap()
                        .as_any_value_enum()
                };
            }

            let rhs = rhs.into_pointer_value();

            macro_rules! build_cmp {
                ($build_op: ident) => {
                    builder
                        .build_int_compare(IntPredicate::$build_op, lhs, rhs, name)
                        .unwrap()
                        .as_any_value_enum()
                };
            }

            return match op {
                BinOp::EqualEqual => build_cmp!(EQ),
                BinOp::NotEqual => build_cmp!(NE),
                BinOp::GE => build_cmp!(UGE),
                BinOp::GT => build_cmp!(UGT),
                BinOp::LE => build_cmp!(ULE),
                BinOp::LT => build_cmp!(ULT),
                BinOp::Minus => builder
                    .build_ptr_diff(self.ptr_type(), lhs, rhs, name)
                    .unwrap()
                    .as_any_value_enum(),
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

    pub(crate) fn lower_unary_op_rvalue(
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

    pub(crate) fn lower_call_rvalue(
        &self,
        on: &Operand,
        args: &[Operand],
        cfg: &CFG,
    ) -> AnyValueEnum<'ctx> {
        let llvm_on = self.lower_operand(on, cfg);

        let Type::FnPtr(fn_ptr_type_key) = self.nir.types[on.typ] else {
            unreachable!()
        };

        let fn_type = self.fn_ptr_types.borrow()[&fn_ptr_type_key].fn_type;
        let args_layout = &self.fn_ptr_types.borrow()[&fn_ptr_type_key].args_layout;
        let args_layout_iter = args_layout.iter().copied().enumerate();
        let llvm_params_types_iter = fn_type.get_param_types().into_iter();
        let llvm_args = Vec::with_capacity(args.len());

        self.lower_call_args(
            llvm_on,
            fn_ptr_type_key,
            fn_type,
            args,
            llvm_args,
            args_layout_iter,
            args_layout.len(),
            llvm_params_types_iter,
            cfg,
        )
    }

    pub(crate) fn lower_call_args(
        &self,
        llvm_on: AnyValueEnum<'ctx>,
        fn_ptr_type_key: FnPtrTypeKey,
        fn_type: FunctionType<'ctx>,
        args: &[Operand],
        mut llvm_args: Vec<BasicMetadataValueEnum<'ctx>>,
        args_layout_iter: impl Iterator<Item = (usize, ArgLayout)>,
        args_layout_len: usize,
        llvm_params_types_iter: impl Iterator<Item = BasicTypeEnum<'ctx>>,
        cfg: &CFG,
    ) -> AnyValueEnum<'ctx> {
        let varargs_len = args.len() - args_layout_len;
        let mut vararg_args_layout = Vec::with_capacity(varargs_len);
        let mut vararg_llvm_params_types = Vec::with_capacity(varargs_len);
        let mut vararg_attributes = Vec::with_capacity(varargs_len);

        if varargs_len > 0 {
            self.lower_fn_params_types(
                args[args_layout_len..].iter().map(|arg| &arg.typ),
                &mut vararg_args_layout,
                &mut vararg_llvm_params_types,
                &mut vararg_attributes,
            );
        }

        let vararg_args_layout_iter = vararg_args_layout
            .into_iter()
            .enumerate()
            .map(|(i, arg_layout)| (i + varargs_len, arg_layout));

        let vararg_llvm_params_types_iter = vararg_llvm_params_types
            .into_iter()
            .map(basic_metadata_type_enum_to_basic_type_enum);

        let args_layout_iter = args_layout_iter.chain(vararg_args_layout_iter);

        let mut llvm_params_types_iter =
            llvm_params_types_iter.chain(vararg_llvm_params_types_iter);

        for (i, arg_layout) in args_layout_iter {
            match arg_layout {
                ArgLayout::RetPtr => unreachable!(),
                ArgLayout::ByvalPtr | ArgLayout::IntStruct | ArgLayout::BinaryStruct => {
                    let llvm_lowered_ty = llvm_params_types_iter.next().unwrap();
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
}
