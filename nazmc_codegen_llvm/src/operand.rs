use crate::*;

impl<'ctx, 'nir> LLVMCodeGen<'ctx, 'nir> {
    #[inline]
    pub(crate) fn lower_operand(&self, operand: &Operand, cfg: &CFG) -> AnyValueEnum<'ctx> {
        self.lower_operand_kind(operand.kind, cfg)
    }

    pub(crate) fn lower_operand_kind(&self, kind: OperandKind, cfg: &CFG) -> AnyValueEnum<'ctx> {
        match kind {
            OperandKind::LValue(lvalue_key) => self.lower_lvalue(lvalue_key, cfg),
            OperandKind::Const(Const::Unit) => unreachable!(),
            OperandKind::Const(Const::Null) => self.ptr_type().const_null().as_any_value_enum(),
            OperandKind::Const(Const::I(n)) => self
                .isize_type()
                .const_int(n as u64, true)
                .as_any_value_enum(),
            OperandKind::Const(Const::I1(n)) => self
                .context
                .i8_type()
                .const_int(n as u64, true)
                .as_any_value_enum(),
            OperandKind::Const(Const::I2(n)) => self
                .context
                .i16_type()
                .const_int(n as u64, true)
                .as_any_value_enum(),
            OperandKind::Const(Const::I4(n)) => self
                .context
                .i32_type()
                .const_int(n as u64, true)
                .as_any_value_enum(),
            OperandKind::Const(Const::I8(n)) => self
                .context
                .i64_type()
                .const_int(n as u64, true)
                .as_any_value_enum(),
            OperandKind::Const(Const::U(n)) => self
                .isize_type()
                .const_int(n as u64, false)
                .as_any_value_enum(),
            OperandKind::Const(Const::U1(n)) => self
                .context
                .i8_type()
                .const_int(n as u64, false)
                .as_any_value_enum(),
            OperandKind::Const(Const::U2(n)) => self
                .context
                .i16_type()
                .const_int(n as u64, false)
                .as_any_value_enum(),
            OperandKind::Const(Const::U4(n)) => self
                .context
                .i32_type()
                .const_int(n as u64, false)
                .as_any_value_enum(),
            OperandKind::Const(Const::U8(n)) => self
                .context
                .i64_type()
                .const_int(n as u64, false)
                .as_any_value_enum(),
            OperandKind::Const(Const::Bool(n)) => self
                .context
                .i8_type()
                .const_int(n as u64, false)
                .as_any_value_enum(),
            OperandKind::Const(Const::Char(n)) => self
                .context
                .i32_type()
                .const_int(n as u64, false)
                .as_any_value_enum(),
            OperandKind::Const(Const::F4(n)) => self
                .context
                .f32_type()
                .const_float(n as f64)
                .as_any_value_enum(),
            OperandKind::Const(Const::F8(n)) => self
                .context
                .f64_type()
                .const_float(n as f64)
                .as_any_value_enum(),
            OperandKind::Const(Const::Fn(fn_key)) => self.llvm_fns[fn_key].as_any_value_enum(),
        }
    }

    pub(crate) fn lower_lvalue(&self, lvalue_key: LValueKey, cfg: &CFG) -> AnyValueEnum<'ctx> {
        let type_key = cfg.lvalues[lvalue_key].typ;
        if let LValueKind::Temp(temp_key) = cfg.lvalues[lvalue_key].kind {
            self.temps.borrow()[&temp_key]
        } else {
            let llvm_ptr = self.lower_lvalue_to_ptr(lvalue_key, cfg);
            self.add_load_instr(type_key, llvm_ptr)
        }
    }

    pub(crate) fn lower_lvalue_to_ptr(
        &self,
        lvalue_key: LValueKey,
        cfg: &CFG,
    ) -> PointerValue<'ctx> {
        match cfg.lvalues[lvalue_key].kind {
            LValueKind::Binding(binding_key) => self.locals.borrow()[&binding_key],
            LValueKind::Static(static_key) => self.llvm_statics[static_key].as_pointer_value(),
            LValueKind::Const(const_key) => {
                self.llvm_consts.borrow()[&const_key].as_pointer_value()
            }
            LValueKind::Arg(arg_key) => self.args.borrow()[&arg_key],
            LValueKind::Temp(temp_key) => self.temps.borrow()[&temp_key].into_pointer_value(),
            LValueKind::Deref(lvalue_key) | LValueKind::MutDeref(lvalue_key) => {
                // For dereference, we already have the pointer, just use it
                self.lower_lvalue(lvalue_key, cfg).into_pointer_value()
            }
            LValueKind::Field { on, idx } | LValueKind::MutField { on, idx } => {
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
                let zero_index = self.context.i64_type().const_int(0, false);
                let index = self.lower_lvalue(idx, cfg).into_int_value();
                unsafe {
                    self.builder
                        .build_gep(
                            any_type_enum_to_basic_type_enum(llvm_array_ty),
                            array_ptr,
                            &[zero_index, index],
                            &self.new_llvm_temp(),
                        )
                        .unwrap()
                }
            }
            LValueKind::ArrayConstIdx { on, idx } | LValueKind::MutArrayConstIdx { on, idx } => {
                let array_ptr = self.lower_lvalue_to_ptr(on, cfg);
                let array_type_key = cfg.lvalues[on].typ;
                let llvm_array_ty = self.lower_type(array_type_key);
                let zero_index = self.context.i64_type().const_int(0, false);
                let index = self.context.i64_type().const_int(idx as u64, false);
                unsafe {
                    self.builder
                        .build_gep(
                            any_type_enum_to_basic_type_enum(llvm_array_ty),
                            array_ptr,
                            &[zero_index, index],
                            &self.new_llvm_temp(),
                        )
                        .unwrap()
                }
            }
        }
    }

    pub(crate) fn add_load_instr(
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
