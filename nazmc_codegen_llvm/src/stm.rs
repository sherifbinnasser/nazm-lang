use crate::*;

impl<'ctx, 'nir> LLVMCodeGen<'ctx, 'nir> {
    pub(crate) fn lower_stm(&self, stm: &Stm, cfg: &CFG) {
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
                if self.get_type_size(*typ) == 0 {
                    return;
                }
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

    pub(crate) fn lower_assign_stm_agg_typ(
        &self,
        lhs: LValueKey,
        rhs: &RValue,
        typ: TypeKey,
        cfg: &CFG,
    ) {
        let ptr = if let LValueKind::Temp(temp_key) = cfg.lvalues[lhs].kind {
            let llvm_ty = self.lower_type(typ);
            let name = format!("tmp{}", temp_key.0);
            let temp_ptr = self
                .builder
                .build_alloca(any_type_enum_to_basic_type_enum(llvm_ty), &name)
                .unwrap();
            let temp = temp_ptr.as_any_value_enum();
            self.temps.borrow_mut().insert(temp_key, temp);
            temp_ptr
        } else {
            self.lower_lvalue_to_ptr(lhs, cfg)
        };

        self.lower_rvalue_agg_type(ptr, rhs, typ, cfg)
    }

    pub(crate) fn lower_assign_stm(&self, lhs: LValueKey, rhs: &RValue, cfg: &CFG) {
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
}
