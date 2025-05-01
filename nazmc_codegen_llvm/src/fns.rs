use crate::*;

impl<'ctx, 'nir> LLVMCodeGen<'ctx, 'nir> {
    pub(crate) fn lower_fns_signatures(&mut self) {
        for _fn in self.nir.fns.iter() {
            let name = match &_fn.linkage {
                FnLinkage::ExternWithSameId => self.get_id(_fn.info.id_key).to_string(),
                FnLinkage::Extern(str_key) => self.nir.str_pool[*str_key].clone(),
                FnLinkage::Local(_)
                    if _fn.info.id_key == IdKey::MAIN
                        && self.nir.files_to_pkgs[_fn.info.file_key] == PkgKey::TOP =>
                {
                    "main".into()
                }
                FnLinkage::Local(_) => self.fmt_item_name(_fn.info),
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

    pub(crate) fn lower_fns_bodies(&self) {
        for (fn_key, _fn) in self.nir.fns.iter_enumerated() {
            let FnLinkage::Local(cfg) = &_fn.linkage else {
                continue;
            };
            self.llvm_temps_counter.set(0);
            self.basic_blocks.borrow_mut().clear();
            self.args.borrow_mut().clear();
            self.locals.borrow_mut().clear();
            self.temps.borrow_mut().clear();

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

    pub(crate) fn lower_ret_ptr_and_args(&self, fn_key: FnKey, _fn: &Fn) {
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

    pub(crate) fn lower_locals(&self, bindings: &TiSlice<BindingKey, Binding>) {
        for (key, binding) in bindings.iter_enumerated() {
            let llvm_ty = self.lower_type(binding.typ);
            let name = format!("loc{}", key.0);
            let ptr_value = match llvm_ty {
                AnyTypeEnum::ArrayType(array_type) => self.builder.build_alloca(array_type, &name),
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

    pub(crate) fn lower_block_jmp(&self, bb: &nazmc_nir::BasicBlock, cfg: &CFG) {
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

            let mut condition = self.lower_operand(&operand, &cfg).into_int_value();

            // Truncate condition to i1 if it's i8
            let condition_type = condition.get_type();
            if condition_type.get_bit_width() == 8 {
                condition = self
                    .builder
                    .build_int_truncate(condition, self.context.bool_type(), "")
                    .unwrap();
            }

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

    pub(crate) fn check_or_add_void_return(&self) {
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
}
