use std::rc::Rc;

use crate::*;

pub struct QbeCodegen<'a> {
    lowered_types: HashMap<TypeKey, qbe::Type>,
    strs: TiVec<StrKey, qbe::Value>,
    statics: TiVec<StaticKey, qbe::Value>,
    args: HashMap<ArgKey, qbe::Value>,
    temps: TiVec<TempKey, qbe::Value>,
    bindings: TiVec<BindingKey, qbe::Value>,
    basic_blocks: TiVec<BasicBlockKey, Rc<String>>,
    qbe_temps: Vec<qbe::Value>,
    qbe_temps_counter: usize,
    base_ptr: qbe::Value,
    module: qbe::Module,
    nir: NIR<'a>,
}

impl<'a> QbeCodegen<'a> {
    pub fn new(nir: NIR<'a>) -> Self {
        Self {
            lowered_types: HashMap::with_capacity(nir.types.len()),
            strs: TiVec::with_capacity(nir.str_pool.len()),
            statics: TiVec::with_capacity(nir.statics.len()),
            args: HashMap::new(),
            temps: TiVec::new(),
            bindings: TiVec::new(),
            basic_blocks: TiVec::new(),
            qbe_temps: Vec::new(),
            qbe_temps_counter: 0,
            module: qbe::Module::new(),
            base_ptr: qbe::Value::Temporary(Rc::new("base_ptr".into())),
            nir,
        }
    }

    fn new_qbe_temp(&mut self) -> qbe::Value {
        if self.qbe_temps_counter == self.qbe_temps.len() {
            self.qbe_temps.push(qbe::Value::Temporary(Rc::new(format!(
                "qbe_tmp{}",
                self.qbe_temps_counter
            ))));
        }
        self.qbe_temps_counter += 1;
        self.qbe_temps[self.qbe_temps_counter - 1].clone()
    }

    fn get_type(&self, type_key: TypeKey) -> qbe::Type {
        self.lowered_types[&type_key].clone()
    }

    fn get_id(&self, id: IdKey) -> &str {
        &self.nir.id_pool[id]
    }

    fn fmt_pkg_name(&self, pkg_key: PkgKey) -> String {
        self.nir.pkgs_names[pkg_key]
            .iter()
            .map(|id| self.get_id(*id))
            .collect::<Vec<_>>()
            .join(".")
    }

    fn fmt_item_name(&self, item_info: ItemInfo) -> String {
        let pkg = self.fmt_pkg_name(self.nir.files_to_pkgs[item_info.file_key]);
        let name = &self.nir.id_pool[item_info.id_key];
        if pkg.is_empty() {
            name.to_owned()
        } else {
            format!("{}.{}", pkg, name)
        }
    }

    fn get_fn_name(&self, fn_key: FnKey) -> Rc<String> {
        self.module.functions[fn_key.0 as usize].name.clone()
    }

    pub fn lower(mut self) -> qbe::Module {
        self.lower_strs();
        // self.lower_statics();
        self.lower_types();
        self.lower_fns();
        self.module
    }

    fn lower_strs(&mut self) {
        let str_pool = std::mem::take(&mut self.nir.str_pool);

        for (str_key, string) in str_pool.into_iter_enumerated() {
            let name = Rc::new(format!("str{}", str_key.0));
            let qbe_value = qbe::Value::Global(name.clone());
            self.strs.push(qbe_value);
            let data_def = qbe::DataDef {
                linkage: qbe::Linkage::private(),
                name,
                align: None,
                items: vec![
                    (qbe::Type::Byte, qbe::DataItem::Str(string)),
                    (qbe::Type::Byte, qbe::DataItem::Const(0)),
                ],
            };
            self.module.add_data(data_def);
        }
    }

    fn lower_types(&mut self) {
        for ty in self.nir.types.keys() {
            self.lower_type(ty);
        }
    }

    fn lower_type(&mut self, type_key: TypeKey) -> qbe::Type {
        if let Some(ty) = self.lowered_types.get(&type_key) {
            ty.clone()
        } else {
            let qbe_ty = match self.nir.types[type_key] {
                Type::Unit => qbe::Type::Void,
                Type::I | Type::U => qbe::Type::Long,
                Type::Bool | Type::I1 | Type::U1 => qbe::Type::Byte,
                Type::I2 | Type::U2 => qbe::Type::Halfword,
                Type::Char | Type::I4 | Type::U4 => qbe::Type::Word,
                Type::I8 | Type::U8 => qbe::Type::Long,
                Type::F4 => qbe::Type::Single,
                Type::F8 => qbe::Type::Double,
                Type::Ptr(_) | Type::MutPtr(_) | Type::FnPtr(_) => qbe::Type::Long,
                Type::Struct(struct_key) => {
                    let _struct = &self.nir.structs[struct_key];
                    let name = self.fmt_item_name(_struct.info);
                    let items = _struct
                        .fields
                        .clone()
                        .values()
                        .map(|ty| (self.lower_type(*ty), 0))
                        .collect();
                    let type_def = qbe::TypeDef::new(name, None, items);
                    let type_def = self.module.add_type(type_def);
                    qbe::Type::Aggregate(type_def)
                }
                Type::Tuple(tuple_type_key) => {
                    let tuple = &self.nir.tuple_types[tuple_type_key];
                    let name = format!("Tuple{}", tuple_type_key.0);
                    let items = tuple
                        .types
                        .clone()
                        .iter()
                        .map(|ty| (self.lower_type(*ty), 0))
                        .collect();
                    let type_def = qbe::TypeDef::new(name, None, items);
                    let type_def = self.module.add_type(type_def);
                    qbe::Type::Aggregate(type_def)
                }
                Type::Slice(type_key) => todo!(),
                Type::MutSlice(type_key) => todo!(),
                Type::Array(array_type_key) => todo!(),
                Type::Lambda(lambda_type_key) => todo!(),
            };
            self.lowered_types.insert(type_key, qbe_ty.clone());
            qbe_ty
        }
    }

    fn lower_fns(&mut self) {
        let mut args = std::mem::take(&mut self.args);
        let mut max_temps_count = 0;
        let mut max_bindings_count = 0;
        let mut max_basic_blocks_count = 0;

        // Lower fns signatures
        for (fn_key, _fn) in self.nir.fns.iter_enumerated() {
            let name = if _fn.info.id_key == IdKey::MAIN
                && self.nir.files_to_pkgs[_fn.info.file_key] == PkgKey::TOP
            {
                format!("main")
            } else {
                format!("fn{}", fn_key.0)
            };

            let qbe_fn = qbe::Function {
                comments: vec![],
                linkage: qbe::Linkage::public(),
                name: Rc::new(name),
                return_ty: Some(self.get_type(_fn.return_type)),
                arguments: _fn
                    .args
                    .iter_enumerated()
                    .map(|(arg_key, arg)| {
                        (
                            self.get_type(arg.typ),
                            args.entry(arg_key)
                                .or_insert_with(|| {
                                    qbe::Value::Temporary(Rc::new(format!("arg{}", arg_key.0)))
                                })
                                .clone(),
                        )
                    })
                    .collect(),
                blocks: Vec::with_capacity(0), // This will be alocated later
            };
            self.module.add_function(qbe_fn);

            if _fn.cfg.temps.len() > max_temps_count {
                max_temps_count = _fn.cfg.temps.len();
            }

            if _fn.cfg.bindings.len() > max_bindings_count {
                max_bindings_count = _fn.cfg.bindings.len();
            }

            if _fn.cfg.basic_blocks.len() > max_basic_blocks_count {
                max_basic_blocks_count = _fn.cfg.basic_blocks.len();
            }
        }

        self.args = args;

        self.temps = TiVec::with_capacity(max_temps_count);
        self.bindings = TiVec::with_capacity(max_bindings_count);
        self.basic_blocks = TiVec::with_capacity(max_basic_blocks_count);

        for i in 0..max_bindings_count {
            self.bindings
                .push(qbe::Value::Temporary(Rc::new(format!("loc{}", i))));
        }

        for i in 0..max_temps_count {
            self.temps
                .push(qbe::Value::Temporary(Rc::new(format!("tmp{}", i))));
        }

        for i in 0..max_basic_blocks_count {
            let label = if i as u32 == BasicBlockKey::START_BASIC_BLOCK.0 {
                "start".into()
            } else if i as u32 == BasicBlockKey::END_BASIC_BLOCK.0 {
                "end".into()
            } else {
                format!("bb{}", i)
            };

            self.basic_blocks.push(Rc::new(label));
        }

        let fns = std::mem::take(&mut self.nir.fns);

        // Lower fns bodys
        for (fn_key, _fn) in fns.into_iter_enumerated() {
            let mut blocks = Vec::with_capacity(_fn.cfg.basic_blocks.len());
            let start_bb = &_fn.cfg.basic_blocks[&BasicBlockKey::START_BASIC_BLOCK];
            let mut start_qbe_bb = qbe::Block {
                label: self.basic_blocks[BasicBlockKey::START_BASIC_BLOCK].clone(),
                items: Vec::with_capacity(start_bb.stms.len()),
            };
            // Reserve for base ptr allocation
            start_qbe_bb.add_instr(qbe::Instr::Ret(None));
            let total_stack_size = self.get_fn_locals_size(&_fn.cfg.bindings, &mut start_qbe_bb);
            start_qbe_bb.items[0] = qbe::BlockItem::Statement(qbe::Statement::Assign(
                self.base_ptr.clone(),
                qbe::Type::Long,
                qbe::Instr::Alloc16(total_stack_size),
            ));
            self.lower_block_jmp(&_fn.cfg, start_bb, &mut start_qbe_bb);
            blocks.push(start_qbe_bb);

            for (bb_key, bb) in &_fn.cfg.basic_blocks {
                if bb_key.0 == BasicBlockKey::START_BASIC_BLOCK.0
                    || bb_key.0 == BasicBlockKey::END_BASIC_BLOCK.0
                {
                    continue;
                }

                let mut qbe_bb = qbe::Block {
                    label: self.basic_blocks[*bb_key].clone(),
                    items: Vec::with_capacity(bb.stms.len()),
                };

                for stm in &bb.stms {
                    match stm {
                        Stm::Assign { lhs, rhs, typ } => {
                            let qbe_rvalue = self.lower_rvalue(rhs, &_fn.cfg, &mut qbe_bb);
                            let qbe_typ = self.get_type(*typ);

                            match _fn.cfg.lvalues[*lhs].kind {
                                LValueKind::Binding(binding_key) => {
                                    let temp = self.new_qbe_temp();
                                    qbe_bb.add_assign(temp.clone(), qbe_typ.clone(), qbe_rvalue);
                                    qbe_bb.add_instr(qbe::Instr::Store(
                                        qbe_typ,
                                        self.bindings[binding_key].clone(),
                                        temp,
                                    ));
                                }
                                LValueKind::Arg(arg_key) => {
                                    let qbe_lvalue = self.args[&arg_key].clone();
                                    qbe_bb.add_assign(qbe_lvalue, qbe_typ, qbe_rvalue);
                                }
                                LValueKind::Static(static_key) => {
                                    let qbe_lvalue = self.statics[static_key].clone();
                                    qbe_bb.add_assign(qbe_lvalue, qbe_typ, qbe_rvalue);
                                }
                                LValueKind::Temp(temp_key) => {
                                    let qbe_lvalue = self.temps[temp_key].clone();
                                    qbe_bb.add_assign(qbe_lvalue, qbe_typ, qbe_rvalue);
                                }
                                LValueKind::MutDeref(lvalue_key) => {
                                    let qbe_temp = self.new_qbe_temp();
                                    qbe_bb.add_assign(
                                        qbe_temp.clone(),
                                        qbe_typ.clone(),
                                        qbe_rvalue,
                                    );
                                    let qbe_ptr =
                                        self.lower_lvalue(lvalue_key, &_fn.cfg, &mut qbe_bb);
                                    qbe_bb.add_instr(qbe::Instr::Store(qbe_typ, qbe_ptr, qbe_temp));
                                }
                                LValueKind::MutField { on, field_id } => todo!(),
                                LValueKind::MutTupleIdx { on, idx } => todo!(),
                                LValueKind::MutArrayIdx { on, idx } => todo!(),
                                LValueKind::MutArrayConstIdx { on, idx } => todo!(),
                                _ => unreachable!(),
                            }
                        }
                        Stm::Phi { lhs, cases, typ } => todo!(),
                        Stm::Return { rvalue, typ } => {
                            let qbe_typ = self.get_type(*typ);
                            let qbe_rvalue = self.lower_rvalue(rvalue, &_fn.cfg, &mut qbe_bb);
                            let qbe_temp = self.new_qbe_temp();
                            qbe_bb.add_assign(qbe_temp.clone(), qbe_typ, qbe_rvalue);
                            let return_val = if let qbe::Type::Void = self.get_type(*typ) {
                                None
                            } else {
                                Some(qbe_temp)
                            };
                            qbe_bb.add_instr(qbe::Instr::Ret(return_val));
                        }
                        Stm::Drop(lvalue_key) => todo!(),
                    }
                }

                self.lower_block_jmp(&_fn.cfg, bb, &mut qbe_bb);

                blocks.push(qbe_bb);
            }

            let qbe_fn = &mut self.module.functions[fn_key.0 as usize];

            qbe_fn.blocks = blocks;
        }
    }

    fn get_fn_locals_size(
        &mut self,
        bindings: &TiSlice<BindingKey, Binding>,
        qbe_bb: &mut qbe::Block,
    ) -> u128 {
        let mut locals = Vec::with_capacity(bindings.len());

        for (key, binding) in bindings.iter_enumerated() {
            let qbe_ty = self.get_type(binding.typ);
            let size = qbe_ty.size();
            let align = qbe_ty.align();
            locals.push((key, size, align));
        }

        // Sort by alignment (largest first)
        locals.sort_by_key(|&(_, _, align)| std::cmp::Reverse(align));

        let mut offset = 0;

        for (key, size, align) in locals {
            // Align the offset to the required alignment
            offset = (offset + (align - 1)) & !(align - 1);

            let local_ptr = self.bindings[key].clone();

            qbe_bb.add_assign(
                local_ptr,
                qbe::Type::Long,
                qbe::Instr::Add(self.base_ptr.clone(), qbe::Value::Const(offset)),
            );

            // Move offset forward by the size of the variable
            offset += size;
        }

        // Round up to the nearest multiple of 16 for stack alignment
        ((offset + 15) & !15) as u128
    }

    fn lower_rvalue(&mut self, rvalue: &RValue, cfg: &CFG, qbe_bb: &mut qbe::Block) -> qbe::Instr {
        match rvalue {
            RValue::Use(operand) => qbe::Instr::Copy(self.lower_operand(operand, cfg, qbe_bb)),
            RValue::Ref(lvalue_key) => todo!(),
            RValue::RefMut(lvalue_key) => todo!(),
            RValue::Tuple(thin_vec) => todo!(),
            RValue::ArrayElements(thin_vec) => todo!(),
            RValue::ArrayRepeated { repeated, size } => todo!(),
            RValue::Struct { struct_key, fields } => todo!(),
            RValue::Cast { val, to } => todo!(),
            RValue::BinOp { op, lhs, rhs } => todo!(),
            RValue::UnaryOp { op, operand } => todo!(),
            RValue::Call { on, args } => qbe::Instr::Call(
                self.lower_operand(on, cfg, qbe_bb),
                args.iter()
                    .map(|op| (self.get_type(op.typ), self.lower_operand(op, cfg, qbe_bb)))
                    .collect(),
                None,
            ),
        }
    }

    fn lower_lvalue(
        &mut self,
        lvalue_key: LValueKey,
        cfg: &CFG,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        let qbe_ty = self.get_type(cfg.lvalues[lvalue_key].typ);

        match cfg.lvalues[lvalue_key].kind {
            LValueKind::Binding(binding_key) => {
                let qbe_loaded_val = self.new_qbe_temp();
                qbe_bb.add_assign(
                    qbe_loaded_val.clone(),
                    qbe_ty.clone(),
                    qbe::Instr::Load(qbe_ty, self.bindings[binding_key].clone()),
                );
                qbe_loaded_val
            }
            LValueKind::Static(static_key) => self.statics[static_key].clone(),
            LValueKind::Arg(arg_key) => self.args[&arg_key].clone(),
            LValueKind::Temp(temp_key) => self.temps[temp_key].clone(),
            LValueKind::Deref(lvalue_key) | LValueKind::MutDeref(lvalue_key) => {
                let qbe_ptr = self.lower_lvalue(lvalue_key, cfg, qbe_bb);
                let qbe_loaded_val = self.new_qbe_temp();
                qbe_bb.add_assign(
                    qbe_loaded_val.clone(),
                    qbe_ty.clone(),
                    qbe::Instr::Load(qbe_ty, qbe_ptr),
                );
                qbe_loaded_val
            }
            LValueKind::Field { on, field_id } => todo!(),
            LValueKind::TupleIdx { on, idx } => todo!(),
            LValueKind::ArrayIdx { on, idx } => todo!(),
            LValueKind::ArrayConstIdx { on, idx } => todo!(),
            LValueKind::MutField { on, field_id } => todo!(),
            LValueKind::MutTupleIdx { on, idx } => todo!(),
            LValueKind::MutArrayIdx { on, idx } => todo!(),
            LValueKind::MutArrayConstIdx { on, idx } => todo!(),
        }
    }

    fn lower_operand(
        &mut self,
        opernad: &Operand,
        cfg: &CFG,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        match opernad.kind {
            OperandKind::LValue(lvalue_key) => self.lower_lvalue(lvalue_key, cfg, qbe_bb),
            OperandKind::Const(c) => match c {
                Const::Unit => qbe::Value::Const(0),
                Const::I(n) => qbe::Value::Const(n as u64),
                Const::I1(n) => qbe::Value::Const(n as u64),
                Const::I2(n) => qbe::Value::Const(n as u64),
                Const::I4(n) => qbe::Value::Const(n as u64),
                Const::I8(n) => qbe::Value::Const(n as u64),
                Const::U(n) => qbe::Value::Const(n as u64),
                Const::U1(n) => qbe::Value::Const(n as u64),
                Const::U2(n) => qbe::Value::Const(n as u64),
                Const::U4(n) => qbe::Value::Const(n as u64),
                Const::U8(n) => qbe::Value::Const(n as u64),
                Const::F4(n) => qbe::Value::Const(n as u64),
                Const::F8(n) => qbe::Value::Const(n as u64),
                Const::Bool(n) => qbe::Value::Const(n as u64),
                Const::Char(n) => qbe::Value::Const(n as u64),
                Const::Str(str_key) => self.strs[str_key].clone(),
                Const::Fn(fn_key) => qbe::Value::Global(self.get_fn_name(fn_key)),
            },
        }
    }

    fn lower_block_jmp(&mut self, cfg: &CFG, bb: &BasicBlock, qbe_bb: &mut qbe::Block) {
        if let Some(branch_key) = bb.conditional_goto {
            let branch = &cfg.branches[&branch_key];
            if branch.to == BasicBlockKey::END_BASIC_BLOCK {
                return;
            }
            let BranchKind::If(operand) = branch.kind else {
                unreachable!()
            };

            let else_branch = &cfg.branches[&bb.goto.unwrap()];
            if else_branch.to == BasicBlockKey::END_BASIC_BLOCK {
                return;
            }

            let qbe_operand = self.lower_operand(&operand, cfg, qbe_bb);
            qbe_bb.add_jnz(
                qbe_operand,
                self.basic_blocks[branch.to].clone(),
                self.basic_blocks[else_branch.to].clone(),
            );
        } else {
            let branch = &cfg.branches[&bb.goto.unwrap()];
            if branch.to == BasicBlockKey::END_BASIC_BLOCK {
                return;
            }
            qbe_bb.add_jmp(self.basic_blocks[branch.to].clone());
        }
    }
}
