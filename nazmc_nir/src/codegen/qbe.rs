use std::rc::Rc;

use crate::*;

pub struct QbeCodegen<'a> {
    lowered_types: HashMap<TypeKey, qbe::Type>,
    locals_offsets: HashMap<BindingKey, u64>,
    module: qbe::Module,
    nir: NIR<'a>,
}

impl<'a> QbeCodegen<'a> {
    pub fn new(nir: NIR<'a>) -> Self {
        Self {
            lowered_types: HashMap::with_capacity(nir.types.len()),
            locals_offsets: HashMap::new(),
            module: qbe::Module::new(),
            nir,
        }
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
        self.lower_types();
        self.lower_fns();
        self.module
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
        // Lower fns signatures
        for _fn in &self.nir.fns {
            let name = if _fn.info.id_key == IdKey::MAIN
                && self.nir.files_to_pkgs[_fn.info.file_key] == PkgKey::TOP
            {
                format!("main")
            } else {
                self.fmt_item_name(_fn.info)
            };

            let qbe_fn = qbe::Function {
                linkage: qbe::Linkage::public(),
                name: Rc::new(name),
                return_ty: Some(self.get_type(_fn.return_type)),
                arguments: _fn
                    .args
                    .iter_enumerated()
                    .map(|(arg_key, arg)| {
                        (
                            self.get_type(arg.typ),
                            qbe::Value::Temporary(fmt_arg_label(arg_key)),
                        )
                    })
                    .collect(),
                blocks: Vec::with_capacity(0), // This will be alocated later
            };
            self.module.add_function(qbe_fn);
        }

        let fns = std::mem::take(&mut self.nir.fns);

        // Lower fns bodys
        for (fn_key, _fn) in fns.into_iter_enumerated() {
            let total_stack_size = self.get_fn_locals_size(&_fn.cfg.bindings);

            let mut blocks = Vec::with_capacity(_fn.cfg.basic_blocks.len());

            for (bb_key, bb) in &_fn.cfg.basic_blocks {
                if bb_key.0 == BasicBlockKey::START_BASIC_BLOCK.0 {
                    let mut start_bb = qbe::Block {
                        label: "start".into(),
                        items: Vec::with_capacity(bb.stms.len()),
                    };
                    start_bb.add_instr(qbe::Instr::Alloc16(total_stack_size));
                    self.lower_block_jmp(&_fn.cfg, bb, &mut start_bb);
                    blocks.push(start_bb);
                    continue;
                }

                if bb_key.0 == BasicBlockKey::END_BASIC_BLOCK.0 {
                    continue;
                }

                let mut qbe_bb = qbe::Block {
                    label: fmt_bb_label(*bb_key),
                    items: Vec::with_capacity(bb.stms.len()),
                };

                for stm in &bb.stms {
                    match stm {
                        Stm::Assign { lhs, rhs, typ } => todo!(),
                        Stm::Phi { lhs, cases, typ } => todo!(),
                        Stm::Return { rvalue, typ } => todo!(),
                        Stm::Drop(lvalue_key) => todo!(),
                    }
                }
            }

            let qbe_fn = &mut self.module.functions[fn_key.0 as usize];

            qbe_fn.blocks = blocks;
        }
    }

    fn get_fn_locals_size(&mut self, bindings: &TiSlice<BindingKey, Binding>) -> u128 {
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

        self.locals_offsets.clear();
        for (key, size, align) in locals {
            // Align the offset to the required alignment
            offset = (offset + (align - 1)) & !(align - 1);

            // Store the offset for this local
            self.locals_offsets.insert(key, offset);

            // Move offset forward by the size of the variable
            offset += size;
        }

        // Round up to the nearest multiple of 16 for stack alignment
        ((offset + 15) & !15) as u128
    }

    fn lower_operand(&self, opernad: &Operand) -> qbe::Value {
        match opernad.kind {
            OperandKind::LValue(_lvalue_key) => todo!(),
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
                Const::Str(str_key) => qbe::Value::Global(Rc::new(fmt_str_label(str_key))),
                Const::Fn(fn_key) => qbe::Value::Global(self.get_fn_name(fn_key)),
            },
        }
    }

    fn lower_block_jmp(&self, cfg: &CFG, bb: &BasicBlock, qbe_bb: &mut qbe::Block) {
        if let Some(branch_key) = bb.conditional_goto {
            let branch = &cfg.branches[&branch_key];
            let BranchKind::If(operand) = branch.kind else {
                unreachable!()
            };
            let else_branch = &cfg.branches[&bb.goto.unwrap()];
            qbe_bb.add_jnz(
                self.lower_operand(&operand),
                fmt_bb_label(branch.to),
                fmt_bb_label(else_branch.to),
            );
        } else {
            let branch = &cfg.branches[&bb.goto.unwrap()];
            qbe_bb.add_jmp(fmt_bb_label(branch.to));
        }
    }
}

fn fmt_str_label(str_key: StrKey) -> String {
    format!("str{}", str_key.0)
}

fn fmt_arg_label(arg_key: ArgKey) -> String {
    format!("arg{}", arg_key.0)
}

fn fmt_tmp_label(temp_key: TempKey) -> String {
    format!("tmp{}", temp_key.0)
}

fn fmt_bb_label(bb_key: BasicBlockKey) -> String {
    format!("bb{}", bb_key.0)
}
