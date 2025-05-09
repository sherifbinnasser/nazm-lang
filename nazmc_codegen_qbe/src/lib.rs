use std::{collections::HashMap, rc::Rc};

use nazmc_data_pool::*;
use nazmc_nir::*;
use typed_index_collections::{TiSlice, TiVec};

pub struct QbeCodegen<'a> {
    lowered_types: HashMap<TypeKey, qbe::Type>,
    structs: HashMap<StructKey, HashMap<IdKey, u32>>,
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
            structs: HashMap::with_capacity(nir.structs.len()),
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
                    let _struct = std::mem::take(self.nir.structs.get_mut(&struct_key).unwrap());
                    let mut offset = 0;
                    let mut fields_offsets = HashMap::with_capacity(_struct.fields.len());
                    let mut items = Vec::with_capacity(_struct.fields.len());

                    for field in _struct.fields.iter() {
                        let qbe_field_type = self.lower_type(field.typ);

                        // Align offset to the field's alignment
                        let alignment: u32 = qbe_field_type.align() as u32;
                        offset = (offset + alignment - 1) & !(alignment - 1); // Round up to alignment

                        // Store the offset for this field
                        fields_offsets.insert(field.id, offset);

                        // Add to QBE type definition (repetition count is 0 for single fields)
                        items.push((qbe_field_type.clone(), 0));

                        // Increment offset by the field's size
                        offset += qbe_field_type.size() as u32;
                    }
                    self.structs.insert(struct_key, fields_offsets);
                    let name = self.fmt_item_name(self.nir.structs[&struct_key].info);
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
            let FnLinkage::Local(cfg) = &_fn.linkage else {
                // TODO: Lower extern functions
                continue;
            };

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

            if cfg.temps.len() > max_temps_count {
                max_temps_count = cfg.temps.len();
            }

            if cfg.bindings.len() > max_bindings_count {
                max_bindings_count = cfg.bindings.len();
            }

            if cfg.basic_blocks.len() > max_basic_blocks_count {
                max_basic_blocks_count = cfg.basic_blocks.len();
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
            let FnLinkage::Local(cfg) = &_fn.linkage else {
                continue;
            };

            self.qbe_temps_counter = 0;
            let mut blocks = Vec::with_capacity(cfg.basic_blocks.len());
            let start_bb = &cfg.basic_blocks[&BasicBlockKey::START_BASIC_BLOCK];
            let mut start_qbe_bb = qbe::Block {
                label: self.basic_blocks[BasicBlockKey::START_BASIC_BLOCK].clone(),
                items: Vec::with_capacity(start_bb.stms.len()),
            };
            // Reserve for base ptr allocation
            start_qbe_bb.add_instr(qbe::Instr::Ret(None));
            let total_stack_size = self.get_fn_locals_size(&cfg.bindings, &mut start_qbe_bb);
            start_qbe_bb.items[0] = qbe::BlockItem::Statement(qbe::Statement::Assign(
                self.base_ptr.clone(),
                qbe::Type::Long,
                qbe::Instr::Alloc16(total_stack_size),
            ));
            self.lower_block_jmp(&cfg, start_bb, &mut start_qbe_bb);
            blocks.push(start_qbe_bb);

            for (bb_key, bb) in &cfg.basic_blocks {
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
                    self.lower_stm(stm, &cfg, &mut qbe_bb)
                }

                self.lower_block_jmp(&cfg, bb, &mut qbe_bb);

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
                qbe::Instr::Add(self.base_ptr.clone(), qbe::Value::UConst(offset)),
            );

            // Move offset forward by the size of the variable
            offset += size;
        }

        // Round up to the nearest multiple of 16 for stack alignment
        ((offset + 15) & !15) as u128
    }

    fn signed_extend(
        &mut self,
        qbe_val: qbe::Value,
        qbe_typ: qbe::Type,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        let qbe_temp = self.new_qbe_temp();
        qbe_bb.add_assign(
            qbe_temp.clone(),
            qbe::Type::Word,
            qbe::Instr::ExtSigned(qbe_typ, qbe_val),
        );
        qbe_temp
    }

    fn unsigned_extend(
        &mut self,
        qbe_val: qbe::Value,
        qbe_typ: qbe::Type,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        let qbe_temp = self.new_qbe_temp();
        qbe_bb.add_assign(
            qbe_temp.clone(),
            qbe::Type::Word,
            qbe::Instr::ExtUnsigned(qbe_typ, qbe_val),
        );
        qbe_temp
    }

    fn lower_stm(&mut self, stm: &Stm, cfg: &CFG, qbe_bb: &mut qbe::Block) {
        match stm {
            Stm::Assign { lhs, rhs, typ } => self.lower_assign_stm(*lhs, rhs, *typ, cfg, qbe_bb),
            Stm::Phi { lhs, cases, typ } => {
                let qbe_typ = self.get_type(*typ);

                let LValueKind::Temp(temp_key) = cfg.lvalues[*lhs].kind else {
                    unreachable!("Phi stms are only assigned to temps")
                };

                let qbe_lvalue = self.temps[temp_key].clone();

                let values = cases
                    .iter()
                    .map(|(bb_key, operand_kind)| {
                        (
                            self.basic_blocks[*bb_key].clone(),
                            self.lower_operand_kind(*operand_kind, cfg, qbe_bb),
                        )
                    })
                    .collect();

                qbe_bb.add_phi(qbe_lvalue, qbe_typ, values);
            }
            Stm::Return { rvalue, typ } => {
                let qbe_typ = self.get_type(*typ);
                let qbe_rvalue = self.lower_rvalue(rvalue, cfg, qbe_bb);
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

    fn lower_assign_stm(
        &mut self,
        lhs: LValueKey,
        rhs: &RValue,
        typ: TypeKey,
        cfg: &CFG,
        qbe_bb: &mut qbe::Block,
    ) {
        let qbe_rvalue = self.lower_rvalue(rhs, cfg, qbe_bb);
        let qbe_typ = self.get_type(typ);

        match cfg.lvalues[lhs].kind {
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
                qbe_bb.add_assign(qbe_temp.clone(), qbe_typ.clone(), qbe_rvalue);
                let qbe_ptr = self.lower_lvalue(lvalue_key, cfg, qbe_bb);
                qbe_bb.add_instr(qbe::Instr::Store(qbe_typ, qbe_ptr, qbe_temp));
            }
            LValueKind::MutField { on, idx: field_id } => todo!(),
            LValueKind::MutArrayIdx { on, idx } => todo!(),
            LValueKind::MutArrayConstIdx { on, idx } => todo!(),
            _ => unreachable!(),
        }
    }

    fn lower_rvalue(&mut self, rvalue: &RValue, cfg: &CFG, qbe_bb: &mut qbe::Block) -> qbe::Instr {
        match rvalue {
            RValue::Use(operand) => qbe::Instr::Copy(self.lower_operand(operand, cfg, qbe_bb)),
            RValue::Str(str_key) => qbe::Instr::Copy(self.strs[*str_key].clone()),
            RValue::Ref(lvalue_key) | RValue::RefMut(lvalue_key) => {
                qbe::Instr::Copy(self.lower_lvalue_to_ptr(*lvalue_key, cfg, qbe_bb))
            }
            RValue::Tuple(thin_vec) => todo!(),
            RValue::ArrayElements(thin_vec) => todo!(),
            RValue::ArrayRepeated { repeated, size } => todo!(),
            RValue::Struct { struct_key, fields } => todo!(),
            RValue::Cast { val, kind: to } => todo!(),
            RValue::BinOp { op, lhs, rhs } => {
                let qbe_lhs = self.lower_operand(lhs, cfg, qbe_bb);
                let qbe_rhs = self.lower_operand(rhs, cfg, qbe_bb);
                let is_unsigned = matches!(
                    self.nir.types[lhs.typ],
                    Type::U | Type::U1 | Type::U2 | Type::U4 | Type::U8
                );

                let is_byte_or_short = matches!(
                    self.nir.types[lhs.typ],
                    Type::U1 | Type::U2 | Type::I1 | Type::I2 | Type::Bool
                );

                let qbe_typ = self.get_type(lhs.typ);

                macro_rules! cmp {
                    ($cmp_op: ident) => {
                        qbe::Instr::Cmp(qbe_typ, qbe::Cmp::$cmp_op, qbe_lhs, qbe_rhs)
                    };
                }

                macro_rules! extu_cmp {
                    ($cmp_op: ident) => {
                        qbe::Instr::Cmp(
                            qbe::Type::Word,
                            qbe::Cmp::$cmp_op,
                            self.unsigned_extend(qbe_lhs, qbe_typ.clone(), qbe_bb),
                            self.unsigned_extend(qbe_rhs, qbe_typ, qbe_bb),
                        )
                    };
                }

                macro_rules! exts_cmp {
                    ($cmp_op: ident) => {
                        qbe::Instr::Cmp(
                            qbe::Type::Word,
                            qbe::Cmp::$cmp_op,
                            self.signed_extend(qbe_lhs, qbe_typ.clone(), qbe_bb),
                            self.signed_extend(qbe_rhs, qbe_typ, qbe_bb),
                        )
                    };
                }

                match op {
                    BinOp::GE if is_unsigned && is_byte_or_short => extu_cmp!(Uge),
                    BinOp::GT if is_unsigned && is_byte_or_short => extu_cmp!(Ugt),
                    BinOp::LE if is_unsigned && is_byte_or_short => extu_cmp!(Ule),
                    BinOp::LT if is_unsigned && is_byte_or_short => extu_cmp!(Ult),
                    BinOp::GE if is_unsigned => cmp!(Uge),
                    BinOp::GT if is_unsigned => cmp!(Ugt),
                    BinOp::LE if is_unsigned => cmp!(Ule),
                    BinOp::LT if is_unsigned => cmp!(Ult),
                    BinOp::GE if is_byte_or_short => exts_cmp!(Sge),
                    BinOp::GT if is_byte_or_short => exts_cmp!(Sgt),
                    BinOp::LE if is_byte_or_short => exts_cmp!(Sle),
                    BinOp::LT if is_byte_or_short => exts_cmp!(Slt),
                    BinOp::EqualEqual if is_byte_or_short => exts_cmp!(Eq),
                    BinOp::NotEqual if is_byte_or_short => exts_cmp!(Ne),
                    BinOp::GE => cmp!(Sge),
                    BinOp::GT => cmp!(Sgt),
                    BinOp::LE => cmp!(Sle),
                    BinOp::LT => cmp!(Slt),
                    BinOp::EqualEqual => cmp!(Eq),
                    BinOp::NotEqual => cmp!(Ne),
                    BinOp::BOr => qbe::Instr::Or(qbe_lhs, qbe_rhs),
                    BinOp::BAnd => qbe::Instr::And(qbe_lhs, qbe_rhs),
                    BinOp::Xor => qbe::Instr::Xor(qbe_lhs, qbe_rhs),
                    BinOp::Shr => qbe::Instr::Shr(qbe_lhs, qbe_rhs),
                    BinOp::Shl => qbe::Instr::Shl(qbe_lhs, qbe_rhs),
                    BinOp::Plus => qbe::Instr::Add(qbe_lhs, qbe_rhs),
                    BinOp::Minus => qbe::Instr::Sub(qbe_lhs, qbe_rhs),
                    BinOp::Times => qbe::Instr::Mul(qbe_lhs, qbe_rhs),
                    BinOp::Div if is_unsigned => qbe::Instr::Udiv(qbe_lhs, qbe_rhs),
                    BinOp::Mod if is_unsigned => qbe::Instr::Urem(qbe_lhs, qbe_rhs),
                    BinOp::Div => qbe::Instr::Div(qbe_lhs, qbe_rhs),
                    BinOp::Mod => qbe::Instr::Rem(qbe_lhs, qbe_rhs),
                }
            }
            RValue::UnaryOp { op, operand } => {
                let qbe_operand = self.lower_operand(operand, cfg, qbe_bb);
                match op {
                    UnaryOp::LNot => qbe::Instr::Xor(qbe_operand, qbe::Value::UConst(1)),
                    UnaryOp::BNot => qbe::Instr::Xor(qbe_operand, qbe::Value::Const(-1)),
                    UnaryOp::Minus => qbe::Instr::Sub(qbe::Value::UConst(0), qbe_operand),
                }
            }
            RValue::Call { on, args } => qbe::Instr::Call(
                self.lower_operand(on, cfg, qbe_bb),
                args.iter()
                    .map(|op| (self.get_type(op.typ), self.lower_operand(op, cfg, qbe_bb)))
                    .collect(),
                None,
            ),
        }
    }

    fn lower_lvalue_to_ptr(
        &mut self,
        lvalue_key: LValueKey,
        cfg: &CFG,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        match cfg.lvalues[lvalue_key].kind {
            LValueKind::Binding(binding_key) => self.bindings[binding_key].clone(),
            LValueKind::Static(static_key) => self.statics[static_key].clone(),
            LValueKind::Arg(arg_key) => self.args[&arg_key].clone(),
            LValueKind::Temp(temp_key) => self.temps[temp_key].clone(),
            LValueKind::Deref(lvalue_key) | LValueKind::MutDeref(lvalue_key) => {
                // For dereference, we already have the pointer, just use it
                self.lower_lvalue(lvalue_key, cfg, qbe_bb)
            }
            LValueKind::Field { on, idx: field_id } => todo!(),
            LValueKind::ArrayIdx { on, idx } => todo!(),
            LValueKind::ArrayConstIdx { on, idx } => todo!(),
            LValueKind::MutField { on, idx: field_id } => todo!(),
            LValueKind::MutArrayIdx { on, idx } => todo!(),
            LValueKind::MutArrayConstIdx { on, idx } => todo!(),
        }
    }

    fn add_load_instr(
        &mut self,
        type_key: TypeKey,
        qbe_ptr: qbe::Value,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        let qbe_ty = self.get_type(type_key);
        let qbe_ty_cloned = qbe_ty.clone();
        let load_instr = match &self.nir.types[type_key] {
            Type::FnPtr(_)
            | Type::Ptr(_)
            | Type::MutPtr(_)
            | Type::I
            | Type::I8
            | Type::U
            | Type::U8
            | Type::F4
            | Type::F8 => qbe::Instr::Load(qbe_ty_cloned, qbe_ptr),
            Type::I1 | Type::I2 | Type::I4 => qbe::Instr::LoadSigned(qbe_ty_cloned, qbe_ptr),
            Type::Bool | Type::Char | Type::U1 | Type::U2 | Type::U4 => {
                qbe::Instr::LoadUnsigned(qbe_ty_cloned, qbe_ptr)
            }
            Type::Unit => todo!(),
            Type::Struct(struct_key) => todo!(),
            Type::Slice(type_key) => todo!(),
            Type::MutSlice(type_key) => todo!(),
            Type::Array(array_type_key) => todo!(),
            Type::Tuple(tuple_type_key) => todo!(),
            Type::Lambda(lambda_type_key) => todo!(),
        };
        let qbe_loaded_val = self.new_qbe_temp();
        qbe_bb.add_assign(qbe_loaded_val.clone(), qbe_ty.clone(), load_instr);
        qbe_loaded_val
    }

    fn lower_lvalue(
        &mut self,
        lvalue_key: LValueKey,
        cfg: &CFG,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        match cfg.lvalues[lvalue_key].kind {
            LValueKind::Static(static_key) => self.statics[static_key].clone(),
            LValueKind::Arg(arg_key) => self.args[&arg_key].clone(),
            LValueKind::Temp(temp_key) => self.temps[temp_key].clone(),
            LValueKind::Binding(binding_key) => {
                let type_key = cfg.lvalues[lvalue_key].typ;
                let qbe_ptr = self.bindings[binding_key].clone();
                self.add_load_instr(type_key, qbe_ptr, qbe_bb)
            }
            LValueKind::Deref(lvalue_key) | LValueKind::MutDeref(lvalue_key) => {
                let type_key = cfg.lvalues[lvalue_key].typ;
                let qbe_ptr = self.lower_lvalue(lvalue_key, cfg, qbe_bb);
                self.add_load_instr(type_key, qbe_ptr, qbe_bb)
            }
            LValueKind::Field { on, idx: field_id } => todo!(),
            LValueKind::ArrayIdx { on, idx } => todo!(),
            LValueKind::ArrayConstIdx { on, idx } => todo!(),
            LValueKind::MutField { on, idx: field_id } => todo!(),
            LValueKind::MutArrayIdx { on, idx } => todo!(),
            LValueKind::MutArrayConstIdx { on, idx } => todo!(),
        }
    }

    #[inline]
    fn lower_operand(
        &mut self,
        opernad: &Operand,
        cfg: &CFG,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        self.lower_operand_kind(opernad.kind, cfg, qbe_bb)
    }

    fn lower_operand_kind(
        &mut self,
        opernad_kind: OperandKind,
        cfg: &CFG,
        qbe_bb: &mut qbe::Block,
    ) -> qbe::Value {
        match opernad_kind {
            OperandKind::LValue(lvalue_key) => self.lower_lvalue(lvalue_key, cfg, qbe_bb),
            OperandKind::Const(c) => match c {
                Const::Unit | Const::Null => qbe::Value::UConst(0),
                Const::I(n) => qbe::Value::Const(n as i64),
                Const::I1(n) => qbe::Value::Const(n as i64),
                Const::I2(n) => qbe::Value::Const(n as i64),
                Const::I4(n) => qbe::Value::Const(n as i64),
                Const::I8(n) => qbe::Value::Const(n as i64),
                Const::U(n) => qbe::Value::UConst(n as u64),
                Const::U1(n) => qbe::Value::UConst(n as u64),
                Const::U2(n) => qbe::Value::UConst(n as u64),
                Const::U4(n) => qbe::Value::UConst(n as u64),
                Const::U8(n) => qbe::Value::UConst(n as u64),
                Const::F4(n) => qbe::Value::Single(n),
                Const::F8(n) => qbe::Value::Double(n),
                Const::Bool(n) => qbe::Value::UConst(n as u64),
                Const::Char(n) => qbe::Value::UConst(n as u64),
                Const::Fn(fn_key) => qbe::Value::Global(self.get_fn_name(fn_key)),
            },
        }
    }

    fn lower_block_jmp(&mut self, cfg: &CFG, bb: &BasicBlock, qbe_bb: &mut qbe::Block) {
        if let Some(branch_key) = bb.conditional_goto {
            let branch = &cfg.branches[&branch_key];
            let BranchKind::If(operand) = branch.kind else {
                unreachable!()
            };
            let else_branch = &cfg.branches[&bb.goto.unwrap()];

            if branch.to == BasicBlockKey::END_BASIC_BLOCK
                || else_branch.to == BasicBlockKey::END_BASIC_BLOCK
            {
                // it should void return
                if !qbe_bb.returns() {
                    qbe_bb.add_instr(qbe::Instr::Ret(None));
                }
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
                // it should void return
                if !qbe_bb.returns() {
                    qbe_bb.add_instr(qbe::Instr::Ret(None));
                }
                return;
            }
            qbe_bb.add_jmp(self.basic_blocks[branch.to].clone());
        }
    }
}
