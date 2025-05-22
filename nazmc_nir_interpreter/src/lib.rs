use mem::{bytes::to_f32, Memory};
use nazmc_data_pool::typed_index_collections::TiVec;
use nazmc_nir::*;
use std::collections::HashMap;
mod mem;
pub use mem::bytes;

pub struct Interpreter<'a> {
    nir: &'a NIR<'a>,
    current_cfg: Option<&'a CFG>,
    current_frame: Frame,
    data: &'a mut InterpreterData,
}

#[derive(Default)]
pub struct InterpreterData {
    pub memory: Memory,
    pub structs_layouts: HashMap<StructKey, AggLayout>,
    pub tuples_layouts: HashMap<TupleTypeKey, AggLayout>,
}

pub struct AggLayout {
    pub offsets: Vec<u32>,
    pub size: u32,
}

#[derive(Default)]
struct Frame {
    args: HashMap<ArgKey, PtrKey>,
    bindings: TiVec<BindingKey, PtrKey>,
    temps: TiVec<TempKey, PtrKey>,
    current_block: BasicBlockKey,
    predecessor: Option<BasicBlockKey>,
}

impl<'a> Interpreter<'a> {
    pub fn new(nir: &'a NIR, data: &'a mut InterpreterData) -> Self {
        Self {
            nir,
            data,
            current_cfg: None,
            current_frame: Default::default(),
        }
    }

    pub fn check_dangling_pointer(&mut self, value: &[u8], type_key: TypeKey) -> Result<(), ()> {
        match self.nir.types[type_key] {
            nazmc_nir::Type::Slice(type_key)
            | nazmc_nir::Type::MutSlice(type_key)
            | nazmc_nir::Type::Ptr(type_key)
            | nazmc_nir::Type::MutPtr(type_key) => self.check_dangling_ptr_key(value, type_key),
            nazmc_nir::Type::Struct(struct_key) => {
                self.compute_struct_layout(struct_key);
                for (offset, typ) in self.data.structs_layouts[&struct_key]
                    .offsets
                    .iter()
                    .copied()
                    .zip(self.nir.structs[&struct_key].fields.iter().map(|f| f.typ))
                    .collect::<Vec<_>>()
                {
                    let value = &value[offset as usize..];
                    self.check_dangling_pointer(value, typ)?;
                }
                Ok(())
            }
            nazmc_nir::Type::Tuple(tuple_type_key) => {
                self.compute_tuple_layout(tuple_type_key);
                for (offset, &typ) in self.data.tuples_layouts[&tuple_type_key]
                    .offsets
                    .iter()
                    .copied()
                    .zip(self.nir.tuple_types[tuple_type_key].types.iter())
                    .collect::<Vec<_>>()
                {
                    let value = &value[offset as usize..];
                    self.check_dangling_pointer(value, typ)?;
                }
                Ok(())
            }
            nazmc_nir::Type::Array(array_type_key) => {
                let mut ptr_offsets = Vec::new();

                self.detect_array_ptr_offset(
                    self.nir.array_types[array_type_key].underlying_typ,
                    &mut ptr_offsets,
                );

                let len = self.nir.array_types[array_type_key].size;

                for (offset, type_key) in ptr_offsets {
                    for i in 0..len {
                        let idx = (i + offset) as usize;
                        let value = &value[idx..];
                        self.check_dangling_ptr_key(value, type_key)?;
                    }
                }

                Ok(())
            }
            nazmc_nir::Type::FnPtr(fn_ptr_type_key) => {
                if bytes::to_fn_key(value).is_some() {
                    Ok(())
                } else {
                    Err(())
                }
            }
            nazmc_nir::Type::Lambda(lambda_type_key) => todo!(),
            _ => Ok(()),
        }
    }

    fn check_dangling_ptr_key(&mut self, value: &[u8], type_key: TypeKey) -> Result<(), ()> {
        let top = self.data.memory.get_top();

        let ptr_key = bytes::to_ptr_key(&value).unwrap();

        if ptr_key.0 >= top.0 {
            return Err(());
        }

        let value = self.get_bytes_at(ptr_key, type_key).to_vec();
        self.check_dangling_pointer(&value, type_key)
    }

    fn detect_array_ptr_offset(
        &self,
        underlying_typ: TypeKey,
        ptr_offsets: &mut Vec<(u32, TypeKey)>,
    ) {
        match self.nir.types[underlying_typ] {
            nazmc_nir::Type::FnPtr(_) => ptr_offsets.push((0, underlying_typ)),
            nazmc_nir::Type::Slice(type_key)
            | nazmc_nir::Type::MutSlice(type_key)
            | nazmc_nir::Type::Ptr(type_key)
            | nazmc_nir::Type::MutPtr(type_key) => {
                ptr_offsets.push((0, type_key));
            }
            nazmc_nir::Type::Struct(struct_key) => {
                for (&offset, typ) in self.data.structs_layouts[&struct_key]
                    .offsets
                    .iter()
                    .zip(self.nir.structs[&struct_key].fields.iter().map(|f| f.typ))
                {
                    let base = ptr_offsets.len();
                    self.detect_array_ptr_offset(typ, ptr_offsets);
                    for (i, _) in &mut ptr_offsets[base..] {
                        *i += offset;
                    }
                }
            }
            nazmc_nir::Type::Tuple(tuple_type_key) => {
                for (&offset, &typ) in self.data.tuples_layouts[&tuple_type_key]
                    .offsets
                    .iter()
                    .zip(self.nir.tuple_types[tuple_type_key].types.iter())
                {
                    let base = ptr_offsets.len();
                    self.detect_array_ptr_offset(typ, ptr_offsets);
                    for (i, _) in &mut ptr_offsets[base..] {
                        *i += offset;
                    }
                }
            }
            nazmc_nir::Type::Array(array_type_key) => {
                self.detect_array_ptr_offset(
                    self.nir.array_types[array_type_key].underlying_typ,
                    ptr_offsets,
                );
            }
            nazmc_nir::Type::Lambda(lambda_type_key) => todo!(),
            _ => {}
        }
    }

    fn get_bytes_at(&mut self, at: PtrKey, type_key: TypeKey) -> &[u8] {
        let type_size = self.get_type_size(type_key);
        self.data.memory.get_bytes_at(at, type_size as usize)
    }

    fn compute_struct_layout(&mut self, struct_key: StructKey) {
        if self.data.structs_layouts.contains_key(&struct_key) {
            return;
        }
        let mut offsets = Vec::with_capacity(self.nir.structs[&struct_key].fields.len());
        let mut size = 0;
        for field in &self.nir.structs[&struct_key].fields {
            offsets.push(size);
            let field_size = self.get_type_size(field.typ);
            size += field_size;
        }

        self.data
            .structs_layouts
            .insert(struct_key, AggLayout { offsets, size });
    }

    fn compute_tuple_layout(&mut self, tuple_type_key: TupleTypeKey) {
        if self.data.tuples_layouts.contains_key(&tuple_type_key) {
            return;
        }

        let mut offsets = Vec::with_capacity(self.nir.tuple_types[tuple_type_key].types.len());
        let mut size = 0;
        for &typ in &self.nir.tuple_types[tuple_type_key].types {
            offsets.push(size);
            let typ_size = self.get_type_size(typ);
            size += typ_size;
        }

        self.data
            .tuples_layouts
            .insert(tuple_type_key, AggLayout { offsets, size });
    }

    fn get_type_size(&mut self, type_key: TypeKey) -> u32 {
        match self.nir.types[type_key] {
            Type::Unit => 0,
            Type::I | Type::U | Type::MutPtr(_) | Type::Ptr(_) | Type::FnPtr(_) => {
                std::mem::size_of::<usize>() as u32
            }
            Type::I1 | Type::U1 | Type::Bool => 1,
            Type::I2 | Type::U2 => 2,
            Type::I4 | Type::U4 | Type::F4 | Type::Char => 4,
            Type::I8 | Type::U8 | Type::F8 => 8,
            Type::Slice(_) | Type::MutSlice(_) => 2 * std::mem::size_of::<usize>() as u32,
            Type::Struct(struct_key) => {
                self.compute_struct_layout(struct_key);
                self.data.structs_layouts[&struct_key].size
            }
            Type::Tuple(tuple_type_key) => {
                self.compute_tuple_layout(tuple_type_key);
                self.data.tuples_layouts[&tuple_type_key].size
            }
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

    pub fn execute_function(
        &mut self,
        fn_key: FnKey,
        args: HashMap<ArgKey, PtrKey>,
    ) -> Result<Vec<u8>, ()> {
        let function = &self.nir.fns[fn_key];
        let FnLinkage::Local(cfg) = &function.linkage else {
            unreachable!()
        };
        self.execute_cfg(&cfg, args)
    }

    pub fn execute_cfg(
        &mut self,
        cfg: &'a CFG,
        args: HashMap<ArgKey, PtrKey>,
    ) -> Result<Vec<u8>, ()> {
        let prev_frame = std::mem::take(&mut self.current_frame);
        let prev_cfg = self.current_cfg;
        self.current_frame.args = args;

        let top = self.data.memory.get_top();

        for binding in &cfg.bindings {
            let type_size = self.get_type_size(binding.typ);
            let ptr = self.data.memory.alloc(type_size as usize);
            self.current_frame.bindings.push(ptr);
        }

        for temp in &cfg.temps {
            let type_size = self.get_type_size(temp.typ);
            let ptr = self.data.memory.alloc(type_size as usize);
            self.current_frame.temps.push(ptr);
        }

        self.current_frame.current_block = BasicBlockKey::START_BASIC_BLOCK;
        self.current_cfg = Some(cfg);
        let mut ret_value = vec![];

        while self.current_frame.current_block != BasicBlockKey::END_BASIC_BLOCK {
            let bb = &cfg.basic_blocks[&self.current_frame.current_block];
            ret_value = self.execute_block(bb)?;
        }

        self.data.memory.set_top(top);
        self.current_frame = prev_frame;
        self.current_cfg = prev_cfg;

        Ok(ret_value)
    }

    fn execute_block(&mut self, bb: &BasicBlock) -> Result<Vec<u8>, ()> {
        for stm in &bb.stms {
            match stm {
                Stm::Assign { lhs, rhs, typ } => {
                    let LValue { typ, kind } = self.current_cfg.unwrap().lvalues[*lhs];
                    let rhs = self.evaluate_rvalue(rhs)?;
                    let lhs = self.evaluate_lvalue_ptr(*lhs)?;
                    self.data.memory.push_bytes_at(lhs, &rhs);
                }
                Stm::Phi { lhs, cases, typ } => {
                    let frame_pred = self.current_frame.predecessor.unwrap();
                    let (_, op) = cases.iter().find(|(pred, _)| *pred == frame_pred).unwrap();
                    let val = self.evaluate_operand_kind(op)?.collect::<Vec<_>>();
                    let lhs = self.evaluate_lvalue_ptr(*lhs)?;
                    self.data.memory.push_bytes_at(lhs, &val);
                }
                Stm::Return { rvalue, typ } => {
                    let value = self.evaluate_rvalue(rvalue);
                    self.current_frame.current_block = BasicBlockKey::END_BASIC_BLOCK;
                    return value;
                }
                Stm::Drop(lvalue) => todo!(),
            }
        }

        self.execute_branches(bb)?;
        Ok(vec![])
    }

    fn execute_branches(&mut self, bb: &BasicBlock) -> Result<(), ()> {
        let cfg = self.current_cfg.unwrap();
        let next_block = if let Some(bk) = bb.conditional_goto {
            let branch = &cfg.branches[&bk];
            let BranchKind::If(op) = &branch.kind else {
                unreachable!()
            };

            let cond_bool = bytes::to_bool(&self.evaluate_operand_to_vec(op)?).unwrap();

            if cond_bool {
                branch.to
            } else {
                cfg.branches[&bb.goto.unwrap()].to
            }
        } else {
            cfg.branches[&bb.goto.unwrap()].to
        };

        self.current_frame.predecessor = Some(self.current_frame.current_block);
        self.current_frame.current_block = next_block;
        Ok(())
    }

    fn evaluate_operand_to_vec(&mut self, op: &Operand) -> Result<Vec<u8>, ()> {
        Ok(self.evaluate_operand(op)?.collect())
    }

    fn evaluate_operand(&mut self, op: &Operand) -> Result<Box<dyn Iterator<Item = u8> + '_>, ()> {
        self.evaluate_operand_kind(&op.kind)
    }

    fn evaluate_operand_kind(
        &mut self,
        kind: &OperandKind,
    ) -> Result<Box<dyn Iterator<Item = u8> + '_>, ()> {
        match kind {
            OperandKind::LValue(lv) => Ok(Box::new(self.evaluate_lvalue(*lv)?.iter().copied())),
            OperandKind::Const(c) => Ok(self.evaluate_constant(c)),
        }
    }

    fn evaluate_lvalue_ptr(&mut self, lv: LValueKey) -> Result<PtrKey, ()> {
        let cfg = self.current_cfg.unwrap();

        Ok(match cfg.lvalues[lv].kind {
            LValueKind::Binding(binding_key) => self.current_frame.bindings[binding_key],
            LValueKind::Const(const_key) => self.nir.consts[&const_key].value,
            LValueKind::Temp(temp_key) => self.current_frame.temps[temp_key],
            LValueKind::Arg(arg_key) => self.current_frame.args[&arg_key],
            LValueKind::Static(static_key) => todo!(),
            LValueKind::Deref(on) | LValueKind::MutDeref(on) => {
                let on = self.evaluate_lvalue(on)?;
                bytes::to_ptr_key(on).unwrap()
            }
            LValueKind::Field { on, idx } | LValueKind::MutField { on, idx } => {
                let field_offset = match self.nir.types[cfg.lvalues[on].typ] {
                    Type::Struct(struct_key) => {
                        self.compute_struct_layout(struct_key);
                        self.data.structs_layouts[&struct_key].offsets[idx as usize]
                    }
                    Type::Tuple(tuple_type_key) => {
                        self.compute_tuple_layout(tuple_type_key);
                        self.data.tuples_layouts[&tuple_type_key].offsets[idx as usize]
                    }
                    Type::Slice(_) | Type::MutSlice(_) => idx * std::mem::size_of::<usize>() as u32,
                    _ => unreachable!(),
                };

                let mut on = self.evaluate_lvalue_ptr(on)?;
                on.0 += field_offset;
                on
            }
            LValueKind::ArrayConstIdx { on, idx } | LValueKind::MutArrayConstIdx { on, idx } => {
                let Type::Array(array_type_key) = self.nir.types[cfg.lvalues[on].typ] else {
                    unreachable!()
                };
                let underlying_size =
                    self.get_type_size(self.nir.array_types[array_type_key].underlying_typ);
                let offset = underlying_size * idx;

                let mut on = self.evaluate_lvalue_ptr(on)?;
                on.0 += offset;
                on
            }
            LValueKind::ArrayIdx { on, idx } | LValueKind::MutArrayIdx { on, idx } => {
                let Type::Array(array_type_key) = self.nir.types[cfg.lvalues[on].typ] else {
                    unreachable!()
                };
                let underlying_size =
                    self.get_type_size(self.nir.array_types[array_type_key].underlying_typ);

                let mut on = self.evaluate_lvalue_ptr(on)?;
                let idx = self.evaluate_lvalue(idx)?;
                let idx = bytes::to_usize(idx).unwrap();
                let offset = underlying_size * idx as u32;
                on.0 += offset;
                on
            }
        })
    }

    fn evaluate_lvalue(&mut self, lv: LValueKey) -> Result<&[u8], ()> {
        let ptr_key = self.evaluate_lvalue_ptr(lv)?;
        if self.data.memory.get_top().0 >= ptr_key.0 {
            Err(())
        } else {
            Ok(self.get_bytes_at(ptr_key, self.current_cfg.unwrap().lvalues[lv].typ))
        }
    }

    fn evaluate_constant(&self, c: &Const) -> Box<dyn Iterator<Item = u8> + '_> {
        let bytes = match c {
            Const::Unit => vec![],
            Const::Null => usize::MAX.to_le_bytes().to_vec(),
            Const::I(v) => v.to_le_bytes().to_vec(),
            Const::I1(v) => v.to_le_bytes().to_vec(),
            Const::I2(v) => v.to_le_bytes().to_vec(),
            Const::I4(v) => v.to_le_bytes().to_vec(),
            Const::I8(v) => v.to_le_bytes().to_vec(),
            Const::U(v) => v.to_le_bytes().to_vec(),
            Const::U1(v) => v.to_le_bytes().to_vec(),
            Const::U2(v) => v.to_le_bytes().to_vec(),
            Const::U4(v) => v.to_le_bytes().to_vec(),
            Const::U8(v) => v.to_le_bytes().to_vec(),
            Const::F4(v) => v.to_le_bytes().to_vec(),
            Const::F8(v) => v.to_le_bytes().to_vec(),
            Const::Bool(b) => vec![*b as u8],
            Const::Char(c) => (*c as u32).to_le_bytes().to_vec(),
            Const::Fn(fk) => (fk.0 as usize).to_le_bytes().to_vec(),
        };

        Box::new(bytes.into_iter())
    }

    fn evaluate_rvalue(&mut self, rvalue: &RValue) -> Result<Vec<u8>, ()> {
        Ok(match rvalue {
            RValue::Use(op) => self.evaluate_operand_to_vec(op)?,
            RValue::Str(sk) => self
                .data
                .memory
                .get_bytes_at(
                    self.nir.interpreter_str_slices_pool[*sk],
                    std::mem::size_of::<usize>() * 2,
                )
                .to_vec(),
            RValue::RefMut(lv) | RValue::Ref(lv) => {
                let ptr = self.evaluate_lvalue_ptr(*lv)?;
                (ptr.0 as usize).to_le_bytes().to_vec()
            }
            RValue::Struct {
                struct_key: _,
                fields: elements,
            }
            | RValue::Tuple(elements)
            | RValue::ArrayElements(elements) => {
                elements.iter().try_fold(Vec::new(), |mut acc, element| {
                    acc.extend(self.evaluate_operand_to_vec(element)?);
                    Ok(acc)
                })?
            }
            RValue::ArrayRepeated { repeated, size } => {
                let val = self.evaluate_operand_to_vec(repeated)?.into_iter();
                (0..*size).flat_map(move |_| val.clone()).collect()
            }
            RValue::UnaryOp { op, operand } => self.apply_unaryop(*op, operand)?,
            RValue::BinOp { op, lhs, rhs } => self.apply_binop(*op, lhs, rhs)?,
            RValue::Cast { val, kind } => self.apply_cast(val, *kind)?,
            RValue::Call { on, args } => {
                let on = self.evaluate_operand_to_vec(on)?;
                let on = bytes::to_usize(&on).unwrap();
                let fn_key = FnKey(on as u32);
                let top = self.data.memory.get_top();

                let mut frame_args = HashMap::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let arg = self.evaluate_operand_to_vec(arg)?;
                    let arg_ptr = self.data.memory.push_bytes(&arg);
                    frame_args.insert(ArgKey::from(i), arg_ptr);
                }

                let return_value = self.execute_function(fn_key, frame_args)?;

                self.data.memory.set_top(top);

                return_value
            }
        })
    }

    fn apply_unaryop(&mut self, op: UnaryOp, operand: &Operand) -> Result<Vec<u8>, ()> {
        let typ = operand.typ;
        let val = self.evaluate_operand_to_vec(operand)?;

        Ok(match op {
            UnaryOp::LNot => vec![!bytes::to_bool(&val).unwrap() as u8],
            UnaryOp::BNot => {
                macro_rules! bnot {
                    ($method: ident) => {
                        (!bytes::$method(&val).unwrap()).to_le_bytes().to_vec()
                    };
                }
                match self.nir.types[typ] {
                    Type::I => bnot!(to_isize),
                    Type::I1 => bnot!(to_i8),
                    Type::I2 => bnot!(to_i16),
                    Type::I4 => bnot!(to_i32),
                    Type::I8 => bnot!(to_i64),
                    Type::U => bnot!(to_usize),
                    Type::U1 => bnot!(to_u8),
                    Type::U2 => bnot!(to_u16),
                    Type::U4 => bnot!(to_u32),
                    Type::U8 => bnot!(to_u64),
                    _ => unreachable!(),
                }
            }
            UnaryOp::Minus => {
                macro_rules! minus {
                    ($method: ident) => {
                        (-bytes::$method(&val).unwrap()).to_le_bytes().to_vec()
                    };
                }
                match self.nir.types[typ] {
                    Type::I => minus!(to_isize),
                    Type::I1 => minus!(to_i8),
                    Type::I2 => minus!(to_i16),
                    Type::I4 => minus!(to_i32),
                    Type::I8 => minus!(to_i64),
                    Type::F4 => minus!(to_f32),
                    Type::F8 => minus!(to_f64),
                    _ => unreachable!(),
                }
            }
        })
    }

    fn apply_binop(&mut self, op: BinOp, lhs: &Operand, rhs: &Operand) -> Result<Vec<u8>, ()> {
        let lhs_typ = lhs.typ;
        let rhs_typ = rhs.typ;
        let lhs = self.evaluate_operand_to_vec(lhs)?;
        let rhs = self.evaluate_operand_to_vec(rhs)?;

        macro_rules! apply_int_op {
            ($method:ident) => {{
                let (lhs, rhs) = (bytes::$method(&lhs).unwrap(), bytes::$method(&rhs).unwrap());
                match op {
                    BinOp::Plus => (lhs + rhs).to_le_bytes().to_vec(),
                    BinOp::Minus => (lhs - rhs).to_le_bytes().to_vec(),
                    BinOp::Times => (lhs * rhs).to_le_bytes().to_vec(),
                    BinOp::Div => (lhs / rhs).to_le_bytes().to_vec(),
                    BinOp::Mod => (lhs % rhs).to_le_bytes().to_vec(),
                    BinOp::EqualEqual => vec![(lhs == rhs) as u8],
                    BinOp::NotEqual => vec![(lhs != rhs) as u8],
                    BinOp::GE => vec![(lhs >= rhs) as u8],
                    BinOp::GT => vec![(lhs > rhs) as u8],
                    BinOp::LE => vec![(lhs <= rhs) as u8],
                    BinOp::LT => vec![(lhs < rhs) as u8],
                    BinOp::BOr => (lhs | rhs).to_le_bytes().to_vec(),
                    BinOp::Xor => (lhs ^ rhs).to_le_bytes().to_vec(),
                    BinOp::BAnd => (lhs & rhs).to_le_bytes().to_vec(),
                    BinOp::Shr => (lhs >> rhs).to_le_bytes().to_vec(),
                    BinOp::Shl => (lhs << rhs).to_le_bytes().to_vec(),
                }
            }};
        }

        macro_rules! apply_float_op {
            ($method:ident) => {{
                let (lhs, rhs) = (bytes::$method(&lhs).unwrap(), bytes::$method(&rhs).unwrap());
                match op {
                    BinOp::Plus => (lhs + rhs).to_le_bytes().to_vec(),
                    BinOp::Minus => (lhs - rhs).to_le_bytes().to_vec(),
                    BinOp::Times => (lhs * rhs).to_le_bytes().to_vec(),
                    BinOp::Div => (lhs / rhs).to_le_bytes().to_vec(),
                    BinOp::Mod => (lhs % rhs).to_le_bytes().to_vec(),
                    BinOp::EqualEqual => vec![(lhs == rhs) as u8],
                    BinOp::NotEqual => vec![(lhs != rhs) as u8],
                    BinOp::GE => vec![(lhs >= rhs) as u8],
                    BinOp::GT => vec![(lhs > rhs) as u8],
                    BinOp::LE => vec![(lhs <= rhs) as u8],
                    BinOp::LT => vec![(lhs < rhs) as u8],
                    _ => unreachable!(),
                }
            }};
        }

        Ok(match self.nir.types[lhs_typ] {
            Type::I => apply_int_op!(to_isize),
            Type::I1 => apply_int_op!(to_i8),
            Type::I2 => apply_int_op!(to_i16),
            Type::I4 => apply_int_op!(to_i32),
            Type::I8 => apply_int_op!(to_i64),
            Type::U => apply_int_op!(to_usize),
            Type::U1 => apply_int_op!(to_u8),
            Type::U2 => apply_int_op!(to_u16),
            Type::U4 => apply_int_op!(to_u32),
            Type::U8 => apply_int_op!(to_u64),
            Type::F4 => apply_float_op!(to_f32),
            Type::F8 => apply_float_op!(to_f64),
            Type::Bool => {
                let (lhs, rhs) = (bytes::to_bool(&lhs).unwrap(), bytes::to_bool(&rhs).unwrap());
                match op {
                    BinOp::EqualEqual => vec![(rhs == lhs) as u8],
                    BinOp::NotEqual => vec![(rhs != lhs) as u8],
                    _ => unreachable!(),
                }
            }
            Type::Ptr(type_key) | Type::MutPtr(type_key)
                if matches!(self.nir.types[rhs_typ], Type::U) =>
            {
                let lhs = bytes::to_ptr_key(&lhs).unwrap().0;
                let rhs = bytes::to_usize(&rhs).unwrap() as u32;
                let type_size = self.get_type_size(type_key);

                let ptr = if let BinOp::Minus = op {
                    lhs - rhs * type_size
                } else {
                    lhs + rhs * type_size
                } as usize;

                ptr.to_le_bytes().to_vec()
            }
            Type::Ptr(type_key) | Type::MutPtr(type_key) => {
                let lhs = bytes::to_ptr_key(&lhs).unwrap().0;
                let rhs = bytes::to_ptr_key(&rhs).unwrap().0;

                vec![match op {
                    BinOp::EqualEqual => lhs == rhs,
                    BinOp::NotEqual => lhs != rhs,
                    BinOp::GE => lhs >= rhs,
                    BinOp::GT => lhs > rhs,
                    BinOp::LE => lhs <= rhs,
                    BinOp::LT => lhs < rhs,
                    BinOp::Minus => {
                        let type_size = self.get_type_size(type_key);
                        return Ok(((lhs - rhs) / type_size).to_le_bytes().to_vec());
                    }
                    _ => unreachable!(),
                } as u8]
            }
            _ => unreachable!(),
        })
    }

    fn apply_cast(&mut self, val: &Operand, kind: CastKind) -> Result<Vec<u8>, ()> {
        use CastKind::*;
        use Size::*;

        if let ArrayToSlice { len } = kind {
            let OperandKind::LValue(lvalue_key) = val.kind else {
                unreachable!()
            };

            let ptr = self.evaluate_lvalue_ptr(lvalue_key)?;
            let mut vec = Vec::with_capacity(2 * std::mem::size_of::<usize>());
            vec.extend_from_slice((ptr.0 as usize).to_le_bytes().as_slice());
            vec.extend_from_slice((len as usize).to_le_bytes().as_slice());
            return Ok(vec);
        }

        let val = self.evaluate_operand_to_vec(val)?;

        macro_rules! convert {
            ($method: ident) => {
                bytes::$method(&val).unwrap()
            };

            ($method: ident as $as_expr: ty) => {
                (convert!($method) as $as_expr).to_le_bytes().to_vec()
            };
        }

        macro_rules! convert_to_int {

            ($e: expr, $int_size: ident) => {
                match $int_size {
                    Ptr => ($e as isize).to_le_bytes().to_vec(),
                    Byte => ($e as i8).to_le_bytes().to_vec(),
                    Word => ($e as i16).to_le_bytes().to_vec(),
                    DWord => ($e as i32).to_le_bytes().to_vec(),
                    QWord => ($e as i64).to_le_bytes().to_vec(),
                }
            };

	    // $m for method
            ($method: ident, $int_size: ident, $m: ident) => {{
                let c = convert!($method);
		convert_to_int!(c, $int_size)
            }};
        }

        macro_rules! convert_to_uint {
            ($e: expr, $int_size: ident) => {
                match $int_size {
                    Ptr => ($e as usize).to_le_bytes().to_vec(),
                    Byte => ($e as u8).to_le_bytes().to_vec(),
                    Word => ($e as u16).to_le_bytes().to_vec(),
                    DWord => ($e as u32).to_le_bytes().to_vec(),
                    QWord => ($e as u64).to_le_bytes().to_vec(),
                }
            };

	    // $m for method
            ($method: ident, $int_size: ident, $m: ident) => {{
                let c = convert!($method);
                convert_to_uint!(c, $int_size)
            }};
        }

        macro_rules! convert_from_int {
            ($int_size: ident as $as_expr: ty) => {{
                match $int_size {
                    Ptr => (convert!(to_isize) as $as_expr),
                    Byte => (convert!(to_i8) as $as_expr),
                    Word => (convert!(to_i16) as $as_expr),
                    DWord => (convert!(to_i32) as $as_expr),
                    QWord => (convert!(to_i64) as $as_expr),
                }
            }};

            ($int_size: ident as $as_expr: ty, $to_vec: ident) => {{
                match $int_size {
                    Ptr => (convert!(to_isize) as $as_expr).to_le_bytes().to_vec(),
                    Byte => (convert!(to_i8) as $as_expr).to_le_bytes().to_vec(),
                    Word => (convert!(to_i16) as $as_expr).to_le_bytes().to_vec(),
                    DWord => (convert!(to_i32) as $as_expr).to_le_bytes().to_vec(),
                    QWord => (convert!(to_i64) as $as_expr).to_le_bytes().to_vec(),
                }
            }};
        }

        macro_rules! convert_from_uint {
            ($int_size: ident as $as_expr: ty, $to_vec: ident) => {{
                match $int_size {
                    Ptr => (convert!(to_usize) as $as_expr).to_le_bytes().to_vec(),
                    Byte => (convert!(to_u8) as $as_expr).to_le_bytes().to_vec(),
                    Word => (convert!(to_u16) as $as_expr).to_le_bytes().to_vec(),
                    DWord => (convert!(to_u32) as $as_expr).to_le_bytes().to_vec(),
                    QWord => (convert!(to_u64) as $as_expr).to_le_bytes().to_vec(),
                }
            }};

            ($int_size: ident as $as_expr: ty) => {{
                match $int_size {
                    Ptr => (convert!(to_usize) as $as_expr),
                    Byte => (convert!(to_u8) as $as_expr),
                    Word => (convert!(to_u16) as $as_expr),
                    DWord => (convert!(to_u32) as $as_expr),
                    QWord => (convert!(to_u64) as $as_expr),
                }
            }};
        }

        Ok(match kind {
            ArrayToSlice { len } => unreachable!(),
            PtrToPtr | PtrToUInt | UIntToPtr => val, // no op
            U1ToChar => (convert!(to_u8) as char as u32).to_le_bytes().to_vec(),
            F4ToF8 => convert!(to_f32 as f64),
            F8ToF4 => convert!(to_f64 as f32),
            F4ToInt { int_size } => convert_to_int!(to_f32, int_size),
            F4ToUInt { int_size } => convert_to_uint!(to_f32, int_size),
            F8ToInt { int_size } => convert_to_int!(to_f64, int_size, m),
            F8ToUInt { int_size } => convert_to_uint!(to_f64, int_size, m),
            BoolToInt { int_size } => convert_to_int!(to_bool, int_size, m),
            BoolToUInt { int_size } => convert_to_uint!(to_bool, int_size, m),
            CharToInt { int_size } => convert_to_int!(to_char, int_size, m),
            CharToUInt { int_size } => convert_to_uint!(to_char, int_size, m),
            IntToF4 { int_size } => convert_from_int!(int_size as f32, to_vec),
            IntToF8 { int_size } => convert_from_int!(int_size as f64, to_vec),
            UIntToF4 { int_size } => convert_from_uint!(int_size as f32, to_vec),
            UIntToF8 { int_size } => convert_from_uint!(int_size as f64, to_vec),
            IntToInt {
                int1_size,
                int2_size,
            } => {
                let int = convert_from_int!(int1_size as i64);
                convert_to_int!(int, int2_size)
            }
            IntToUInt {
                int1_size,
                int2_size,
            } => {
                let int = convert_from_int!(int1_size as i64);
                convert_to_uint!(int, int2_size)
            }
            UIntToInt {
                int1_size,
                int2_size,
            } => {
                let int = convert_from_uint!(int1_size as u64);
                convert_to_int!(int, int2_size)
            }
            UIntToUInt {
                int1_size,
                int2_size,
            } => {
                let int = convert_from_uint!(int1_size as u64);
                convert_to_uint!(int, int2_size)
            }
        })
    }
}
