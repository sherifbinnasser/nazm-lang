use nazmc_nir::*;
use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, VecDeque},
    rc::Rc,
};

#[derive(Default, Debug, Clone)]
pub struct RcValue {
    data: Rc<RefCell<Value>>,
}

impl RcValue {
    pub fn new(value: Value) -> Self {
        Self {
            data: Rc::new(RefCell::new(value)),
        }
    }

    pub fn copy(&self) -> Self {
        let data = match &*self.borrow() {
            Value::Agg(elements) => Value::Agg(Rc::new(
                elements.iter().map(|element| element.copy()).collect(),
            )),
            data => data.clone(),
        };
        Self {
            data: Rc::new(RefCell::new(data)),
        }
    }

    pub fn borrow(&self) -> Ref<'_, Value> {
        self.data.borrow()
    }

    pub fn inner(&self) -> Value {
        self.borrow().clone()
    }
}

#[derive(Default, Debug, Clone)]
pub enum Value {
    #[default]
    Unit,
    Int(i64),
    UInt(u64),
    Float(f64),
    Bool(bool),
    Char(char),
    FnPtr(FnKey),
    Ptr(RcValue),
    Agg(Rc<Vec<RcValue>>),
}

pub struct Interpreter<'a> {
    nir: &'a NIR<'a>,
    str_pool: Vec<RcValue>,
    current_cfg: Option<&'a CFG>,
    current_frame: Frame,
    null_ptr: RcValue,
}

#[derive(Default)]
struct Frame {
    args: HashMap<ArgKey, RcValue>,
    bindings: HashMap<BindingKey, RcValue>,
    temps: HashMap<TempKey, RcValue>,
    current_block: BasicBlockKey,
    predecessor: Option<BasicBlockKey>,
}

impl<'a> Interpreter<'a> {
    pub fn new(nir: &'a NIR) -> Self {
        let mut str_pool = Vec::with_capacity(nir.str_pool.len());
        for string in &nir.str_pool {
            let byte_array = RcValue::new(Value::Agg(Rc::new(
                string
                    .bytes()
                    .map(|byte| RcValue::new(Value::UInt(byte as u64)))
                    .collect(),
            )));
            let slice = RcValue::new(Value::Agg(Rc::new(vec![
                RcValue::new(Value::Ptr(byte_array)),
                RcValue::new(Value::UInt(string.len() as u64)),
            ])));
            str_pool.push(slice);
        }

        Self {
            str_pool,
            nir,
            current_cfg: None,
            current_frame: Default::default(),
            null_ptr: RcValue::default(),
        }
    }

    pub fn execute_function(
        &mut self,
        fn_key: FnKey,
        args: HashMap<ArgKey, RcValue>,
    ) -> Result<RcValue, String> {
        let function = &self.nir.fns[fn_key];
        let cfg = match &function.linkage {
            FnLinkage::Local(cfg) => cfg,
            _ => return Err("External functions cannot be executed".into()),
        };
        self.execute_cfg(&cfg, args)
    }

    fn execute_cfg(
        &mut self,
        cfg: &'a CFG,
        args: HashMap<ArgKey, RcValue>,
    ) -> Result<RcValue, String> {
        let prev_frame = std::mem::take(&mut self.current_frame);
        let prev_cfg = self.current_cfg;
        self.current_frame.args = args;
        self.current_frame.current_block = BasicBlockKey::START_BASIC_BLOCK;
        self.current_cfg = Some(cfg);
        let mut ret_value = RcValue::new(Value::Unit);

        while self.current_frame.current_block != BasicBlockKey::END_BASIC_BLOCK {
            let bb = cfg
                .basic_blocks
                .get(&self.current_frame.current_block)
                .ok_or_else(|| {
                    format!("Missing basic block {:?}", self.current_frame.current_block)
                })?;

            ret_value = self.execute_block(bb)?;
        }

        self.current_frame = prev_frame;
        self.current_cfg = prev_cfg;
        Ok(ret_value)
    }

    fn execute_block(&mut self, bb: &BasicBlock) -> Result<RcValue, String> {
        for stm in &bb.stms {
            match stm {
                Stm::Assign { lhs, rhs, typ } => {
                    let rhs = self.evaluate_rvalue(rhs)?;
                    let lhs = self.evaluate_lvalue(*lhs)?;
                    *lhs.data.borrow_mut() = rhs.inner();
                }
                Stm::Phi { lhs, cases, typ } => {
                    let val = cases
                        .iter()
                        .find(|(pred, _)| *pred == self.current_frame.predecessor.unwrap())
                        .map(|(_, op)| self.evaluate_operand_kind(op))
                        .ok_or("Phi node missing predecessor")??;
                    let ptr = self.evaluate_lvalue(*lhs)?;
                    *ptr.data.borrow_mut() = val.inner();
                }
                Stm::Return { rvalue, typ } => {
                    let value = self.evaluate_rvalue(rvalue)?;
                    self.current_frame.current_block = BasicBlockKey::END_BASIC_BLOCK;
                    return Ok(value);
                }
                Stm::Drop(lvalue) => todo!(),
            }
        }

        self.execute_branches(bb)?;
        Ok(RcValue::new(Value::Unit))
    }

    fn execute_branches(&mut self, bb: &BasicBlock) -> Result<(), String> {
        let cfg = self.current_cfg.unwrap();
        let next_block = if let Some(bk) = bb.conditional_goto {
            let branch = &cfg.branches[&bk];
            if let BranchKind::If(op) = &branch.kind {
                let Value::Bool(cond_bool) = self.evaluate_operand(op)?.inner() else {
                    return Err("Non-boolean condition in if branch".into());
                };

                if cond_bool {
                    branch.to
                } else {
                    cfg.branches[&bb.goto.unwrap()].to
                }
            } else {
                return Err("Non-conditional branch marked as conditional".into());
            }
        } else {
            cfg.branches[&bb.goto.unwrap()].to
        };

        self.current_frame.predecessor = Some(self.current_frame.current_block);
        self.current_frame.current_block = next_block;
        Ok(())
    }

    fn evaluate_operand(&mut self, op: &Operand) -> Result<RcValue, String> {
        self.evaluate_operand_kind(&op.kind)
    }

    fn evaluate_operand_kind(&mut self, kind: &OperandKind) -> Result<RcValue, String> {
        match kind {
            OperandKind::LValue(lv) => self.evaluate_lvalue(*lv).map(|v| v.copy()),
            OperandKind::Const(c) => self.evaluate_constant(*c),
        }
    }

    fn evaluate_lvalue(&mut self, lv: LValueKey) -> Result<RcValue, String> {
        let rc_value = match self.current_cfg.unwrap().lvalues[lv].kind {
            LValueKind::Binding(binding_key) => self
                .current_frame
                .bindings
                .entry(binding_key)
                .or_default()
                .clone(),
            LValueKind::Temp(temp_key) => self
                .current_frame
                .temps
                .entry(temp_key)
                .or_default()
                .clone(),
            LValueKind::Arg(arg_key) => self.current_frame.args[&arg_key].clone(), // Args should be provided before any fn call, so no entry
            LValueKind::Static(static_key) => todo!(),
            LValueKind::Deref(on) | LValueKind::MutDeref(on) => {
                let on = self.evaluate_lvalue(on)?;
                if Rc::ptr_eq(&on.data, &self.null_ptr.data) {
                    return Err("NullPointerException".into());
                };
                let Value::Ptr(ptr) = &*on.borrow() else {
                    unreachable!()
                };
                ptr.clone()
            }
            LValueKind::Field { on, idx }
            | LValueKind::MutField { on, idx }
            | LValueKind::ArrayConstIdx { on, idx }
            | LValueKind::MutArrayConstIdx { on, idx } => {
                let on = self.evaluate_lvalue(on)?;
                let Value::Agg(elements) = &*on.borrow() else {
                    unreachable!()
                };
                elements[idx as usize].clone()
            }
            LValueKind::ArrayIdx { on, idx } | LValueKind::MutArrayIdx { on, idx } => {
                let on = self.evaluate_lvalue(on)?;
                let Value::Agg(elements) = &*on.borrow() else {
                    unreachable!()
                };
                let Value::Int(idx) = *self.evaluate_lvalue(idx)?.borrow() else {
                    unreachable!()
                };
                elements[idx as usize].clone()
            }
        };
        Ok(rc_value)
    }

    fn evaluate_constant(&self, c: Const) -> Result<RcValue, String> {
        let value = match c {
            Const::Unit => Value::Unit,
            Const::I(v) => Value::Int(v as i64),
            Const::I1(v) => Value::Int(v as i64),
            Const::I2(v) => Value::Int(v as i64),
            Const::I4(v) => Value::Int(v as i64),
            Const::I8(v) => Value::Int(v),
            Const::U(v) => Value::UInt(v as u64),
            Const::U1(v) => Value::UInt(v as u64),
            Const::U2(v) => Value::UInt(v as u64),
            Const::U4(v) => Value::UInt(v as u64),
            Const::U8(v) => Value::UInt(v as u64),
            Const::F4(v) => Value::Float(v as f64),
            Const::F8(v) => Value::Float(v),
            Const::Bool(b) => Value::Bool(b),
            Const::Char(c) => Value::Char(c),
            Const::Fn(fk) => Value::FnPtr(fk),
            Const::Null => Value::Ptr(self.null_ptr.clone()),
        };
        Ok(RcValue::new(value))
    }

    fn evaluate_rvalue(&mut self, rvalue: &RValue) -> Result<RcValue, String> {
        let value = match rvalue {
            RValue::Use(op) => return self.evaluate_operand(op),
            RValue::Str(sk) => return Ok(self.str_pool[sk.0 as usize].clone()),
            RValue::RefMut(lv) | RValue::Ref(lv) => Value::Ptr(self.evaluate_lvalue(*lv)?),
            RValue::Tuple(elements) | RValue::ArrayElements(elements) => {
                let mut eval_elements = Vec::with_capacity(elements.len());
                for element in elements {
                    let eval_element = self.evaluate_operand(element)?;
                    eval_elements.push(eval_element);
                }
                Value::Agg(Rc::new(eval_elements))
            }
            RValue::ArrayRepeated { repeated, size } => {
                let val = self.evaluate_operand(repeated)?;
                let mut eval_elements = Vec::with_capacity(*size as usize);
                for _ in 0..*size {
                    eval_elements.push(val.copy());
                }
                Value::Agg(Rc::new(eval_elements))
            }
            RValue::Struct { struct_key, fields } => {
                let mut eval_elements = vec![RcValue::default(); fields.len()];
                for (idx, op) in fields {
                    eval_elements[*idx as usize] = self.evaluate_operand(op)?;
                }
                Value::Agg(Rc::new(eval_elements))
            }
            RValue::Cast { val, kind } => self.apply_cast(val, *kind)?,
            RValue::BinOp { op, lhs, rhs } => {
                let lhs_val = self.evaluate_operand(lhs)?;
                let rhs_val = self.evaluate_operand(rhs)?;
                self.apply_binop(*op, lhs_val.inner(), rhs_val.inner())?
            }
            RValue::UnaryOp { op, operand } => {
                let val = self.evaluate_operand(operand)?;
                self.apply_unaryop(*op, val.inner())?
            }
            RValue::Call { on, args } => {
                let Value::FnPtr(fn_key) = self.evaluate_operand(on)?.inner() else {
                    unreachable!();
                };

                let mut frame_args = HashMap::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let arg = self.evaluate_operand(arg)?;
                    frame_args.insert(ArgKey::from(i), arg);
                }

                return self.execute_function(fn_key, frame_args);
            }
        };
        Ok(RcValue::new(value))
    }

    fn apply_unaryop(&self, op: UnaryOp, val: Value) -> Result<Value, String> {
        match op {
            UnaryOp::LNot => match val {
                Value::Bool(b) => Ok(Value::Bool(!b)),
                _ => Err(format!(
                    "Logical NOT requires boolean operand, got {:?}",
                    val
                )),
            },
            UnaryOp::BNot => match val {
                Value::Int(i) => Ok(Value::Int(!i)),
                Value::UInt(i) => Ok(Value::UInt(!i)),
                _ => Err(format!(
                    "Bitwise NOT requires integer operand, got {:?}",
                    val
                )),
            },
            UnaryOp::Minus => match val {
                Value::Int(i) => Ok(Value::Int(-i)),
                Value::Float(f) => Ok(Value::Float(-f)),
                _ => Err(format!("Negation requires numeric operand, got {:?}", val)),
            },
        }
    }

    fn apply_binop(&self, op: BinOp, lhs: Value, rhs: Value) -> Result<Value, String> {
        match (lhs, rhs) {
            (Value::Int(a), Value::Int(b)) => match op {
                BinOp::Plus => Ok(Value::Int(a + b)),
                BinOp::Minus => Ok(Value::Int(a - b)),
                BinOp::Times => Ok(Value::Int(a * b)),
                BinOp::Div => Ok(Value::Int(a / b)),
                BinOp::Mod => Ok(Value::Int(a % b)),
                BinOp::EqualEqual => Ok(Value::Bool(a == b)),
                BinOp::NotEqual => Ok(Value::Bool(a != b)),
                BinOp::GE => Ok(Value::Bool(a >= b)),
                BinOp::GT => Ok(Value::Bool(a > b)),
                BinOp::LE => Ok(Value::Bool(a <= b)),
                BinOp::LT => Ok(Value::Bool(a < b)),
                BinOp::BOr => Ok(Value::Int(a | b)),
                BinOp::Xor => Ok(Value::Int(a ^ b)),
                BinOp::BAnd => Ok(Value::Int(a & b)),
                BinOp::Shr => Ok(Value::Int(a >> b)),
                BinOp::Shl => Ok(Value::Int(a << b)),
            },
            (Value::UInt(a), Value::UInt(b)) => match op {
                BinOp::Plus => Ok(Value::UInt(a + b)),
                BinOp::Minus => Ok(Value::UInt(a - b)),
                BinOp::Times => Ok(Value::UInt(a * b)),
                BinOp::Div => Ok(Value::UInt(a / b)),
                BinOp::Mod => Ok(Value::UInt(a % b)),
                BinOp::EqualEqual => Ok(Value::Bool(a == b)),
                BinOp::NotEqual => Ok(Value::Bool(a != b)),
                BinOp::GE => Ok(Value::Bool(a >= b)),
                BinOp::GT => Ok(Value::Bool(a > b)),
                BinOp::LE => Ok(Value::Bool(a <= b)),
                BinOp::LT => Ok(Value::Bool(a < b)),
                BinOp::BOr => Ok(Value::UInt(a | b)),
                BinOp::Xor => Ok(Value::UInt(a ^ b)),
                BinOp::BAnd => Ok(Value::UInt(a & b)),
                BinOp::Shr => Ok(Value::UInt(a >> b)),
                BinOp::Shl => Ok(Value::UInt(a << b)),
            },
            (Value::Float(a), Value::Float(b)) => match op {
                BinOp::Plus => Ok(Value::Float(a + b)),
                BinOp::Minus => Ok(Value::Float(a - b)),
                BinOp::Times => Ok(Value::Float(a * b)),
                BinOp::Div => Ok(Value::Float(a / b)),
                BinOp::EqualEqual => Ok(Value::Bool(a == b)),
                BinOp::NotEqual => Ok(Value::Bool(a != b)),
                BinOp::GE => Ok(Value::Bool(a >= b)),
                BinOp::GT => Ok(Value::Bool(a > b)),
                BinOp::LE => Ok(Value::Bool(a <= b)),
                BinOp::LT => Ok(Value::Bool(a < b)),
                _ => Err("Invalid operation for floats".into()),
            },
            (Value::Bool(a), Value::Bool(b)) => match op {
                BinOp::EqualEqual => Ok(Value::Bool(a == b)),
                BinOp::NotEqual => Ok(Value::Bool(a != b)),
                _ => Err("Invalid operation for booleans".into()),
            },
            _ => Err("Type mismatch in binary operation".into()),
        }
    }

    fn apply_cast(&mut self, val: &Operand, kind: CastKind) -> Result<Value, String> {
        use CastKind::*;
        use Value::*;

        let rc_value = self.evaluate_operand(val)?;
        let value = &*rc_value.borrow();

        match kind {
            U1ToChar => match value {
                UInt(i) => Ok(Char(*i as u8 as char)),
                _ => Err("U1ToChar requires integer operand".into()),
            },

            F4ToF8 => match value {
                Float(f) => Ok(Float(*f)),
                _ => Err("F4ToF8 requires float operand".into()),
            },

            F8ToF4 => match value {
                Float(f) => Ok(Float(*f)), // Preserve f32 precision
                _ => Err("F8ToF4 requires float operand".into()),
            },

            ArrayToSlice { len } => match value {
                Agg(_elements) => Ok(Value::Agg(Rc::new(vec![
                    RcValue::new(Value::Ptr(rc_value.clone())),
                    RcValue::new(Value::UInt(len as u64)),
                ]))),
                _ => Err("ArrayToSlice requires array operand".into()),
            },

            PtrToPtr => Ok(value.clone()),

            UIntToPtr { int_size } => match value {
                UInt(i) => todo!(),
                _ => Err("UIntToPtr requires integer operand".into()),
            },

            PtrToUInt { int_size } => match value {
                Value::Ptr(ptr) => Ok(UInt(ptr.data.as_ptr() as u64)),
                _ => Err("PtrToUInt requires pointer operand".into()),
            },

            F4ToInt { int_size } => match value {
                Float(f) => Ok(Int(*f as i64)),
                _ => Err("F4ToInt requires float operand".into()),
            },

            F4ToUInt { int_size } => match value {
                Float(f) => Ok(UInt(*f as u64)),
                _ => Err("F4ToUInt requires float operand".into()),
            },

            F8ToInt { int_size } => match value {
                Float(f) => Ok(Int(*f as i64)),
                _ => Err("F8ToInt requires float operand".into()),
            },

            F8ToUInt { int_size } => match value {
                Float(f) => Ok(UInt(*f as u64)),
                _ => Err("F8ToUInt requires float operand".into()),
            },

            BoolToInt { int_size } => match value {
                Bool(b) => Ok(Int(*b as i64)),
                _ => Err("BoolToInt requires boolean operand".into()),
            },

            BoolToUInt { int_size } => match value {
                Bool(b) => Ok(Int(*b as i64)),
                _ => Err("BoolToUInt requires boolean operand".into()),
            },

            CharToInt { int_size } => match value {
                Char(c) => Ok(Int(*c as i64)),
                _ => Err("CharToInt requires char operand".into()),
            },

            CharToUInt { int_size } => match value {
                Char(c) => Ok(UInt(*c as u64)),
                _ => Err("CharToUInt requires char operand".into()),
            },

            IntToInt {
                int1_size,
                int2_size,
            } => {
                let mask = mask_for_size(int2_size);
                match value {
                    Int(i) => Ok(Int((*i as u64 & mask) as i64)),
                    _ => Err("IntToInt requires integer operand".into()),
                }
            }

            IntToUInt {
                int1_size,
                int2_size,
            } => {
                let mask = mask_for_size(int2_size);
                match value {
                    Int(i) => Ok(Int((*i as u64 & mask) as i64)),
                    _ => Err("IntToUInt requires integer operand".into()),
                }
            }

            IntToF4 { int_size } => match value {
                Int(i) => Ok(Float(*i as f64)),
                _ => Err("IntToF4 requires integer operand".into()),
            },

            IntToF8 { int_size } => match value {
                Int(i) => Ok(Float(*i as f64)),
                _ => Err("IntToF8 requires integer operand".into()),
            },

            UIntToInt {
                int1_size,
                int2_size,
            } => {
                let mask = mask_for_size(int2_size);
                match value {
                    UInt(i) => Ok(Int((*i & mask) as i64)),
                    _ => Err("UIntToInt requires integer operand".into()),
                }
            }

            UIntToUInt {
                int1_size,
                int2_size,
            } => {
                let mask = mask_for_size(int2_size);
                match value {
                    UInt(i) => Ok(UInt((*i as u64 & mask) as u64)),
                    _ => Err("UIntToUInt requires integer operand".into()),
                }
            }

            UIntToF4 { int_size } => match value {
                UInt(i) => Ok(Float(*i as f64)),
                _ => Err("UIntToF4 requires integer operand".into()),
            },

            UIntToF8 { int_size } => match value {
                UInt(i) => Ok(Float(*i as f64)),
                _ => Err("UIntToF8 requires integer operand".into()),
            },
        }
    }
}

// Helper function to create bit masks for different integer sizes
fn mask_for_size(size: Size) -> u64 {
    match size {
        Size::Byte => 0xFF,
        Size::Word => 0xFFFF,
        Size::DWord => 0xFFFFFFFF,
        Size::QWord => 0xFFFFFFFFFFFFFFFF,
        Size::Ptr => match std::mem::size_of::<usize>() {
            4 => 0xFFFFFFFF,
            8 => 0xFFFFFFFFFFFFFFFF,
            _ => unreachable!(),
        },
    }
}
