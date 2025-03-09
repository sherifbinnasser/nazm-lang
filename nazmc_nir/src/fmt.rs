use crate::*;
use std::fs::File;
use std::io::Write;

impl<'a> NIR<'a> {
    pub fn fmt_cfg(&self, cfg: &CFG, filename: &str) {
        let mut f = File::create(filename).unwrap();

        writeln!(f, "digraph CFG {{");
        writeln!(f, "    node [shape=rect];");

        // Write basic blocks
        for (bb_key, bb) in cfg.basic_blocks.iter_enumerated() {
            let label = if bb_key == START_BASIC_BLOCK {
                "Start"
            } else if bb_key == END_BASIC_BLOCK {
                "End"
            } else {
                &format!("BB{:?}", bb_key)
            };

            let mut stms = String::new();

            for stm in &bb.stms {
                match stm {
                    Stm::Assign { lhs, rhs } => {
                        stms.push_str(
                            format!(
                                "{} = {}\n",
                                self.fmt_lvalue(cfg, *lhs),
                                self.fmt_rvalue(cfg, rhs)
                            )
                            .as_str(),
                        );
                    }
                    Stm::Drop(lvalue_key) => todo!(),
                }
            }

            writeln!(f, "    BB{} [label=\"{}\n{}\"];", bb_key.0, label, stms);
        }

        // Write edges
        for branch in &cfg.branches {
            let label = match branch.kind {
                BranchKind::Straight => "",
                BranchKind::JZ => "JZ",
                BranchKind::JNZ => "JNZ",
            };
            writeln!(
                f,
                "    BB{} -> BB{} [label=\"{}\"]",
                branch.from.0, branch.to.0, label
            );
        }

        writeln!(f, "}}");
    }

    pub(crate) fn fmt_pkg_name(&self, pkg_key: PkgKey) -> String {
        self.pkgs_names[pkg_key]
            .iter()
            .map(|id| self.id_pool[*id].as_str())
            .collect::<Vec<_>>()
            .join("::")
    }

    pub(crate) fn fmt_item_name(&self, item_info: ItemInfo) -> String {
        let pkg = self.fmt_pkg_name(self.files_to_pkgs[item_info.file_key]);
        let name = &self.id_pool[item_info.id_key];
        if pkg.is_empty() {
            name.to_owned()
        } else {
            format!("{}::{}", pkg, name)
        }
    }

    pub fn fmt_typ(&self, type_key: TypeKey) -> String {
        match self.types[type_key] {
            Type::Unit => format!("()"),
            Type::I => format!("i"),
            Type::I1 => format!("i1"),
            Type::I2 => format!("i2"),
            Type::I4 => format!("i4"),
            Type::I8 => format!("i8"),
            Type::U => format!("u"),
            Type::U1 => format!("u1"),
            Type::U2 => format!("u2"),
            Type::U4 => format!("u4"),
            Type::U8 => format!("u8"),
            Type::F4 => format!("f4"),
            Type::F8 => format!("f8"),
            Type::Bool => format!("bool"),
            Type::Char => format!("char"),
            Type::Struct(struct_key) => {
                let item_info = self.structs[struct_key].info;
                self.fmt_item_name(item_info)
            }
            Type::Slice(type_key) => format!("[{}]", self.fmt_typ(type_key)),
            Type::MutSlice(type_key) => format!("[mut {}]", self.fmt_typ(type_key)),
            Type::Ptr(type_key) => format!("*{}", self.fmt_typ(type_key)),
            Type::MutPtr(type_key) => format!("*mut {}", self.fmt_typ(type_key)),
            Type::Array(array_type_key) => format!(
                "[{}; {}]",
                self.fmt_typ(self.array_types[array_type_key].underlying_typ),
                self.array_types[array_type_key].size
            ),
            Type::Tuple(tuple_type_key) => format!(
                "({})",
                self.tuple_types[tuple_type_key]
                    .types
                    .iter()
                    .map(|&ty| self.fmt_typ(ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Type::Lambda(lambda_type_key) => format!(
                "({}) -> {}",
                self.lambda_types[lambda_type_key]
                    .params_types
                    .iter()
                    .map(|&ty| self.fmt_typ(ty))
                    .collect::<Vec<_>>()
                    .join(", "),
                self.fmt_typ(self.lambda_types[lambda_type_key].return_type)
            ),
            Type::FnPtr(fn_ptr_type_key) => format!(
                "fn({}) -> {}",
                self.fn_ptr_types[fn_ptr_type_key]
                    .params_types
                    .iter()
                    .map(|&ty| self.fmt_typ(ty))
                    .collect::<Vec<_>>()
                    .join(", "),
                self.fmt_typ(self.fn_ptr_types[fn_ptr_type_key].return_type)
            ),
        }
    }

    pub fn fmt_operand(&self, cfg: &CFG, o: &Operand) -> String {
        format!(
            "{} {}",
            self.fmt_typ(o.typ),
            self.fmt_operand_kind(cfg, &o.kind)
        )
    }

    pub fn fmt_operand_kind(&self, cfg: &CFG, kind: &OperandKind) -> String {
        match kind {
            OperandKind::LValue(lvalue_key) => self.fmt_lvalue(cfg, *lvalue_key),
            OperandKind::Const(c) => match c {
                Const::Unit => format!("()"),
                Const::I(n) => format!("{n}"),
                Const::I1(n) => format!("{n}"),
                Const::I2(n) => format!("{n}"),
                Const::I4(n) => format!("{n}"),
                Const::I8(n) => format!("{n}"),
                Const::U(n) => format!("{n}"),
                Const::U1(n) => format!("{n}"),
                Const::U2(n) => format!("{n}"),
                Const::U4(n) => format!("{n}"),
                Const::U8(n) => format!("{n}"),
                Const::F4(n) => format!("{n}"),
                Const::F8(n) => format!("{n}"),
                Const::Bool(n) => format!("{n}"),
                Const::Char(n) => format!("'{n}'"),
                Const::Str(str_key) => format!("\"{}\"", &self.str_pool[*str_key]),
                Const::Fn(fn_key) => {
                    let item_info = self.fns[*fn_key].info;
                    self.fmt_item_name(item_info)
                }
            },
        }
    }

    pub fn fmt_lvalue(&self, cfg: &CFG, lvalue_key: LValueKey) -> String {
        match cfg.lvalues[lvalue_key] {
            LValue::ReturnPtr => format!("RET"),
            LValue::Binding(binding_key) => format!("VAR_{}", binding_key.0),
            LValue::Arg(arg_key) => format!("ARG_{}", arg_key.0),
            LValue::Static(static_key) => format!("STATIC_{}", static_key.0),
            LValue::Temp(temp_key) => format!("TEMP_{}", temp_key.0),
            LValue::Deref(lvalue_key) | LValue::MutDeref(lvalue_key) => {
                format!("*{}", self.fmt_lvalue(cfg, lvalue_key))
            }
            LValue::Field { on, field_id } | LValue::MutField { on, field_id } => {
                let field_id = &self.id_pool[field_id];
                format!("{}.{}", self.fmt_lvalue(cfg, on), field_id)
            }
            LValue::TupleIdx { on, idx } | LValue::MutTupleIdx { on, idx } => {
                format!("{}.{}", self.fmt_lvalue(cfg, on), idx)
            }
            LValue::ArrayIdx { on, idx } | LValue::MutArrayIdx { on, idx } => {
                format!(
                    "{}[{}]",
                    self.fmt_lvalue(cfg, on),
                    self.fmt_lvalue(cfg, idx)
                )
            }
            LValue::ArrayConstIdx { on, idx } | LValue::MutArrayConstIdx { on, idx } => {
                format!("{}[{}]", self.fmt_lvalue(cfg, on), idx)
            }
        }
    }

    pub fn fmt_rvalue(&self, cfg: &CFG, rvalue: &RValue) -> String {
        match rvalue {
            RValue::Use(operand) => format!("{}", self.fmt_operand(cfg, operand)),
            RValue::Ref(lvalue_key) => format!("&{}", self.fmt_lvalue(cfg, *lvalue_key)),
            RValue::RefMut(lvalue_key) => format!("&mut {}", self.fmt_lvalue(cfg, *lvalue_key)),
            RValue::Tuple(operands) => format!(
                "({})",
                operands
                    .iter()
                    .map(|op| self.fmt_operand(cfg, op))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            RValue::ArrayElements(operands) => format!(
                "[{}]",
                operands
                    .iter()
                    .map(|op| self.fmt_operand(cfg, op))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            RValue::ArrayRepeated { repeated, size } => {
                format!("[{}; {}]", self.fmt_operand(cfg, repeated), size)
            }
            RValue::Struct { struct_key, fields } => format!(
                "{} {{ {} }}",
                self.fmt_item_name(self.structs[*struct_key].info),
                fields
                    .iter()
                    .map(|(id, op)| format!(
                        "{}: {}",
                        &self.id_pool[*id],
                        self.fmt_operand(cfg, op)
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            RValue::Cast { val, to } => {
                format!("{} as {}", self.fmt_operand(cfg, val), self.fmt_typ(*to))
            }
            RValue::BinOp { op, lhs, rhs } => format!(
                "{:?} {}, {}",
                op,
                self.fmt_operand(cfg, lhs),
                self.fmt_operand(cfg, rhs)
            ),
            RValue::UnaryOp { op, operand } => {
                format!("{:?} {}", op, self.fmt_operand(cfg, operand))
            }
            RValue::Call { on, args } => format!(
                "call {}({})",
                self.fmt_operand(cfg, on),
                args.iter()
                    .map(|op| self.fmt_operand(cfg, op))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}
