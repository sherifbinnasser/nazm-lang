use crate::*;
use std::fs::File;
use std::io::Write;

impl<'a> NIR<'a> {
    pub fn fmt_cfg(&self, cfg: &CFG, filename: &str) {
        let mut f = File::create(filename).unwrap();

        writeln!(f, "digraph CFG {{");
        writeln!(f, "    node [shape=rect];");

        // Write basic blocks

        writeln!(
            f,
            "    BB{} [style = \"rounded\", label=\"Start\"];",
            BasicBlockKey::START_BASIC_BLOCK.0
        );

        writeln!(
            f,
            "    BB{} [style = \"rounded\", label=\"End\"];",
            BasicBlockKey::END_BASIC_BLOCK.0
        );

        for (bb_key, bb) in cfg.basic_blocks.iter() {
            if bb_key.0 == BasicBlockKey::START_BASIC_BLOCK.0
                || bb_key.0 == BasicBlockKey::END_BASIC_BLOCK.0
            {
                continue;
            }

            let mut stms = String::new();

            for stm in &bb.stms {
                let stm = match stm {
                    Stm::Assign { lhs, rhs, typ } => {
                        format!(
                            "{}: {} = {}\\l",
                            self.fmt_lvalue(cfg, *lhs),
                            self.fmt_typ(*typ),
                            self.fmt_rvalue(cfg, rhs)
                        )
                    }
                    Stm::Phi { lhs, cases, typ } => {
                        format!(
                            "{}: {} = Φ({})\\l",
                            self.fmt_lvalue(cfg, *lhs),
                            self.fmt_typ(*typ),
                            cases
                                .iter()
                                .map(|(bb, operand)| {
                                    format!("@BB{} {}", bb.0, self.fmt_operand_kind(cfg, operand))
                                })
                                .collect::<Vec<_>>()
                                .join(", "),
                        )
                    }
                    Stm::Return { rvalue, typ } => {
                        format!(
                            "return {} {}\\l",
                            self.fmt_typ(*typ),
                            self.fmt_rvalue(cfg, rvalue)
                        )
                    }
                    Stm::Drop(lvalue_key) => todo!(),
                };

                stms.push_str(stm.as_str());
            }

            writeln!(
                f,
                "    BB{} [label=\"@BB{}\\l{}\"];",
                bb_key.0, bb_key.0, stms
            );
        }

        // Write edges
        for (i, (_, branch)) in cfg.branches.iter().enumerate() {
            match branch.kind {
                BranchKind::Else => {}
                BranchKind::Straight => {
                    writeln!(f, "    BB{} -> BB{}", branch.from.0, branch.to.0);
                }
                BranchKind::If(o) => {
                    writeln!(
                        f,
                        "    Branch_{} [shape = \"diamond\", label=\"If {}\"];",
                        i,
                        self.fmt_operand_kind(&cfg, &o.kind)
                    );
                    writeln!(f, "    BB{} -> Branch_{}", branch.from.0, i);
                    writeln!(f, "    Branch_{} -> BB{} [label=\"Yes\"]", i, branch.to.0);

                    let else_branch_key = cfg.basic_blocks[&branch.from].goto.unwrap();
                    let else_block_key = cfg.branches[&else_branch_key].to;
                    writeln!(
                        f,
                        "    Branch_{} -> BB{} [label=\"No\"]",
                        i, else_block_key.0
                    );
                }
            }
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
        match cfg.lvalues[lvalue_key].kind {
            LValueKind::Binding(binding_key) => format!("VAR_{}", binding_key.0),
            LValueKind::Arg(arg_key) => format!("ARG_{}", arg_key.0),
            LValueKind::Static(static_key) => format!("STATIC_{}", static_key.0),
            LValueKind::Temp(temp_key) => format!("TEMP_{}", temp_key.0),
            LValueKind::Deref(lvalue_key) | LValueKind::MutDeref(lvalue_key) => {
                format!("*{}", self.fmt_lvalue(cfg, lvalue_key))
            }
            LValueKind::Field { on, idx } | LValueKind::MutField { on, idx } => {
                format!("{}.{}", self.fmt_lvalue(cfg, on), idx)
            }
            LValueKind::TupleIdx { on, idx } | LValueKind::MutTupleIdx { on, idx } => {
                format!("{}.{}", self.fmt_lvalue(cfg, on), idx)
            }
            LValueKind::ArrayIdx { on, idx } | LValueKind::MutArrayIdx { on, idx } => {
                format!(
                    "{}[{}]",
                    self.fmt_lvalue(cfg, on),
                    self.fmt_lvalue(cfg, idx)
                )
            }
            LValueKind::ArrayConstIdx { on, idx } | LValueKind::MutArrayConstIdx { on, idx } => {
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
                    .map(|(idx, op)| format!("{}: {}", idx, self.fmt_operand(cfg, op)))
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
