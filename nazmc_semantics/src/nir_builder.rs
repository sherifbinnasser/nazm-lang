use std::{collections::HashMap, ops::DerefMut, usize};

use nazmc_ast::{ExprKey, LetStmKey, ScopeKey};
use nazmc_data_pool::{typed_index_collections::TiVec, DataPoolBuilder, IdKey};
use nazmc_nir::{
    ArgKey, ArrayType, ArrayTypeKey, BasicBlockKey, BindingKey, Const, FnKey, FnPtrType,
    FnPtrTypeKey, LValue, LValueKey, LambdaType, LambdaTypeKey, Operand, OperandKind, RValue,
    StaticKey, Stm, Struct, StructKey, Temp, TupleType, TupleTypeKey, Type, TypeKey, CFG, NIR,
};

use crate::SemanticsAnalyzer;

#[derive(Default)]
pub(crate) struct NIRBuilder {
    pub(crate) nir: NIR,
    pub(crate) all_types: DataPoolBuilder<TypeKey, Type>,
    pub(crate) all_array_types: DataPoolBuilder<ArrayTypeKey, ArrayType>,
    pub(crate) all_tuple_types: DataPoolBuilder<TupleTypeKey, TupleType>,
    pub(crate) all_lambda_types: DataPoolBuilder<LambdaTypeKey, LambdaType>,
    pub(crate) all_fn_ptr_types: DataPoolBuilder<FnPtrTypeKey, FnPtrType>,
    pub(crate) exprs_types: TiVec<ExprKey, TypeKey>,
}

impl NIRBuilder {
    pub(crate) fn get_unique_type(&mut self, typ: crate::ConcreteType) -> TypeKey {
        let typ = match typ {
            crate::ConcreteType::Composite(composite_type) => match composite_type {
                crate::CompositeType::Slice(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = *underlying_typ else {
                        unreachable!()
                    };
                    Type::Slice(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::Ptr(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = *underlying_typ else {
                        unreachable!()
                    };
                    Type::Ptr(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::PtrMut(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = *underlying_typ else {
                        unreachable!()
                    };
                    Type::MutPtr(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::Ref(underlying_typ) => todo!(),
                crate::CompositeType::RefMut(underlying_typ) => todo!(),
                crate::CompositeType::Array {
                    underlying_typ,
                    size,
                } => {
                    let crate::Type::Concrete(underlying_typ) = *underlying_typ else {
                        unreachable!()
                    };

                    let underlying_typ_key = self.get_unique_type(underlying_typ);

                    let array_typ = ArrayType {
                        underlying_typ: underlying_typ_key,
                        size,
                    };

                    let array_type_key = self.all_array_types.get_key(&array_typ);

                    Type::Array(array_type_key)
                }
                crate::CompositeType::Tuple { types } => {
                    let types = types
                        .into_iter()
                        .map(|typ| {
                            let crate::Type::Concrete(typ) = typ else {
                                unreachable!()
                            };

                            self.get_unique_type(typ)
                        })
                        .collect();

                    let tuple_type = TupleType { types };

                    let tuple_type_key = self.all_tuple_types.get_key(&tuple_type);

                    Type::Tuple(tuple_type_key)
                }
                crate::CompositeType::Lambda {
                    params_types,
                    return_type,
                } => {
                    let params_types = params_types
                        .into_iter()
                        .map(|typ| {
                            let crate::Type::Concrete(typ) = typ else {
                                unreachable!()
                            };

                            self.get_unique_type(typ)
                        })
                        .collect();

                    let crate::Type::Concrete(return_type) = *return_type else {
                        unreachable!()
                    };

                    let return_type = self.get_unique_type(return_type);

                    let lambda_type = LambdaType {
                        params_types,
                        return_type,
                    };

                    let lambda_type_key = self.all_lambda_types.get_key(&lambda_type);

                    Type::Lambda(lambda_type_key)
                }
                crate::CompositeType::FnPtr {
                    params_types,
                    return_type,
                } => {
                    let params_types = params_types
                        .into_iter()
                        .map(|typ| {
                            let crate::Type::Concrete(typ) = typ else {
                                unreachable!()
                            };

                            self.get_unique_type(typ)
                        })
                        .collect();

                    let crate::Type::Concrete(return_type) = *return_type else {
                        unreachable!()
                    };

                    let return_type = self.get_unique_type(return_type);

                    let fn_ptr_type = FnPtrType {
                        params_types,
                        return_type,
                    };

                    let fn_ptr_type_key = self.all_fn_ptr_types.get_key(&fn_ptr_type);

                    Type::FnPtr(fn_ptr_type_key)
                }
            },
            crate::ConcreteType::UnitStruct(unit_struct_key) => todo!(),
            crate::ConcreteType::TupleStruct(tuple_struct_key) => todo!(),
            crate::ConcreteType::FieldsStruct(fields_struct_key) => {
                Type::Struct(StructKey::from(usize::from(fields_struct_key)))
            }
            crate::ConcreteType::Primitive(primitive_type) => match primitive_type {
                crate::type_infer::PrimitiveType::Unit => Type::Unit,
                crate::type_infer::PrimitiveType::I => Type::I,
                crate::type_infer::PrimitiveType::I1 => Type::I1,
                crate::type_infer::PrimitiveType::I2 => Type::I2,
                crate::type_infer::PrimitiveType::I4 => Type::I4,
                crate::type_infer::PrimitiveType::I8 => Type::I8,
                crate::type_infer::PrimitiveType::U => Type::U,
                crate::type_infer::PrimitiveType::U1 => Type::U1,
                crate::type_infer::PrimitiveType::U2 => Type::U2,
                crate::type_infer::PrimitiveType::U4 => Type::U4,
                crate::type_infer::PrimitiveType::U8 => Type::U8,
                crate::type_infer::PrimitiveType::F4 => Type::F4,
                crate::type_infer::PrimitiveType::F8 => Type::F8,
                crate::type_infer::PrimitiveType::Bool => Type::Bool,
                crate::type_infer::PrimitiveType::Char => Type::Char,
                crate::type_infer::PrimitiveType::Str => {
                    Type::Slice(self.all_types.get_key(&Type::U1))
                }
            },
        };

        self.all_types.get_key(&typ)
    }
}

#[derive(Default)]
pub(crate) struct CFGBuilder {
    pub(crate) cfg: CFG,
    pub(crate) locals: HashMap<(LetStmKey, IdKey), BindingKey>,
    pub(crate) lvalues: HashMap<LValue, LValueKey>,
}

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn lower_scope(&mut self, scope_key: ScopeKey) {
        let stms = std::mem::take(&mut self.ast.scopes[scope_key].stms);
        for stm in stms {
            match stm {
                nazmc_ast::Stm::Let(let_stm_key) => todo!(),
                nazmc_ast::Stm::While(while_stm) => todo!(),
                nazmc_ast::Stm::Expr(expr_key) => {}
            }
        }
    }

    fn get_lvalue_key(&mut self, lvalue: LValue) -> LValueKey {
        if let Some(&lvalue_key) = self.cfg_builder.lvalues.get(&lvalue) {
            lvalue_key
        } else {
            let lvalue_key = self.cfg_builder.cfg.lvalues.push_and_get_key(lvalue);
            self.cfg_builder.lvalues.insert(lvalue, lvalue_key);
            lvalue_key
        }
    }

    fn add_new_temp_assign_stm(&mut self, typ: TypeKey, rvalue: RValue) -> OperandKind {
        let assign_stm_idx = self.cfg_builder.cfg.basic_blocks.last().unwrap().stms.len() as u32;

        let temp = Temp {
            typ,
            assign_stm_idx,
        };

        let temp_key = self.cfg_builder.cfg.temps.push_and_get_key(temp);

        let lvalue_key = self.get_lvalue_key(LValue::Temp(temp_key));

        let assign = Stm::Assign {
            lhs: lvalue_key,
            rhs: rvalue,
        };

        self.cfg_builder
            .cfg
            .basic_blocks
            .last_mut()
            .unwrap()
            .stms
            .push(assign);

        OperandKind::LValue(lvalue_key)
    }

    fn is_mut_lvalue(&self, lvalue_key: LValueKey) -> bool {
        match &self.cfg_builder.cfg.lvalues[lvalue_key] {
            LValue::ReturnPtr => unreachable!(),
            LValue::Binding(binding_key) => {
                self.cfg_builder.cfg.mut_bindings.contains_key(binding_key)
            }
            LValue::Arg(arg_key) => {
                let fn_key = FnKey::from(usize::from(self.current_fn_key));
                self.nir_builder.nir.fns[fn_key].args[*arg_key].is_mut
            }
            LValue::Deref(_)
            | LValue::Field { .. }
            | LValue::TupleIdx { .. }
            | LValue::ArrayIdx { .. }
            | LValue::ArrayConstIdx { .. } => false,
            LValue::Temp(_)
            | LValue::Static(_)
            | LValue::MutDeref(_)
            | LValue::MutField { .. }
            | LValue::MutTupleIdx { .. }
            | LValue::MutArrayIdx { .. }
            | LValue::MutArrayConstIdx { .. } => true,
        }
    }

    fn lower_expr(&mut self, expr_key: ExprKey) -> Operand {
        let expr_kind = std::mem::take(&mut self.ast.exprs[expr_key].kind);

        let typ = self.nir_builder.exprs_types[expr_key];

        let kind = match expr_kind {
            nazmc_ast::ExprKind::Unit => OperandKind::Const(Const::Unit),
            nazmc_ast::ExprKind::Literal(literal_expr) => {
                let const_opernad = match literal_expr {
                    nazmc_ast::LiteralExpr::Str(str_key) => Const::Str(str_key),
                    nazmc_ast::LiteralExpr::Char(ch) => Const::Char(ch),
                    nazmc_ast::LiteralExpr::Bool(b) => Const::Bool(b),
                    nazmc_ast::LiteralExpr::Num(num_kind) => match num_kind {
                        nazmc_ast::NumKind::F4(n) => Const::F4(n),
                        nazmc_ast::NumKind::F8(n) => Const::F8(n),
                        nazmc_ast::NumKind::I(n) => Const::I(n),
                        nazmc_ast::NumKind::I1(n) => Const::I1(n),
                        nazmc_ast::NumKind::I2(n) => Const::I2(n),
                        nazmc_ast::NumKind::I4(n) => Const::I4(n),
                        nazmc_ast::NumKind::I8(n) => Const::I8(n),
                        nazmc_ast::NumKind::U(n) => Const::U(n),
                        nazmc_ast::NumKind::U1(n) => Const::U1(n),
                        nazmc_ast::NumKind::U2(n) => Const::U2(n),
                        nazmc_ast::NumKind::U4(n) => Const::U4(n),
                        nazmc_ast::NumKind::U8(n) => Const::U8(n),
                        _ => unreachable!(),
                    },
                };

                OperandKind::Const(const_opernad)
            }
            nazmc_ast::ExprKind::PathNoPkg(path_no_pkg_key) => {
                let item = self.ast.state.paths_no_pkgs_exprs[path_no_pkg_key];

                match item {
                    nazmc_ast::Item::Const { vis, key } => todo!(),
                    nazmc_ast::Item::Static { vis, key } => {
                        let static_key = StaticKey::from(usize::from(key));
                        let lvalue_key = self.get_lvalue_key(LValue::Static(static_key));
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::Fn { vis, key } => {
                        let fn_key = FnKey::from(usize::from(key));
                        OperandKind::Const(Const::Fn(fn_key))
                    }
                    nazmc_ast::Item::LocalVar { id, key } => {
                        let binding_key = self.cfg_builder.locals[&(key, id)];
                        let lvalue_key = self.get_lvalue_key(LValue::Binding(binding_key));
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::FnParam { idx, fn_key } => {
                        let lvalue_key = self.get_lvalue_key(LValue::Arg(ArgKey::from(idx)));
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::LambdaParam { id, scope_key } => todo!(),
                    _ => unreachable!(),
                }
            }
            nazmc_ast::ExprKind::PathInPkg(path_with_pkg_key) => {
                let item = self.ast.state.paths_with_pkgs_exprs[path_with_pkg_key];

                match item {
                    nazmc_ast::Item::Const { vis, key } => todo!(),
                    nazmc_ast::Item::Static { vis, key } => {
                        let static_key = StaticKey::from(usize::from(key));
                        let lvalue_key = self.get_lvalue_key(LValue::Static(static_key));
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::Fn { vis, key } => {
                        let fn_key = FnKey::from(usize::from(key));
                        OperandKind::Const(Const::Fn(fn_key))
                    }
                    _ => unreachable!(),
                }
            }
            nazmc_ast::ExprKind::Call(call_expr) => {
                let on = self.lower_expr(call_expr.on);

                let args = call_expr
                    .args
                    .iter()
                    .map(|&arg_expr_key| self.lower_expr(arg_expr_key))
                    .collect();

                let rvalue = RValue::Call { on, args };

                self.add_new_temp_assign_stm(typ, rvalue)
            }
            nazmc_ast::ExprKind::FieldsStruct(fields_struct_expr) => {
                let fields = fields_struct_expr
                    .fields
                    .iter()
                    .map(|(id, expr_key)| (id.id, self.lower_expr(*expr_key)))
                    .collect();

                let struct_key =
                    self.ast.state.field_structs_paths_exprs[fields_struct_expr.path_key];

                let struct_key = StructKey::from(usize::from(struct_key));

                let rvalue = RValue::Struct { struct_key, fields };

                self.add_new_temp_assign_stm(typ, rvalue)
            }
            nazmc_ast::ExprKind::Tuple(elements) => {
                let elements = elements
                    .iter()
                    .map(|expr_key| self.lower_expr(*expr_key))
                    .collect();

                let rvalue = RValue::Tuple(elements);

                self.add_new_temp_assign_stm(typ, rvalue)
            }
            nazmc_ast::ExprKind::ArrayElements(elements) => {
                let elements = elements
                    .iter()
                    .map(|expr_key| self.lower_expr(*expr_key))
                    .collect();

                let rvalue = RValue::ArrayElements(elements);

                self.add_new_temp_assign_stm(typ, rvalue)
            }
            nazmc_ast::ExprKind::ArrayRepeated(array_repeated_expr) => {
                let repeated = self.lower_expr(array_repeated_expr.repeat);

                let Type::Array(array_type_key) = self.nir_builder.nir.types[typ] else {
                    unreachable!()
                };

                let ArrayType {
                    underlying_typ: _,
                    size,
                } = self.nir_builder.nir.array_types[array_type_key];

                let rvalue = RValue::ArrayRepeated { repeated, size };

                self.add_new_temp_assign_stm(typ, rvalue)
            }
            nazmc_ast::ExprKind::Field(field_expr) => {
                let Operand {
                    typ: _,
                    kind: OperandKind::LValue(lvalue_key),
                } = self.lower_expr(field_expr.on)
                else {
                    unreachable!()
                };

                let lvalue = if self.is_mut_lvalue(lvalue_key) {
                    LValue::MutField {
                        on: lvalue_key,
                        field_id: field_expr.name.id,
                    }
                } else {
                    LValue::Field {
                        on: lvalue_key,
                        field_id: field_expr.name.id,
                    }
                };

                let lvalue_key = self.get_lvalue_key(lvalue);

                OperandKind::LValue(lvalue_key)
            }
            nazmc_ast::ExprKind::TupleIdx(tuple_idx_expr) => {
                let Operand {
                    typ: _,
                    kind: OperandKind::LValue(lvalue_key),
                } = self.lower_expr(tuple_idx_expr.on)
                else {
                    unreachable!()
                };

                let lvalue = if self.is_mut_lvalue(lvalue_key) {
                    LValue::MutTupleIdx {
                        on: lvalue_key,
                        idx: tuple_idx_expr.idx,
                    }
                } else {
                    LValue::TupleIdx {
                        on: lvalue_key,
                        idx: tuple_idx_expr.idx,
                    }
                };

                let lvalue_key = self.get_lvalue_key(lvalue);

                OperandKind::LValue(lvalue_key)
            }

            nazmc_ast::ExprKind::Idx(idx_expr) => {
                let Operand {
                    typ: _,
                    kind: OperandKind::LValue(on_lvalue_key),
                } = self.lower_expr(idx_expr.on)
                else {
                    unreachable!()
                };

                let Operand {
                    typ: _,
                    kind: idx_operand_kind,
                } = self.lower_expr(idx_expr.idx);

                // TODO: Support ranges indexing
                let lvalue = if self.is_mut_lvalue(on_lvalue_key) {
                    match idx_operand_kind {
                        OperandKind::LValue(idx_lvalue_key) => LValue::MutArrayIdx {
                            on: on_lvalue_key,
                            idx: idx_lvalue_key,
                        },
                        OperandKind::Const(Const::U(idx)) => LValue::MutArrayConstIdx {
                            on: on_lvalue_key,
                            idx: idx as u32,
                        },
                        _ => unreachable!(), // Other numeric consts are invalid
                    }
                } else {
                    match idx_operand_kind {
                        OperandKind::LValue(idx_lvalue_key) => LValue::ArrayIdx {
                            on: on_lvalue_key,
                            idx: idx_lvalue_key,
                        },
                        OperandKind::Const(Const::U(idx)) => LValue::ArrayConstIdx {
                            on: on_lvalue_key,
                            idx: idx as u32,
                        },
                        _ => unreachable!(), // Other numeric consts are invalid
                    }
                };

                let lvalue_key = self.get_lvalue_key(lvalue);

                OperandKind::LValue(lvalue_key)
            }
            nazmc_ast::ExprKind::UnaryOp(unary_op_expr) => 'label: {
                let operand = self.lower_expr(unary_op_expr.expr);

                match operand.kind {
                    OperandKind::LValue(lvalue_key) => {
                        let rvalue = match unary_op_expr.op {
                            nazmc_ast::UnaryOp::Deref => {
                                let operand_type_key =
                                    self.nir_builder.exprs_types[unary_op_expr.expr];
                                let lvalue = if let Type::MutPtr(_) =
                                    self.nir_builder.nir.types[operand_type_key]
                                {
                                    LValue::MutDeref(lvalue_key)
                                } else {
                                    LValue::Deref(lvalue_key)
                                };
                                let lvalue_key = self.get_lvalue_key(lvalue);
                                break 'label OperandKind::LValue(lvalue_key);
                            }
                            nazmc_ast::UnaryOp::Minus => RValue::UnaryOp {
                                op: nazmc_nir::UnaryOp::Minus,
                                operand,
                            },
                            nazmc_ast::UnaryOp::LNot => RValue::UnaryOp {
                                op: nazmc_nir::UnaryOp::LNot,
                                operand,
                            },
                            nazmc_ast::UnaryOp::BNot => RValue::UnaryOp {
                                op: nazmc_nir::UnaryOp::BNot,
                                operand,
                            },
                            nazmc_ast::UnaryOp::Borrow => {
                                let lvalue = self.cfg_builder.cfg.lvalues[lvalue_key];
                                if let LValue::Temp(_) = lvalue {
                                    self.add_cannot_borrow_rvalue(
                                        unary_op_expr.op_span,
                                        self.get_expr_span(unary_op_expr.expr),
                                    );
                                }
                                RValue::Ref(lvalue_key)
                            }
                            nazmc_ast::UnaryOp::BorrowMut => {
                                let lvalue = self.cfg_builder.cfg.lvalues[lvalue_key];
                                if let LValue::Temp(_) = lvalue {
                                    self.add_cannot_borrow_rvalue(
                                        unary_op_expr.op_span,
                                        self.get_expr_span(unary_op_expr.expr),
                                    );
                                }
                                RValue::RefMut(lvalue_key)
                            }
                        };
                        self.add_new_temp_assign_stm(typ, rvalue)
                    }
                    OperandKind::Const(_const) => match unary_op_expr.op {
                        nazmc_ast::UnaryOp::Deref => unreachable!(),
                        nazmc_ast::UnaryOp::Minus => OperandKind::Const(match _const {
                            Const::I(n) => Const::I(-n),
                            Const::I1(n) => Const::I1(-n),
                            Const::I2(n) => Const::I2(-n),
                            Const::I4(n) => Const::I4(-n),
                            Const::I8(n) => Const::I8(-n),
                            Const::F4(n) => Const::F4(-n),
                            Const::F8(n) => Const::F8(-n),
                            _ => unreachable!(),
                        }),
                        nazmc_ast::UnaryOp::LNot => OperandKind::Const(match _const {
                            Const::Bool(b) => Const::Bool(!b),
                            _ => unreachable!(),
                        }),
                        nazmc_ast::UnaryOp::BNot => OperandKind::Const(match _const {
                            Const::I(n) => Const::I(!n),
                            Const::I1(n) => Const::I1(!n),
                            Const::I2(n) => Const::I2(!n),
                            Const::I4(n) => Const::I4(!n),
                            Const::I8(n) => Const::I8(!n),
                            Const::U(n) => Const::U(!n),
                            Const::U1(n) => Const::U1(!n),
                            Const::U2(n) => Const::U2(!n),
                            Const::U4(n) => Const::U4(!n),
                            Const::U8(n) => Const::U8(!n),
                            _ => unreachable!(),
                        }),
                        nazmc_ast::UnaryOp::Borrow => {
                            self.add_cannot_borrow_rvalue(
                                unary_op_expr.op_span,
                                self.get_expr_span(unary_op_expr.expr),
                            );
                            let lvalue_key = self.get_lvalue_key(LValue::ReturnPtr);
                            let rvalue = RValue::Ref(lvalue_key);
                            self.add_new_temp_assign_stm(typ, rvalue)
                        }
                        nazmc_ast::UnaryOp::BorrowMut => {
                            self.add_cannot_borrow_rvalue(
                                unary_op_expr.op_span,
                                self.get_expr_span(unary_op_expr.expr),
                            );
                            let lvalue_key = self.get_lvalue_key(LValue::ReturnPtr);
                            let rvalue = RValue::RefMut(lvalue_key);
                            self.add_new_temp_assign_stm(typ, rvalue)
                        }
                    },
                }
            }
            nazmc_ast::ExprKind::BinaryOp(binary_op_expr) => todo!(),
            nazmc_ast::ExprKind::UnitStruct(unit_struct_path_key) => todo!(),
            nazmc_ast::ExprKind::TupleStruct(tuple_struct_expr) => todo!(),
            nazmc_ast::ExprKind::If(if_expr) => todo!(),
            nazmc_ast::ExprKind::Lambda(lambda_expr) => todo!(),
            nazmc_ast::ExprKind::Return(return_expr) => todo!(),
            nazmc_ast::ExprKind::Break(scope_key) => todo!(),
            nazmc_ast::ExprKind::Continue(scope_key) => todo!(),
            nazmc_ast::ExprKind::On => todo!(),
        };

        Operand { typ, kind }
    }
}
