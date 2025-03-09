use std::collections::HashMap;

use nazmc_ast::{ASTId, BinaryOpExpr, ExprKey, LetStmKey, ScopeKey};
use nazmc_data_pool::{typed_index_collections::TiVec, DataPoolBuilder, IdKey};
use nazmc_nir::{
    ArgKey, ArrayType, ArrayTypeKey, BasicBlock, BasicBlockKey, BinOp, Binding, BindingKey, Const,
    FnKey, FnPtrType, FnPtrTypeKey, LValue, LValueKey, LambdaType, LambdaTypeKey, Operand,
    OperandKind, RValue, StaticKey, Stm, Struct, StructKey, Temp, TupleType, TupleTypeKey, Type,
    TypeKey, CFG, NIR,
};

use crate::{get_bin_op_span, SemanticsAnalyzer};

#[derive(Default)]
pub(crate) struct NIRBuilder {
    pub(crate) nir: NIR,
    pub(crate) all_types: DataPoolBuilder<TypeKey, Type>,
    pub(crate) all_array_types: DataPoolBuilder<ArrayTypeKey, ArrayType>,
    pub(crate) all_tuple_types: DataPoolBuilder<TupleTypeKey, TupleType>,
    pub(crate) all_lambda_types: DataPoolBuilder<LambdaTypeKey, LambdaType>,
    pub(crate) all_fn_ptr_types: DataPoolBuilder<FnPtrTypeKey, FnPtrType>,
    pub(crate) exprs_types: TiVec<ExprKey, TypeKey>,
    pub(crate) bindings_types: HashMap<(LetStmKey, IdKey), TypeKey>,
}

impl NIRBuilder {
    pub(crate) fn get_unique_type(&mut self, typ: &crate::ConcreteType) -> TypeKey {
        let typ = match typ {
            crate::ConcreteType::Composite(composite_type) => match composite_type {
                crate::CompositeType::Slice(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = &**underlying_typ else {
                        unreachable!()
                    };
                    Type::Slice(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::Ptr(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = &**underlying_typ else {
                        unreachable!()
                    };
                    Type::Ptr(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::PtrMut(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = &**underlying_typ else {
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
                    let crate::Type::Concrete(underlying_typ) = &**underlying_typ else {
                        unreachable!()
                    };

                    let underlying_typ_key = self.get_unique_type(underlying_typ);

                    let array_typ = ArrayType {
                        underlying_typ: underlying_typ_key,
                        size: *size,
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

                    let crate::Type::Concrete(return_type) = &**return_type else {
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

                    let crate::Type::Concrete(return_type) = &**return_type else {
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
                Type::Struct(StructKey::from(usize::from(*fields_struct_key)))
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

impl CFGBuilder {
    pub(crate) fn build(&mut self) -> CFG {
        self.locals.clear();
        self.lvalues.clear();
        let cfg = std::mem::take(&mut self.cfg);
        // The end block
        self.cfg.basic_blocks.push(BasicBlock::default());
        // The start block
        self.cfg.basic_blocks.push(BasicBlock::default());
        cfg
    }
}

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn lower_scope(&mut self, scope_key: ScopeKey) {
        let stms = std::mem::take(&mut self.ast.scopes[scope_key].stms);
        for stm in stms {
            match stm {
                nazmc_ast::Stm::Let(let_stm_key) => {
                    let let_stm = std::mem::take(&mut self.ast.lets[let_stm_key]);
                    let binding_kind = let_stm.binding.kind;

                    let Some(expr_key) = let_stm.assign else {
                        self.lower_unassigned_bindings(let_stm_key, &binding_kind);
                        continue;
                    };

                    let expr_operand = self.lower_expr(expr_key);
                    let typ = self.nir_builder.exprs_types[expr_key];
                    let rvalue = RValue::Use(expr_operand);
                    self.lower_assigned_bindings(let_stm_key, &binding_kind, typ, rvalue);
                }
                nazmc_ast::Stm::While(while_stm) => todo!(),
                nazmc_ast::Stm::Expr(expr_key) => {
                    self.lower_expr(expr_key);
                }
            }
        }
    }

    fn lower_unassigned_bindings(&mut self, let_stm_key: LetStmKey, kind: &nazmc_ast::BindingKind) {
        match kind {
            nazmc_ast::BindingKind::Id(ast_id) => {
                self.add_new_binding(let_stm_key, ast_id, false);
            }
            nazmc_ast::BindingKind::MutId { id, mut_span: _ } => {
                self.add_new_binding(let_stm_key, id, true);
            }
            nazmc_ast::BindingKind::Tuple(bindings, _) => {
                bindings.iter().for_each(|binding_kind| {
                    self.lower_unassigned_bindings(let_stm_key, binding_kind);
                });
            }
        }
    }

    fn lower_assigned_bindings(
        &mut self,
        let_stm_key: LetStmKey,
        kind: &nazmc_ast::BindingKind,
        typ: TypeKey,
        rvalue: RValue,
    ) {
        match kind {
            nazmc_ast::BindingKind::Id(ast_id) => {
                let binding_key = self.add_new_binding(let_stm_key, ast_id, false);
                let lvalue_key = self.get_lvalue_key(LValue::Binding(binding_key));
                self.assign_to_lvalue(lvalue_key, rvalue);
            }
            nazmc_ast::BindingKind::MutId { id, mut_span: _ } => {
                let binding_key = self.add_new_binding(let_stm_key, id, true);
                let lvalue_key = self.get_lvalue_key(LValue::Binding(binding_key));
                self.assign_to_lvalue(lvalue_key, rvalue);
            }
            nazmc_ast::BindingKind::Tuple(bindings, _) => {
                let (OperandKind::LValue(temp_lvalue_key), Type::Tuple(tuple_type_key)) = (
                    self.add_new_temp_assign_stm(typ, rvalue),
                    self.nir_builder.nir.types[typ],
                ) else {
                    unreachable!()
                };

                bindings.iter().enumerate().for_each(|(i, binding_kind)| {
                    let typ = self.nir_builder.nir.tuple_types[tuple_type_key].types[i];
                    let tuple_idx_lvalue = LValue::MutTupleIdx {
                        on: temp_lvalue_key,
                        idx: i as u32,
                    };
                    let tuple_idx_lvalue_key = self.get_lvalue_key(tuple_idx_lvalue);
                    let tuple_idx_operand = Operand {
                        typ,
                        kind: OperandKind::LValue(tuple_idx_lvalue_key),
                    };
                    let rvalue = RValue::Use(tuple_idx_operand);
                    self.lower_assigned_bindings(let_stm_key, binding_kind, typ, rvalue);
                });
            }
        }
    }

    fn add_new_binding(
        &mut self,
        let_stm_key: LetStmKey,
        ast_id: &ASTId,
        is_mut: bool,
    ) -> BindingKey {
        let key = (let_stm_key, ast_id.id);

        let typ = self.nir_builder.bindings_types[&key];

        let binding_key = self.cfg_builder.cfg.bindings.push_and_get_key(Binding {
            id_key: key.1,
            id_span: ast_id.span,
            typ,
        });

        self.cfg_builder.locals.insert(key, binding_key);

        if is_mut {
            self.cfg_builder.cfg.mut_bindings.insert(binding_key, ());
        }

        binding_key
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

    fn assign_to_lvalue(&mut self, lvalue_key: LValueKey, rvalue: RValue) {
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
    }

    fn add_new_temp_assign_stm(&mut self, typ: TypeKey, rvalue: RValue) -> OperandKind {
        let assign_stm_idx = self.cfg_builder.cfg.basic_blocks.last().unwrap().stms.len() as u32;

        let temp = Temp {
            typ,
            assign_stm_idx,
        };

        let temp_key = self.cfg_builder.cfg.temps.push_and_get_key(temp);

        let lvalue_key = self.get_lvalue_key(LValue::Temp(temp_key));

        self.assign_to_lvalue(lvalue_key, rvalue);

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

    fn assign_to_lhs(
        &mut self,
        lhs: Operand,
        rvalue: RValue,
        binary_op_expr: &BinaryOpExpr,
    ) -> OperandKind {
        if let OperandKind::LValue(lvalue_key) = lhs.kind {
            if self.is_mut_lvalue(lvalue_key) {
                self.assign_to_lvalue(lvalue_key, rvalue);
            } else {
                self.add_cannot_mutate_immutable_lvalue(
                    self.get_expr_span(binary_op_expr.left),
                    get_bin_op_span(binary_op_expr.op, binary_op_expr.op_span_cursor),
                );
            }
        } else {
            self.add_cannot_assign_to_rvalue(
                self.get_expr_span(binary_op_expr.left),
                get_bin_op_span(binary_op_expr.op, binary_op_expr.op_span_cursor),
            );
        }

        OperandKind::Const(Const::Unit)
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
            nazmc_ast::ExprKind::BinaryOp(binary_op_expr) => 'label: {
                let lhs = self.lower_expr(binary_op_expr.left);
                let rhs = self.lower_expr(binary_op_expr.right);

                if let (OperandKind::Const(lhs), OperandKind::Const(rhs)) = (lhs.kind, rhs.kind) {
                    macro_rules! eval_bin_op_int_const {
			($op: tt) => {
			    match (lhs, rhs) {
				(Const::I(n1), Const::I(n2)) => Const::I(n1 $op n2),
				(Const::I1(n1), Const::I1(n2)) => Const::I1(n1 $op n2),
				(Const::I2(n1), Const::I2(n2)) => Const::I2(n1 $op n2),
				(Const::I4(n1), Const::I4(n2)) => Const::I4(n1 $op n2),
				(Const::I8(n1), Const::I8(n2)) => Const::I8(n1 $op n2),
				(Const::U(n1), Const::U(n2)) => Const::U(n1 $op n2),
				(Const::U1(n1), Const::U1(n2)) => Const::U1(n1 $op n2),
				(Const::U2(n1), Const::U2(n2)) => Const::U2(n1 $op n2),
				(Const::U4(n1), Const::U4(n2)) => Const::U4(n1 $op n2),
				(Const::U8(n1), Const::U8(n2)) => Const::U8(n1 $op n2),
				_ => unreachable!()
			    }
			};
		    }

                    macro_rules! eval_bin_op_num_const {
			($op: tt) => {
			    match (lhs, rhs) {
				(Const::F4(n1), Const::F4(n2)) => Const::F4(n1 $op n2),
				(Const::F8(n1), Const::F8(n2)) => Const::F8(n1 $op n2),
				_ => eval_bin_op_int_const!($op),
			    }
			};
		    }

                    macro_rules! eval_bin_op_cmp_num_const {
			($op: tt) => {
			    Const::Bool(match (lhs, rhs) {
				(Const::I(n1), Const::I(n2)) => n1 $op n2,
				(Const::I1(n1), Const::I1(n2)) => n1 $op n2,
				(Const::I2(n1), Const::I2(n2)) => n1 $op n2,
				(Const::I4(n1), Const::I4(n2)) => n1 $op n2,
				(Const::I8(n1), Const::I8(n2)) => n1 $op n2,
				(Const::U(n1), Const::U(n2)) => n1 $op n2,
				(Const::U1(n1), Const::U1(n2)) => n1 $op n2,
				(Const::U2(n1), Const::U2(n2)) => n1 $op n2,
				(Const::U4(n1), Const::U4(n2)) => n1 $op n2,
				(Const::U8(n1), Const::U8(n2)) => n1 $op n2,
				(Const::F4(n1), Const::F4(n2)) => n1 $op n2,
				(Const::F8(n1), Const::F8(n2)) => n1 $op n2,
				_ => unreachable!()
			    })
			};
		    }

                    let new_const = match binary_op_expr.op {
                        nazmc_ast::BinOp::LOr => {
                            let (Const::Bool(lhs), Const::Bool(rhs)) = (lhs, rhs) else {
                                unreachable!()
                            };
                            Const::Bool(lhs || rhs)
                        }
                        nazmc_ast::BinOp::LAnd => {
                            let (Const::Bool(lhs), Const::Bool(rhs)) = (lhs, rhs) else {
                                unreachable!()
                            };
                            Const::Bool(lhs && rhs)
                        }
                        nazmc_ast::BinOp::EqualEqual => Const::Bool(lhs == rhs),
                        nazmc_ast::BinOp::NotEqual => Const::Bool(lhs != rhs),
                        nazmc_ast::BinOp::GE => eval_bin_op_cmp_num_const!(>=),
                        nazmc_ast::BinOp::GT => eval_bin_op_cmp_num_const!(>),
                        nazmc_ast::BinOp::LE => eval_bin_op_cmp_num_const!(<=),
                        nazmc_ast::BinOp::LT => eval_bin_op_cmp_num_const!(<),
                        nazmc_ast::BinOp::OpenOpenRange => todo!(),
                        nazmc_ast::BinOp::CloseOpenRange => todo!(),
                        nazmc_ast::BinOp::OpenCloseRange => todo!(),
                        nazmc_ast::BinOp::CloseCloseRange => todo!(),
                        nazmc_ast::BinOp::BOr => eval_bin_op_int_const!(|),
                        nazmc_ast::BinOp::Xor => eval_bin_op_int_const!(^),
                        nazmc_ast::BinOp::BAnd => eval_bin_op_int_const!(&),
                        nazmc_ast::BinOp::Shr => eval_bin_op_int_const!(>>),
                        nazmc_ast::BinOp::Shl => eval_bin_op_int_const!(<<),
                        nazmc_ast::BinOp::Plus => eval_bin_op_num_const!(+),
                        nazmc_ast::BinOp::Minus => eval_bin_op_num_const!(-),
                        nazmc_ast::BinOp::Times => eval_bin_op_num_const!(*),
                        nazmc_ast::BinOp::Div => eval_bin_op_num_const!(/),
                        nazmc_ast::BinOp::Mod => eval_bin_op_num_const!(%),
                        _ => {
                            self.add_cannot_assign_to_rvalue(
                                self.get_expr_span(binary_op_expr.left),
                                get_bin_op_span(binary_op_expr.op, binary_op_expr.op_span_cursor),
                            );
                            Const::Unit
                        }
                    };

                    break 'label OperandKind::Const(new_const);
                }

                macro_rules! bin_op {
                    ($op: expr) => {
                        self.add_new_temp_assign_stm(typ, RValue::BinOp { op: $op, lhs, rhs })
                    };
                }

                macro_rules! aug_assign {
                    ($op: expr) => {
                        self.assign_to_lhs(
                            lhs,
                            RValue::BinOp { op: $op, lhs, rhs },
                            &binary_op_expr,
                        )
                    };
                }

                match binary_op_expr.op {
                    nazmc_ast::BinOp::LOr => todo!(),
                    nazmc_ast::BinOp::LAnd => todo!(),
                    nazmc_ast::BinOp::OpenOpenRange => todo!(),
                    nazmc_ast::BinOp::CloseOpenRange => todo!(),
                    nazmc_ast::BinOp::OpenCloseRange => todo!(),
                    nazmc_ast::BinOp::CloseCloseRange => todo!(),
                    nazmc_ast::BinOp::EqualEqual => bin_op!(BinOp::EqualEqual),
                    nazmc_ast::BinOp::NotEqual => bin_op!(BinOp::NotEqual),
                    nazmc_ast::BinOp::GE => bin_op!(BinOp::GE),
                    nazmc_ast::BinOp::GT => bin_op!(BinOp::GT),
                    nazmc_ast::BinOp::LE => bin_op!(BinOp::LE),
                    nazmc_ast::BinOp::LT => bin_op!(BinOp::LT),
                    nazmc_ast::BinOp::BOr => bin_op!(BinOp::BOr),
                    nazmc_ast::BinOp::Xor => bin_op!(BinOp::Xor),
                    nazmc_ast::BinOp::BAnd => bin_op!(BinOp::BAnd),
                    nazmc_ast::BinOp::Shr => bin_op!(BinOp::Shr),
                    nazmc_ast::BinOp::Shl => bin_op!(BinOp::Shl),
                    nazmc_ast::BinOp::Plus => bin_op!(BinOp::Plus),
                    nazmc_ast::BinOp::Minus => bin_op!(BinOp::Minus),
                    nazmc_ast::BinOp::Times => bin_op!(BinOp::Times),
                    nazmc_ast::BinOp::Div => bin_op!(BinOp::Div),
                    nazmc_ast::BinOp::Mod => bin_op!(BinOp::Mod),
                    nazmc_ast::BinOp::MinusAssign => aug_assign!(BinOp::Minus),
                    nazmc_ast::BinOp::TimesAssign => aug_assign!(BinOp::Times),
                    nazmc_ast::BinOp::DivAssign => aug_assign!(BinOp::Div),
                    nazmc_ast::BinOp::ModAssign => aug_assign!(BinOp::Mod),
                    nazmc_ast::BinOp::BOrAssign => aug_assign!(BinOp::BOr),
                    nazmc_ast::BinOp::XorAssign => aug_assign!(BinOp::Xor),
                    nazmc_ast::BinOp::BAndAssign => aug_assign!(BinOp::BAnd),
                    nazmc_ast::BinOp::ShrAssign => aug_assign!(BinOp::Shr),
                    nazmc_ast::BinOp::ShlAssign => aug_assign!(BinOp::Shl),
                    nazmc_ast::BinOp::PlusAssign => aug_assign!(BinOp::Plus),
                    nazmc_ast::BinOp::Assign => {
                        self.assign_to_lhs(lhs, RValue::Use(rhs), &binary_op_expr)
                    }
                }
            }
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
