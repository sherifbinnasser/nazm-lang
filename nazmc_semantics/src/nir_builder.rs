use std::collections::HashMap;

use iter_tools::Itertools;
use nazmc_ast::{ASTId, BinaryOpExpr, CastExpr, ExprKey, IfExpr, LetStmKey, ScopeKey};
use nazmc_data_pool::{typed_index_collections::TiVec, DataPoolBuilder, IdKey};
use nazmc_nir::{
    ArgKey, ArrayType, ArrayTypeKey, BasicBlock, BasicBlockKey, BinOp, Binding, BindingKey, Branch,
    BranchKey, CastKind, Const, FnKey, FnPtrType, FnPtrTypeKey, LValue, LValueKey, LValueKind,
    LambdaType, LambdaTypeKey, Operand, OperandKind, RValue, StaticKey, Stm, StructKey, Temp,
    TupleType, TupleTypeKey, Type, TypeKey, CFG, NIR,
};
use thin_vec::ThinVec;

use crate::{get_bin_op_span, SemanticsAnalyzer};

#[derive(Default)]
pub(crate) struct NIRBuilder<'a> {
    pub(crate) nir: NIR<'a>,
    pub(crate) all_types: DataPoolBuilder<TypeKey, Type>,
    pub(crate) all_array_types: DataPoolBuilder<ArrayTypeKey, ArrayType>,
    pub(crate) all_tuple_types: DataPoolBuilder<TupleTypeKey, TupleType>,
    pub(crate) all_lambda_types: DataPoolBuilder<LambdaTypeKey, LambdaType>,
    pub(crate) all_fn_ptr_types: DataPoolBuilder<FnPtrTypeKey, FnPtrType>,
    pub(crate) exprs_types: HashMap<ExprKey, TypeKey>,
    pub(crate) bindings_types: HashMap<(LetStmKey, IdKey), TypeKey>,
}

impl<'a> NIRBuilder<'a> {
    pub(crate) fn build_types(&mut self) {
        if self.all_types.map.len() <= self.nir.types.len() {
            return;
        }

        self.nir.types = self.all_types.build_cloned();
        self.nir.array_types = self.all_array_types.build_cloned();
        self.nir.tuple_types = self.all_tuple_types.build_cloned();
        self.nir.lambda_types = self.all_lambda_types.build_cloned();
        self.nir.fn_ptr_types = self.all_fn_ptr_types.build_cloned();
    }

    pub(crate) fn get_unique_type(&mut self, typ: &crate::ConcreteType) -> TypeKey {
        let typ = match typ {
            crate::ConcreteType::Composite(composite_type) => match composite_type {
                crate::CompositeType::Slice(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = &**underlying_typ else {
                        unreachable!()
                    };
                    Type::Slice(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::SliceMut(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = &**underlying_typ else {
                        unreachable!()
                    };
                    Type::MutSlice(self.get_unique_type(underlying_typ))
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
                    is_vararg,
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
                        is_vararg: *is_vararg,
                    };

                    let fn_ptr_type_key = self.all_fn_ptr_types.get_key(&fn_ptr_type);

                    Type::FnPtr(fn_ptr_type_key)
                }
            },
            crate::ConcreteType::Struct(fields_struct_key) => {
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
    /// Map a loop scope to the starts of its continue and break blocks
    pub(crate) loops_basic_blocks: HashMap<ScopeKey, (BasicBlockKey, BasicBlockKey)>,
    pub(crate) current_basic_block_key: BasicBlockKey,
}

impl CFGBuilder {
    pub(crate) fn build(&mut self) -> CFG {
        self.locals.clear();
        self.lvalues.clear();
        self.loops_basic_blocks.clear();
        let cfg = std::mem::take(&mut self.cfg);
        // The end block
        self.new_basic_block();
        // The start block
        self.new_basic_block();
        // The block after start
        self.new_current_basic_block();
        // TODO: Do we need this only for presentation puproses?
        self.add_straight_goto(
            BasicBlockKey::START_BASIC_BLOCK,
            self.current_basic_block_key,
        );
        cfg
    }

    fn get_current_basic_block(&self) -> &BasicBlock {
        self.cfg
            .basic_blocks
            .get(&self.current_basic_block_key)
            .unwrap()
    }

    fn get_current_basic_block_mut(&mut self) -> &mut BasicBlock {
        self.cfg
            .basic_blocks
            .get_mut(&self.current_basic_block_key)
            .unwrap()
    }

    fn get_basic_block_mut(&mut self, basic_block_key: BasicBlockKey) -> &mut BasicBlock {
        self.cfg.basic_blocks.get_mut(&basic_block_key).unwrap()
    }

    fn new_basic_block(&mut self) -> BasicBlockKey {
        let key = BasicBlockKey::from(self.cfg.basic_blocks.len());
        self.cfg.basic_blocks.insert(key, BasicBlock::default());
        key
    }

    fn new_current_basic_block(&mut self) -> BasicBlockKey {
        let key = self.new_basic_block();
        self.current_basic_block_key = key;
        key
    }

    fn new_branch(&mut self, branch: Branch) -> BranchKey {
        let key = BranchKey::from(self.cfg.branches.len());
        self.cfg.branches.insert(key, branch);
        key
    }

    fn add_straight_goto(&mut self, from: BasicBlockKey, to: BasicBlockKey) {
        let branch_key = self.new_branch(Branch {
            from,
            to,
            kind: nazmc_nir::BranchKind::Straight,
        });
        self.get_basic_block_mut(from).goto = Some(branch_key);
        self.get_basic_block_mut(to).incoming.insert(branch_key, ());
    }

    fn add_else_goto(&mut self, from: BasicBlockKey, to: BasicBlockKey) {
        let branch_key = self.new_branch(Branch {
            from,
            to,
            kind: nazmc_nir::BranchKind::Else,
        });
        self.get_basic_block_mut(from).goto = Some(branch_key);
        self.get_basic_block_mut(to).incoming.insert(branch_key, ());
    }
}

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn lower_scope_to_cfg(&mut self, scope_key: ScopeKey) -> CFG {
        self.lower_scope(scope_key);
        self.lower_return_expr(self.ast.scopes[scope_key].return_expr);
        self.cfg_builder.build()
    }

    fn lower_return_expr(&mut self, return_expr: Option<ExprKey>) {
        if let Some(expr_key) = return_expr {
            // Calculate it early as lower_expr will take the ownership of the expression kind
            let is_return_expr = matches!(
                self.ast.exprs[expr_key].kind,
                nazmc_ast::ExprKind::Return(_)
            );

            let return_value = self.lower_expr(expr_key);

            if !is_return_expr {
                let typ = self.nir_builder.exprs_types[&expr_key];
                let rvalue = RValue::Use(return_value);
                self.cfg_builder
                    .get_current_basic_block_mut()
                    .stms
                    .push(Stm::Return { rvalue, typ });
            }
        }

        self.cfg_builder.add_straight_goto(
            self.cfg_builder.current_basic_block_key,
            BasicBlockKey::END_BASIC_BLOCK,
        );

        self.cfg_builder.new_current_basic_block(); // Unreachable code
    }

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
                    let typ = self.nir_builder.exprs_types[&expr_key];
                    let rvalue = RValue::Use(expr_operand);
                    self.lower_assigned_bindings(let_stm_key, &binding_kind, typ, rvalue);
                }
                nazmc_ast::Stm::While(while_stm) => {
                    let current_block = self.cfg_builder.current_basic_block_key;
                    let loop_break_start = self.cfg_builder.new_basic_block(); // Reserve it for break expressions
                    let loop_continue_start = self.cfg_builder.new_current_basic_block();

                    self.cfg_builder
                        .loops_basic_blocks
                        .insert(while_stm.scope_key, (loop_continue_start, loop_break_start));

                    let (loop_continue_end, _) = self.add_branch_blocks_with_prepared_else(
                        while_stm.cond_expr_key,
                        while_stm.scope_key,
                        loop_break_start,
                    );

                    if let Some(expr_key) = self.ast.scopes[while_stm.scope_key].return_expr {
                        self.lower_expr(expr_key);
                    }

                    self.cfg_builder.current_basic_block_key = loop_break_start;

                    self.cfg_builder
                        .loops_basic_blocks
                        .remove(&while_stm.scope_key);

                    self.cfg_builder
                        .add_straight_goto(current_block, loop_continue_start);
                    self.cfg_builder
                        .add_straight_goto(loop_continue_end, loop_continue_start);
                }
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
                let key = (let_stm_key, ast_id.id);
                let typ = self.nir_builder.bindings_types[&key];
                let binding_key = self.add_new_binding(let_stm_key, ast_id, false);
                let lvalue_key = self.get_lvalue_key(LValueKind::Binding(binding_key), typ);
                self.assign_to_lvalue(lvalue_key, rvalue, typ);
            }
            nazmc_ast::BindingKind::MutId { id, mut_span: _ } => {
                let key = (let_stm_key, id.id);
                let typ = self.nir_builder.bindings_types[&key];
                let binding_key = self.add_new_binding(let_stm_key, id, true);
                let lvalue_key = self.get_lvalue_key(LValueKind::Binding(binding_key), typ);
                self.assign_to_lvalue(lvalue_key, rvalue, typ);
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
                    let tuple_idx_lvalue = LValueKind::MutField {
                        on: temp_lvalue_key,
                        idx: i as u32,
                    };
                    let tuple_idx_lvalue_key = self.get_lvalue_key(tuple_idx_lvalue, typ);
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

    fn get_lvalue_key(&mut self, lvalue_kind: LValueKind, typ: TypeKey) -> LValueKey {
        let lvalue = LValue {
            kind: lvalue_kind,
            typ,
        };
        if let Some(&lvalue_key) = self.cfg_builder.lvalues.get(&lvalue) {
            lvalue_key
        } else {
            let lvalue_key = self.cfg_builder.cfg.lvalues.push_and_get_key(lvalue);
            self.cfg_builder.lvalues.insert(lvalue, lvalue_key);
            lvalue_key
        }
    }

    fn assign_to_lvalue(&mut self, lvalue_key: LValueKey, rvalue: RValue, typ: TypeKey) {
        let assign = Stm::Assign {
            lhs: lvalue_key,
            rhs: rvalue,
            typ,
        };

        self.cfg_builder
            .get_current_basic_block_mut()
            .stms
            .push(assign);
    }

    fn new_temp(&mut self, typ: TypeKey, assign_stm_idx: u32) -> LValueKey {
        let temp = Temp {
            typ,
            assign_stm_idx,
        };
        let temp_key = self.cfg_builder.cfg.temps.push_and_get_key(temp);
        self.get_lvalue_key(LValueKind::Temp(temp_key), typ)
    }

    fn add_new_temp_assign_stm(&mut self, typ: TypeKey, rvalue: RValue) -> OperandKind {
        let assign_stm_idx = self.cfg_builder.get_current_basic_block().stms.len() as u32;
        let temp_lvalue_key = self.new_temp(typ, assign_stm_idx);
        self.assign_to_lvalue(temp_lvalue_key, rvalue, typ);
        OperandKind::LValue(temp_lvalue_key)
    }

    fn is_mut_lvalue(&self, lvalue_key: LValueKey) -> bool {
        match &self.cfg_builder.cfg.lvalues[lvalue_key].kind {
            LValueKind::Binding(binding_key) => {
                self.cfg_builder.cfg.mut_bindings.contains_key(binding_key)
            }
            LValueKind::Arg(arg_key) => {
                let fn_key = FnKey::from(usize::from(self.current_fn_key));
                self.nir_builder.nir.fns[fn_key].args[*arg_key].is_mut
            }
            LValueKind::Const(_)
            | LValueKind::Deref(_)
            | LValueKind::Field { .. }
            | LValueKind::ArrayIdx { .. }
            | LValueKind::ArrayConstIdx { .. } => false,
            LValueKind::Temp(_)
            | LValueKind::Static(_)
            | LValueKind::MutDeref(_)
            | LValueKind::MutField { .. }
            | LValueKind::MutArrayIdx { .. }
            | LValueKind::MutArrayConstIdx { .. } => true,
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
                self.assign_to_lvalue(lvalue_key, rvalue, lhs.typ);
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

    fn add_branch_blocks_with_prepared_else(
        &mut self,
        cond_expr_key: ExprKey,
        then_scope_key: ScopeKey,
        else_basic_block_start: BasicBlockKey,
    ) -> (BasicBlockKey, OperandKind) {
        let mut cond_operand = 'label: {
            let nazmc_ast::ExprKind::UnaryOp(unary_op_expr) =
                self.ast.exprs[cond_expr_key].kind.clone()
            else {
                break 'label self.lower_expr(cond_expr_key);
            };

            let nazmc_ast::UnaryOp::LNot = unary_op_expr.op else {
                break 'label self.lower_expr(cond_expr_key);
            };

            let (Type::Ptr(_) | Type::MutPtr(_)) =
                self.nir_builder.nir.types[self.nir_builder.exprs_types[&unary_op_expr.expr]]
            else {
                break 'label self.lower_expr(cond_expr_key);
            };

            let ptr_expr_operand = self.lower_expr(unary_op_expr.expr);
            let bool_type_key = TypeKey::from(0u32);

            let temp_operand_kind = self.add_new_temp_assign_stm(
                bool_type_key,
                RValue::BinOp {
                    op: BinOp::EqualEqual,
                    rhs: Operand {
                        typ: ptr_expr_operand.typ,
                        kind: OperandKind::Const(Const::Null),
                    },
                    lhs: ptr_expr_operand,
                },
            );

            Operand {
                typ: bool_type_key,
                kind: temp_operand_kind,
            }
        };

        if let Type::Ptr(_) | Type::MutPtr(_) =
            self.nir_builder.nir.types[self.nir_builder.exprs_types[&cond_expr_key]]
        {
            let bool_type_key = TypeKey::from(0u32);

            let temp_operand_kind = self.add_new_temp_assign_stm(
                bool_type_key,
                RValue::BinOp {
                    op: BinOp::NotEqual,
                    rhs: Operand {
                        typ: cond_operand.typ,
                        kind: OperandKind::Const(Const::Null),
                    },
                    lhs: cond_operand,
                },
            );

            cond_operand = Operand {
                typ: bool_type_key,
                kind: temp_operand_kind,
            };
        }

        let current_basic_block = self.cfg_builder.current_basic_block_key;
        let then_basic_block_start = self.cfg_builder.new_current_basic_block();

        self.lower_scope(then_scope_key);

        let return_operand = if let Some(expr_key) = self.ast.scopes[then_scope_key].return_expr {
            self.lower_expr(expr_key).kind
        } else {
            OperandKind::Const(Const::Unit)
        };

        let then_basic_block_end = self.cfg_builder.current_basic_block_key;

        let current_to_then = self.cfg_builder.new_branch(Branch {
            from: current_basic_block,
            to: then_basic_block_start,
            kind: nazmc_nir::BranchKind::If(cond_operand),
        });

        self.cfg_builder
            .get_basic_block_mut(current_basic_block)
            .conditional_goto = Some(current_to_then);
        self.cfg_builder
            .get_basic_block_mut(then_basic_block_start)
            .incoming
            .insert(current_to_then, ());

        self.cfg_builder
            .add_else_goto(current_basic_block, else_basic_block_start);

        (then_basic_block_end, return_operand)
    }

    fn add_branch_blocks(
        &mut self,
        cond_expr_key: ExprKey,
        then_scope_key: ScopeKey,
    ) -> (BasicBlockKey, OperandKind) {
        let else_basic_block_start = self.cfg_builder.new_basic_block();
        let (then_basic_block_end, return_operand) = self.add_branch_blocks_with_prepared_else(
            cond_expr_key,
            then_scope_key,
            else_basic_block_start,
        );
        self.cfg_builder.current_basic_block_key = else_basic_block_start;
        (then_basic_block_end, return_operand)
    }

    fn lower_expr(&mut self, expr_key: ExprKey) -> Operand {
        let expr_kind = std::mem::take(&mut self.ast.exprs[expr_key].kind);

        let typ = self.nir_builder.exprs_types[&expr_key];

        let kind = match expr_kind {
            nazmc_ast::ExprKind::Unit => OperandKind::Const(Const::Unit),
            nazmc_ast::ExprKind::Null => OperandKind::Const(Const::Null),
            nazmc_ast::ExprKind::Literal(literal_expr) => 'label: {
                let const_opernad = match literal_expr {
                    nazmc_ast::LiteralExpr::Str(str_key) => {
                        break 'label self.add_new_temp_assign_stm(typ, RValue::Str(str_key))
                    }
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
                    nazmc_ast::Item::Const { vis, key } => {
                        let const_key = nazmc_nir::ConstKey(key.0);
                        let lvalue_key = self.get_lvalue_key(LValueKind::Const(const_key), typ);
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::Static { vis, key } => {
                        let static_key = StaticKey::from(usize::from(key));
                        let lvalue_key = self.get_lvalue_key(LValueKind::Static(static_key), typ);
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::Fn { vis, key } => {
                        let fn_key = FnKey::from(usize::from(key));
                        OperandKind::Const(Const::Fn(fn_key))
                    }
                    nazmc_ast::Item::LocalVar { id, key } => {
                        let binding_key = self.cfg_builder.locals[&(key, id)];
                        let lvalue_key = self.get_lvalue_key(LValueKind::Binding(binding_key), typ);
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::FnParam { idx, fn_key } => {
                        let lvalue_key =
                            self.get_lvalue_key(LValueKind::Arg(ArgKey::from(idx)), typ);
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::LambdaParam { id, scope_key } => todo!(),
                    _ => unreachable!(),
                }
            }
            nazmc_ast::ExprKind::PathInPkg(path_with_pkg_key) => {
                let item = self.ast.state.paths_with_pkgs_exprs[path_with_pkg_key];

                match item {
                    nazmc_ast::Item::Const { vis, key } => {
                        let const_key = nazmc_nir::ConstKey(key.0);
                        let lvalue_key = self.get_lvalue_key(LValueKind::Const(const_key), typ);
                        OperandKind::LValue(lvalue_key)
                    }
                    nazmc_ast::Item::Static { vis, key } => {
                        let static_key = StaticKey::from(usize::from(key));
                        let lvalue_key = self.get_lvalue_key(LValueKind::Static(static_key), typ);
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
            nazmc_ast::ExprKind::Struct(fields_struct_expr) => {
                let struct_key = self.ast.state.structs_paths_exprs[fields_struct_expr.path_key];

                let struct_key = StructKey::from(usize::from(struct_key));

                let fields = fields_struct_expr
                    .fields
                    .iter()
                    .map(|(id, expr_key)| {
                        (
                            self.nir_builder.nir.structs[&struct_key]
                                .fields
                                .iter()
                                .find_position(|f| f.id == id.id)
                                .unwrap()
                                .0 as u32,
                            self.lower_expr(*expr_key),
                        )
                    })
                    .collect::<HashMap<_, _>>();

                let fields = fields.into_iter().sorted().collect();

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
                    typ: on_typ,
                    kind: OperandKind::LValue(lvalue_key),
                } = self.lower_expr(field_expr.on)
                else {
                    unreachable!()
                };

                let idx = match self.nir_builder.nir.types[on_typ] {
                    Type::Struct(struct_key) => {
                        // REVIEW: Should we cache fields indecies
                        self.nir_builder.nir.structs[&struct_key]
                            .fields
                            .iter()
                            .find_position(|f| f.id == field_expr.name.id)
                            .unwrap()
                            .0 as u32
                    }
                    Type::Slice(_) | Type::MutSlice(_)
                        if field_expr.name.id == IdKey::SLICE_PTR_FIELD =>
                    {
                        0
                    }
                    Type::Slice(_) | Type::MutSlice(_)
                        if field_expr.name.id == IdKey::SLICE_LEN_FIELD =>
                    {
                        1
                    }
                    _ => unreachable!(),
                };

                let lvalue = if self.is_mut_lvalue(lvalue_key) {
                    LValueKind::MutField {
                        on: lvalue_key,
                        idx,
                    }
                } else {
                    LValueKind::Field {
                        on: lvalue_key,
                        idx,
                    }
                };

                let lvalue_key = self.get_lvalue_key(lvalue, typ);

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
                    LValueKind::MutField {
                        on: lvalue_key,
                        idx: tuple_idx_expr.idx,
                    }
                } else {
                    LValueKind::Field {
                        on: lvalue_key,
                        idx: tuple_idx_expr.idx,
                    }
                };

                let lvalue_key = self.get_lvalue_key(lvalue, typ);

                OperandKind::LValue(lvalue_key)
            }

            nazmc_ast::ExprKind::Idx(idx_expr) => {
                let on_operand @ Operand {
                    typ: lvalue_typ_key,
                    kind: OperandKind::LValue(on_lvalue_key),
                } = self.lower_expr(idx_expr.on)
                else {
                    unreachable!()
                };

                let lvalue_typ = self.nir_builder.nir.types[lvalue_typ_key];

                let idx_operand @ Operand {
                    typ: _,
                    kind: idx_operand_kind,
                } = self.lower_expr(idx_expr.idx);

                // TODO: Support ranges indexing
                let lvalue = if let Type::Ptr(_) = lvalue_typ {
                    let OperandKind::LValue(temp_key) = self.add_new_temp_assign_stm(
                        lvalue_typ_key,
                        RValue::BinOp {
                            op: BinOp::Plus,
                            lhs: on_operand,
                            rhs: idx_operand,
                        },
                    ) else {
                        unreachable!()
                    };
                    LValueKind::Deref(temp_key)
                } else if let Type::MutPtr(_) = lvalue_typ {
                    let OperandKind::LValue(temp_key) = self.add_new_temp_assign_stm(
                        lvalue_typ_key,
                        RValue::BinOp {
                            op: BinOp::Plus,
                            lhs: on_operand,
                            rhs: idx_operand,
                        },
                    ) else {
                        unreachable!()
                    };
                    LValueKind::MutDeref(temp_key)
                } else if self.is_mut_lvalue(on_lvalue_key) {
                    match idx_operand_kind {
                        OperandKind::LValue(idx_lvalue_key) => LValueKind::MutArrayIdx {
                            on: on_lvalue_key,
                            idx: idx_lvalue_key,
                        },
                        OperandKind::Const(Const::U(idx)) => LValueKind::MutArrayConstIdx {
                            on: on_lvalue_key,
                            idx: idx as u32,
                        },
                        _ => unreachable!(), // Other numeric consts are invalid
                    }
                } else {
                    match idx_operand_kind {
                        OperandKind::LValue(idx_lvalue_key) => LValueKind::ArrayIdx {
                            on: on_lvalue_key,
                            idx: idx_lvalue_key,
                        },
                        OperandKind::Const(Const::U(idx)) => LValueKind::ArrayConstIdx {
                            on: on_lvalue_key,
                            idx: idx as u32,
                        },
                        _ => unreachable!(), // Other numeric consts are invalid
                    }
                };

                let lvalue_key = self.get_lvalue_key(lvalue, typ);

                OperandKind::LValue(lvalue_key)
            }
            nazmc_ast::ExprKind::UnaryOp(unary_op_expr) => 'label: {
                let operand = self.lower_expr(unary_op_expr.expr);

                match operand.kind {
                    OperandKind::LValue(lvalue_key) => {
                        let rvalue = match unary_op_expr.op {
                            nazmc_ast::UnaryOp::Deref => {
                                let operand_type_key =
                                    self.nir_builder.exprs_types[&unary_op_expr.expr];
                                let lvalue = if let Type::MutPtr(_) =
                                    self.nir_builder.nir.types[operand_type_key]
                                {
                                    LValueKind::MutDeref(lvalue_key)
                                } else {
                                    LValueKind::Deref(lvalue_key)
                                };
                                let lvalue_key = self.get_lvalue_key(lvalue, typ);
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
                                let lvalue = self.cfg_builder.cfg.lvalues[lvalue_key].kind;
                                if let LValueKind::Temp(_) = lvalue {
                                    self.add_cannot_borrow_rvalue(
                                        unary_op_expr.op_span,
                                        self.get_expr_span(unary_op_expr.expr),
                                    );
                                }
                                RValue::Ref(lvalue_key)
                            }
                            nazmc_ast::UnaryOp::BorrowMut => {
                                let lvalue = self.cfg_builder.cfg.lvalues[lvalue_key].kind;
                                if let LValueKind::Temp(_) = lvalue {
                                    self.add_cannot_borrow_rvalue(
                                        unary_op_expr.op_span,
                                        self.get_expr_span(unary_op_expr.expr),
                                    );
                                } else if !self.is_mut_lvalue(lvalue_key) {
                                    self.add_cannot_take_mutable_ref_for_immutable_lvalue(
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
                            let lvalue_key = self.new_temp(typ, 0);
                            let rvalue = RValue::Ref(lvalue_key);
                            self.add_new_temp_assign_stm(typ, rvalue)
                        }
                        nazmc_ast::UnaryOp::BorrowMut => {
                            self.add_cannot_borrow_rvalue(
                                unary_op_expr.op_span,
                                self.get_expr_span(unary_op_expr.expr),
                            );
                            let lvalue_key = self.new_temp(typ, 0);
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
            nazmc_ast::ExprKind::Cast(cast_expr) => {
                let from_typ = self.nir_builder.exprs_types[&cast_expr.expr];
                let val = self.lower_expr(cast_expr.expr);

                let kind = if from_typ == typ {
                    return val;
                } else if let Some(kind) = self.get_cast_kind(from_typ, typ) {
                    kind
                } else {
                    self.add_cannot_perfrom_type_cast(
                        self.nir_builder.nir.fmt_typ(from_typ),
                        self.nir_builder.nir.fmt_typ(typ),
                        self.get_expr_span(expr_key),
                    );
                    CastKind::PtrToPtr
                };

                self.add_new_temp_assign_stm(typ, RValue::Cast { val, kind })
            }
            nazmc_ast::ExprKind::If(if_expr) => {
                let IfExpr {
                    if_,
                    else_ifs,
                    else_,
                } = *if_expr;

                let mut cases = ThinVec::with_capacity(1 + else_ifs.len() + else_.map_or(0, |_| 1));

                let (then_end, return_operand) = self.add_branch_blocks(if_.1, if_.2);

                cases.push((then_end, return_operand));

                let mut thens_ends = Vec::with_capacity(else_ifs.len());

                for else_if in else_ifs {
                    let (then_end, return_operand) = self.add_branch_blocks(else_if.1, else_if.2);
                    thens_ends.push(then_end);
                    cases.push((then_end, return_operand));
                }

                let remaining_block = if let Some((_, else_scope)) = else_ {
                    self.lower_scope(else_scope);

                    let return_operand =
                        if let Some(expr_key) = self.ast.scopes[else_scope].return_expr {
                            self.lower_expr(expr_key).kind
                        } else {
                            OperandKind::Const(Const::Unit)
                        };

                    let else_end = self.cfg_builder.current_basic_block_key;
                    cases.push((else_end, return_operand));
                    self.cfg_builder.new_current_basic_block()
                } else {
                    self.cfg_builder.current_basic_block_key
                };

                for (end, _) in &cases {
                    self.cfg_builder.add_straight_goto(*end, remaining_block);
                }

                let assign_stm_idx = self.cfg_builder.get_current_basic_block().stms.len() as u32;

                let temp_lvalue_key = self.new_temp(typ, assign_stm_idx);

                self.cfg_builder
                    .get_current_basic_block_mut()
                    .stms
                    .push(Stm::Phi {
                        lhs: temp_lvalue_key,
                        cases,
                        typ,
                    });

                OperandKind::LValue(temp_lvalue_key)
            }
            nazmc_ast::ExprKind::Return(return_expr) => {
                self.lower_return_expr(return_expr.expr);
                OperandKind::Const(Const::Unit)
            }
            nazmc_ast::ExprKind::Break(scope_key) => {
                let loop_break_start = self.cfg_builder.loops_basic_blocks[&scope_key].1;
                self.cfg_builder
                    .add_straight_goto(self.cfg_builder.current_basic_block_key, loop_break_start);
                self.cfg_builder.new_current_basic_block(); // Unreachable code
                OperandKind::Const(Const::Unit)
            }
            nazmc_ast::ExprKind::Continue(scope_key) => {
                let loop_continue_start = self.cfg_builder.loops_basic_blocks[&scope_key].0;
                self.cfg_builder.add_straight_goto(
                    self.cfg_builder.current_basic_block_key,
                    loop_continue_start,
                );
                self.cfg_builder.new_current_basic_block(); // Unreachable code
                OperandKind::Const(Const::Unit)
            }
            nazmc_ast::ExprKind::Lambda(lambda_expr) => todo!(),
            nazmc_ast::ExprKind::On => todo!(),
        };

        Operand { typ, kind }
    }

    fn get_cast_kind(&mut self, from: TypeKey, to: TypeKey) -> Option<CastKind> {
        let from = &self.nir_builder.nir.types[from];
        let to = &self.nir_builder.nir.types[to];
        use nazmc_nir::Size::*;
        use CastKind::*;
        use Type::*;

        fn get_int_size(i: &Type) -> nazmc_nir::Size {
            match i {
                I | U => nazmc_nir::Size::Ptr,
                I1 | U1 => Byte,
                I2 | U2 => Word,
                I4 | U4 => DWord,
                I8 | U8 => QWord,
                _ => unreachable!(),
            }
        }

        macro_rules! int_matches {
            () => {
                I | I1 | I2 | I4 | I8
            };
        }

        macro_rules! uint_matches {
            () => {
                U | U1 | U2 | U4 | U8
            };
        }

        macro_rules! ptr_matches {
            () => {
                Type::Ptr(_) | MutPtr(_)
            };
            ($type_key: expr) => {
                matches!(self.nir_builder.nir.types[$type_key], ptr_matches!())
            };
        }

        match (from, to) {
            (U1, Char) => Some(U1ToChar),
            (F4, F8) => Some(F4ToF8),
            (F8, F4) => Some(F8ToF4),
            // Primtives to integers
            (F4, i @ int_matches!()) => Some(F4ToInt {
                int_size: get_int_size(i),
            }),
            (F4, i @ uint_matches!()) => Some(F4ToUInt {
                int_size: get_int_size(i),
            }),
            (F8, i @ int_matches!()) => Some(F8ToInt {
                int_size: get_int_size(i),
            }),
            (F8, i @ uint_matches!()) => Some(F8ToUInt {
                int_size: get_int_size(i),
            }),
            (Bool, i @ int_matches!()) => Some(BoolToInt {
                int_size: get_int_size(i),
            }),
            (Bool, i @ uint_matches!()) => Some(BoolToUInt {
                int_size: get_int_size(i),
            }),
            (Char, i @ int_matches!()) => Some(CharToInt {
                int_size: get_int_size(i),
            }),
            (Char, i @ uint_matches!()) => Some(CharToUInt {
                int_size: get_int_size(i),
            }),
            // Integers to primitves
            (i1 @ int_matches!(), t2) => match t2 {
                int_matches!() => Some(IntToInt {
                    int1_size: get_int_size(i1),
                    int2_size: get_int_size(t2),
                }),
                uint_matches!() => Some(IntToUInt {
                    int1_size: get_int_size(i1),
                    int2_size: get_int_size(t2),
                }),
                F4 => Some(IntToF4 {
                    int_size: get_int_size(i1),
                }),
                F8 => Some(IntToF8 {
                    int_size: get_int_size(i1),
                }),
                _ => None,
            },
            (i1 @ uint_matches!(), t2) => match t2 {
                int_matches!() => Some(UIntToInt {
                    int1_size: get_int_size(i1),
                    int2_size: get_int_size(t2),
                }),
                uint_matches!() => Some(UIntToUInt {
                    int1_size: get_int_size(i1),
                    int2_size: get_int_size(t2),
                }),
                F4 => Some(UIntToF4 {
                    int_size: get_int_size(i1),
                }),
                F8 => Some(UIntToF8 {
                    int_size: get_int_size(i1),
                }),
                ptr_matches!() => Some(UIntToPtr {
                    int_size: get_int_size(i1),
                }),
                _ => None,
            },
            (ptr_matches!(), i @ uint_matches!()) => Some(PtrToUInt {
                int_size: get_int_size(i),
            }),
            (ptr_matches!(), ptr_matches!()) => Some(PtrToPtr),
            (Slice(type_key1) | MutSlice(type_key1), Slice(type_key2) | MutSlice(type_key2))
                if type_key1 == type_key2
                    || ptr_matches!(*type_key1) && ptr_matches!(*type_key2) =>
            {
                Some(PtrToPtr)
            }
            (Array(type_key1), Array(type_key2))
                if ptr_matches!(self.nir_builder.nir.array_types[*type_key1].underlying_typ)
                    && ptr_matches!(
                        self.nir_builder.nir.array_types[*type_key2].underlying_typ
                    )
                    && self.nir_builder.nir.array_types[*type_key1].size
                        == self.nir_builder.nir.array_types[*type_key1].size =>
            {
                Some(PtrToPtr)
            }
            (Array(type_key1), Slice(type_key2) | MutSlice(type_key2))
                if self.nir_builder.nir.array_types[*type_key1].underlying_typ == *type_key2 =>
            {
                Some(ArrayToSlice {
                    len: self.nir_builder.nir.array_types[*type_key1].size,
                })
            }
            _ => None,
        }
    }
}
