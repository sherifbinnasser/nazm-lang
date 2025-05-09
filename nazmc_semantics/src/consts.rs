use nazmc_nir_interpreter::RcValue;
use typed_ast::Const;

use crate::*;

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn analyze_consts(&mut self) {
        println!("consts len: {}", self.ast.consts.len());
        for const_key in self.ast.consts.keys() {
            self.analyze_const(const_key);
        }
    }

    pub(crate) fn analyze_const(&mut self, const_key: ConstKey) {
        if self.typed_ast.consts.contains_key(&const_key) {
            // The const is computed already
            return;
        } else if self.semantics_stack.consts.contains_key(&const_key) {
            self.semantics_stack.is_cycle_detected = CycleDetected::Const(const_key);

            self.typed_ast.consts.insert(const_key, Default::default());

            self.semantics_stack.consts.remove(&const_key);

            return;
        }

        self.semantics_stack.consts.insert(const_key, ());

        let at = self.ast.consts[const_key].info.file_key;

        // self.current_file_key should be set to const's file key
        let current_file_key = self.current_file_key;
        let unknown_ty_vars = std::mem::take(&mut self.unknown_ty_vars);
        self.current_file_key = at;

        let called_from = CycleDetected::Const(const_key);
        let typ = self.analyze_type_expr_checked(self.ast.consts[const_key].typ, at, called_from);
        let expr_scope_key = self.ast.consts[const_key].expr_scope_key;
        let scope_type = self.infer_scope(expr_scope_key);

        if let Err(err) = self.type_inf_ctx.unify(&typ, &scope_type) {
            let expected_span = self.get_type_expr_span(self.ast.consts[const_key].typ);
            let found_span = self.ast.scopes[expr_scope_key].span;

            if expected_span == found_span {
                // Array expressions size type has the same span of the size expression, so no need to mark the type size
                self.add_type_mismatch_err(&typ, &scope_type, expected_span);
            } else {
                self.add_type_mismatch_in_let_stm_err(&typ, &scope_type, expected_span, found_span);
            }
        }

        let value = if self.check_and_report_unknown_type_vars(expr_scope_key) {
            self.walk_lower_scope_type_to_nir(expr_scope_key);
            todo!("Interpret")
        } else {
            RcValue::default()
        };

        self.unknown_ty_vars = unknown_ty_vars;
        self.current_file_key = current_file_key;
        self.semantics_stack.consts.remove(&const_key);

        self.typed_ast
            .consts
            .insert(const_key, Const { typ, value });
    }

    fn walk_lower_scope_type_to_nir(&mut self, scope_key: ScopeKey) {
        let stms = std::mem::take(&mut self.ast.scopes[scope_key].stms);
        for stm in &stms {
            match stm {
                Stm::Let(let_stm_key) => {
                    if let Some(expr_key) = self.ast.lets[*let_stm_key].assign {
                        self.walk_lower_expr_type_to_nir(expr_key);
                    }
                    let let_binding =
                        std::mem::take(self.typed_ast.lets.get_mut(let_stm_key).unwrap());
                    self.lower_let_type_to_nir(*let_stm_key, &let_binding);
                    self.typed_ast.lets.insert(*let_stm_key, let_binding);
                }
                Stm::While(while_stm) => {
                    self.walk_lower_expr_type_to_nir(while_stm.cond_expr_key);
                    self.walk_lower_scope_type_to_nir(while_stm.scope_key);
                }
                Stm::Expr(expr_key) => self.walk_lower_expr_type_to_nir(*expr_key),
            }
        }

        self.ast.scopes[scope_key].stms = stms;

        if let Some(expr_key) = self.ast.scopes[scope_key].return_expr {
            self.walk_lower_expr_type_to_nir(expr_key);
        }
    }

    fn walk_lower_expr_type_to_nir(&mut self, expr_key: ExprKey) {
        let kind = std::mem::take(&mut self.ast.exprs[expr_key].kind);
        let kind = match kind {
            ExprKind::Call(call_expr) => {
                self.walk_lower_expr_type_to_nir(call_expr.on);
                for arg in &call_expr.args {
                    self.walk_lower_expr_type_to_nir(*arg);
                }
                ExprKind::Call(call_expr)
            }
            ExprKind::Struct(struct_expr) => {
                for (_, field) in &struct_expr.fields {
                    self.walk_lower_expr_type_to_nir(*field);
                }
                ExprKind::Struct(struct_expr)
            }
            ExprKind::Field(field_expr) => {
                self.walk_lower_expr_type_to_nir(field_expr.on);
                ExprKind::Field(field_expr)
            }
            ExprKind::Idx(idx_expr) => {
                self.walk_lower_expr_type_to_nir(idx_expr.on);
                self.walk_lower_expr_type_to_nir(idx_expr.idx);
                ExprKind::Idx(idx_expr)
            }
            ExprKind::TupleIdx(tuple_idx_expr) => {
                self.walk_lower_expr_type_to_nir(tuple_idx_expr.on);
                ExprKind::TupleIdx(tuple_idx_expr)
            }
            ExprKind::Tuple(elements) => {
                for &element in &elements {
                    self.walk_lower_expr_type_to_nir(element);
                }
                ExprKind::Tuple(elements)
            }
            ExprKind::ArrayElements(elements) => {
                for &element in &elements {
                    self.walk_lower_expr_type_to_nir(element);
                }
                ExprKind::ArrayElements(elements)
            }
            ExprKind::ArrayRepeated(array_repeated_expr) => {
                self.walk_lower_expr_type_to_nir(array_repeated_expr.repeat);
                ExprKind::ArrayRepeated(array_repeated_expr)
            }
            ExprKind::UnaryOp(unary_op_expr) => {
                self.walk_lower_expr_type_to_nir(unary_op_expr.expr);
                ExprKind::UnaryOp(unary_op_expr)
            }
            ExprKind::BinaryOp(binary_op_expr) => {
                self.walk_lower_expr_type_to_nir(binary_op_expr.left);
                self.walk_lower_expr_type_to_nir(binary_op_expr.right);
                ExprKind::BinaryOp(binary_op_expr)
            }
            ExprKind::Cast(cast_expr) => {
                self.walk_lower_expr_type_to_nir(cast_expr.expr);
                ExprKind::Cast(cast_expr)
            }
            ExprKind::Return(return_expr) => {
                if let Some(return_expr) = return_expr.expr {
                    self.walk_lower_expr_type_to_nir(return_expr);
                }
                ExprKind::Return(return_expr)
            }
            ExprKind::If(if_expr) => {
                self.lower_expr_type_to_nir(if_expr.if_.1);
                self.walk_lower_scope_type_to_nir(if_expr.if_.2);

                for (_, cond_expr, scope) in &if_expr.else_ifs {
                    self.walk_lower_expr_type_to_nir(*cond_expr);
                    self.walk_lower_scope_type_to_nir(*scope);
                }
                if let Some((_, else_scope)) = if_expr.else_ {
                    self.walk_lower_scope_type_to_nir(else_scope);
                }
                ExprKind::If(if_expr)
            }
            ExprKind::Lambda(lambda_expr) => todo!(),
            kind => kind,
        };
        self.lower_expr_type_to_nir(expr_key);
        self.ast.exprs[expr_key].kind = kind;
    }
}
