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
        let typed_ast_exprs = std::mem::take(&mut self.typed_ast.exprs);
        let typed_ast_lets = std::mem::take(&mut self.typed_ast.lets);
        let type_inf_ctx = std::mem::take(&mut self.type_inf_ctx);
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

        let value = if self.check_unkown_ty_vars_and_lower_to_nir(expr_scope_key) {
            self.nir_builder.build_types();
            todo!("Interpret")
        } else {
            RcValue::default()
        };

        self.typed_ast.exprs = typed_ast_exprs;
        self.typed_ast.lets = typed_ast_lets;
        self.unknown_ty_vars = unknown_ty_vars;
        self.type_inf_ctx = type_inf_ctx;
        self.current_file_key = current_file_key;
        self.semantics_stack.consts.remove(&const_key);

        self.typed_ast
            .consts
            .insert(const_key, Const { typ, value });
    }
}
