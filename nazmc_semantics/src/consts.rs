use nazmc_nir::RcValue;
use typed_ast::Const;

use crate::*;

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn analyze_consts(&mut self) {
        for const_key in self.ast.consts.keys() {
            self.analyze_const(const_key);
        }

        for (const_key, cnst) in &self.nir_builder.nir.consts {
            println!("const{} = {:?}", const_key.0, cnst.value);
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

        let mut type_key = nazmc_nir::TypeKey::default();

        let value = if self.check_unkown_ty_vars_and_lower_to_nir(expr_scope_key) {
            self.nir_builder.build_types();
            let mut cfg = self.lower_scope_to_cfg(expr_scope_key);

            type_key =
                self.nir_builder.exprs_types[&self.ast.scopes[expr_scope_key].return_expr.unwrap()];

            let is_unit = matches!(self.nir_builder.nir.types[type_key], nazmc_nir::Type::Unit);

            self.analyze_const_cfg(is_unit, &mut cfg, const_key);

            if self.diagnostics.is_empty() {
                let mut interpreter =
                    nazmc_nir_interpreter::Interpreter::new(&self.nir_builder.nir);
                let return_value = interpreter.execute_cfg(&cfg, HashMap::new());
                return_value.unwrap_or_default()
            } else {
                RcValue::default()
            }
        } else {
            RcValue::default()
        };

        self.typed_ast.exprs = typed_ast_exprs;
        self.typed_ast.lets = typed_ast_lets;
        self.unknown_ty_vars = unknown_ty_vars;
        self.type_inf_ctx = type_inf_ctx;
        self.current_file_key = current_file_key;
        self.semantics_stack.consts.remove(&const_key);

        self.typed_ast.consts.insert(const_key, Const { typ });
        self.nir_builder.nir.consts.insert(
            nazmc_nir::ConstKey(const_key.0),
            nazmc_nir::NamedConst {
                info: self.ast.consts[const_key].info,
                typ: type_key,
                value,
            },
        );
    }

    fn analyze_const_cfg(&mut self, is_unit_typ: bool, cfg: &mut CFG, const_key: ConstKey) {
        let nir = std::mem::take(&mut self.nir_builder.nir);
        let mut analyzer = nazmc_nir::nir_analyzer::NIRAnalyzer {
            nir,
            errors: Vec::new(),
        };

        analyzer.remove_dead_code(cfg);

        if !is_unit_typ {
            analyzer.check_all_paths_must_return(&cfg, &self.ast.consts[const_key].info);
        }

        let errors = std::mem::take(&mut analyzer.errors);

        for err in errors {
            self.diagnostics.push(err);
        }

        self.nir_builder.nir = analyzer.drop();
    }
}
