use nazmc_nir_interpreter::RcValue;
use typed_ast::Const;

use crate::*;

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn analyze_consts(&mut self) {
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
        let called_from = CycleDetected::Const(const_key);
        let typ = self.analyze_type_expr_checked(self.ast.consts[const_key].typ, at, called_from);
        let expr_scope_key = self.ast.consts[const_key].expr_scope_key;

        self.semantics_stack.consts.remove(&const_key);
        self.typed_ast.consts.insert(
            const_key,
            Const {
                typ,
                value: RcValue::default(),
            },
        );
    }
}
