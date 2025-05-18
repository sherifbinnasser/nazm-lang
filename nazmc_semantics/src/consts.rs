use std::rc::Rc;

use nazmc_nir::{PtrKey, TypeKey};
use typed_ast::Const;

use crate::*;

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn analyze_consts(&mut self) {
        for const_key in self.ast.consts.keys() {
            let call_file = self.ast.consts[const_key].info.file_key;
            let call_span = self.ast.consts[const_key].info.id_span;
            self.analyze_const(const_key, call_file, call_span);
        }

        for (const_key, cnst) in &self.nir_builder.nir.consts {
            println!("const{} = {:?}", const_key.0, cnst.value);
        }
    }

    pub(crate) fn analyze_const(
        &mut self,
        const_key: ConstKey,
        call_file: FileKey,
        call_span: Span,
    ) {
        if self.typed_ast.consts.contains_key(&const_key) {
            // The const is computed already
            return;
        } else if self.semantics_stack.consts.contains_key(&const_key) {
            self.typed_ast.consts.insert(const_key, Default::default());
            self.semantics_stack.bad_consts_detected = true;
            self.report_cycle_detected(call_file, call_span);
            return;
        }

        // To not consider array sizes constants
        if self.ast.consts[const_key].info.id_key != IdKey::EMPTY {
            self.semantics_stack.stack.push(ItemStackCall {
                call_file,
                call_span,
                kind: ItemStackCallKind::Const(const_key),
            });
        }

        self.semantics_stack.consts.insert(const_key, ());

        // self.current_file_key should be set to const's file key
        let current_file_key = self.current_file_key;
        let typed_ast_exprs = std::mem::take(&mut self.typed_ast.exprs);
        let typed_ast_lets = std::mem::take(&mut self.typed_ast.lets);
        let type_inf_ctx = std::mem::take(&mut self.type_inf_ctx);
        let unknown_ty_vars = std::mem::take(&mut self.unknown_ty_vars);
        self.current_file_key = self.ast.consts[const_key].info.file_key;

        let typ = self.analyze_type_expr(self.ast.consts[const_key].typ);
        let expr_scope_key = self.ast.consts[const_key].expr_scope_key;
        let scope_type = self.infer_scope(expr_scope_key);

        if !self.semantics_stack.bad_consts_detected {
            if let Err(err) = self.type_inf_ctx.unify(&typ, &scope_type) {
                let expected_span = self.get_type_expr_span(self.ast.consts[const_key].typ);
                let found_span = self.ast.scopes[expr_scope_key].span;

                if expected_span == found_span {
                    // Array expressions size type has the same span of the size expression, so no need to mark the type size
                    self.add_type_mismatch_err(&typ, &scope_type, expected_span);
                } else {
                    self.add_type_mismatch_in_let_stm_err(
                        &typ,
                        &scope_type,
                        expected_span,
                        found_span,
                    );
                }
            }
        }

        let mut type_key = nazmc_nir::TypeKey::default();

        let value_vec = if !self.semantics_stack.bad_consts_detected
            && self.check_unkown_ty_vars_and_lower_to_nir(expr_scope_key)
        {
            self.nir_builder.build_types();
            let mut cfg = self.lower_scope_to_cfg(expr_scope_key);

            type_key =
                self.nir_builder.exprs_types[&self.ast.scopes[expr_scope_key].return_expr.unwrap()];

            let is_unit = matches!(self.nir_builder.nir.types[type_key], nazmc_nir::Type::Unit);

            self.analyze_const_cfg(is_unit, &mut cfg, const_key);

            if self.diagnostics.is_empty() {
                let mut interpreter = nazmc_nir_interpreter::Interpreter::new(
                    &self.nir_builder.nir,
                    &mut self.interpreter_data,
                );
                interpreter.execute_cfg(&cfg, HashMap::new())
            } else {
                vec![0]
            }
        } else {
            vec![0]
        };

        let value = self.interpreter_data.memory.push_bytes(&value_vec);

        if self.check_dangling_pointer(&value_vec, type_key).is_err() {
            let msg = format!(
                "تم العثور على مؤشر منقطع عند حساب قيمة الثابت `{}`",
                self.fmt_item_name(self.ast.consts[const_key].info)
            );
            let const_id_span = self.ast.consts[const_key].info.id_span;
            let mut code_window = CodeWindow::new(
                &self.files_infos[self.current_file_key],
                const_id_span.start,
            );
            code_window.mark_error(const_id_span, vec![]);
            let diagnostic = Diagnostic::error(msg, vec![code_window]);
            self.diagnostics.push(diagnostic);
        }

        self.typed_ast.exprs = typed_ast_exprs;
        self.typed_ast.lets = typed_ast_lets;
        self.unknown_ty_vars = unknown_ty_vars;
        self.type_inf_ctx = type_inf_ctx;
        self.current_file_key = current_file_key;
        self.semantics_stack.consts.remove(&const_key);

        // To not consider array sizes constants
        if self.ast.consts[const_key].info.id_key != IdKey::EMPTY {
            self.semantics_stack.stack.pop();
        }

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

    fn check_dangling_pointer(&self, value: &[u8], type_key: TypeKey) -> Result<(), ()> {
        match self.nir_builder.nir.types[type_key] {
            nazmc_nir::Type::Struct(struct_key) => todo!(),
            nazmc_nir::Type::Slice(type_key)
            | nazmc_nir::Type::MutSlice(type_key)
            | nazmc_nir::Type::Ptr(type_key)
            | nazmc_nir::Type::MutPtr(type_key) => {
                let ptr_key = nazmc_nir_interpreter::bytes::to_ptr_key(&value).unwrap();
                self.check_dangling_ptr_key(ptr_key)?;
                let value = self.interpreter_data.memory.get_bytes_at(ptr_key);
                self.check_dangling_pointer(value, type_key)
            }
            nazmc_nir::Type::Array(array_type_key) => todo!(),
            nazmc_nir::Type::Tuple(tuple_type_key) => todo!(),
            nazmc_nir::Type::Lambda(lambda_type_key) => todo!(),
            nazmc_nir::Type::FnPtr(fn_ptr_type_key) => todo!(),
            _ => Ok(()),
        }
    }

    fn check_dangling_ptr_key(&self, ptr_key: PtrKey) -> Result<(), ()> {
        let top = self.interpreter_data.memory.get_top();
        if ptr_key.0 >= top.0 {
            Err(())
        } else {
            Ok(())
        }
    }
}
