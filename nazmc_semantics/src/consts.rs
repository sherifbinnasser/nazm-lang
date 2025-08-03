use nazmc_data_pool::ItemInfo;
use nazmc_nir_interpreter::InterpreterErr;
use typed_ast::{Const, Static};

use crate::*;

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn analyze_consts_and_statics(&mut self) {
        for const_key in self.ast.consts.keys() {
            let call_file = self.ast.consts[const_key].info.file_key;
            let call_span = self.ast.consts[const_key].info.id_span;
            self.analyze_const(const_key, call_file, call_span);
        }

        for static_key in self.ast.statics.keys() {
            let call_file = self.ast.statics[static_key].info.file_key;
            let call_span = self.ast.statics[static_key].info.id_span;
            self.analyze_static(static_key, call_file, call_span);
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
            self.typed_ast.consts.insert(
                const_key,
                Const {
                    typ: self.type_inf_ctx.new_never_ty_var(),
                },
            );
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

        let info = self.ast.consts[const_key].info.clone();
        let (typ, type_key, linkage) = self.analyze_const_or_static(
            self.ast.consts[const_key].info.file_key,
            self.ast.consts[const_key].typ,
            self.ast.consts[const_key].linkage,
            &info,
            true,
        );

        self.semantics_stack.consts.remove(&const_key);

        // To not consider array sizes constants
        if self.ast.consts[const_key].info.id_key != IdKey::EMPTY {
            self.semantics_stack.stack.pop();
        }

        self.typed_ast.consts.insert(const_key, Const { typ });
        self.nir_builder.nir.consts.insert(
            nazmc_nir::ConstKey(const_key.0),
            nazmc_nir::GlobalConst {
                info,
                typ: type_key,
                linkage,
            },
        );
    }

    pub(crate) fn analyze_static(
        &mut self,
        static_key: StaticKey,
        call_file: FileKey,
        call_span: Span,
    ) {
        if self.typed_ast.statics.contains_key(&static_key) {
            // The static is computed already
            return;
        } else if self.semantics_stack.statics.contains_key(&static_key) {
            self.typed_ast.statics.insert(
                static_key,
                Static {
                    typ: self.type_inf_ctx.new_never_ty_var(),
                },
            );
            self.semantics_stack.bad_consts_detected = true;
            self.report_cycle_detected(call_file, call_span);
            return;
        }

        self.semantics_stack.stack.push(ItemStackCall {
            call_file,
            call_span,
            kind: ItemStackCallKind::Static(static_key),
        });

        self.semantics_stack.statics.insert(static_key, ());

        let info = self.ast.statics[static_key].info.clone();
        let (typ, type_key, linkage) = self.analyze_const_or_static(
            self.ast.statics[static_key].info.file_key,
            self.ast.statics[static_key].typ,
            self.ast.statics[static_key].linkage,
            &info,
            false,
        );

        self.semantics_stack.statics.remove(&static_key);
        self.semantics_stack.stack.pop();

        self.typed_ast.statics.insert(static_key, Static { typ });
        self.nir_builder.nir.statics.insert(
            nazmc_nir::StaticKey(static_key.0),
            nazmc_nir::GlobalConst {
                info,
                typ: type_key,
                linkage,
            },
        );
    }

    fn analyze_const_or_static(
        &mut self,
        decl_file_key: FileKey,
        type_expr_key: TypeExprKey,
        linkage: Linkage,
        info: &ItemInfo,
        is_const: bool,
    ) -> (Type, nazmc_nir::TypeKey, nazmc_nir::Linkage) {
        let current_file_key = self.current_file_key;
        let typed_ast_exprs = std::mem::take(&mut self.typed_ast.exprs);
        let typed_ast_lets = std::mem::take(&mut self.typed_ast.lets);
        let type_inf_ctx = std::mem::take(&mut self.type_inf_ctx);
        let unknown_ty_vars = std::mem::take(&mut self.unknown_ty_vars);
        self.current_file_key = decl_file_key;

        let typ = self.analyze_type_expr(type_expr_key);

        let Linkage::Local { expr_scope_key } = linkage else {
            let linkage = if let Linkage::Extern { name } = linkage {
                nazmc_nir::Linkage::Extern(name)
            } else {
                nazmc_nir::Linkage::ExternWithSameId
            };

            let Type::Concrete(concrete_ty) = &typ else {
                unreachable!()
            };

            let type_key = self.nir_builder.get_unique_type(concrete_ty);

            return (typ, type_key, linkage);
        };
        let scope_type = self.infer_scope(expr_scope_key);

        if !self.semantics_stack.bad_consts_detected {
            if let Err(err) = self.type_inf_ctx.unify(&typ, &scope_type) {
                let expected_span = self.get_type_expr_span(type_expr_key);
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

            self.analyze_cfg(is_unit, &mut cfg, info);

            if self.diagnostics.is_empty() {
                self.interpret_cfg(&cfg, info, is_const, type_key)
            } else {
                vec![0]
            }
        } else {
            vec![0]
        };

        let value = self.interpreter_data.memory.push_bytes(&value_vec);

        self.typed_ast.exprs = typed_ast_exprs;
        self.typed_ast.lets = typed_ast_lets;
        self.unknown_ty_vars = unknown_ty_vars;
        self.type_inf_ctx = type_inf_ctx;
        self.current_file_key = current_file_key;

        (typ, type_key, nazmc_nir::Linkage::Local(value))
    }

    fn analyze_cfg(&mut self, is_unit_typ: bool, cfg: &mut CFG, info: &ItemInfo) {
        let nir = std::mem::take(&mut self.nir_builder.nir);
        let mut analyzer = nazmc_nir::nir_analyzer::NIRAnalyzer {
            nir,
            errors: Vec::new(),
        };

        analyzer.remove_dead_code(cfg);

        if !is_unit_typ {
            analyzer.check_all_paths_must_return(&cfg, &info);
        }

        let errors = std::mem::take(&mut analyzer.errors);

        for err in errors {
            self.diagnostics.push(err);
        }

        self.nir_builder.nir = analyzer.drop();
    }

    fn interpret_cfg(
        &mut self,
        cfg: &CFG,
        info: &ItemInfo,
        is_const: bool,
        type_key: nazmc_nir::TypeKey,
    ) -> Vec<u8> {
        self.interpreter_data.memory.set_const_mem_len_to_top();
        let mut interpreter = nazmc_nir_interpreter::Interpreter::new(
            &self.nir_builder.nir,
            &mut self.interpreter_data,
        );
        let value = interpreter.execute_const_static_cfg(&cfg, type_key);

        let Err(err) = value else {
            return value.unwrap();
        };

        let global_type = if is_const {
            "الثابت"
        } else {
            "المشترك"
        };

        let msg = match err {
            InterpreterErr::ModifyingConstOrStatic => "يوجد محاولة تعديل على قيمة ثابت أو مشترك",
            InterpreterErr::DanglingPtr => "تم العثور على مؤشر منقطع",
            InterpreterErr::NonCompileTimeConst(_) => "يوجد محاولة قراءة ثابت مربوط",
            InterpreterErr::NonCompileTimeStatic(_) => "يوجد محاولة قراءة مشترك مربوط",
        };

        let msg = format!(
            "{} عند حساب قيمة {} `{}`",
            msg,
            global_type,
            self.fmt_item_name(*info)
        );
        let const_id_span = info.id_span;
        let mut code_window = CodeWindow::new(
            &self.files_infos[self.current_file_key],
            const_id_span.start,
        );
        code_window.mark_error(const_id_span, vec![]);
        let mut diagnostic = Diagnostic::error(msg, vec![code_window]);

        if let InterpreterErr::NonCompileTimeConst(const_key) = err {
            let const_key = ConstKey(const_key.0);
            let const_file = self.ast.consts[const_key].info.file_key;
            let const_span = self.ast.consts[const_key].info.id_span;

            let msg = "تم ربط الثابت هنا".to_string();
            let mut code_window = CodeWindow::new(&self.files_infos[const_file], const_span.start);
            code_window.mark_note(const_span, vec![]);
            let note = Diagnostic::note(msg, vec![code_window]);
            diagnostic.chain(note);
        } else if let InterpreterErr::NonCompileTimeStatic(static_key) = err {
            let static_key = StaticKey(static_key.0);
            let static_file = self.ast.statics[static_key].info.file_key;
            let static_span = self.ast.statics[static_key].info.id_span;

            let msg = "تم ربط المشترك هنا".to_string();
            let mut code_window =
                CodeWindow::new(&self.files_infos[static_file], static_span.start);
            code_window.mark_note(static_span, vec![]);
            let note = Diagnostic::note(msg, vec![code_window]);
            diagnostic.chain(note);
        }

        self.diagnostics.push(diagnostic);

        return vec![0];
    }
}
