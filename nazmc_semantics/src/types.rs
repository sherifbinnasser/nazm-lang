use typed_ast::{FieldsStruct, TupleStruct};

use crate::*;

impl<'a> SemanticsAnalyzer<'a> {
    fn analyze_type_expr_checked(
        &mut self,
        type_expr_key: TypeExprKey,
        at: FileKey,
        called_from: CycleDetected,
    ) -> Type {
        let result = self.analyze_type_expr(type_expr_key);

        if self.semantics_stack.is_cycle_detected == CycleDetected::None {
            return result;
        }

        let type_expr_span = self.get_type_expr_span(type_expr_key);

        if self.semantics_stack.is_cycle_detected == called_from {
            match called_from {
                CycleDetected::None => {}
                CycleDetected::Const(const_key) => todo!(),
                CycleDetected::TupleStruct(tuple_struct_key) => {
                    let item_info = self.ast.tuple_structs[tuple_struct_key].info;
                    let msg = format!(
                        "توجد حلقة لا متناهية في تحديد حجم الهيكل `{}`",
                        self.fmt_item_name(item_info)
                    );
                    let sec_label = format!("لتحديد حجم الهيكل");
                    let err_label = if self.cycle_stack.is_empty() {
                        format!("يجب تحديد حجم نفس الهيكل مرة أخرى")
                    } else {
                        format!("ستنشأ الحلقة عند تحديد حجم هذا النوع")
                    };

                    let mut code_window =
                        CodeWindow::new(&self.files_infos[at], type_expr_span.start);

                    code_window.mark_secondary(item_info.id_span, vec![sec_label.into()]);
                    code_window.mark_error(type_expr_span, vec![err_label]);

                    let mut diagnostic = Diagnostic::error(msg, vec![code_window]);

                    for cycle in std::mem::take(&mut self.cycle_stack).into_iter().rev() {
                        diagnostic.chain(cycle);
                    }

                    self.diagnostics.push(diagnostic);
                }
                CycleDetected::FieldsStruct(fields_struct_key) => {
                    let item_info = self.ast.fields_structs[fields_struct_key].info;
                    let msg = format!(
                        "توجد حلقة لا متناهية في تحديد حجم الهيكل `{}`",
                        self.fmt_item_name(item_info)
                    );
                    let sec_label = format!("لتحديد حجم الهيكل");
                    let err_label = if self.cycle_stack.is_empty() {
                        format!("يجب تحديد حجم نفس الهيكل مرة أخرى")
                    } else {
                        format!("ستنشأ الحلقة عند تحديد حجم هذا النوع")
                    };

                    let mut code_window =
                        CodeWindow::new(&self.files_infos[at], type_expr_span.start);

                    code_window.mark_secondary(item_info.id_span, vec![sec_label.into()]);
                    code_window.mark_error(type_expr_span, vec![err_label]);

                    let mut diagnostic = Diagnostic::error(msg, vec![code_window]);

                    for cycle in std::mem::take(&mut self.cycle_stack).into_iter().rev() {
                        diagnostic.chain(cycle);
                    }

                    self.diagnostics.push(diagnostic);
                }
            }

            self.semantics_stack.is_cycle_detected = CycleDetected::None;
        } else {
            match called_from {
                CycleDetected::None => {}
                CycleDetected::Const(const_key) => todo!(),
                CycleDetected::TupleStruct(tuple_struct_key) => {
                    let item_info = self.ast.tuple_structs[tuple_struct_key].info;

                    let msg = format!("عند تحديد حجم الهيكل `{}`", self.fmt_item_name(item_info));
                    let sec_label = format!("لتحديد حجم الهيكل");
                    let note_label = format!("يجب تحديد حجم هذا النوع");

                    let mut code_window =
                        CodeWindow::new(&self.files_infos[at], type_expr_span.start);

                    code_window.mark_secondary(item_info.id_span, vec![sec_label]);
                    code_window.mark_note(type_expr_span, vec![note_label]);

                    let diagnostic = Diagnostic::note(msg, vec![code_window]);

                    self.cycle_stack.push(diagnostic);
                }
                CycleDetected::FieldsStruct(fields_struct_key) => {
                    let item_info = self.ast.fields_structs[fields_struct_key].info;

                    let msg = format!("عند تحديد حجم الهيكل `{}`", self.fmt_item_name(item_info));
                    let sec_label = format!("لتحديد حجم الهيكل");
                    let note_label = format!("يجب تحديد حجم هذا النوع");

                    let mut code_window =
                        CodeWindow::new(&self.files_infos[at], type_expr_span.start);

                    code_window.mark_secondary(item_info.id_span, vec![sec_label]);
                    code_window.mark_note(type_expr_span, vec![note_label]);

                    let diagnostic = Diagnostic::note(msg, vec![code_window]);

                    self.cycle_stack.push(diagnostic);
                }
            }
        }
        result
    }

    pub(crate) fn analyze_type_expr(&mut self, type_expr_key: TypeExprKey) -> Type {
        let type_expr = &self.ast.types_exprs.all[type_expr_key];
        match type_expr {
            TypeExpr::Path(path_type_expr_key) => self.analyze_path_type_expr(*path_type_expr_key),
            TypeExpr::Tuple(tuple_type_expr_key) => self.analyze_tuple(*tuple_type_expr_key),
            TypeExpr::Array(array_type_expr_key) => self.analyze_array(*array_type_expr_key),
            TypeExpr::Lambda(lambda_type_expr_key) => self.analyze_lambda(*lambda_type_expr_key),
            TypeExpr::Paren(paren_type_expr_key) => {
                return self.analyze_type_expr(
                    self.ast.types_exprs.parens[*paren_type_expr_key].underlying_typ,
                );
            }
            TypeExpr::Slice(slice_type_expr_key) => {
                let underlying_typ =
                    self.ast.types_exprs.slices[*slice_type_expr_key].underlying_typ;
                let type_key = self.analyze_type_expr(underlying_typ);
                Type::slice(type_key)
            }
            TypeExpr::Ptr(ptr_type_expr_key) => {
                let underlying_typ = self.ast.types_exprs.ptrs[*ptr_type_expr_key].underlying_typ;
                let underlying_type_key = self.analyze_type_expr(underlying_typ);
                Type::ptr(underlying_type_key)
            }
            TypeExpr::PtrMut(ptr_mut_type_expr_key) => {
                let underlying_typ =
                    self.ast.types_exprs.ptrs_mut[*ptr_mut_type_expr_key].underlying_typ;
                let underlying_type_key = self.analyze_type_expr(underlying_typ);
                Type::ptr_mut(underlying_type_key)
            }
        }
    }

    #[inline]
    fn analyze_path_type_expr(&mut self, key: PathTypeExprKey) -> Type {
        let (path_type, _span) = &self.ast.state.types_paths[key];
        match path_type {
            Item::UnitStruct { vis: _, key } => self.analyze_unit_struct(*key),
            Item::TupleStruct { vis: _, key } => {
                let key = *key;
                self.analyze_tuple_struct(key);
                let s = self.typed_ast.tuple_structs.get(&key).unwrap();
                Type::Concrete(ConcreteType::TupleStruct(key))
            }
            Item::FieldsStruct { vis: _, key } => {
                let key = *key;
                self.analyze_fields_struct(key);
                let s = self.typed_ast.fields_structs.get(&key).unwrap();
                Type::Concrete(ConcreteType::FieldsStruct(key))
            }
            _ => unreachable!(),
        }
    }

    #[inline]
    fn analyze_unit_struct(&mut self, key: UnitStructKey) -> Type {
        let info = &self.ast.unit_structs[key].info;
        let file_path = &self.files_infos[info.file_key].path;
        if file_path != "أساسي.نظم" {
            return Type::unit_struct(key);
        }

        match info.id_key {
            IdKey::I_TYPE => Type::i(),
            IdKey::I1_TYPE => Type::i1(),
            IdKey::I2_TYPE => Type::i2(),
            IdKey::I4_TYPE => Type::i4(),
            IdKey::I8_TYPE => Type::i8(),
            IdKey::U_TYPE => Type::u(),
            IdKey::U1_TYPE => Type::u1(),
            IdKey::U2_TYPE => Type::u2(),
            IdKey::U4_TYPE => Type::u4(),
            IdKey::U8_TYPE => Type::u8(),
            IdKey::F4_TYPE => Type::f4(),
            IdKey::F8_TYPE => Type::f8(),
            IdKey::BOOL_TYPE => Type::boolean(),
            IdKey::CHAR_TYPE => Type::character(),
            _ => unreachable!(),
        }
    }

    #[inline]
    fn analyze_tuple_struct(&mut self, key: TupleStructKey) {
        if self.typed_ast.tuple_structs.contains_key(&key) {
            // It is already computed
            return;
        } else if self.semantics_stack.tuple_structs.contains_key(&key) {
            self.semantics_stack.is_cycle_detected = CycleDetected::TupleStruct(key);

            self.typed_ast.tuple_structs.insert(key, Default::default());

            self.semantics_stack.tuple_structs.remove(&key);

            return;
        }

        self.semantics_stack.tuple_structs.insert(key, ());

        let at = self.ast.tuple_structs[key].info.file_key;
        let called_from = CycleDetected::TupleStruct(key);
        let types_len = self.ast.tuple_structs[key].types.len();
        let mut types = ThinVec::with_capacity(types_len);

        for i in 0..types_len {
            let type_expr_key = self.ast.tuple_structs[key].types[i].1;
            let typ = self.analyze_type_expr_checked(type_expr_key, at, called_from);
            types.push(typed_ast::FieldInfo { typ, idx: i as u32 });
        }

        self.semantics_stack.tuple_structs.remove(&key);

        self.typed_ast
            .tuple_structs
            .insert(key, TupleStruct { types });
    }

    #[inline]
    pub(crate) fn analyze_fields_struct(&mut self, key: FieldsStructKey) {
        if self.typed_ast.fields_structs.contains_key(&key) {
            // It is already computed
            return;
        } else if self.semantics_stack.fields_structs.contains_key(&key) {
            self.semantics_stack.is_cycle_detected = CycleDetected::FieldsStruct(key);

            self.typed_ast
                .fields_structs
                .insert(key, Default::default());

            self.semantics_stack.fields_structs.remove(&key);

            return;
        }

        self.semantics_stack.fields_structs.insert(key, ());

        let at = self.ast.fields_structs[key].info.file_key;
        let called_from = CycleDetected::FieldsStruct(key);
        let fields_len = self.ast.fields_structs[key].fields.len();
        let mut fields = HashMap::with_capacity(fields_len);

        for i in 0..fields_len {
            let FieldInfo {
                vis: _,
                id: ASTId { span: _, id },
                typ,
            } = self.ast.fields_structs[key].fields[i];
            let typ = self.analyze_type_expr_checked(typ, at, called_from);
            fields.insert(id, typed_ast::FieldInfo { typ, idx: i as u32 });
        }

        self.semantics_stack.fields_structs.remove(&key);

        self.typed_ast
            .fields_structs
            .insert(key, FieldsStruct { fields });
    }

    #[inline]
    fn analyze_tuple(&mut self, key: TupleTypeExprKey) -> Type {
        let types_len = self.ast.types_exprs.tuples[key].types.len();

        if types_len == 0 {
            return Type::unit();
        }

        let mut types = ThinVec::with_capacity(types_len);

        for i in 0..types_len {
            let type_expr_key = self.ast.types_exprs.tuples[key].types[i];
            let typ = self.analyze_type_expr(type_expr_key);
            types.push(typ);
        }

        Type::tuple(types)
    }

    #[inline]
    fn analyze_array(&mut self, key: ArrayTypeExprKey) -> Type {
        let underlying_typ = self.ast.types_exprs.arrays[key].underlying_typ;
        let underlying_typ = self.analyze_type_expr(underlying_typ);
        let size_expr_scope_key = self.ast.types_exprs.arrays[key].size_expr_scope_key;
        todo!()
    }

    #[inline]
    fn analyze_lambda(&mut self, key: LambdaTypeExprKey) -> Type {
        let params_types_len = self.ast.types_exprs.lambdas[key].params_types.len();
        let mut params_types = ThinVec::with_capacity(params_types_len);

        for i in 0..params_types_len {
            let type_expr_key = self.ast.types_exprs.lambdas[key].params_types[i];
            params_types.push(self.analyze_type_expr(type_expr_key));
        }

        let return_type = self.analyze_type_expr(self.ast.types_exprs.lambdas[key].return_type);

        Type::lambda(params_types, return_type)
    }
}
