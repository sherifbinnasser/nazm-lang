use typed_ast::Struct;

use crate::*;

impl<'a> SemanticsAnalyzer<'a> {
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
            TypeExpr::SliceMut(slice_mut_type_expr_key) => {
                let underlying_typ =
                    self.ast.types_exprs.slices_mut[*slice_mut_type_expr_key].underlying_typ;
                let type_key = self.analyze_type_expr(underlying_typ);
                Type::slice_mut(type_key)
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
            TypeExpr::FnPtr(fn_ptr_type_expr_key) => {
                let fn_ptr_type_expr_key = *fn_ptr_type_expr_key;

                let is_vararg = self.ast.types_exprs.fn_ptrs[fn_ptr_type_expr_key].is_vararg;

                let return_type = self.analyze_type_expr(
                    self.ast.types_exprs.fn_ptrs[fn_ptr_type_expr_key].return_type,
                );

                let params_len = self.ast.types_exprs.fn_ptrs[fn_ptr_type_expr_key]
                    .params_types
                    .len();

                let params_types = (0..params_len).map(|i| {
                    let param = self.ast.types_exprs.fn_ptrs[fn_ptr_type_expr_key].params_types[i];
                    self.analyze_type_expr(param)
                });

                Type::fn_ptr(params_types, return_type, is_vararg)
            }
        }
    }

    #[inline]
    fn analyze_path_type_expr(&mut self, key: PathTypeExprKey) -> Type {
        let (path_type, call_file, call_span) = &self.ast.state.types_paths[key];

        let Item::Struct { vis: _, key } = *path_type else {
            unreachable!()
        };

        if let Some(typ) = self.try_analyze_as_primitive_type(key) {
            return typ;
        }

        self.analyze_struct(key, *call_file, *call_span);
        Type::Concrete(ConcreteType::Struct(key))
    }

    pub(crate) fn try_analyze_as_primitive_type(&self, key: StructKey) -> Option<Type> {
        let info = &self.ast.structs[key].info;
        let file_path = &self.files_infos[info.file_key].path;

        if file_path != "أساسي.نظم" {
            return None;
        }

        Some(match info.id_key {
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
        })
    }

    #[inline]
    pub(crate) fn analyze_struct(
        &mut self,
        struct_key: StructKey,
        call_file: FileKey,
        call_span: Span,
    ) {
        if self.typed_ast.structs.contains_key(&struct_key) {
            // It is already computed
            return;
        } else if self.semantics_stack.structs.contains_key(&struct_key) {
            self.typed_ast
                .structs
                .insert(struct_key, Default::default());
            self.report_cycle_detected(call_file, call_span);
            return;
        }

        self.semantics_stack.stack.push(ItemStackCall {
            call_file,
            call_span,
            kind: ItemStackCallKind::Struct(struct_key),
        });

        self.semantics_stack.structs.insert(struct_key, ());

        let at = self.ast.structs[struct_key].info.file_key;
        let fields_len = self.ast.structs[struct_key].fields.len();
        let mut fields = HashMap::with_capacity(fields_len);

        for i in 0..fields_len {
            let FieldInfo {
                vis: _,
                id: ASTId { span: _, id },
                typ,
            } = self.ast.structs[struct_key].fields[i];
            let typ = self.analyze_type_expr(typ);
            fields.insert(id, typed_ast::FieldInfo { typ, idx: i as u32 });
        }

        self.semantics_stack.structs.remove(&struct_key);
        self.semantics_stack.stack.pop();
        self.typed_ast.structs.insert(struct_key, Struct { fields });

        // Lower struct tyo NIR

        let nir_struct_key = nazmc_nir::StructKey(struct_key.0);
        let fields = self.ast.structs[struct_key]
            .fields
            .iter()
            .map(|field_info| {
                let id = field_info.id.id;
                let field_info = &self.typed_ast.structs[&struct_key].fields[&id];
                let Type::Concrete(field_typ) = &field_info.typ else {
                    unreachable!()
                };
                let typ = self.nir_builder.get_unique_type(field_typ);
                Field { id, typ }
            })
            .collect();
        self.nir_builder.nir.structs.insert(
            nir_struct_key,
            nazmc_nir::Struct {
                info: self.ast.structs[struct_key].info,
                fields,
            },
        );
    }

    #[inline]
    fn analyze_tuple(&mut self, key: TupleTypeExprKey) -> Type {
        let types_len = self.ast.types_exprs.tuples[key].types.len();

        if types_len == 0 {
            return Type::unit();
        }

        let iter = (0..types_len).map(|i| {
            let type_expr_key = self.ast.types_exprs.tuples[key].types[i];
            self.analyze_type_expr(type_expr_key)
        });

        Type::tuple(iter)
    }

    #[inline]
    fn analyze_array(&mut self, key: ArrayTypeExprKey) -> Type {
        let underlying_typ = self.ast.types_exprs.arrays[key].underlying_typ;
        let underlying_typ = self.analyze_type_expr(underlying_typ);
        let size_const = self.ast.types_exprs.arrays[key].size_const;
        self.analyze_const(
            size_const,
            self.ast.consts[size_const].info.file_key,
            self.ast.consts[size_const].info.id_span,
        );
        let ptr = self.nir_builder.nir.consts[&nazmc_nir::ConstKey(size_const.0)].value;
        let size = self.interpreter_data.memory.get_bytes_at(ptr);
        let size = nazmc_nir_interpreter::bytes::to_usize(size).unwrap_or(0) as u32;
        Type::array(underlying_typ, size)
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
