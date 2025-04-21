use nazmc_diagnostics::span::SpanCursor;

use crate::{
    type_infer::{CompositeType, ConcreteType, NumberConstraints},
    typed_ast::{FieldInfo, LambdaParams},
    *,
};

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn infer(&mut self, expr_key: ExprKey) -> Type {
        let kind = std::mem::take(&mut self.ast.exprs[expr_key].kind);
        let (ty, kind) = match kind {
            ExprKind::Unit => (Type::unit(), ExprKind::Unit),
            ExprKind::Literal(lit_expr) => {
                (self.infer_lit_expr(lit_expr), ExprKind::Literal(lit_expr))
            }
            ExprKind::PathNoPkg(path_no_pkg_key) => (
                self.infer_path_no_pkg_expr(path_no_pkg_key),
                ExprKind::PathNoPkg(path_no_pkg_key),
            ),
            ExprKind::PathInPkg(path_with_pkg_key) => (
                self.infer_path_with_pkg_expr(path_with_pkg_key),
                ExprKind::PathInPkg(path_with_pkg_key),
            ),
            ExprKind::UnitStruct(unit_struct_path_key) => {
                let key = self.ast.state.unit_structs_paths_exprs[unit_struct_path_key];
                (
                    Type::unit_struct(key),
                    ExprKind::UnitStruct(unit_struct_path_key),
                )
            }
            ExprKind::Tuple(thin_vec) => {
                let types = thin_vec.iter().map(|&expr_key| self.infer(expr_key));
                (Type::tuple(types), ExprKind::Tuple(thin_vec))
            }
            ExprKind::Call(call_expr) => {
                (self.infer_call_expr(&call_expr), ExprKind::Call(call_expr))
            }
            ExprKind::Idx(idx_expr) => (self.infer_idx_expr(&idx_expr), ExprKind::Idx(idx_expr)),
            ExprKind::ArrayElements(elements) => (
                self.infer_array_elements(&elements),
                ExprKind::ArrayElements(elements),
            ),
            ExprKind::TupleIdx(tuple_idx_expr) => (
                self.infer_tuple_idx_expr(&tuple_idx_expr),
                ExprKind::TupleIdx(tuple_idx_expr),
            ),
            ExprKind::FieldsStruct(fields_struct_expr) => (
                self.infer_fields_struct_expr(&fields_struct_expr, expr_key),
                ExprKind::FieldsStruct(fields_struct_expr),
            ),
            ExprKind::If(if_expr) => (self.infer_if_expr(&if_expr), ExprKind::If(if_expr)),
            ExprKind::Field(field_expr) => (
                self.infer_field_expr(&field_expr),
                ExprKind::Field(field_expr),
            ),
            ExprKind::Lambda(lambda_expr) => (
                self.infer_lambda_expr(&lambda_expr),
                ExprKind::Lambda(lambda_expr),
            ),
            ExprKind::TupleStruct(_) => todo!(),
            ExprKind::ArrayRepeated(_) => todo!(),
            ExprKind::On => todo!(),
            ExprKind::UnaryOp(unary_op_expr) => (
                self.infer_unary_op_expr(&unary_op_expr),
                ExprKind::UnaryOp(unary_op_expr),
            ),
            ExprKind::BinaryOp(binary_op_expr) => (
                self.infer_bin_op_expr(&binary_op_expr),
                ExprKind::BinaryOp(binary_op_expr),
            ),
            kind @ (ExprKind::Break(_) | ExprKind::Continue(_)) => {
                (self.type_inf_ctx.new_never_ty_var(), kind)
            }
            ExprKind::Return(return_expr) => (
                self.infer_return_expr(&return_expr),
                ExprKind::Return(return_expr),
            ),
        };

        self.ast.exprs[expr_key].kind = kind;

        self.typed_ast.exprs.insert(expr_key, ty.clone());

        ty
    }

    fn infer_lit_expr(&mut self, lit_expr: LiteralExpr) -> Type {
        match lit_expr {
            LiteralExpr::Str(_) => Type::slice(Type::u1()),
            LiteralExpr::Char(_) => Type::character(),
            LiteralExpr::Bool(_) => Type::boolean(),
            LiteralExpr::Num(num_kind) => match num_kind {
                NumKind::F4(_) => Type::f4(),
                NumKind::F8(_) => Type::f8(),
                NumKind::I(_) => Type::i(),
                NumKind::I1(_) => Type::i1(),
                NumKind::I2(_) => Type::i2(),
                NumKind::I4(_) => Type::i4(),
                NumKind::I8(_) => Type::i8(),
                NumKind::U(_) => Type::u(),
                NumKind::U1(_) => Type::u1(),
                NumKind::U2(_) => Type::u2(),
                NumKind::U4(_) => Type::u4(),
                NumKind::U8(_) => Type::u8(),
                NumKind::UnspecifiedInt(_) => self.type_inf_ctx.new_int_ty_var(),
                NumKind::UnspecifiedFloat(_) => self.type_inf_ctx.new_float_ty_var(),
            },
        }
    }

    fn infer_path_no_pkg_expr(&mut self, path_no_pkg_key: PathNoPkgKey) -> Type {
        let item = self.ast.state.paths_no_pkgs_exprs[path_no_pkg_key];

        let typ = match item {
            Item::Const { vis: _, key } => todo!(),
            Item::Static { vis: _, key } => todo!(),
            Item::Fn { vis: _, key } => &self.typed_ast.fns_signatures[&key],
            Item::LocalVar { id, key } => self
                .typed_ast
                .lets
                .get(&key)
                .unwrap()
                .bindings
                .get(&id)
                .unwrap(),
            Item::FnParam { idx, fn_key: _ } => {
                let Type::Concrete(ConcreteType::Composite(CompositeType::FnPtr {
                    params_types,
                    return_type: _,
                })) = &self.typed_ast.fns_signatures[&self.current_fn_key]
                else {
                    unreachable!()
                };

                return params_types[idx as usize].clone();
            }
            Item::LambdaParam { id, scope_key } => self
                .typed_ast
                .lambdas_params
                .get(&scope_key)
                .unwrap()
                .bindings
                .get(&id)
                .unwrap(),
            _ => unreachable!(),
        };

        typ.clone()
    }

    fn infer_path_with_pkg_expr(&mut self, path_with_pkg_key: PathWithPkgKey) -> Type {
        let item = self.ast.state.paths_with_pkgs_exprs[path_with_pkg_key];

        let typ: &Type = match item {
            Item::Const { vis: _, key } => todo!(),
            Item::Static { vis: _, key } => todo!(),
            Item::Fn { vis: _, key } => &self.typed_ast.fns_signatures[&key],
            _ => unreachable!(),
        };

        typ.clone()
    }

    fn infer_call_expr(
        &mut self,
        CallExpr {
            on,
            args,
            parens_span,
        }: &CallExpr,
    ) -> Type {
        let on = *on;
        let parens_span = *parens_span;

        let on_expr_ty = self.infer(on);
        let on_expr_ty = self.type_inf_ctx.apply(&on_expr_ty);

        let (params_types, return_type, is_fn) = match on_expr_ty {
            Type::Concrete(ConcreteType::Composite(CompositeType::FnPtr {
                params_types,
                return_type,
            })) => (params_types, return_type, true),
            Type::Concrete(ConcreteType::Composite(CompositeType::Lambda {
                params_types,
                return_type,
            })) => (params_types, return_type, false),
            Type::TypeVar(key) if self.type_inf_ctx.make_ty_var_error(key) => {
                // Infer more types to collect more errors
                for arg in args {
                    self.infer(*arg);
                }
                return on_expr_ty;
            }
            _ => {
                for arg in args {
                    self.infer(*arg);
                }
                self.add_calling_non_callable_err(&on_expr_ty, self.get_expr_span(on), parens_span);
                return self.type_inf_ctx.new_never_ty_var();
            }
        };

        if params_types.len() == args.len() {
            for i in 0..args.len() {
                let arg_ty = self.infer(args[i]);
                if let Err(err) = self.type_inf_ctx.unify(&params_types[i], &arg_ty) {
                    self.add_incorrect_fn_args_err(
                        &params_types[i],
                        &arg_ty,
                        self.get_expr_span(args[i]),
                        i,
                        on,
                        is_fn,
                    );
                }
            }
        } else {
            // Infer more types to collect more errors
            for i in 0..args.len() {
                let arg_ty = self.infer(args[i]);
                if i < params_types.len() {
                    if let Err(err) = self.type_inf_ctx.unify(&params_types[i], &arg_ty) {
                        self.add_incorrect_fn_args_err(
                            &params_types[i],
                            &arg_ty,
                            self.get_expr_span(args[i]),
                            i,
                            on,
                            is_fn,
                        );
                    }
                }
            }

            self.add_incorrect_fn_args_len_err(parens_span, on, true);
        }

        *return_type
    }

    fn infer_idx_expr(
        &mut self,
        IdxExpr {
            on,
            idx,
            brackets_span,
        }: &IdxExpr,
    ) -> Type {
        let on = *on;
        let brackets_span = *brackets_span;

        let on_expr_ty = self.infer(on);
        let on_expr_ty = self.type_inf_ctx.apply(&on_expr_ty);

        let (underlying_ty, is_array) = match on_expr_ty {
            Type::Concrete(ConcreteType::Composite(CompositeType::Array {
                underlying_typ,
                size: _,
            })) => (*underlying_typ, true),
            Type::Concrete(ConcreteType::Composite(CompositeType::Slice(underlying_ty))) => {
                (*underlying_ty, false)
            }
            Type::TypeVar(key) if self.type_inf_ctx.make_ty_var_error(key) => (on_expr_ty, true),
            _ => {
                self.add_indexing_non_indexable_err(&on_expr_ty, on, brackets_span);
                (self.type_inf_ctx.new_never_ty_var(), true)
            }
        };

        let idx_ty = self.infer(*idx);

        // TODO: Support ranges indexing
        if let Err(err) = self.type_inf_ctx.unify(&Type::u(), &idx_ty) {
            self.add_type_mismatch_err(&Type::u(), &idx_ty, self.get_expr_span(*idx));
        }

        underlying_ty
    }

    fn infer_array_elements(&mut self, elements: &ThinVec<ExprKey>) -> Type {
        if elements.is_empty() {
            let unknown_ty = self.type_inf_ctx.new_ty_var();
            return Type::array(unknown_ty, 0);
        }

        let first_ty = self.infer(elements[0]);

        for &elem in &elements[1..] {
            let elem_ty = self.infer(elem);
            if let Err(_) = self.type_inf_ctx.unify(&first_ty, &elem_ty) {
                self.add_array_element_type_mismatch_err(
                    &first_ty,
                    &elem_ty,
                    self.get_expr_span(elements[0]),
                    self.get_expr_span(elem),
                );
            }
        }

        Type::array(first_ty, elements.len() as u32)
    }

    fn infer_tuple_idx_expr(&mut self, TupleIdxExpr { on, idx, idx_span }: &TupleIdxExpr) -> Type {
        let on = *on;
        let idx = *idx as usize;

        let on_expr_ty = self.infer(on);
        let on_expr_ty = self.type_inf_ctx.apply(&on_expr_ty);

        match on_expr_ty {
            Type::Concrete(ConcreteType::Composite(CompositeType::Tuple { types })) => {
                if idx < types.len() {
                    types[idx].clone()
                } else {
                    self.add_out_of_bounds_tuple_idx_err(idx, types.len(), *idx_span);
                    self.type_inf_ctx.new_never_ty_var()
                }
            }
            _ => {
                self.add_indexing_non_tuple_err(&on_expr_ty, on, *idx_span);
                self.type_inf_ctx.new_never_ty_var()
            }
        }
    }

    fn infer_fields_struct_expr(
        &mut self,
        FieldsStructExpr {
            path_key,
            fields: fields_exprs,
        }: &FieldsStructExpr,
        expr_key: ExprKey,
    ) -> Type {
        let struct_key = self.ast.state.field_structs_paths_exprs[*path_key];

        let mut struct_fields = self.typed_ast.fields_structs[&struct_key].fields.clone();

        let mut used_fields = HashMap::with_capacity(struct_fields.len());

        for (field_id_expr, field_expr_key) in fields_exprs {
            let field_expr_ty = self.infer(*field_expr_key);

            if let Some(used_span) = used_fields.get(&field_id_expr.id) {
                self.add_field_is_used_more_than_once_err(
                    struct_key,
                    field_id_expr.id,
                    *used_span,
                    field_id_expr.span,
                );
            } else if let Some(FieldInfo { typ: field_ty, idx }) =
                struct_fields.get(&field_id_expr.id)
            {
                if let Err(err) = self.type_inf_ctx.unify(&field_ty, &field_expr_ty) {
                    self.add_field_type_mismatch_err(
                        &field_ty,
                        &field_expr_ty,
                        struct_key,
                        *idx,
                        field_id_expr.span,
                        self.get_expr_span(*field_expr_key),
                    );
                }

                self.check_field_is_accessible_in_current_file(
                    struct_key,
                    *idx,
                    field_id_expr.span,
                );

                used_fields.insert(
                    field_id_expr.id,
                    field_id_expr
                        .span
                        .merged_with(&self.get_expr_span(*field_expr_key)),
                );

                struct_fields.remove(&field_id_expr.id);
            } else {
                self.add_unknown_field_in_struct_expr_err(
                    struct_key,
                    field_id_expr.id,
                    field_id_expr.span,
                );
            }
        }

        if !struct_fields.is_empty() {
            self.add_missing_fields_in_struct_expr_err(
                struct_key,
                struct_fields.iter().map(|(id, _)| *id).collect(),
                self.get_expr_span(expr_key),
            );
        }

        Type::fields_struct(struct_key)
    }

    fn check_field_is_accessible_in_current_file(
        &mut self,
        struct_key: FieldsStructKey,
        field_idx: u32,
        field_id_expr_span: Span,
    ) {
        let struct_file_key = self.ast.fields_structs[struct_key].info.file_key;
        let struct_pkg_key = self.files_to_pkgs[struct_file_key];
        let current_file_pkg_key = self.files_to_pkgs[self.current_file_key];

        let vis = self.ast.fields_structs[struct_key].fields[field_idx as usize].vis;

        if matches!(vis, VisModifier::Private) && struct_file_key != self.current_file_key
            || matches!(vis, VisModifier::Default) && struct_pkg_key != current_file_pkg_key
        {
            self.add_filed_is_inaccessable_err(struct_key, field_idx, field_id_expr_span);
        }
    }

    pub(crate) fn infer_if_expr(
        &mut self,
        IfExpr {
            if_: (if_keyword_span, if_cond_expr_key, if_scope_key),
            else_ifs,
            else_,
        }: &IfExpr,
    ) -> Type {
        let if_cond_ty = self.infer(*if_cond_expr_key);

        if let Err(err) = self.type_inf_ctx.unify(&Type::boolean(), &if_cond_ty) {
            self.add_branch_stm_condition_type_mismatch_err(
                &if_cond_ty,
                "لو",
                *if_keyword_span,
                *if_cond_expr_key,
            );
        }

        let if_ty = self.infer_scope(*if_scope_key);

        for (else_if_keyword_span, else_if_cond_expr_key, else_if_scope_key) in else_ifs {
            let else_if_cond_ty = self.infer(*else_if_cond_expr_key);

            if let Err(err) = self.type_inf_ctx.unify(&Type::boolean(), &else_if_cond_ty) {
                self.add_branch_stm_condition_type_mismatch_err(
                    &else_if_cond_ty,
                    "وإلا لو",
                    *else_if_keyword_span,
                    *else_if_cond_expr_key,
                );
            }

            let else_if_ty = self.infer_scope(*else_if_scope_key);

            if let Err(err) = self.type_inf_ctx.unify(&if_ty, &else_if_ty) {
                self.add_type_mismatch_in_if_branches_err(
                    &if_ty,
                    &else_if_ty,
                    *if_scope_key,
                    *else_if_scope_key,
                    *if_keyword_span,
                    *else_if_keyword_span,
                );
            }
        }

        if let Some((else_keyword_span, else_scope_key)) = else_ {
            let else_ty = self.infer_scope(*else_scope_key);

            if let Err(err) = self.type_inf_ctx.unify(&if_ty, &else_ty) {
                self.add_type_mismatch_in_if_branches_err(
                    &if_ty,
                    &else_ty,
                    *if_scope_key,
                    *else_scope_key,
                    *if_keyword_span,
                    *else_keyword_span,
                );
            }
        } else if let Err(err) = self.type_inf_ctx.unify(&Type::unit(), &if_ty) {
            self.add_missing_else_branch_err(&if_ty, *if_keyword_span, *if_scope_key);
        }

        if_ty
    }

    fn infer_field_expr(&mut self, FieldExpr { on, name }: &FieldExpr) -> Type {
        let on = *on;

        let on_expr_ty = self.infer(on);
        let on_expr_ty = self.type_inf_ctx.apply(&on_expr_ty);

        // TODO: Support methods and the length method on slices
        match on_expr_ty {
            Type::Concrete(ConcreteType::FieldsStruct(struct_key)) => {
                let struct_fields = &self.typed_ast.fields_structs[&struct_key].fields;
                if let Some(FieldInfo { typ, idx }) = struct_fields.get(&name.id) {
                    let ty = typ.clone();
                    self.check_field_is_accessible_in_current_file(struct_key, *idx, name.span);
                    ty
                } else {
                    self.add_unknown_field_in_struct_expr_err(struct_key, name.id, name.span);
                    self.type_inf_ctx.new_never_ty_var()
                }
            }
            _ => {
                self.add_type_doesnt_have_fields_err(&on_expr_ty, on, *name);
                self.type_inf_ctx.new_never_ty_var()
            }
        }
    }

    fn infer_return_expr(
        &mut self,
        ReturnExpr {
            return_scope,
            return_keyword_span,
            expr,
        }: &ReturnExpr,
    ) -> Type {
        let (found_return_ty, span) = expr.map_or_else(
            || (Type::unit(), *return_keyword_span),
            |expr_key| {
                let span = self.get_expr_span(expr_key);
                if self.current_lambda_scope_key.is_some()
                    && self.current_lambda_first_implicit_return_ty_span.is_none()
                {
                    self.current_lambda_first_implicit_return_ty_span = Some(span);
                }
                (self.infer(expr_key), span)
            },
        );

        if let Err(err) = self
            .type_inf_ctx
            .unify(&self.current_scope_expected_return_ty, &found_return_ty)
        {
            if let Some(lambda_scope_key) = self.current_lambda_scope_key {
                self.add_type_mismatch_in_lambda_return_ty_err(
                    lambda_scope_key,
                    &self.current_scope_expected_return_ty.clone(),
                    &found_return_ty,
                    span,
                );
            } else {
                let _fn = &self.ast.fns[self.current_fn_key];

                self.add_type_mismatch_in_fn_return_ty_err(
                    self.current_fn_key,
                    &self.current_scope_expected_return_ty.clone(),
                    &found_return_ty,
                    span,
                );
            }
        }

        self.type_inf_ctx.new_never_ty_var()
    }

    fn infer_lambda_expr(&mut self, LambdaExpr { params, body }: &LambdaExpr) -> Type {
        let lambda_scope_key = *body;
        let curly_braces_span = self.ast.scopes[lambda_scope_key].span;

        self.typed_ast.lambdas_params.insert(
            lambda_scope_key,
            LambdaParams {
                bindings: HashMap::new(),
            },
        );

        let mut params_tys = ThinVec::with_capacity(params.len());

        for Binding { kind, typ } in params {
            let binding_ty = if let Some(type_expr_key) = typ {
                self.analyze_type_expr(*type_expr_key)
            } else {
                self.type_inf_ctx.new_ty_var()
            };

            self.set_bindnig_ty_for_lambda(lambda_scope_key, &kind, &binding_ty);

            params_tys.push(binding_ty);
        }

        let outer_scope_expected_return_ty = self.current_scope_expected_return_ty.clone();
        let outer_lambda_first_return_ty_span = self.current_lambda_first_implicit_return_ty_span;
        let outer_scope_key = self.current_lambda_scope_key;

        self.current_scope_expected_return_ty = self.type_inf_ctx.new_ty_var();
        self.current_lambda_first_implicit_return_ty_span = None;
        self.current_lambda_scope_key = Some(lambda_scope_key);

        let last_expr_return_ty = self.infer_scope(lambda_scope_key);

        let expected_lambda_return_ty = self.current_scope_expected_return_ty.clone();

        if let Err(err) = self
            .type_inf_ctx
            .unify(&expected_lambda_return_ty, &last_expr_return_ty)
        {
            let span = if let Some(return_expr_key) = self.ast.scopes[lambda_scope_key].return_expr
            {
                self.get_expr_span(return_expr_key)
            } else {
                curly_braces_span
            };
            self.add_type_mismatch_in_lambda_return_ty_err(
                lambda_scope_key,
                &expected_lambda_return_ty,
                &last_expr_return_ty,
                span,
            );
        }

        self.current_scope_expected_return_ty = outer_scope_expected_return_ty;
        self.current_lambda_first_implicit_return_ty_span = outer_lambda_first_return_ty_span;
        self.current_lambda_scope_key = outer_scope_key;

        Type::lambda(params_tys, expected_lambda_return_ty)
    }

    fn set_bindnig_ty_for_lambda(
        &mut self,
        lambda_scope_key: ScopeKey,
        kind: &BindingKind,
        ty: &Type,
    ) {
        match kind {
            BindingKind::Id(id) => {
                self.typed_ast
                    .lambdas_params
                    .get_mut(&lambda_scope_key)
                    .unwrap()
                    .bindings
                    .insert(id.id, ty.clone());
            }
            BindingKind::MutId { id, .. } => {
                self.typed_ast
                    .lambdas_params
                    .get_mut(&lambda_scope_key)
                    .unwrap()
                    .bindings
                    .insert(id.id, ty.clone());
            }
            BindingKind::Tuple(kinds, span) => {
                if let Type::Concrete(ConcreteType::Composite(CompositeType::Tuple { types })) = ty
                {
                    if kinds.len() == types.len() {
                        for i in 0..kinds.len() {
                            let kind = &kinds[i];
                            let ty = &types[i];
                            self.set_bindnig_ty_for_lambda(lambda_scope_key, kind, ty);
                        }
                    } else {
                        let found_ty = self.destructed_tuple_to_ty_with_unknown_for_lambda(
                            lambda_scope_key,
                            &kinds,
                        );
                        self.add_type_mismatch_err(ty, &found_ty, *span);
                    }
                } else {
                    let found_ty = self
                        .destructed_tuple_to_ty_with_unknown_for_lambda(lambda_scope_key, &kinds);
                    if let Err(err) = self.type_inf_ctx.unify(ty, &found_ty) {
                        self.add_type_mismatch_err(&ty, &found_ty, *span);
                    }
                }
            }
        }
    }

    fn destructed_tuple_to_ty_with_unknown_for_lambda(
        &mut self,
        lambda_scope_key: ScopeKey,
        kinds: &[BindingKind],
    ) -> Type {
        let mut tuple_types = ThinVec::with_capacity(kinds.len());
        for i in 0..kinds.len() {
            let kind = &kinds[i];
            let ty = self.type_inf_ctx.new_ty_var();
            self.set_bindnig_ty_for_lambda(lambda_scope_key, kind, &ty);
            tuple_types.push(ty);
        }

        Type::tuple(tuple_types)
    }

    fn infer_unary_op_expr(&mut self, UnaryOpExpr { op, op_span, expr }: &UnaryOpExpr) -> Type {
        let inner = self.infer(*expr);

        match op {
            UnaryOp::Minus => {
                if let Err(err) = self
                    .type_inf_ctx
                    .constrain_type_var(&inner, NumberConstraints::Signed)
                {
                    self.add_type_mismatch_in_op_err(&Type::i4(), &inner, *expr, *op_span);
                    Type::i4()
                } else {
                    inner
                }
            }
            UnaryOp::LNot => {
                self.unify_with_int_num(&Type::boolean(), *expr, &op_span);
                Type::boolean()
            }
            UnaryOp::BNot => {
                if self.unify_with_int_num(&inner, *expr, &op_span) {
                    inner
                } else {
                    Type::i4()
                }
            }
            UnaryOp::Deref => {
                let found_ty = self.type_inf_ctx.apply(&inner);
                match found_ty {
                    Type::Concrete(ConcreteType::Composite(CompositeType::Ptr(underlying_ty)))
                    | Type::Concrete(ConcreteType::Composite(CompositeType::PtrMut(
                        underlying_ty,
                    ))) => *underlying_ty,
                    Type::TypeVar(key) if self.type_inf_ctx.make_ty_var_error(key) => found_ty,
                    _ => {
                        self.add_cannot_deref_type(&found_ty, *expr, *op_span);
                        return self.type_inf_ctx.new_never_ty_var();
                    }
                }
            }
            UnaryOp::Borrow => Type::ptr(inner),
            UnaryOp::BorrowMut => Type::ptr_mut(inner),
        }
    }

    fn infer_bin_op_expr(
        &mut self,
        BinaryOpExpr {
            op,
            op_span_cursor,
            left,
            right,
        }: &BinaryOpExpr,
    ) -> Type {
        let left_ty = self.infer(*left);

        let op_span = get_bin_op_span(*op, *op_span_cursor);

        match op {
            BinOp::LOr | BinOp::LAnd => {
                self.unify_with_check(&Type::boolean(), &left_ty, *left, &op_span);
                let right_ty = self.infer(*right);
                self.unify_with_check(&Type::boolean(), &right_ty, *right, &op_span);
                Type::boolean()
            }
            BinOp::GE | BinOp::GT | BinOp::LE | BinOp::LT => {
                if self.unify_with_num(&left_ty, *left, &op_span) {
                    let right_ty = self.infer(*right);
                    self.unify_with_check(&left_ty, &right_ty, *right, &op_span);
                } else {
                    let right_ty = self.infer(*right);
                    self.unify_with_num(&right_ty, *right, &op_span);
                }
                Type::boolean()
            }
            BinOp::EqualEqual | BinOp::NotEqual => {
                let right_ty = self.infer(*right);
                self.unify_with_check(&left_ty, &right_ty, *right, &op_span);
                Type::boolean()
            }
            BinOp::Assign => {
                let right_ty = self.infer(*right);
                self.unify_with_check(&left_ty, &right_ty, *right, &op_span);
                Type::unit()
            }
            BinOp::OpenOpenRange
            | BinOp::CloseOpenRange
            | BinOp::OpenCloseRange
            | BinOp::CloseCloseRange => todo!(), // TODO
            BinOp::BOr | BinOp::Xor | BinOp::BAnd | BinOp::Shr | BinOp::Shl => {
                if self.unify_with_int_num(&left_ty, *left, &op_span) {
                    let right_ty = self.infer(*right);
                    self.unify_with_check(&left_ty, &right_ty, *right, &op_span);
                } else {
                    let right_ty = self.infer(*right);
                    self.unify_with_int_num(&right_ty, *right, &op_span);
                }
                left_ty
            }
            BinOp::Plus | BinOp::Minus | BinOp::Times | BinOp::Div | BinOp::Mod => {
                if self.unify_with_num(&left_ty, *left, &op_span) {
                    let right_ty = self.infer(*right);
                    self.unify_with_check(&left_ty, &right_ty, *right, &op_span);
                } else {
                    let right_ty = self.infer(*right);
                    self.unify_with_num(&right_ty, *right, &op_span);
                }
                left_ty
            }
            BinOp::BOrAssign
            | BinOp::XorAssign
            | BinOp::BAndAssign
            | BinOp::ShrAssign
            | BinOp::ShlAssign => {
                if self.unify_with_int_num(&left_ty, *left, &op_span) {
                    let right_ty = self.infer(*right);
                    self.unify_with_check(&left_ty, &right_ty, *right, &op_span);
                } else {
                    let right_ty = self.infer(*right);
                    self.unify_with_int_num(&right_ty, *right, &op_span);
                }
                Type::unit()
            }
            BinOp::PlusAssign
            | BinOp::MinusAssign
            | BinOp::TimesAssign
            | BinOp::DivAssign
            | BinOp::ModAssign => {
                if self.unify_with_num(&left_ty, *left, &op_span) {
                    let right_ty = self.infer(*right);
                    self.unify_with_check(&left_ty, &right_ty, *right, &op_span);
                } else {
                    let right_ty = self.infer(*right);
                    self.unify_with_num(&right_ty, *right, &op_span);
                }
                Type::unit()
            }
        }
    }

    fn unify_with_int_num(&mut self, found_ty: &Type, expr_key: ExprKey, op_span: &Span) -> bool {
        if let Err(err) = self
            .type_inf_ctx
            .constrain_type_var(&found_ty, NumberConstraints::Int)
        {
            self.add_type_mismatch_in_op_err(&Type::i4(), &found_ty, expr_key, *op_span);
            false
        } else {
            true
        }
    }

    fn unify_with_num(&mut self, found_ty: &Type, expr_key: ExprKey, op_span: &Span) -> bool {
        if let Err(err) = self
            .type_inf_ctx
            .constrain_type_var(&found_ty, NumberConstraints::Any)
        {
            self.add_type_mismatch_in_op_err(&Type::i4(), &found_ty, expr_key, *op_span);
            false
        } else {
            true
        }
    }

    fn unify_with_check(
        &mut self,
        expected_ty: &Type,
        found_ty: &Type,
        expr_key: ExprKey,
        op_span: &Span,
    ) -> bool {
        if let Err(err) = self.type_inf_ctx.unify(expected_ty, found_ty) {
            self.add_type_mismatch_in_op_err(expected_ty, &found_ty, expr_key, *op_span);
            false
        } else {
            true
        }
    }
}
