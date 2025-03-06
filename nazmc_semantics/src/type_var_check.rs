use crate::{
    type_infer::{NumberConstraints, PrimitiveType, TypeVarSubstitution},
    *,
};

macro_rules! check_int_bounds {
    ($self: ident, $lit_span: ident, $n: ident, $typ: ty, $type_name: expr) => {
        if $n > <$typ>::MAX as u64 {
            $self.add_num_lit_exceeds_its_limits(
                $lit_span,
                $type_name,
                &<$typ>::MIN.to_string(),
                &<$typ>::MAX.to_string(),
            );
        }
    };
}

macro_rules! check_signed_int_bounds {
    ($self: ident, $lit_span: ident, $n: ident, $typ: ty, $type_name: expr) => {
        if $n > <$typ>::MAX as u64 + 1 {
            $self.add_num_lit_exceeds_its_limits(
                $lit_span,
                $type_name,
                &<$typ>::MIN.to_string(),
                &<$typ>::MAX.to_string(),
            );
        }
    };
}

macro_rules! num_lit_expr_kind {
    ($num_expr: expr) => {
        ExprKind::Literal(LiteralExpr::Num($num_expr))
    };
}

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn ty_var_check(&mut self, base_ty: &Type, span: Span, is_expr: bool) -> Type {
        let applied_ty = self.type_inf_ctx.apply(base_ty);
        self.ty_check(
            base_ty,
            &applied_ty,
            span,
            self.unknown_type_errors.len(),
            is_expr,
        );
        applied_ty
    }

    pub(crate) fn ty_check(
        &mut self,
        base_ty: &Type,
        applied_ty: &Type,
        span: Span,
        possible_new_err_msg_idx: usize,
        is_expr: bool,
    ) {
        match applied_ty {
            Type::TypeVar(key) => match &self.type_inf_ctx.ty_vars[*key] {
                TypeVarSubstitution::Never => {}
                TypeVarSubstitution::Any
                | TypeVarSubstitution::Error
                | TypeVarSubstitution::ConstrainedNumber(
                    NumberConstraints::Any | NumberConstraints::Signed,
                ) => {
                    if let Some(&err_msg_idx) = self.unknown_ty_vars.get(key) {
                        if self.unknown_type_errors[err_msg_idx].2.is_none() && is_expr {
                            self.unknown_type_errors[err_msg_idx].2 = Some(span)
                        }
                    } else {
                        let mut err_msg_idx = self.unknown_type_errors.len();
                        if err_msg_idx == possible_new_err_msg_idx {
                            self.unknown_type_errors.push((base_ty.clone(), span, None));
                        } else {
                            // May be the same type have multiple unknown type variables
                            // So the first one will push the error message to unknown_type_errors
                            // But the others need to share the same error message
                            // So it will be provied by possible_new_err_msg_idx
                            // And here it will be greater than unknown_type_errors.len()
                            err_msg_idx = possible_new_err_msg_idx;
                            if self.unknown_type_errors[err_msg_idx].2.is_none() && is_expr {
                                self.unknown_type_errors[err_msg_idx].2 = Some(span)
                            }
                        }
                        self.unknown_ty_vars.insert(*key, err_msg_idx);
                    }
                }
                TypeVarSubstitution::ConstrainedNumber(
                    NumberConstraints::Int | NumberConstraints::SignedInt,
                ) => {
                    self.type_inf_ctx.ty_vars[*key] = TypeVarSubstitution::Determined(Type::i4());
                }
                TypeVarSubstitution::ConstrainedNumber(NumberConstraints::Float) => {
                    self.type_inf_ctx.ty_vars[*key] = TypeVarSubstitution::Determined(Type::f4());
                }
                TypeVarSubstitution::Determined(determined) => self.ty_check(
                    base_ty,
                    &determined.clone(),
                    span,
                    possible_new_err_msg_idx,
                    is_expr,
                ),
            },
            Type::Concrete(con_ty) => {
                self.concrete_ty_check(base_ty, con_ty, span, possible_new_err_msg_idx, is_expr)
            }
        }
    }

    pub(crate) fn concrete_ty_check(
        &mut self,
        base_ty: &Type,
        con_ty: &ConcreteType,
        span: Span,
        possible_new_err_msg_idx: usize,
        is_expr: bool,
    ) {
        match con_ty {
            ConcreteType::Composite(comp_ty) => match comp_ty {
                CompositeType::Slice(underlying_typ)
                | CompositeType::Ptr(underlying_typ)
                | CompositeType::Ref(underlying_typ)
                | CompositeType::PtrMut(underlying_typ)
                | CompositeType::RefMut(underlying_typ)
                | CompositeType::Array {
                    underlying_typ,
                    size: _,
                } => self.ty_check(
                    base_ty,
                    underlying_typ,
                    span,
                    possible_new_err_msg_idx,
                    is_expr,
                ),
                CompositeType::Tuple { types } => types.iter().for_each(|ty| {
                    self.ty_check(base_ty, ty, span, possible_new_err_msg_idx, is_expr)
                }),
                CompositeType::Lambda {
                    params_types,
                    return_type,
                }
                | CompositeType::FnPtr {
                    params_types,
                    return_type,
                } => {
                    params_types.iter().for_each(|ty| {
                        self.ty_check(base_ty, ty, span, possible_new_err_msg_idx, is_expr)
                    });

                    self.ty_check(
                        base_ty,
                        return_type,
                        span,
                        possible_new_err_msg_idx,
                        is_expr,
                    );
                }
            },
            _ => {}
        }
    }

    pub(crate) fn check_scope_ty_vars(&mut self, scope_key: ScopeKey) {
        let stms = std::mem::take(&mut self.ast.scopes[scope_key].stms);
        for stm in &stms {
            match stm {
                Stm::Let(let_stm_key) => {
                    if self.ast.lets[*let_stm_key].binding.typ.is_none() {
                        self.ty_var_check(
                            &self.typed_ast.lets[let_stm_key].ty.clone(),
                            self.ast.lets[*let_stm_key].binding.kind.get_span(),
                            false,
                        );
                    }
                    if let Some(expr_key) = self.ast.lets[*let_stm_key].assign {
                        self.check_expr_ty_vars(expr_key);
                    }
                }
                Stm::While(while_stm) => {
                    self.check_expr_ty_vars(while_stm.cond_expr_key);
                    self.check_scope_ty_vars(while_stm.scope_key);
                }
                Stm::Expr(expr_key) => {
                    self.check_expr_ty_vars(*expr_key);
                }
            }
        }

        self.ast.scopes[scope_key].stms = stms;
    }

    pub(crate) fn check_expr_ty_vars(&mut self, expr_key: ExprKey) {
        let kind = std::mem::take(&mut self.ast.exprs[expr_key].kind);

        let kind = match kind {
            ExprKind::Call(call_expr) => {
                self.check_expr_ty_vars(call_expr.on);
                call_expr
                    .args
                    .iter()
                    .for_each(|&expr_key| self.check_expr_ty_vars(expr_key));

                ExprKind::Call(call_expr)
            }
            ExprKind::Field(field_expr) => {
                self.check_expr_ty_vars(field_expr.on);
                ExprKind::Field(field_expr)
            }
            ExprKind::Idx(idx_expr) => {
                self.check_expr_ty_vars(idx_expr.on);
                self.check_expr_ty_vars(idx_expr.idx);
                ExprKind::Idx(idx_expr)
            }
            ExprKind::TupleIdx(tuple_idx_expr) => {
                self.check_expr_ty_vars(tuple_idx_expr.on);
                ExprKind::TupleIdx(tuple_idx_expr)
            }
            ExprKind::Tuple(exprs) => {
                exprs
                    .iter()
                    .for_each(|&expr_key| self.check_expr_ty_vars(expr_key));

                ExprKind::Tuple(exprs)
            }
            ExprKind::ArrayElements(elements) => {
                elements
                    .iter()
                    .for_each(|&expr_key| self.check_expr_ty_vars(expr_key));

                ExprKind::ArrayElements(elements)
            }
            ExprKind::If(if_expr) => {
                self.check_expr_ty_vars(if_expr.if_.1);
                self.check_scope_ty_vars(if_expr.if_.2);

                for else_if in &if_expr.else_ifs {
                    self.check_expr_ty_vars(else_if.1);
                    self.check_scope_ty_vars(else_if.2);
                }

                if let Some(else_) = if_expr.else_ {
                    self.check_scope_ty_vars(else_.1);
                }

                ExprKind::If(if_expr)
            }
            ExprKind::Lambda(lambda_expr) => {
                let Some(
                    ref ty @ Type::Concrete(ConcreteType::Composite(CompositeType::Lambda {
                        ref params_types,
                        ref return_type,
                    })),
                ) = self.typed_ast.exprs.remove(&expr_key)
                else {
                    unreachable!()
                };

                for (i, param_type) in params_types.iter().enumerate() {
                    let binding = &lambda_expr.params[i];
                    if binding.typ.is_none() {
                        self.ty_var_check(param_type, binding.kind.get_span(), false);
                    }
                }

                self.ty_var_check(&return_type, self.get_expr_span(expr_key), false);

                self.check_scope_ty_vars(lambda_expr.body);

                // Early return as it will recheck the lambda params types and will set is_expr to true
                // Which will make the second span of the unknown type error message
                // will make it larger than the first span

                let ty = self.type_inf_ctx.apply(&ty);
                self.typed_ast.exprs.insert(expr_key, ty);

                self.ast.exprs[expr_key].kind = ExprKind::Lambda(lambda_expr);

                return;
            }
            ExprKind::UnaryOp(unary_op_expr) => {
                if let (ExprKind::Literal(LiteralExpr::Num(num)), UnaryOp::Minus) =
                    (&self.ast.exprs[unary_op_expr.expr].kind, &unary_op_expr.op)
                {
                    match num {
                        NumKind::F4(f) => num_lit_expr_kind!(NumKind::F4(-f)),
                        NumKind::F8(f) => num_lit_expr_kind!(NumKind::F8(-f)),
                        NumKind::I(n) => num_lit_expr_kind!(NumKind::I(-n)),
                        NumKind::I1(n) => num_lit_expr_kind!(NumKind::I1(-n)),
                        NumKind::I2(n) => num_lit_expr_kind!(NumKind::I2(-n)),
                        NumKind::I4(n) => num_lit_expr_kind!(NumKind::I4(-n)),
                        NumKind::I8(n) => num_lit_expr_kind!(NumKind::I8(-n)),
                        NumKind::UnspecifiedFloat(f) => {
                            self.check_unspecified_float(
                                expr_key,
                                self.get_expr_span(unary_op_expr.expr), // Show the literal span
                                -f,
                            );

                            self.typed_ast.exprs.insert(
                                unary_op_expr.expr,
                                self.typed_ast.exprs[&expr_key].clone(),
                            ); // Set the literal type to the whole expression type

                            return;
                        }
                        NumKind::UnspecifiedInt(n) => {
                            let lit_span = self.get_expr_span(expr_key); // The span includes the minus sign

                            self.check_signed_unspecified_int(expr_key, lit_span, *n);

                            self.typed_ast.exprs.insert(
                                unary_op_expr.expr,
                                self.typed_ast.exprs[&expr_key].clone(),
                            ); // Set the literal type to the whole expression type

                            return;
                        }
                        _ => {
                            self.check_expr_ty_vars(unary_op_expr.expr);
                            ExprKind::UnaryOp(unary_op_expr)
                        }
                    }
                } else {
                    self.check_expr_ty_vars(unary_op_expr.expr);
                    ExprKind::UnaryOp(unary_op_expr)
                }
            }
            ExprKind::BinaryOp(binary_op_expr) => {
                self.check_expr_ty_vars(binary_op_expr.left);
                self.check_expr_ty_vars(binary_op_expr.right);
                ExprKind::BinaryOp(binary_op_expr)
            }
            ExprKind::Return(return_expr) => {
                if let Some(expr_key) = return_expr.expr {
                    self.check_expr_ty_vars(expr_key);
                }

                let ty = &self.typed_ast.exprs[&expr_key];
                let ty = self.type_inf_ctx.apply(&ty);
                self.typed_ast.exprs.insert(expr_key, ty);

                self.ast.exprs[expr_key].kind = ExprKind::Return(return_expr);

                // Eearly return as this should has never type but it might be changed to error
                // So the error must be reported where it is and not here
                return;
            }
            kind @ (ExprKind::Break(_) | ExprKind::Continue(_)) => {
                let ty = &self.typed_ast.exprs[&expr_key];
                let ty = self.type_inf_ctx.apply(&ty);
                self.typed_ast.exprs.insert(expr_key, ty);

                self.ast.exprs[expr_key].kind = kind;

                // Eearly return as this should has never type but it might be changed to error
                // So the error must be reported where it is and not here
                return;
            }
            ExprKind::Literal(LiteralExpr::Num(NumKind::UnspecifiedInt(n))) => {
                self.check_unspecified_int(expr_key, self.get_expr_span(expr_key), n);
                return;
            }
            ExprKind::Literal(LiteralExpr::Num(NumKind::UnspecifiedFloat(f))) => {
                self.check_unspecified_float(expr_key, self.get_expr_span(expr_key), f);
                return;
            }
            ExprKind::TupleStruct(_) => todo!(),
            ExprKind::ArrayRepeated(_) => todo!(),
            ExprKind::On => todo!(),
            kind @ _ => kind,
        };

        self.ast.exprs[expr_key].kind = kind;

        let span = self.get_expr_span(expr_key);

        let Some(ty) = self.typed_ast.exprs.remove(&expr_key) else {
            unreachable!();
        };

        let ty = self.ty_var_check(&ty, span, true);

        self.typed_ast.exprs.insert(expr_key, ty);
    }

    fn check_signed_unspecified_int(&mut self, expr_key: ExprKey, lit_span: Span, n: u64) {
        let Some(ty) = self.typed_ast.exprs.remove(&expr_key) else {
            unreachable!();
        };

        let span = self.get_expr_span(expr_key);

        let ty = self.ty_var_check(&ty, span, true);

        let kind = if let Type::Concrete(ConcreteType::Primitive(prim_ty)) = &ty {
            match prim_ty {
                PrimitiveType::I => {
                    check_signed_int_bounds!(self, lit_span, n, isize, "ص");
                    let n = if n == isize::MAX as u64 + 1 {
                        isize::MIN
                    } else {
                        -(n as isize)
                    };
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I(n)))
                }
                PrimitiveType::I1 => {
                    check_signed_int_bounds!(self, lit_span, n, i8, "ص1");
                    let n = if n == i8::MAX as u64 + 1 {
                        i8::MIN
                    } else {
                        -(n as i8)
                    };
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I1(n)))
                }
                PrimitiveType::I2 => {
                    check_signed_int_bounds!(self, lit_span, n, i16, "ص2");
                    let n = if n == i16::MAX as u64 + 1 {
                        i16::MIN
                    } else {
                        -(n as i16)
                    };
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I2(n)))
                }
                PrimitiveType::I4 => {
                    check_signed_int_bounds!(self, lit_span, n, i32, "ص4");
                    let n = if n == i32::MAX as u64 + 1 {
                        i32::MIN
                    } else {
                        -(n as i32)
                    };
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I4(n)))
                }
                PrimitiveType::I8 => {
                    check_signed_int_bounds!(self, lit_span, n, i64, "ص8");
                    let n = if n == i64::MAX as u64 + 1 {
                        i64::MIN
                    } else {
                        -(n as i64)
                    };
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I8(n)))
                }
                _ => ExprKind::Literal(LiteralExpr::Num(NumKind::I8(n as i64))),
            }
        } else {
            ExprKind::Literal(LiteralExpr::Num(NumKind::I8(n as i64)))
        };

        self.ast.exprs[expr_key].kind = kind;

        self.typed_ast.exprs.insert(expr_key, ty);
    }

    fn check_unspecified_int(&mut self, expr_key: ExprKey, lit_span: Span, n: u64) {
        let Some(ty) = self.typed_ast.exprs.remove(&expr_key) else {
            unreachable!();
        };

        let span = self.get_expr_span(expr_key);

        let ty = self.ty_var_check(&ty, span, true);

        let kind = if let Type::Concrete(ConcreteType::Primitive(prim_ty)) = &ty {
            match prim_ty {
                PrimitiveType::I => {
                    check_int_bounds!(self, lit_span, n, isize, "ص");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I(n as isize)))
                }
                PrimitiveType::I1 => {
                    check_int_bounds!(self, lit_span, n, i8, "ص1");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I1(n as i8)))
                }
                PrimitiveType::I2 => {
                    check_int_bounds!(self, lit_span, n, i16, "ص2");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I2(n as i16)))
                }
                PrimitiveType::I4 => {
                    check_int_bounds!(self, lit_span, n, i32, "ص4");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I4(n as i32)))
                }
                PrimitiveType::I8 => {
                    check_int_bounds!(self, lit_span, n, i64, "ص8");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::I8(n as i64)))
                }
                PrimitiveType::U => {
                    check_int_bounds!(self, lit_span, n, usize, "ط");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::U(n as usize)))
                }
                PrimitiveType::U1 => {
                    check_int_bounds!(self, lit_span, n, u8, "ط1");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::U1(n as u8)))
                }
                PrimitiveType::U2 => {
                    check_int_bounds!(self, lit_span, n, u16, "ط2");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::U2(n as u16)))
                }
                PrimitiveType::U4 => {
                    check_int_bounds!(self, lit_span, n, u32, "ط4");
                    ExprKind::Literal(LiteralExpr::Num(NumKind::U4(n as u32)))
                }
                _ => ExprKind::Literal(LiteralExpr::Num(NumKind::U8(n))),
            }
        } else {
            ExprKind::Literal(LiteralExpr::Num(NumKind::U8(n)))
        };

        self.ast.exprs[expr_key].kind = kind;

        self.typed_ast.exprs.insert(expr_key, ty);
    }

    fn check_unspecified_float(&mut self, expr_key: ExprKey, lit_span: Span, f: f64) {
        let Some(ty) = self.typed_ast.exprs.remove(&expr_key) else {
            unreachable!();
        };

        let ty = self.ty_var_check(&ty, lit_span, true);

        let kind = if let Type::Concrete(ConcreteType::Primitive(prim_ty)) = &ty {
            if let PrimitiveType::F4 = prim_ty {
                if f.abs() < f32::MIN_POSITIVE as f64 || f.abs() > f32::MAX as f64 {
                    self.add_num_lit_exceeds_its_limits(
                        lit_span,
                        "ع4",
                        "1.17549435^^-38",
                        "3.40282347^^+38",
                    );
                }
                ExprKind::Literal(LiteralExpr::Num(NumKind::F4(f as f32)))
            } else {
                ExprKind::Literal(LiteralExpr::Num(NumKind::F8(f)))
            }
        } else {
            ExprKind::Literal(LiteralExpr::Num(NumKind::F8(f)))
        };

        self.ast.exprs[expr_key].kind = kind;

        self.typed_ast.exprs.insert(expr_key, ty);
    }
}
