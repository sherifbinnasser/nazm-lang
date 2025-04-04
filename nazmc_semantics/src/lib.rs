mod consts;
mod errors;
mod exprs;
mod nir_builder;
mod type_infer;
mod type_var_check;
mod typed_ast;
mod types;

use nazmc_data_pool::{
    typed_index_collections::{TiSlice, TiVec},
    FileKey, IdKey, PkgKey,
};

pub(crate) use nazmc_ast::*;
use nazmc_diagnostics::{
    eprint_diagnostics,
    file_info::FileInfo,
    span::{Span, SpanCursor},
    CodeWindow, Diagnostic,
};
use nazmc_nir::{Arg, Struct, CFG, NIR};
use nir_builder::{CFGBuilder, NIRBuilder};
use std::{collections::HashMap, process::exit};
use thin_vec::ThinVec;
use type_infer::{CompositeType, ConcreteType, Type, TypeInferenceCtx, TypeVarKey};
use typed_ast::{LetStm, TypedAST};

#[derive(Clone, Copy, Default, PartialEq, Eq)]
enum CycleDetected {
    #[default]
    None,
    Const(ConstKey),
    TupleStruct(TupleStructKey),
    FieldsStruct(FieldsStructKey),
}

#[derive(Default)]
struct SemanticsStack {
    consts: HashMap<ConstKey, ()>,
    tuple_structs: HashMap<TupleStructKey, ()>,
    fields_structs: HashMap<FieldsStructKey, ()>,
    is_cycle_detected: CycleDetected,
}

#[derive(Default)]
pub struct SemanticsAnalyzer<'a> {
    files_infos: &'a TiSlice<FileKey, FileInfo>,
    files_to_pkgs: &'a TiSlice<FileKey, PkgKey>,
    id_pool: &'a TiSlice<IdKey, String>,
    pkgs_names: &'a TiSlice<PkgKey, &'a ThinVec<IdKey>>,
    ast: AST<Resolved>,
    typed_ast: TypedAST,
    semantics_stack: SemanticsStack,
    diagnostics: Vec<Diagnostic<'a>>,
    cycle_stack: Vec<Diagnostic<'a>>,
    current_file_key: FileKey,
    current_fn_key: FnKey,
    type_inf_ctx: TypeInferenceCtx,
    nir_builder: NIRBuilder<'a>,
    cfg_builder: CFGBuilder,
    /// For fns and lambdas only
    current_scope_expected_return_ty: Type,
    current_lambda_first_implicit_return_ty_span: Option<Span>,
    current_lambda_scope_key: Option<ScopeKey>,
    /// Map unkown type varialbes to its error message,
    /// where multiple type variable could share the same unknown type
    unknown_ty_vars: HashMap<TypeVarKey, usize>,
    /// The error messages of unknown types,
    /// it will have a span and an optional span where that type is first used
    unknown_type_errors: ThinVec<(Type, Span, Option<Span>)>,
}

impl<'a> SemanticsAnalyzer<'a> {
    pub fn new(
        files_infos: &'a TiSlice<FileKey, FileInfo>,
        files_to_pkgs: &'a TiSlice<FileKey, PkgKey>,
        id_pool: &'a TiSlice<IdKey, String>,
        pkgs_names: &'a TiSlice<PkgKey, &'a ThinVec<IdKey>>,
        ast: nazmc_ast::AST<Resolved>,
    ) -> Self {
        Self {
            files_infos,
            files_to_pkgs,
            id_pool,
            pkgs_names,
            typed_ast: TypedAST {
                consts: HashMap::with_capacity(ast.consts.len()),
                statics: HashMap::with_capacity(ast.statics.len()),
                tuple_structs: HashMap::with_capacity(ast.tuple_structs.len()),
                fields_structs: HashMap::with_capacity(ast.fields_structs.len()),
                fns_signatures: HashMap::with_capacity(ast.fns.len()),
                lets: HashMap::with_capacity(ast.lets.len()),
                exprs: HashMap::with_capacity(ast.exprs.len()),
                lambdas_params: HashMap::new(),
            },
            nir_builder: NIRBuilder {
                nir: NIR {
                    structs: TiVec::with_capacity(ast.fields_structs.len()),
                    statics: TiVec::with_capacity(ast.statics.len()),
                    fns: TiVec::with_capacity(ast.fns.len()),
                    ..Default::default()
                },
                exprs_types: TiVec::with_capacity(ast.exprs.len()),
                bindings_types: HashMap::with_capacity(ast.lets.len()),
                ..Default::default()
            },
            ast,
            ..Default::default()
        }
    }

    pub fn analyze(mut self) -> NIR<'a> {
        // for type_expr_key in self.ast.types_exprs.all.keys() {
        //     self.analyze_type_expr(type_expr_key);
        // }

        for struct_key in self.ast.fields_structs.keys() {
            self.analyze_fields_struct(struct_key);
        }

        self.analyze_fn_signatures();

        self.analyze_fn_bodies();

        if !self.diagnostics.is_empty() {
            eprint_diagnostics(self.diagnostics);
            exit(1);
        }

        self.ast
            .exprs
            .iter_enumerated()
            .for_each(|(expr_key, _expr)| {
                let Type::Concrete(con_ty) = &self.typed_ast.exprs[&expr_key] else {
                    unreachable!()
                };
                let type_key = self.nir_builder.get_unique_type(con_ty);
                self.nir_builder.exprs_types.push(type_key);
            });

        self.typed_ast
            .lets
            .iter()
            .for_each(|(let_stm_key, let_binding)| {
                let Type::Concrete(let_ty) = &let_binding.ty else {
                    unreachable!()
                };
                self.nir_builder.get_unique_type(let_ty);
                let_binding
                    .bindings
                    .iter()
                    .for_each(|(binding_id_key, binding_ty)| {
                        let Type::Concrete(binding_ty) = &binding_ty else {
                            unreachable!()
                        };
                        let binding_ty_key = self.nir_builder.get_unique_type(binding_ty);
                        self.nir_builder
                            .bindings_types
                            .insert((*let_stm_key, *binding_id_key), binding_ty_key);
                    });
            });

        self.ast
            .fields_structs
            .iter_enumerated()
            .for_each(|(struct_key, _struct)| {
                let fields_types = self.typed_ast.fields_structs[&struct_key]
                    .fields
                    .iter()
                    .map(|(field_id, field_info)| {
                        let Type::Concrete(field_typ) = &field_info.typ else {
                            unreachable!()
                        };
                        let field_typ = self.nir_builder.get_unique_type(field_typ);
                        (*field_id, field_typ)
                    })
                    .collect();
                let fields_order = _struct
                    .fields
                    .iter()
                    .map(|field_info| field_info.id.id)
                    .collect();
                self.nir_builder.nir.structs.push(Struct {
                    info: _struct.info,
                    fields_types,
                    fields_order,
                });
            });

        let fns_signatures = self
            .typed_ast
            .fns_signatures
            .iter()
            .map(|(fn_key, ty)| {
                let Type::Concrete(con_ty) = ty else {
                    unreachable!()
                };
                (*fn_key, self.nir_builder.get_unique_type(con_ty))
            })
            .collect::<HashMap<_, _>>();

        let all_types = std::mem::take(&mut self.nir_builder.all_types);
        let all_tuple_types = std::mem::take(&mut self.nir_builder.all_tuple_types);
        let all_array_types = std::mem::take(&mut self.nir_builder.all_array_types);
        let all_lambda_types = std::mem::take(&mut self.nir_builder.all_lambda_types);
        let all_fn_ptr_types = std::mem::take(&mut self.nir_builder.all_fn_ptr_types);

        self.nir_builder.nir.types = all_types.build();
        self.nir_builder.nir.array_types = all_array_types.build();
        self.nir_builder.nir.tuple_types = all_tuple_types.build();
        self.nir_builder.nir.lambda_types = all_lambda_types.build();
        self.nir_builder.nir.fn_ptr_types = all_fn_ptr_types.build();

        let fns = std::mem::take(&mut self.ast.fns);
        self.cfg_builder.build(); // To init first cfg start and end blocks

        fns.iter_enumerated().for_each(|(fn_key, _fn)| {
            self.current_fn_key = fn_key;

            let fn_ptr_type = fns_signatures[&fn_key];

            let nazmc_nir::Type::FnPtr(fn_ptr_type_key) = &self.nir_builder.nir.types[fn_ptr_type]
            else {
                unreachable!()
            };

            let nazmc_nir::FnPtrType {
                params_types,
                return_type,
            } = &self.nir_builder.nir.fn_ptr_types[*fn_ptr_type_key];

            let return_type = *return_type;

            let mut args = TiVec::with_capacity(params_types.len());

            for i in 0..params_types.len() {
                args.push(Arg {
                    id_key: _fn.params[i].0.id,
                    id_span: _fn.params[i].0.span,
                    typ: params_types[i],
                    is_mut: false,
                })
            }

            self.lower_fn_scope(_fn.scope_key);

            self.nir_builder.nir.fns.push(nazmc_nir::Fn {
                info: _fn.info,
                args,
                fn_ptr_type,
                return_type,
                cfg: CFG::default(),
            });

            let cfg = self.cfg_builder.build();
            self.nir_builder.nir.fns.last_mut().unwrap().cfg = cfg;
        });

        if !self.diagnostics.is_empty() {
            eprint_diagnostics(self.diagnostics);
            exit(1);
        }

        self.nir_builder.nir

        // TODO
    }

    fn analyze_fn_signatures(&mut self) {
        let fns = std::mem::take(&mut self.ast.fns);

        for (fn_key, _fn) in fns.iter_enumerated() {
            let params = _fn
                .params
                .iter()
                .map(|(_, type_expr_key)| self.analyze_type_expr(*type_expr_key))
                .collect::<ThinVec<_>>();

            let return_type = _fn.return_type.map_or_else(
                || Type::unit(),
                |type_expr_key| self.analyze_type_expr(type_expr_key),
            );

            self.typed_ast
                .fns_signatures
                .insert(fn_key, Type::fn_ptr(params, return_type));
        }

        self.ast.fns = fns;
    }

    fn analyze_fn_bodies(&mut self) {
        self.current_lambda_scope_key = None;
        self.current_lambda_first_implicit_return_ty_span = None;

        for fn_key in self.ast.fns.keys() {
            self.analyze_fn_body(fn_key);
        }
    }

    fn analyze_fn_body(&mut self, fn_key: FnKey) {
        self.current_fn_key = fn_key;
        self.current_file_key = self.ast.fns[fn_key].info.file_key;

        self.current_scope_expected_return_ty =
            if let Type::Concrete(ConcreteType::Composite(CompositeType::FnPtr {
                params_types: _,
                return_type,
            })) = &self.typed_ast.fns_signatures[&fn_key]
            {
                return_type.as_ref().clone()
            } else {
                unreachable!()
            };

        let found_return_ty = self.infer_scope(self.ast.fns[fn_key].scope_key);

        if let Err(err) = self
            .type_inf_ctx
            .unify(&self.current_scope_expected_return_ty, &found_return_ty)
        {
            // Show error if there is a return expr
            // and let control flow analysis detect explicit returns
            if let Some(return_expr_key) =
                self.ast.scopes[self.ast.fns[fn_key].scope_key].return_expr
            {
                let span = self.get_expr_span(return_expr_key);

                self.add_type_mismatch_in_fn_return_ty_err(
                    fn_key,
                    &self.current_scope_expected_return_ty.clone(),
                    &found_return_ty,
                    span,
                );
            }
        }

        self.check_scope_ty_vars(self.ast.fns[fn_key].scope_key);

        for (unknown_ty, span, first_used_span) in &self.unknown_type_errors {
            println!("Span: {:?}", span);
            let mut code_window =
                CodeWindow::new(&self.files_infos[self.current_file_key], span.start);

            if let Some(span) = first_used_span {
                code_window.mark_secondary(*span, vec!["يجب معرفة النوع هنا".into()]);
            }

            code_window.mark_error(*span, vec!["لا يمكن تحديد النوع هنا ضمنياً".into()]);

            let diagnostic = Diagnostic::error(
                format!("يجب تحديد النوع `{}` بشكل خارجي", self.fmt_ty(unknown_ty)),
                vec![code_window],
            );
            self.diagnostics.push(diagnostic);
        }

        self.unknown_ty_vars.clear();
        self.unknown_type_errors.clear();
        // self.s.ty_vars.clear();
    }

    fn infer_scope(&mut self, scope_key: ScopeKey) -> Type {
        self.analyze_scope(scope_key);

        let return_ty = self.ast.scopes[scope_key]
            .return_expr
            .map_or_else(|| Type::unit(), |expr_key| self.infer(expr_key));

        return_ty
    }

    fn analyze_scope(&mut self, scope_key: ScopeKey) {
        let stms = std::mem::take(&mut self.ast.scopes[scope_key].stms);

        for stm in &stms {
            match stm {
                Stm::Let(let_stm_key) => {
                    let let_stm_type =
                        if let Some(type_expr_key) = self.ast.lets[*let_stm_key].binding.typ {
                            self.analyze_type_expr(type_expr_key)
                        } else {
                            self.type_inf_ctx.new_ty_var()
                        };

                    if let Some(expr_key) = self.ast.lets[*let_stm_key].assign {
                        let expr_ty = self.infer(expr_key);

                        if let Err(err) = self.type_inf_ctx.unify(&let_stm_type, &expr_ty) {
                            let expected_type_expr_key =
                                self.ast.lets[*let_stm_key].binding.typ.unwrap();
                            self.add_type_mismatch_in_let_stm_err(
                                &let_stm_type,
                                &expr_ty,
                                expected_type_expr_key,
                                expr_key,
                            );
                        }
                    }

                    self.typed_ast.lets.insert(
                        *let_stm_key,
                        LetStm {
                            bindings: HashMap::new(),
                            ty: let_stm_type.clone(),
                        },
                    );

                    self.set_bindnig_ty(
                        *let_stm_key,
                        &self.ast.lets[*let_stm_key].binding.kind.clone(),
                        &let_stm_type,
                    );
                }
                Stm::While(while_stm) => {
                    let WhileStm {
                        while_keyword_span,
                        cond_expr_key: while_cond_expr_key,
                        scope_key: while_scope_key,
                    } = **while_stm;

                    let while_cond_ty = self.infer(while_cond_expr_key);

                    if let Err(err) = self.type_inf_ctx.unify(&Type::boolean(), &while_cond_ty) {
                        self.add_branch_stm_condition_type_mismatch_err(
                            &while_cond_ty,
                            "طالما",
                            while_keyword_span,
                            while_cond_expr_key,
                        );
                    }

                    let while_scope_ty = self.infer_scope(while_scope_key);

                    if let Err(err) = self.type_inf_ctx.unify(&Type::unit(), &while_scope_ty) {
                        self.add_while_stm_should_return_unit_err(
                            &while_scope_ty,
                            while_keyword_span,
                            while_scope_key,
                        );
                    }
                }
                Stm::Expr(expr_key) => {
                    self.infer(*expr_key);
                }
            }
        }

        self.ast.scopes[scope_key].stms = stms;
    }

    fn set_bindnig_ty(&mut self, let_stm_key: LetStmKey, kind: &BindingKind, ty: &Type) {
        match kind {
            BindingKind::Id(id) => {
                self.typed_ast
                    .lets
                    .get_mut(&let_stm_key)
                    .unwrap()
                    .bindings
                    .insert(id.id, ty.clone());
            }
            BindingKind::MutId { id, .. } => {
                self.typed_ast
                    .lets
                    .get_mut(&let_stm_key)
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
                            self.set_bindnig_ty(let_stm_key, kind, ty);
                        }
                    } else {
                        let found_ty =
                            self.destructed_tuple_to_ty_with_unknown(let_stm_key, &kinds);
                        self.add_type_mismatch_err(ty, &found_ty, *span);
                    }
                } else {
                    let found_ty = self.destructed_tuple_to_ty_with_unknown(let_stm_key, &kinds);
                    if let Err(err) = self.type_inf_ctx.unify(ty, &found_ty) {
                        self.add_type_mismatch_err(&ty, &found_ty, *span);
                    }
                }
            }
        }
    }

    fn destructed_tuple_to_ty_with_unknown(
        &mut self,
        let_stm_key: LetStmKey,
        kinds: &[BindingKind],
    ) -> Type {
        let mut tuple_types = ThinVec::with_capacity(kinds.len());
        for i in 0..kinds.len() {
            let kind = &kinds[i];
            let ty = self.type_inf_ctx.new_ty_var();
            self.set_bindnig_ty(let_stm_key, kind, &ty);
            tuple_types.push(ty);
        }

        Type::tuple(tuple_types)
    }
}

fn get_bin_op_span(op: BinOp, op_span_cursor: SpanCursor) -> Span {
    let op_len = match op {
        BinOp::OpenOpenRange => 4,
        BinOp::CloseOpenRange | BinOp::OpenCloseRange | BinOp::ShlAssign | BinOp::ShrAssign => 3,

        BinOp::LOr
        | BinOp::LAnd
        | BinOp::EqualEqual
        | BinOp::NotEqual
        | BinOp::GE
        | BinOp::LE
        | BinOp::Shr
        | BinOp::Shl
        | BinOp::PlusAssign
        | BinOp::MinusAssign
        | BinOp::TimesAssign
        | BinOp::DivAssign
        | BinOp::ModAssign
        | BinOp::BAndAssign
        | BinOp::BOrAssign
        | BinOp::XorAssign
        | BinOp::CloseCloseRange => 2,

        BinOp::GT
        | BinOp::LT
        | BinOp::BOr
        | BinOp::Xor
        | BinOp::BAnd
        | BinOp::Plus
        | BinOp::Minus
        | BinOp::Times
        | BinOp::Div
        | BinOp::Mod
        | BinOp::Assign => 1,
    };

    Span {
        start: op_span_cursor,
        end: SpanCursor {
            line: op_span_cursor.line,
            col: op_span_cursor.col + op_len,
        },
    }
}
