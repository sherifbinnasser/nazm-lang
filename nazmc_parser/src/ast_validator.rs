use crate::*;
use nazmc_ast::{ASTId, ExprKind, ReturnExpr, ScopeKey};
use nazmc_data_pool::{typed_index_collections::TiSlice, IdKey};
use nazmc_diagnostics::eprint_diagnostics;
use std::{collections::HashMap, process::exit};
use thin_vec::ThinVec;

type ItemsConflictsInPkgs = HashMap<PkgKey, HashMap<IdKey, HashMap<FileKey, Vec<Span>>>>;
//                               ^^^^^^          ^^^^^          ^^^^^           ^^^^ spans found in each file
//                               |               |              |
//                               |               |              file key: All conflicts in a file that belong to the same pkg
//                               |               The conflicting name in a pkg
//                               pkg key (The pkg that has conflicts)

type StructFieldsConflictsInFiles = HashMap<(IdKey, FileKey, Span), Vec<Span>>;
//                                           ^^^^^  ^^^^^^^  ^^^^       ^^^^ spans found
//                                           |      |        |
//                                           |      |        The struct id span
//                                           |      The file key
//                                           The conflicting field name in a file

type FnParamsConflictsInFiles = HashMap<(IdKey, FileKey, Span), Vec<Span>>;
//                                       ^^^^^  ^^^^^^^  ^^^^       ^^^^ spans found
//                                       |      |        |
//                                       |      |        The fn id span
//                                       |      The file key
//                                       The conflicting param name in a file

type BindingsConflicts = HashMap<(FileKey, Span), (IdKey, Span)>;
//                                ^^^^^^   ^^^^    ^^^^   ^^^^ The second span found
//                                |        |       |
//                                |        |       The conflicting param name in a file
//                                |        The first span found
//                                The file key
//

type ItemsAndImportsConflictsInFiles = HashMap<(IdKey, FileKey), Vec<Span>>;
//                                              ^^^^^  ^^^^^^^       ^^^^ spans found
//                                              |      |
//                                              |      The file key
//                                              The conflicting name in a file

type ReturnOutsideFnBody = Vec<(FileKey, Span)>;
type BreakOutsideLoopBody = Vec<(FileKey, Span)>;
type ContinueOutsideLoopBody = Vec<(FileKey, Span)>;

pub struct ASTValidator<'a> {
    pub(crate) pkg_key: PkgKey,
    pub(crate) file_key: FileKey,
    pub(crate) ast: &'a mut nazmc_ast::AST<nazmc_ast::Unresolved>,
    pub(crate) items_names_in_current_file: HashMap<IdKey, Span>,
    pub(crate) params_names_in_current_fn: HashMap<IdKey, Span>,
    pub(crate) items_conflicts_in_pkgs: ItemsConflictsInPkgs,
    pub(crate) struct_fields_conflicts_in_files: StructFieldsConflictsInFiles,
    pub(crate) fn_params_conflicts_in_files: FnParamsConflictsInFiles,
    pub(crate) bindings_conflicts: BindingsConflicts,
    pub(crate) items_and_imports_conflicts_in_files: ItemsAndImportsConflictsInFiles,
    pub(crate) return_outside_fn_body_errs: ReturnOutsideFnBody,
    pub(crate) break_outside_loop_body_errs: BreakOutsideLoopBody,
    pub(crate) continue_outside_loop_body_errs: ContinueOutsideLoopBody,
    pub(crate) current_fn_scope_key: Option<ScopeKey>,
    pub(crate) current_lambda_scope_key: Option<ScopeKey>,
    pub(crate) current_loop_scope_key: Option<ScopeKey>,
    pub(crate) current_scope_key: ScopeKey,
}

impl<'a> ASTValidator<'a> {
    pub fn new(ast: &'a mut nazmc_ast::AST<nazmc_ast::Unresolved>) -> Self {
        Self {
            ast,
            pkg_key: Default::default(),
            file_key: Default::default(),
            items_names_in_current_file: Default::default(),
            params_names_in_current_fn: Default::default(),
            items_conflicts_in_pkgs: Default::default(),
            struct_fields_conflicts_in_files: Default::default(),
            fn_params_conflicts_in_files: Default::default(),
            bindings_conflicts: Default::default(),
            items_and_imports_conflicts_in_files: Default::default(),
            return_outside_fn_body_errs: Default::default(),
            break_outside_loop_body_errs: Default::default(),
            continue_outside_loop_body_errs: Default::default(),
            current_fn_scope_key: Default::default(),
            current_lambda_scope_key: Default::default(),
            current_loop_scope_key: Default::default(),
            current_scope_key: Default::default(),
        }
    }

    pub(crate) fn lower_file(&mut self, file: File) {
        self.items_names_in_current_file.clear();
        self.lower_file_items(file.content.items);
    }

    #[inline]
    fn new_pkg_path(&self) -> nazmc_ast::PkgPath {
        nazmc_ast::PkgPath {
            pkg_key: self.pkg_key,
            file_key: self.file_key,
            ids: ThinVec::new(),
            spans: ThinVec::new(),
        }
    }

    #[inline]
    fn lower_import_stm(&mut self, import_stm: ImportStm) {
        let mut pkg_path = self.new_pkg_path();

        let mut import_all = false;

        let top_pkg_span = if let Ok(s) = import_stm.sec {
            let span = if let Some(id) = import_stm.top {
                pkg_path.ids.push(id.data.val);
                pkg_path.spans.push(id.span);
                None
            } else {
                Some(s.double_colons.span)
            };

            match s.seg.unwrap() {
                syntax::PathSegInImportStm::Id(id) => {
                    pkg_path.ids.push(id.data.val);
                    pkg_path.spans.push(id.span);
                }
                syntax::PathSegInImportStm::Star(_) => import_all = true,
            }
            span
        } else {
            unreachable!()
        };

        for s in import_stm.segs {
            match s.seg.unwrap() {
                syntax::PathSegInImportStm::Id(id) => {
                    pkg_path.ids.push(id.data.val);
                    pkg_path.spans.push(id.span);
                }
                syntax::PathSegInImportStm::Star(_) => import_all = true,
            }
        }

        if import_all {
            self.ast.state.paths.star_imports[self.file_key].push(nazmc_ast::StarImportStm {
                top_pkg_span,
                pkg_path,
            });
        } else {
            let item_id = pkg_path.ids.pop().unwrap();
            let item_span = pkg_path.spans.pop().unwrap();
            let item = nazmc_ast::ASTId {
                span: item_span,
                id: item_id,
            };

            let alias = if let Some(alias) = import_stm.alias {
                let id = alias.id.unwrap();
                nazmc_ast::ASTId {
                    span: id.span,
                    id: id.data.val,
                }
            } else {
                nazmc_ast::ASTId {
                    span: item_span,
                    id: item_id,
                }
            };

            if let Some(span_of_item_with_same_name) =
                self.items_names_in_current_file.get(&alias.id)
            {
                self.items_and_imports_conflicts_in_files
                    .entry((alias.id, self.file_key))
                    .or_insert_with(|| vec![*span_of_item_with_same_name])
                    .push(alias.span);
            }

            self.ast.state.paths.imports[self.file_key].push(nazmc_ast::ImportStm {
                item_path: nazmc_ast::ItemPath {
                    pkg_path,
                    item,
                    top_pkg_span,
                },
                alias,
            });
        }
    }

    #[inline]
    fn lower_file_items(&mut self, file_items: Vec<ParseResult<FileItem>>) {
        let mut imports_stms = vec![];
        for file_item in file_items {
            let (item, vis) = match file_item.unwrap() {
                syntax::FileItem::ImportStm(import_stm) => {
                    imports_stms.push(import_stm);
                    continue;
                }
                syntax::FileItem::WithVisModifier(item_with_vis) => {
                    let Ok(item) = item_with_vis.item else {
                        unreachable!()
                    };

                    (
                        item,
                        match item_with_vis.visibility.data {
                            syntax::VisModifierToken::Public => nazmc_ast::VisModifier::Public,
                            syntax::VisModifierToken::Private => nazmc_ast::VisModifier::Private,
                        },
                    )
                }
                syntax::FileItem::WithoutModifier(item) => (item, nazmc_ast::VisModifier::Default),
            };

            match item {
                Item::Const(c) => {
                    let body = c.body.unwrap();
                    let name = body.id;
                    let id_key = name.data.val;
                    let id_span = name.span;

                    if self.check_if_name_conflicts(id_key, id_span) {
                        continue;
                    }

                    self.items_names_in_current_file.insert(id_key, id_span);

                    let info = nazmc_data_pool::ItemInfo {
                        file_key: self.file_key,
                        id_key,
                        id_span,
                    };

                    let typ = self.lower_type(body.typ.unwrap());

                    let expr_scope_key =
                        self.lower_staic_or_const_expr_to_scope(body.expr.unwrap());

                    let key = self.ast.consts.push_and_get_key(nazmc_ast::Const {
                        info,
                        typ,
                        expr_scope_key,
                    });

                    let item = nazmc_ast::Item::Const { vis, key };

                    self.ast.state.pkgs_to_items[self.pkg_key].insert(id_key, item);
                }
                Item::Static(s) => {
                    let body = s.body.unwrap();
                    let name = body.id;
                    let id_key = name.data.val;
                    let id_span = name.span;

                    if self.check_if_name_conflicts(id_key, id_span) {
                        continue;
                    }

                    self.items_names_in_current_file.insert(id_key, id_span);

                    let info = nazmc_data_pool::ItemInfo {
                        file_key: self.file_key,
                        id_key,
                        id_span,
                    };

                    let typ = self.lower_type(body.typ.unwrap());

                    let expr_scope_key =
                        self.lower_staic_or_const_expr_to_scope(body.expr.unwrap());

                    let key = self.ast.statics.push_and_get_key(nazmc_ast::Static {
                        info,
                        typ,
                        expr_scope_key,
                    });

                    let item = nazmc_ast::Item::Static { vis, key };

                    self.ast.state.pkgs_to_items[self.pkg_key].insert(id_key, item);
                }
                Item::Struct(s) => {
                    let name = s.name.unwrap();
                    let id_key = name.data.val;
                    let id_span = name.span;

                    if self.check_if_name_conflicts(id_key, id_span) {
                        continue;
                    }

                    self.items_names_in_current_file.insert(id_key, id_span);

                    let info = nazmc_data_pool::ItemInfo {
                        file_key: self.file_key,
                        id_key,
                        id_span,
                    };

                    let struct_fields = s.fields.unwrap();

                    let mut fields_map = HashMap::new();
                    let mut fields = ThinVec::new();

                    if let Some(PunctuatedStructField {
                        first_item,
                        rest_items,
                        trailing_comma: _,
                    }) = struct_fields.items
                    {
                        let (id, field_info) = self.lower_struct_field(first_item.unwrap());
                        fields_map.insert(id, field_info.id.span);
                        fields.push(field_info);

                        for r in rest_items {
                            let (id, field_info) = self.lower_struct_field(r.unwrap().item);

                            if let Some(span_of_field_with_same_id) = fields_map.get(&id) {
                                self.struct_fields_conflicts_in_files
                                    .entry((id, self.file_key, name.span))
                                    .or_insert_with(|| vec![*span_of_field_with_same_id])
                                    .push(field_info.id.span);
                            } else {
                                fields_map.insert(id, field_info.id.span);
                                fields.push(field_info);
                            }
                        }
                    }

                    let key = self
                        .ast
                        .structs
                        .push_and_get_key(nazmc_ast::Struct { info, fields });

                    let item = nazmc_ast::Item::Struct { vis, key };

                    self.ast.state.pkgs_to_items[self.pkg_key].insert(id_key, item);
                }
                Item::Fn(f) => {
                    let name = f.name.unwrap();
                    let id_key = name.data.val;
                    let id_span = name.span;

                    if self.check_if_name_conflicts(id_key, id_span) {
                        continue;
                    }

                    self.items_names_in_current_file.insert(id_key, id_span);

                    let info = nazmc_data_pool::ItemInfo {
                        file_key: self.file_key,
                        id_key,
                        id_span,
                    };

                    self.params_names_in_current_fn.clear();

                    let mut params = ThinVec::new();

                    if let Some(PunctuatedFnParam {
                        first_item,
                        rest_items,
                        trailing_comma: _,
                    }) = f.params_decl.unwrap().items
                    {
                        let first = self.lower_fn_param(first_item.unwrap());
                        self.params_names_in_current_fn
                            .insert(first.ast_id.id, first.ast_id.span);
                        params.push(first);

                        for r in rest_items {
                            let param = self.lower_fn_param(r.unwrap().item);

                            if let Some(span_of_param_with_same_name) =
                                self.params_names_in_current_fn.get(&param.ast_id.id)
                            {
                                self.fn_params_conflicts_in_files
                                    .entry((param.ast_id.id, self.file_key, name.span))
                                    .or_insert_with(|| vec![*span_of_param_with_same_name])
                                    .push(param.ast_id.span);
                            }

                            params.push(param);
                        }
                    }

                    let return_type = f
                        .return_type
                        .map(|colon_with_type| self.lower_type(colon_with_type.typ.unwrap()));

                    self.current_fn_scope_key = Some(ScopeKey::from(self.ast.scopes.len()));

                    let scope_key = self.lower_lambda_as_body(f.body.unwrap(), true);

                    self.current_fn_scope_key = None;

                    let key = self.ast.fns.push_and_get_key(nazmc_ast::Fn {
                        info,
                        params,
                        return_type,
                        scope_key,
                    });

                    let item = nazmc_ast::Item::Fn { vis, key };

                    self.ast.state.pkgs_to_items[self.pkg_key].insert(id_key, item);
                }
            }
        }

        for import_stm in imports_stms {
            self.lower_import_stm(import_stm);
        }
    }

    fn check_if_name_conflicts(&mut self, id: IdKey, id_span: Span) -> bool {
        let Some(item_with_same_id) = self.ast.state.pkgs_to_items[self.pkg_key].get(&id) else {
            return false;
        };

        self.items_conflicts_in_pkgs
            .entry(self.pkg_key)
            .or_default()
            .entry(id)
            .or_insert_with(|| {
                let first_occurrence_info = match *item_with_same_id {
                    nazmc_ast::Item::Struct { key, .. } => self.ast.structs[key].info,
                    nazmc_ast::Item::Const { key, .. } => self.ast.consts[key].info,
                    nazmc_ast::Item::Static { key, .. } => self.ast.statics[key].info,
                    nazmc_ast::Item::Fn { key, .. } => self.ast.fns[key].info,
                    nazmc_ast::Item::Pkg
                    | nazmc_ast::Item::LocalVar { .. }
                    | nazmc_ast::Item::FnParam { .. }
                    | nazmc_ast::Item::LambdaParam { .. } => {
                        unreachable!()
                    }
                };
                HashMap::from([(
                    first_occurrence_info.file_key,
                    vec![first_occurrence_info.id_span],
                )])
            })
            .entry(self.file_key)
            .or_default()
            .push(id_span);

        return true;
    }

    fn lower_struct_field(&mut self, field: StructField) -> (IdKey, nazmc_ast::FieldInfo) {
        let vis = match field.visibility {
            Some(Terminal {
                data: syntax::VisModifierToken::Public,
                ..
            }) => nazmc_ast::VisModifier::Public,
            Some(Terminal {
                data: syntax::VisModifierToken::Private,
                ..
            }) => nazmc_ast::VisModifier::Private,
            None => nazmc_ast::VisModifier::Default,
        };

        let typ = self.lower_type(field.typ.unwrap().typ.unwrap());

        (
            field.name.data.val,
            nazmc_ast::FieldInfo {
                vis,
                id: ASTId {
                    span: field.name.span,
                    id: field.name.data.val,
                },
                typ,
            },
        )
    }

    fn lower_fn_param(&mut self, param: FnParam) -> nazmc_ast::FnParam {
        let ast_id = nazmc_ast::ASTId {
            span: param.name.span,
            id: param.name.data.val,
        };

        let type_expr_key = self.lower_type(param.typ.unwrap().typ.unwrap());

        nazmc_ast::FnParam {
            ast_id,
            is_mut: param.mut_keyword.is_some(),
            type_expr_key,
        }
    }

    fn lower_type(&mut self, typ: Type) -> nazmc_ast::TypeExprKey {
        let typ_expr =
            match typ {
                Type::Path(simple_path) => {
                    let item_path = self.lower_simple_path(*simple_path);
                    let type_path_key = self.ast.types_exprs.paths.push_and_get_key(item_path);
                    nazmc_ast::TypeExpr::Path(type_path_key)
                }
                Type::Ptr(ptr_type) => {
                    let underlying_typ = self.lower_type(ptr_type.typ.unwrap());

                    let span = ptr_type.star.span;

                    if let Some(mut_) = ptr_type.mut_keyword {
                        let span = span.merged_with(&mut_.span);

                        let key = self.ast.types_exprs.ptrs_mut.push_and_get_key(
                            nazmc_ast::PtrMutTypeExpr {
                                underlying_typ,
                                file_key: self.file_key,
                                span,
                            },
                        );

                        nazmc_ast::TypeExpr::PtrMut(key)
                    } else {
                        let key =
                            self.ast
                                .types_exprs
                                .ptrs
                                .push_and_get_key(nazmc_ast::PtrTypeExpr {
                                    underlying_typ,
                                    file_key: self.file_key,
                                    span,
                                });

                        nazmc_ast::TypeExpr::Ptr(key)
                    }
                }
                Type::Slice(slice_type) => {
                    let underlying_typ = self.lower_type(slice_type.typ.unwrap());

                    let span = slice_type
                        .open_bracket
                        .span
                        .merged_with(&slice_type.close_bracket.unwrap().span);

                    if let Some(array_size) = slice_type.array_size {
                        let size_expr_scope_key =
                            self.lower_staic_or_const_expr_to_scope(array_size.expr.unwrap());

                        let key = self.ast.types_exprs.arrays.push_and_get_key(
                            nazmc_ast::ArrayTypeExpr {
                                underlying_typ,
                                size_expr_scope_key,
                                file_key: self.file_key,
                                span,
                            },
                        );

                        nazmc_ast::TypeExpr::Array(key)
                    } else {
                        let key = self.ast.types_exprs.slices.push_and_get_key(
                            nazmc_ast::SliceTypeExpr {
                                underlying_typ,
                                file_key: self.file_key,
                                span,
                            },
                        );

                        nazmc_ast::TypeExpr::Slice(key)
                    }
                }
                Type::Paren(paren_type) => {
                    let span = paren_type
                        .tuple
                        .open_delim
                        .span
                        .merged_with(&paren_type.tuple.close_delim.unwrap().span);

                    let mut types = ThinVec::new();

                    let mut trailing_comma_in_types = false;

                    if let Some(PunctuatedType {
                        first_item,
                        rest_items,
                        trailing_comma,
                    }) = paren_type.tuple.items
                    {
                        let first = self.lower_type(first_item.unwrap());
                        types.push(first);
                        for r in rest_items {
                            let r = self.lower_type(r.unwrap().item);
                            types.push(r);
                        }

                        trailing_comma_in_types = trailing_comma.is_some();
                    }

                    if let Some(lambda_type) = paren_type.lambda {
                        let return_type = self.lower_type(lambda_type.typ.unwrap());

                        let key = self.ast.types_exprs.lambdas.push_and_get_key(
                            nazmc_ast::LambdaTypeExpr {
                                params_types: types,
                                return_type,
                                file_key: self.file_key,
                                params_span: span,
                                arrow_span: lambda_type.r_arrow.span,
                            },
                        );

                        nazmc_ast::TypeExpr::Lambda(key)
                    } else {
                        if !trailing_comma_in_types && types.len() == 1 {
                            let key = self.ast.types_exprs.parens.push_and_get_key(
                                nazmc_ast::ParenTypeExpr {
                                    underlying_typ: types.pop().unwrap(),
                                    file_key: self.file_key,
                                    span,
                                },
                            );

                            nazmc_ast::TypeExpr::Paren(key)
                        } else {
                            let key = self.ast.types_exprs.tuples.push_and_get_key(
                                nazmc_ast::TupleTypeExpr {
                                    types,
                                    file_key: self.file_key,
                                    span,
                                },
                            );

                            nazmc_ast::TypeExpr::Tuple(key)
                        }
                    }
                }
            };

        self.ast.types_exprs.all.push_and_get_key(typ_expr)
    }

    fn lower_simple_path(&mut self, mut simple_path: SimplePath) -> nazmc_ast::ItemPath {
        let mut pkg_path = self.new_pkg_path();

        let item = if simple_path.inners.is_empty() {
            nazmc_ast::ASTId {
                span: simple_path.top.span,
                id: simple_path.top.data.val,
            }
        } else {
            let item = simple_path.inners.pop().unwrap().inner.unwrap();

            let item = nazmc_ast::ASTId {
                span: item.span,
                id: item.data.val,
            };

            pkg_path.ids.push(simple_path.top.data.val);
            pkg_path.spans.push(simple_path.top.span);

            for inner in simple_path.inners {
                let inner = inner.inner.unwrap();
                pkg_path.ids.push(inner.data.val);
                pkg_path.spans.push(inner.span);
            }

            item
        };

        nazmc_ast::ItemPath {
            pkg_path,
            item,
            top_pkg_span: simple_path.double_colons.map(|c| c.span),
        }
    }

    /// This has the same implementation of `lower_lambda_stms_and_return_expr` but with no stms
    fn lower_staic_or_const_expr_to_scope(&mut self, expr: Expr) -> nazmc_ast::ScopeKey {
        let scope = nazmc_ast::Scope::default();
        let last_scope_key = self.current_scope_key;
        self.current_scope_key = self.ast.scopes.push_and_get_key(scope);
        self.ast.state.scope_events.push(ThinVec::new());

        let expr_key = self.lower_expr(expr);
        let expr_span = self.ast.exprs[expr_key].span;
        self.ast.scopes[self.current_scope_key].return_expr = Some(expr_key);
        self.ast.scopes[self.current_scope_key].span = expr_span;

        let scope_key = self.current_scope_key;
        self.current_scope_key = last_scope_key;
        scope_key
    }

    #[inline]
    fn lower_lambda_as_body(
        &mut self,
        lambda: LambdaExpr,
        is_fn_scope: bool,
    ) -> nazmc_ast::ScopeKey {
        self.lower_lambda_stms_and_return_expr(
            lambda.stms,
            lambda.last_expr,
            lambda
                .open_curly
                .span
                .merged_with(&lambda.close_curly.unwrap().span),
            is_fn_scope,
        )
    }

    fn lower_lambda_stms_and_return_expr(
        &mut self,
        stms: Vec<ParseResult<Stm>>,
        return_expr: Option<Expr>,
        span: Span,
        is_fn_scope: bool,
    ) -> nazmc_ast::ScopeKey {
        let scope = nazmc_ast::Scope {
            span,
            ..Default::default()
        };
        let last_scope_key = self.current_scope_key;
        self.current_scope_key = self.ast.scopes.push_and_get_key(scope);
        self.ast.state.scope_events.push(ThinVec::new());

        for stm in stms {
            let stm = match stm.unwrap() {
                Stm::Semicolon(_) => continue,
                Stm::Let(let_stm) => {
                    let mut bound_names_map = HashMap::new();

                    let binding =
                        self.lower_binding(let_stm.binding.unwrap(), &mut bound_names_map);

                    let assign = let_stm.let_assign.map(|a| self.lower_expr(a.expr.unwrap()));

                    let let_stm = nazmc_ast::LetStm { binding, assign };

                    let let_stm_key = self.ast.lets.push_and_get_key(let_stm);

                    self.ast.state.bound_lets_names.push(bound_names_map);

                    self.ast.state.scope_events[self.current_scope_key]
                        .push(nazmc_ast::ScopeEvent::Let(let_stm_key));

                    nazmc_ast::Stm::Let(let_stm_key)
                }
                Stm::While(while_stm) => {
                    let cond_expr_key =
                        self.lower_expr(while_stm.conditional_block.condition.unwrap());

                    let outter_loop_scope_key = self.current_loop_scope_key;

                    self.current_loop_scope_key = Some(ScopeKey::from(self.ast.scopes.len()));

                    let scope_key = self
                        .lower_lambda_as_body(while_stm.conditional_block.block.unwrap(), false);

                    self.current_loop_scope_key = outter_loop_scope_key;

                    nazmc_ast::Stm::While(Box::new(nazmc_ast::WhileStm {
                        while_keyword_span: while_stm.while_keyword.span,
                        cond_expr_key,
                        scope_key,
                    }))
                }
                Stm::If(if_expr) => {
                    let span = get_if_expr_span(&if_expr);
                    let if_expr = Box::new(self.lower_if_expr(if_expr));
                    let expr = self.new_expr(span, nazmc_ast::ExprKind::If(if_expr));
                    nazmc_ast::Stm::Expr(expr)
                }
                Stm::When(_when_expr) => todo!(),
                Stm::Expr(stm) => nazmc_ast::Stm::Expr(self.lower_expr(stm.expr)),
            };
            self.ast.scopes[self.current_scope_key].stms.push(stm);
        }

        let return_expr = return_expr.map(|expr| self.lower_expr(expr));

        self.ast.scopes[self.current_scope_key].return_expr = return_expr;

        let scope_key = self.current_scope_key;

        self.current_scope_key = last_scope_key;

        if !is_fn_scope {
            self.ast.state.scope_events[self.current_scope_key]
                .push(nazmc_ast::ScopeEvent::Scope(scope_key));
        }

        scope_key
    }

    fn lower_binding(
        &mut self,
        binding: Binding,
        bound_names_map: &mut HashMap<IdKey, Span>,
    ) -> nazmc_ast::Binding {
        let kind = self.lower_binding_kind(binding.kind, bound_names_map);

        let typ = binding.typ.map(|t| self.lower_type(t.typ.unwrap()));

        nazmc_ast::Binding { kind, typ }
    }

    fn lower_binding_kind(
        &mut self,
        kind: BindingKind,
        bound_names_map: &mut HashMap<IdKey, Span>,
    ) -> nazmc_ast::BindingKind {
        match kind {
            BindingKind::Id(id_token) => {
                let id_key = id_token.data.val;
                let id_span = id_token.span;

                if let Some(first_span) = bound_names_map.get(&id_key) {
                    self.bindings_conflicts
                        .entry((self.file_key, *first_span))
                        .or_insert((id_key, id_span));
                } else {
                    bound_names_map.insert(id_key, id_span);
                }

                nazmc_ast::BindingKind::Id(nazmc_ast::ASTId {
                    span: id_span,
                    id: id_key,
                })
            }
            BindingKind::MutId(mut_id_binding) => {
                let id_token = mut_id_binding.id.unwrap();
                let id_key = id_token.data.val;
                let id_span = id_token.span;

                if let Some(first_span) = bound_names_map.get(&id_key) {
                    self.bindings_conflicts
                        .entry((self.file_key, *first_span))
                        .or_insert((id_key, id_span));
                } else {
                    bound_names_map.insert(id_key, id_span);
                };

                nazmc_ast::BindingKind::MutId {
                    id: nazmc_ast::ASTId {
                        span: id_span,
                        id: id_key,
                    },
                    mut_span: mut_id_binding.mut_keyword.span,
                }
            }
            BindingKind::Destructed(destructed_tuple) => {
                let span = destructed_tuple
                    .open_delim
                    .span
                    .merged_with(&destructed_tuple.close_delim.unwrap().span);

                let mut destructed_bindings = ThinVec::new();

                if let Some(PunctuatedBindingKind {
                    first_item,
                    rest_items,
                    trailing_comma,
                }) = destructed_tuple.items
                {
                    let first = self.lower_binding_kind(first_item.unwrap(), bound_names_map);

                    if trailing_comma.is_none() && rest_items.is_empty() {
                        return first;
                    }

                    destructed_bindings.push(first);

                    for r in rest_items {
                        let r = self.lower_binding_kind(r.unwrap().item, bound_names_map);
                        destructed_bindings.push(r);
                    }
                }
                nazmc_ast::BindingKind::Tuple(destructed_bindings, span)
            }
        }
    }

    fn new_expr(&mut self, span: Span, kind: ExprKind) -> nazmc_ast::ExprKey {
        let expr = nazmc_ast::Expr { span, kind };
        self.ast.exprs.push_and_get_key(expr)
    }

    #[inline]
    fn get_expr_span(&self, expr_key: nazmc_ast::ExprKey) -> Span {
        self.ast.exprs[expr_key].span
    }

    #[inline]
    fn get_expr_merged_span(
        &self,
        expr_key_1: nazmc_ast::ExprKey,
        expr_key_2: nazmc_ast::ExprKey,
    ) -> Span {
        self.get_expr_span(expr_key_1)
            .merged_with(&self.get_expr_span(expr_key_2))
    }

    fn lower_expr(&mut self, expr: Expr) -> nazmc_ast::ExprKey {
        let left = self.lower_primary_expr(*expr.left);
        let mut ops_stack = ThinVec::new();
        let mut expr_stack = vec![left]; // Stack to keep track of expressions

        // Shunting-yard algorithm
        for b in expr.bin {
            let right = self.lower_primary_expr(b.right.unwrap());
            let op = lower_bin_op(b.op.data);
            let op_span_cursor = b.op.span.start;

            // Pop operators from the stack while they have higher or equal precedence
            while let Some((last_op, _)) = ops_stack.last() {
                if get_precendence(&op) > get_precendence(last_op) {
                    break;
                }

                let (last_op, last_op_span_cursor) = ops_stack.pop().unwrap();
                let right_expr = expr_stack.pop().unwrap();
                let left_expr = expr_stack.pop().unwrap();

                // Combine left and right expressions using the last operator
                let combined_expr = self.new_expr(
                    self.get_expr_merged_span(left_expr, right_expr),
                    nazmc_ast::ExprKind::BinaryOp(Box::new(nazmc_ast::BinaryOpExpr {
                        op: last_op,
                        op_span_cursor: last_op_span_cursor,
                        left: left_expr,
                        right: right_expr,
                    })),
                );

                expr_stack.push(combined_expr);
            }

            // Push the current operator and the right-hand expression onto the stacks
            ops_stack.push((op, op_span_cursor));
            expr_stack.push(right);
        }

        // Apply remaining operators in the stack
        while let Some((last_op, last_op_span_cursor)) = ops_stack.pop() {
            let right_expr = expr_stack.pop().unwrap();
            let left_expr = expr_stack.pop().unwrap();

            // Combine left and right expressions using the remaining operators
            let combined_expr = self.new_expr(
                self.get_expr_merged_span(left_expr, right_expr),
                nazmc_ast::ExprKind::BinaryOp(Box::new(nazmc_ast::BinaryOpExpr {
                    op: last_op,
                    op_span_cursor: last_op_span_cursor,
                    left: left_expr,
                    right: right_expr,
                })),
            );

            expr_stack.push(combined_expr);
        }

        // Return the final expression
        expr_stack.pop().unwrap()
    }

    fn lower_primary_expr(&mut self, primary_expr: PrimaryExpr) -> nazmc_ast::ExprKey {
        let expr = match primary_expr.kind {
            PrimaryExprKind::Unary(unary_expr) => self.lower_unary_expr(*unary_expr),
            PrimaryExprKind::Atomic(atomic_expr) => self.lower_atomic_expr(atomic_expr),
        };

        let expr = self.lower_post_ops_exprs(expr, primary_expr.post_ops);

        let expr = self.lower_inner_access_expr(expr, primary_expr.inner_access);

        expr
    }

    #[inline]
    fn lower_inner_access_expr(
        &mut self,
        mut on: nazmc_ast::ExprKey,
        inner_access_exprs: Vec<InnerAccessExpr>,
    ) -> nazmc_ast::ExprKey {
        for inner_access_expr in inner_access_exprs {
            let field = inner_access_expr.field.unwrap();

            let expr = match field {
                InnerAccessField::Id(id) => {
                    let name = nazmc_ast::ASTId {
                        span: id.span,
                        id: id.data.val,
                    };

                    self.new_expr(
                        self.get_expr_span(on).merged_with(&name.span),
                        nazmc_ast::ExprKind::Field(Box::new(nazmc_ast::FieldExpr { on, name })),
                    )
                }
                InnerAccessField::TupleIdx(idx) => self.new_expr(
                    self.get_expr_span(on).merged_with(&idx.span),
                    nazmc_ast::ExprKind::TupleIdx(Box::new(nazmc_ast::TupleIdxExpr {
                        on,
                        idx: idx.data as u32,
                        idx_span: idx.span,
                    })),
                ),
            };

            on = self.lower_post_ops_exprs(expr, inner_access_expr.post_ops);
        }
        on
    }

    fn lower_post_ops_exprs(
        &mut self,
        mut on: nazmc_ast::ExprKey,
        ops: Vec<PostOpExpr>,
    ) -> nazmc_ast::ExprKey {
        for op in ops {
            on = match op {
                PostOpExpr::Invoke(paren_expr) => {
                    let parens_span = paren_expr
                        .open_delim
                        .span
                        .merged_with(&paren_expr.close_delim.unwrap().span);

                    let span = self.get_expr_span(on).merged_with(&parens_span);

                    let mut args = ThinVec::new();

                    if let Some(PunctuatedExpr {
                        first_item,
                        rest_items,
                        trailing_comma: _,
                    }) = paren_expr.items
                    {
                        let first = self.lower_expr(first_item.unwrap());
                        args.push(first);
                        for r in rest_items {
                            args.push(self.lower_expr(r.unwrap().item));
                        }
                    }

                    let call = nazmc_ast::CallExpr {
                        on,
                        args,
                        parens_span,
                    };

                    self.new_expr(span, nazmc_ast::ExprKind::Call(Box::new(call)))
                }
                PostOpExpr::Lambda(lambda_expr) => {
                    let parens_span = lambda_expr
                        .open_curly
                        .span
                        .merged_with(&lambda_expr.close_curly.as_ref().unwrap().span);

                    let span = self.get_expr_span(on).merged_with(&parens_span);

                    let mut args = ThinVec::new();

                    args.push(self.lower_lambda_expr(lambda_expr));

                    let call = nazmc_ast::CallExpr {
                        on,
                        args,
                        parens_span,
                    };

                    self.new_expr(span, nazmc_ast::ExprKind::Call(Box::new(call)))
                }
                PostOpExpr::Index(idx_expr) => {
                    let brackets_span = idx_expr
                        .open_bracket
                        .span
                        .merged_with(&idx_expr.close_bracket.unwrap().span);

                    let span = self.get_expr_span(on).merged_with(&brackets_span);

                    let index = self.lower_expr(idx_expr.expr.unwrap());

                    let index = nazmc_ast::IdxExpr {
                        on,
                        idx: index,
                        brackets_span,
                    };

                    self.new_expr(span, nazmc_ast::ExprKind::Idx(Box::new(index)))
                }
            };
        }
        on
    }

    fn lower_unary_expr(&mut self, unary_expr: UnaryExpr) -> nazmc_ast::ExprKey {
        let mut expr = self.lower_primary_expr(unary_expr.expr.unwrap());

        let op_span = unary_expr.op.span;
        let op = lower_unary_op(unary_expr.op.data);

        self.new_expr(
            op_span.merged_with(&self.get_expr_span(expr)),
            nazmc_ast::ExprKind::UnaryOp(Box::new(nazmc_ast::UnaryOpExpr { op, op_span, expr })),
        )
    }

    fn lower_atomic_expr(&mut self, atomic_expr: AtomicExpr) -> nazmc_ast::ExprKey {
        match atomic_expr {
            AtomicExpr::Array(array_expr) => self.lower_array_expr(array_expr),
            AtomicExpr::Paren(paren_expr) => self.lower_paren_expr(paren_expr),
            AtomicExpr::Struct(struct_expr) => self.lower_struct_expr(struct_expr),
            AtomicExpr::Lambda(lambda_expr) => self.lower_lambda_expr(lambda_expr),
            AtomicExpr::When(when_expr) => self.lower_when_expr(when_expr),
            AtomicExpr::If(if_expr) => {
                let span = get_if_expr_span(&if_expr);

                let kind = nazmc_ast::ExprKind::If(Box::new(self.lower_if_expr(if_expr)));

                self.new_expr(span, kind)
            }
            AtomicExpr::Path(simple_path) => {
                let item_path = self.lower_simple_path(simple_path);

                let span = if item_path.pkg_path.spans.is_empty() {
                    item_path.item.span
                } else {
                    item_path
                        .pkg_path
                        .spans
                        .first()
                        .unwrap()
                        .merged_with(&item_path.item.span)
                };

                let kind = if item_path.pkg_path.ids.is_empty() {
                    let path_key = self
                        .ast
                        .state
                        .paths
                        .paths_no_pkgs_exprs
                        .push_and_get_key((item_path.item, item_path.pkg_path.pkg_key));

                    self.ast.state.scope_events[self.current_scope_key]
                        .push(nazmc_ast::ScopeEvent::Path(path_key));

                    nazmc_ast::ExprKind::PathNoPkg(path_key)
                } else {
                    let path_key = self
                        .ast
                        .state
                        .paths
                        .paths_with_pkgs_exprs
                        .push_and_get_key(item_path);

                    nazmc_ast::ExprKind::PathInPkg(path_key)
                };

                self.new_expr(span, kind)
            }
            AtomicExpr::Literal(lit) => {
                let literal_expr = match lit.data {
                    LiteralKind::Str(pool_idx) => nazmc_ast::LiteralExpr::Str(pool_idx),
                    LiteralKind::Char(ch) => nazmc_ast::LiteralExpr::Char(ch),
                    LiteralKind::Bool(b) => nazmc_ast::LiteralExpr::Bool(b),
                    LiteralKind::Num(num_kind) => {
                        let num_kind = match num_kind {
                            NumKind::F4(f4) => nazmc_ast::NumKind::F4(f4),
                            NumKind::F8(f8) => nazmc_ast::NumKind::F8(f8),
                            NumKind::I(i) => nazmc_ast::NumKind::I(i),
                            NumKind::I1(i1) => nazmc_ast::NumKind::I1(i1),
                            NumKind::I2(i2) => nazmc_ast::NumKind::I2(i2),
                            NumKind::I4(i4) => nazmc_ast::NumKind::I4(i4),
                            NumKind::I8(i8) => nazmc_ast::NumKind::I8(i8),
                            NumKind::U(u) => nazmc_ast::NumKind::U(u),
                            NumKind::U1(u1) => nazmc_ast::NumKind::U1(u1),
                            NumKind::U2(u2) => nazmc_ast::NumKind::U2(u2),
                            NumKind::U4(u4) => nazmc_ast::NumKind::U4(u4),
                            NumKind::U8(u8) => nazmc_ast::NumKind::U8(u8),
                            NumKind::UnspecifiedInt(i) => nazmc_ast::NumKind::UnspecifiedInt(i),
                            NumKind::UnspecifiedFloat(f) => nazmc_ast::NumKind::UnspecifiedFloat(f),
                        };
                        nazmc_ast::LiteralExpr::Num(num_kind)
                    }
                };

                self.new_expr(lit.span, nazmc_ast::ExprKind::Literal(literal_expr))
            }
            AtomicExpr::Return(return_expr) => {
                let expr = return_expr.expr.map(|e| self.lower_expr(e));

                let span = if let Some(e) = expr.as_ref() {
                    return_expr
                        .return_keyword
                        .span
                        .merged_with(&self.get_expr_span(*e))
                } else {
                    return_expr.return_keyword.span
                };

                let return_scope = if let Some(lambda_scope_key) = self.current_lambda_scope_key {
                    lambda_scope_key
                } else if let Some(fn_scope_key) = self.current_fn_scope_key {
                    fn_scope_key
                } else {
                    self.return_outside_fn_body_errs.push((self.file_key, span));
                    Default::default()
                };

                let return_expr = Box::new(ReturnExpr {
                    return_scope,
                    return_keyword_span: return_expr.return_keyword.span,
                    expr,
                });

                self.new_expr(span, nazmc_ast::ExprKind::Return(return_expr))
            }
            AtomicExpr::Break(break_keyword) => {
                let loop_scope_key = if let Some(loop_scope_key) = self.current_loop_scope_key {
                    loop_scope_key
                } else {
                    self.break_outside_loop_body_errs
                        .push((self.file_key, break_keyword.span));
                    Default::default()
                };

                self.new_expr(
                    break_keyword.span,
                    nazmc_ast::ExprKind::Break(loop_scope_key),
                )
            }
            AtomicExpr::Continue(continue_keyword) => {
                let loop_scope_key = if let Some(loop_scope_key) = self.current_loop_scope_key {
                    loop_scope_key
                } else {
                    self.continue_outside_loop_body_errs
                        .push((self.file_key, continue_keyword.span));
                    Default::default()
                };

                self.new_expr(
                    continue_keyword.span,
                    nazmc_ast::ExprKind::Continue(loop_scope_key),
                )
            }
            AtomicExpr::On(on) => self.new_expr(on.span, nazmc_ast::ExprKind::On),
        }
    }

    #[inline]
    fn lower_array_expr(&mut self, array_expr: ArrayExpr) -> nazmc_ast::ExprKey {
        let span = array_expr
            .open_bracket
            .span
            .merged_with(&array_expr.close_bracket.unwrap().span);

        if let Some(ArrayExprKind::Elements(ElementsArrayExpr {
            first,
            rest,
            trailing_comma: _,
        })) = array_expr.expr_kind
        {
            let mut elements = ThinVec::new();
            let first = self.lower_expr(first.unwrap());
            elements.push(first);
            for r in rest {
                elements.push(self.lower_expr(r.unwrap().item));
            }

            self.new_expr(span, nazmc_ast::ExprKind::ArrayElements(elements))
        } else if let Some(ArrayExprKind::ExplicitSize(ExplicitSizeArrayExpr {
            repeated_expr,
            semicolon: _,
            size_expr,
        })) = array_expr.expr_kind
        {
            let repeat = self.lower_expr(repeated_expr.unwrap());
            let size = self.lower_expr(size_expr.unwrap());
            let array_elements_sized_expr = Box::new(nazmc_ast::ArrayRepeatedExpr { repeat, size });

            self.new_expr(
                span,
                nazmc_ast::ExprKind::ArrayRepeated(array_elements_sized_expr),
            )
        } else {
            let elements = ThinVec::new();

            self.new_expr(span, nazmc_ast::ExprKind::ArrayElements(elements))
        }
    }

    #[inline]
    fn lower_paren_expr(&mut self, paren_expr: ParenExpr) -> nazmc_ast::ExprKey {
        let span = paren_expr
            .open_delim
            .span
            .merged_with(&paren_expr.close_delim.unwrap().span);

        if let Some(PunctuatedExpr {
            first_item,
            rest_items,
            trailing_comma,
        }) = paren_expr.items
        {
            let first = self.lower_expr(first_item.unwrap());
            if rest_items.is_empty() && trailing_comma.is_none() {
                // Parentheses expression
                first
            } else {
                let mut exprs = ThinVec::new();
                exprs.push(first);
                for r in rest_items {
                    exprs.push(self.lower_expr(r.unwrap().item));
                }
                self.new_expr(span, nazmc_ast::ExprKind::Tuple(exprs))
            }
        } else {
            // Unit Expression
            self.new_expr(span, nazmc_ast::ExprKind::Unit)
        }
    }

    #[inline]
    fn lower_struct_expr(&mut self, struct_expr: StructExpr) -> nazmc_ast::ExprKey {
        let item_path = self.lower_simple_path(struct_expr.path.unwrap());

        let init_expr = struct_expr.init.unwrap();

        let span = struct_expr
            .dot
            .span
            .merged_with(&init_expr.close_delim.unwrap().span);

        let mut fields = ThinVec::new();

        if let Some(PunctuatedFieldInitExpr {
            first_item,
            rest_items,
            trailing_comma: _,
        }) = init_expr.items
        {
            let first = self.lower_struct_field_expr(first_item.unwrap());
            fields.push(first);
            for r in rest_items {
                fields.push(self.lower_struct_field_expr(r.unwrap().item));
            }
        }

        let fields_struct_path_key = self
            .ast
            .state
            .paths
            .structs_paths_exprs
            .push_and_get_key(item_path);

        let fields_struct = Box::new(nazmc_ast::StructExpr {
            path_key: fields_struct_path_key,
            fields,
        });

        self.new_expr(span, nazmc_ast::ExprKind::Struct(fields_struct))
    }

    fn lower_struct_field_expr(
        &mut self,
        e: FieldInitExpr,
    ) -> (nazmc_ast::ASTId, nazmc_ast::ExprKey) {
        let name = nazmc_ast::ASTId {
            span: e.name.span,
            id: e.name.data.val,
        };

        let expr = if let Some(e) = e.expr {
            self.lower_expr(e.expr.unwrap())
        } else {
            let item = nazmc_ast::ASTId {
                span: name.span,
                id: name.id,
            };

            let path_key = self
                .ast
                .state
                .paths
                .paths_no_pkgs_exprs
                .push_and_get_key((item, self.pkg_key));

            self.ast.state.scope_events[self.current_scope_key]
                .push(nazmc_ast::ScopeEvent::Path(path_key));

            self.new_expr(name.span, nazmc_ast::ExprKind::PathNoPkg(path_key))
        };

        (name, expr)
    }

    #[inline]
    fn lower_lambda_expr(&mut self, lambda_expr: LambdaExpr) -> nazmc_ast::ExprKey {
        let span = lambda_expr
            .open_curly
            .span
            .merged_with(&lambda_expr.close_curly.unwrap().span);

        let outter_lambda_scope = self.current_lambda_scope_key;

        self.current_lambda_scope_key = Some(ScopeKey::from(self.ast.scopes.len()));

        let lambda_scope_key = self.lower_lambda_stms_and_return_expr(
            lambda_expr.stms,
            lambda_expr.last_expr,
            span,
            false,
        );

        self.current_lambda_scope_key = outter_lambda_scope;

        let mut bound_names_map = HashMap::new();

        let lambda = if let Some(arrow) = lambda_expr.lambda_arrow {
            let mut params = ThinVec::new();

            if let LambdaArrow::WithParams(LambdaParams {
                first,
                rest,
                trailing_comma: _,
                r_arrow: _,
            }) = arrow
            {
                let first = self.lower_binding(first, &mut bound_names_map);
                params.push(first);

                for r in rest {
                    params.push(self.lower_binding(r.item, &mut bound_names_map));
                }
            }

            nazmc_ast::LambdaExpr {
                params,
                body: lambda_scope_key,
            }
        } else {
            let mut params = ThinVec::new();
            params.push(nazmc_ast::Binding {
                kind: nazmc_ast::BindingKind::Id(nazmc_ast::ASTId {
                    span: lambda_expr.open_curly.span,
                    id: IdKey::IMPLICIT_LAMBDA_PARAM,
                }),
                typ: None,
            });
            nazmc_ast::LambdaExpr {
                params,
                body: lambda_scope_key,
            }
        };

        self.ast
            .state
            .bound_lambdas_names
            .insert(lambda_scope_key, bound_names_map);

        self.new_expr(span, nazmc_ast::ExprKind::Lambda(Box::new(lambda)))
    }

    fn lower_if_expr(&mut self, if_expr: IfExpr) -> nazmc_ast::IfExpr {
        let if_condition = self.lower_expr(if_expr.conditional_block.condition.unwrap());
        let if_body = self.lower_lambda_as_body(if_expr.conditional_block.block.unwrap(), false);

        let if_ = (if_expr.if_keyword.span, if_condition, if_body);

        let mut else_ifs = ThinVec::new();

        for else_if in if_expr.else_ifs {
            let condition = self.lower_expr(else_if.conditional_block.condition.unwrap());
            let body = self.lower_lambda_as_body(else_if.conditional_block.block.unwrap(), false);

            else_ifs.push((
                else_if
                    .else_keyword
                    .span
                    .merged_with(&else_if.if_keyword.span),
                condition,
                body,
            ));
        }

        let else_ = if_expr.else_cluase.map(|e| {
            let body = self.lower_lambda_as_body(e.block.unwrap(), false);
            (e.else_keyword.span, body)
        });

        nazmc_ast::IfExpr {
            if_,
            else_ifs,
            else_,
        }
    }

    fn lower_when_expr(&mut self, _when_expr: WhenExpr) -> nazmc_ast::ExprKey {
        todo!()
    }

    pub fn validate(
        self,
        pkgs: &TiSlice<PkgKey, &ThinVec<IdKey>>,
        files_infos: &TiSlice<FileKey, FileInfo>,
        id_pool: &TiSlice<IdKey, String>,
    ) {
        let mut diagnostics = vec![];

        for (pkg_key, conflicts) in self.items_conflicts_in_pkgs {
            let pkg_display_name = pkgs[pkg_key]
                .iter()
                .map(|name| id_pool[*name].as_str())
                .collect::<Vec<_>>()
                .join("::");

            for (conflicting_name, files_conflicts) in conflicts {
                let name = &id_pool[conflicting_name];
                let mut msg = format!("يوجد أكثر من عنصر لهم نفس الاسم `{}` في نفس الحزمة", name,);
                if !pkg_display_name.is_empty() {
                    msg.push_str(&format!(" `{}`", pkg_display_name));
                }

                let mut diagnostic = Diagnostic::error(msg, vec![]);
                let mut occurrences = 1;
                for (file_key, spans) in files_conflicts {
                    let file_info = &files_infos[file_key];
                    let code_window =
                        occurrences_code_window(file_info, &mut occurrences, spans, "عنصر");
                    diagnostic.push_code_window(code_window);
                }
                diagnostics.push(diagnostic);
            }
        }

        for ((field_id_key, file_key, struct_id_span), spans) in
            self.struct_fields_conflicts_in_files
        {
            let file_info = &files_infos[file_key];

            let name = &id_pool[field_id_key];

            let msg = format!("يوجد أكثر من حقل لهم نفس الاسم `{}` في نفس الهيكل", name);

            let mut occurrences = 1;

            let mut code_window =
                occurrences_code_window(file_info, &mut occurrences, spans, "حقل");

            code_window.mark_secondary(struct_id_span, vec!["في هذا الهيكل".to_string()]);

            let diagnostic = Diagnostic::error(msg, vec![code_window]);

            diagnostics.push(diagnostic);
        }

        for ((param_id_key, file_key, fn_id_span), spans) in self.fn_params_conflicts_in_files {
            let file_info = &files_infos[file_key];

            let name = &id_pool[param_id_key];

            let msg = format!("يوجد أكثر من مُعامِل لهم نفس الاسم `{}` في نفس الدالة", name);

            let mut occurrences = 1;

            let mut code_window =
                occurrences_code_window(file_info, &mut occurrences, spans, "مُعامِل");

            code_window.mark_secondary(fn_id_span, vec!["في هذه الدالة".to_string()]);

            let diagnostic = Diagnostic::error(msg, vec![code_window]);

            diagnostics.push(diagnostic);
        }

        for ((file_key, first_span), (id_key, sec_span)) in self.bindings_conflicts {
            let file_info = &files_infos[file_key];

            let name = &id_pool[id_key];

            let msg = format!("تم حجز الاسم `{}` أكثر من مرة", name);

            let mut code_window = CodeWindow::new(file_info, sec_span.start);

            code_window.mark_secondary(first_span, vec!["تم حجز الاسم هنا أول مرة".into()]);

            code_window.mark_error(sec_span, vec!["تم حجز الاسم هنا للمرة الثانية".to_string()]);

            let diangostic = Diagnostic::error(msg, vec![code_window]);

            diagnostics.push(diangostic);
        }

        for ((id_key, file_key), spans) in self.items_and_imports_conflicts_in_files {
            let file_info = &files_infos[file_key];

            let name = &id_pool[id_key];

            let msg = format!("يوجد أكثر من عنصر لهم نفس الاسم `{}` في نفس الملف", name);

            let mut occurrences = 1;

            let code_window = occurrences_code_window(file_info, &mut occurrences, spans, "عنصر");

            let diagnostic = Diagnostic::error(msg, vec![code_window]);

            diagnostics.push(diagnostic);
        }

        for (file_key, span) in self.return_outside_fn_body_errs {
            let file_info = &files_infos[file_key];

            let mut code_window = CodeWindow::new(file_info, span.start);

            code_window.mark_error(span, vec![]);

            let msg = "لا يمكن استخدام `أرجع` إلا من داخل نطاق الدوال أو داخل تعبيرات اللامدا".into();

            let diagnostic = Diagnostic::error(msg, vec![code_window]);

            diagnostics.push(diagnostic);
        }

        for (file_key, span) in self.break_outside_loop_body_errs {
            let file_info = &files_infos[file_key];

            let mut code_window = CodeWindow::new(file_info, span.start);

            code_window.mark_error(span, vec![]);

            let msg = "لا يمكن استخدام `قطع` إلا من داخل حلقة تكرارية".into();

            let diagnostic = Diagnostic::error(msg, vec![code_window]);

            diagnostics.push(diagnostic);
        }

        for (file_key, span) in self.continue_outside_loop_body_errs {
            let file_info = &files_infos[file_key];

            let mut code_window = CodeWindow::new(file_info, span.start);

            code_window.mark_error(span, vec![]);

            let msg = "لا يمكن استخدام `وصل` إلا من داخل حلقة تكرارية".into();

            let diagnostic = Diagnostic::error(msg, vec![code_window]);

            diagnostics.push(diagnostic);
        }

        if !diagnostics.is_empty() {
            eprint_diagnostics(diagnostics);
            exit(1)
        }
    }
}

#[inline]
fn get_precendence(op: &nazmc_ast::BinOp) -> u8 {
    match op {
        nazmc_ast::BinOp::Assign
        | nazmc_ast::BinOp::PlusAssign
        | nazmc_ast::BinOp::MinusAssign
        | nazmc_ast::BinOp::TimesAssign
        | nazmc_ast::BinOp::DivAssign
        | nazmc_ast::BinOp::ModAssign
        | nazmc_ast::BinOp::BAndAssign
        | nazmc_ast::BinOp::BOrAssign
        | nazmc_ast::BinOp::XorAssign
        | nazmc_ast::BinOp::ShlAssign
        | nazmc_ast::BinOp::ShrAssign => 0, // Assignments have the lowest precedence
        nazmc_ast::BinOp::LOr => 1,
        nazmc_ast::BinOp::LAnd => 2,
        nazmc_ast::BinOp::EqualEqual | nazmc_ast::BinOp::NotEqual => 3,
        nazmc_ast::BinOp::GE
        | nazmc_ast::BinOp::GT
        | nazmc_ast::BinOp::LE
        | nazmc_ast::BinOp::LT => 4,
        nazmc_ast::BinOp::OpenOpenRange
        | nazmc_ast::BinOp::CloseOpenRange
        | nazmc_ast::BinOp::OpenCloseRange
        | nazmc_ast::BinOp::CloseCloseRange => 5,
        nazmc_ast::BinOp::BOr => 6,
        nazmc_ast::BinOp::Xor => 7,
        nazmc_ast::BinOp::BAnd => 8,
        nazmc_ast::BinOp::Shl | nazmc_ast::BinOp::Shr => 9,
        nazmc_ast::BinOp::Plus | nazmc_ast::BinOp::Minus => 10,
        nazmc_ast::BinOp::Times | nazmc_ast::BinOp::Div | nazmc_ast::BinOp::Mod => 11,
    }
}

#[inline]
fn lower_bin_op(op: BinOpToken) -> nazmc_ast::BinOp {
    match op {
        BinOpToken::LOr => nazmc_ast::BinOp::LOr,
        BinOpToken::LAnd => nazmc_ast::BinOp::LAnd,
        BinOpToken::EqualEqual => nazmc_ast::BinOp::EqualEqual,
        BinOpToken::NotEqual => nazmc_ast::BinOp::NotEqual,
        BinOpToken::GE => nazmc_ast::BinOp::GE,
        BinOpToken::GT => nazmc_ast::BinOp::GT,
        BinOpToken::LE => nazmc_ast::BinOp::LE,
        BinOpToken::LT => nazmc_ast::BinOp::LT,
        BinOpToken::OpenOpenRange => nazmc_ast::BinOp::OpenOpenRange,
        BinOpToken::CloseOpenRange => nazmc_ast::BinOp::CloseOpenRange,
        BinOpToken::OpenCloseRange => nazmc_ast::BinOp::OpenCloseRange,
        BinOpToken::CloseCloseRange => nazmc_ast::BinOp::CloseCloseRange,
        BinOpToken::BOr => nazmc_ast::BinOp::BOr,
        BinOpToken::Xor => nazmc_ast::BinOp::Xor,
        BinOpToken::BAnd => nazmc_ast::BinOp::BAnd,
        BinOpToken::Shr => nazmc_ast::BinOp::Shr,
        BinOpToken::Shl => nazmc_ast::BinOp::Shl,
        BinOpToken::Plus => nazmc_ast::BinOp::Plus,
        BinOpToken::Minus => nazmc_ast::BinOp::Minus,
        BinOpToken::Times => nazmc_ast::BinOp::Times,
        BinOpToken::Div => nazmc_ast::BinOp::Div,
        BinOpToken::Mod => nazmc_ast::BinOp::Mod,
        BinOpToken::Assign => nazmc_ast::BinOp::Assign,
        BinOpToken::PlusAssign => nazmc_ast::BinOp::PlusAssign,
        BinOpToken::MinusAssign => nazmc_ast::BinOp::MinusAssign,
        BinOpToken::TimesAssign => nazmc_ast::BinOp::TimesAssign,
        BinOpToken::DivAssign => nazmc_ast::BinOp::DivAssign,
        BinOpToken::ModAssign => nazmc_ast::BinOp::ModAssign,
        BinOpToken::BAndAssign => nazmc_ast::BinOp::BAndAssign,
        BinOpToken::BOrAssign => nazmc_ast::BinOp::BOrAssign,
        BinOpToken::XorAssign => nazmc_ast::BinOp::XorAssign,
        BinOpToken::ShlAssign => nazmc_ast::BinOp::ShlAssign,
        BinOpToken::ShrAssign => nazmc_ast::BinOp::ShrAssign,
    }
}

fn lower_unary_op(op: UnaryOpToken) -> nazmc_ast::UnaryOp {
    match op {
        UnaryOpToken::Minus => nazmc_ast::UnaryOp::Minus,
        UnaryOpToken::LNot => nazmc_ast::UnaryOp::LNot,
        UnaryOpToken::BNot => nazmc_ast::UnaryOp::BNot,
        UnaryOpToken::Deref => nazmc_ast::UnaryOp::Deref,
        UnaryOpToken::Borrow => nazmc_ast::UnaryOp::Borrow,
        UnaryOpToken::BorrowMut => nazmc_ast::UnaryOp::BorrowMut,
    }
}

fn occurrences_code_window<'a>(
    file_info: &'a FileInfo,
    occurrences: &mut usize,
    mut spans: Vec<Span>,
    name: &'static str,
) -> CodeWindow<'a> {
    let mut code_window = CodeWindow::new(file_info, spans[0].start);

    nazmc_diagnostics::span::sort_spans(&mut spans);

    for span in spans {
        let occurrence_str = match *occurrences {
            1 => format!("هنا تم العثور على أول {} بهذا الاسم", name),
            2 => "هنا تم العثور على نفس الاسم للمرة الثانية".to_string(),
            3 => "هنا تم العثور على نفس الاسم للمرة الثالثة".to_string(),
            4 => "هنا تم العثور على نفس الاسم للمرة الرابعة".to_string(),
            5 => "هنا تم العثور على نفس الاسم للمرة الخامسة".to_string(),
            6 => "هنا تم العثور على نفس الاسم للمرة السادسة".to_string(),
            7 => "هنا تم العثور على نفس الاسم للمرة السابعة".to_string(),
            8 => "هنا تم العثور على نفس الاسم للمرة الثامنة".to_string(),
            9 => "هنا تم العثور على نفس الاسم للمرة التاسعة".to_string(),
            10 => "هنا تم العثور على نفس الاسم للمرة العاشرة".to_string(),
            o => format!("هنا تم العثور على نفس الاسم للمرة {}", o),
        };

        if *occurrences == 1 {
            code_window.mark_error(span, vec![occurrence_str]);
        } else {
            code_window.mark_secondary(span, vec![occurrence_str]);
        }

        *occurrences += 1;
    }

    code_window
}

fn get_if_expr_span(if_expr: &IfExpr) -> Span {
    let span_end = if let Some(ref else_) = if_expr.else_cluase {
        &else_
            .block
            .as_ref()
            .unwrap()
            .close_curly
            .as_ref()
            .unwrap()
            .span
    } else if !if_expr.else_ifs.is_empty() {
        &if_expr
            .else_ifs
            .last()
            .unwrap()
            .conditional_block
            .block
            .as_ref()
            .unwrap()
            .close_curly
            .as_ref()
            .unwrap()
            .span
    } else {
        &if_expr
            .conditional_block
            .block
            .as_ref()
            .unwrap()
            .close_curly
            .as_ref()
            .unwrap()
            .span
    };

    if_expr.if_keyword.span.merged_with(span_end)
}
