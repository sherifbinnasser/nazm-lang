use nazmc_ast::{
    ASTId, ArrayTypeExprKey, ConstKey, FnKey, FnParam, Item, ItemPath, LetStmKey, PathNoPkgKey,
    PathTypeExprKey, PathWithPkgKey, PkgPath, ScopeKey, StarImportStm, StaticKey, StructKey,
    StructPathKey, VisModifier,
};
use nazmc_data_pool::{
    typed_index_collections::{ti_vec, TiSlice, TiVec},
    IdKey,
};
use nazmc_data_pool::{FileKey, ItemInfo, PkgKey};
use nazmc_diagnostics::{
    eprint_diagnostics, file_info::FileInfo, span::Span, CodeWindow, Diagnostic,
};
use std::{collections::HashMap, process::exit};
use thin_vec::ThinVec;

pub struct NameResolver<'a> {
    files_infos: &'a TiSlice<FileKey, FileInfo>,
    id_pool: &'a TiSlice<IdKey, String>,
    pkgs: &'a HashMap<ThinVec<IdKey>, usize>,
    pkgs_names: &'a TiSlice<PkgKey, &'a ThinVec<IdKey>>,
    ast: nazmc_ast::AST<nazmc_ast::Unresolved>,
    diagnostics: Vec<Diagnostic<'a>>,
}

struct ResolvedImport {
    resolved_item: Item,
}

struct ResolvedStarImport {
    pkg_path_span: Span,
    resolved_pkg_key: PkgKey,
}

impl<'a> NameResolver<'a> {
    pub fn new(
        files_infos: &'a TiSlice<FileKey, FileInfo>,
        id_pool: &'a TiSlice<IdKey, String>,
        pkgs: &'a HashMap<ThinVec<IdKey>, usize>,
        pkgs_names: &'a TiSlice<PkgKey, &'a ThinVec<IdKey>>,
        ast: nazmc_ast::AST<nazmc_ast::Unresolved>,
    ) -> Self {
        Self {
            files_infos,
            id_pool,
            pkgs,
            pkgs_names,
            ast,
            diagnostics: vec![],
        }
    }

    pub fn resolve(mut self) -> nazmc_ast::AST<nazmc_ast::Resolved> {
        let paths = std::mem::take(&mut self.ast.state.paths);

        let resolved_imports = paths
            .imports
            .into_iter_enumerated()
            .map(|(file_key, file_imports)| {
                file_imports
                    .into_iter()
                    .map(|import| {
                        let resolved_item = self
                            .resolve_non_pkg_item_path(|_| true, "", file_key, import.item_path)
                            .unwrap_or_default();
                        (
                            import.alias.id,
                            ResolvedImport {
                                // alias_span: import.alias.span,
                                resolved_item,
                            },
                        )
                    })
                    .collect()
            })
            .collect::<TiVec<FileKey, HashMap<_, _>>>();

        let resolved_star_imports = paths
            .star_imports
            .into_iter()
            .map(|star_imports_stms| {
                star_imports_stms
                    .into_iter()
                    .map(
                        |StarImportStm {
                             top_pkg_span,
                             pkg_path,
                         }| {
                            let start_span =
                                top_pkg_span.unwrap_or_else(|| *pkg_path.spans.first().unwrap());

                            let pkg_path_span = if let Some(span) = pkg_path.spans.last() {
                                start_span.merged_with(&span)
                            } else {
                                start_span
                            };

                            let resolved_pkg_key =
                                self.resolve_pkg_path(pkg_path).unwrap_or_default();

                            ResolvedStarImport {
                                pkg_path_span,
                                resolved_pkg_key,
                            }
                        },
                    )
                    .collect()
            })
            .collect::<TiVec<FileKey, ThinVec<_>>>();

        let resolved_types_paths = std::mem::take(&mut self.ast.types_exprs.paths)
            .into_iter()
            .map(|item_path| {
                let file_key = item_path.pkg_path.file_key;
                let span = item_path.get_span();

                let item = self
                    .resolve_item_path_from_local_file(
                        file_key,
                        item_path,
                        &resolved_imports,
                        &resolved_star_imports,
                        |item| matches!(item, Item::Struct { .. }),
                        "هيكل",
                    )
                    .unwrap_or_default();

                (item, span)
            })
            .collect::<TiVec<PathTypeExprKey, (Item, Span)>>();

        let resolved_structs_exprs = paths
            .structs_paths_exprs
            .into_iter()
            .map(|item_path| {
                let file_key = item_path.pkg_path.file_key;

                self.resolve_item_path_from_local_file(
                    file_key,
                    item_path,
                    &resolved_imports,
                    &resolved_star_imports,
                    |item| matches!(item, Item::Struct { .. }),
                    item_kind_to_str(Item::Struct {
                        vis: VisModifier::Default,
                        key: StructKey::default(),
                    }),
                )
                .map(|item| {
                    if let Item::Struct { key, .. } = item {
                        key
                    } else {
                        Default::default()
                    }
                })
                .unwrap_or_default()
            })
            .collect::<TiVec<StructPathKey, StructKey>>();

        let resolved_paths_with_pkgs_exprs = paths
            .paths_with_pkgs_exprs
            .into_iter()
            .map(|item_path| {
                let file_key = item_path.pkg_path.file_key;

                self.resolve_item_path_from_local_file(
                    file_key,
                    item_path,
                    &resolved_imports,
                    &resolved_star_imports,
                    |item| {
                        matches!(
                            item,
                            Item::Const { .. } | Item::Static { .. } | Item::Fn { .. }
                        )
                    },
                    "عنصر",
                )
                .unwrap_or_default()
            })
            .collect::<TiVec<PathWithPkgKey, Item>>();

        // Resolve paths that has no leading pkg path
        let mut resolved_paths_no_pkgs_exprs =
            ti_vec![Default::default(); paths.paths_no_pkgs_exprs.len()];

        let mut names_stack = vec![];

        let fns_len = self.ast.fns.len();

        for i in 0..fns_len {
            names_stack.clear();
            let fn_key = FnKey::from(i);
            let at = self.ast.fns[fn_key].info.file_key;
            let scope_key = self.ast.fns[fn_key].scope_key;
            self.resolve_paths_in_scope(
                at,
                &mut names_stack,
                Some(fn_key),
                scope_key,
                &paths.paths_no_pkgs_exprs,
                &mut resolved_paths_no_pkgs_exprs,
                &resolved_imports,
                &resolved_star_imports,
            );
        }

        let consts_len = self.ast.consts.len();

        for i in 0..consts_len {
            names_stack.clear();
            let const_key = ConstKey::from(i);
            let at = self.ast.consts[const_key].info.file_key;
            let scope_key = self.ast.consts[const_key].expr_scope_key;
            self.resolve_paths_in_scope(
                at,
                &mut names_stack,
                None,
                scope_key,
                &paths.paths_no_pkgs_exprs,
                &mut resolved_paths_no_pkgs_exprs,
                &resolved_imports,
                &resolved_star_imports,
            );
        }

        let statics_len = self.ast.statics.len();

        for i in 0..statics_len {
            names_stack.clear();
            let static_key = StaticKey::from(i);
            let at = self.ast.statics[static_key].info.file_key;
            let scope_key = self.ast.statics[static_key].expr_scope_key;
            self.resolve_paths_in_scope(
                at,
                &mut names_stack,
                None,
                scope_key,
                &paths.paths_no_pkgs_exprs,
                &mut resolved_paths_no_pkgs_exprs,
                &resolved_imports,
                &resolved_star_imports,
            );
        }

        let array_types_exprs_len = self.ast.types_exprs.arrays.len();

        for i in 0..array_types_exprs_len {
            let array_type_expr_key = ArrayTypeExprKey::from(i);
            let at = self.ast.types_exprs.arrays[array_type_expr_key].file_key;
            let scope_key = self.ast.types_exprs.arrays[array_type_expr_key].size_expr_scope_key;
            self.resolve_paths_in_scope(
                at,
                &mut names_stack,
                None,
                scope_key,
                &paths.paths_no_pkgs_exprs,
                &mut resolved_paths_no_pkgs_exprs,
                &resolved_imports,
                &resolved_star_imports,
            );
        }

        if !self.diagnostics.is_empty() {
            eprint_diagnostics(self.diagnostics);
            exit(1);
        }

        let state = nazmc_ast::Resolved {
            structs_paths_exprs: resolved_structs_exprs,
            paths_no_pkgs_exprs: resolved_paths_no_pkgs_exprs,
            paths_with_pkgs_exprs: resolved_paths_with_pkgs_exprs,
            types_paths: resolved_types_paths,
        };

        nazmc_ast::AST {
            state,
            types_exprs: self.ast.types_exprs,
            consts: self.ast.consts,
            statics: self.ast.statics,
            structs: self.ast.structs,
            fns: self.ast.fns,
            scopes: self.ast.scopes,
            lets: self.ast.lets,
            exprs: self.ast.exprs,
        }
    }

    fn resolve_paths_in_scope(
        &mut self,
        at: FileKey,
        lets_haystacks: &mut Vec<LetStmKey>,
        fn_key: Option<FnKey>,
        scope_key: ScopeKey,
        paths: &TiSlice<PathNoPkgKey, (ASTId, PkgKey)>,
        resolved_paths: &mut TiSlice<PathNoPkgKey, Item>,
        resolved_imports: &TiSlice<FileKey, HashMap<IdKey, ResolvedImport>>,
        resolved_star_imports: &TiSlice<FileKey, ThinVec<ResolvedStarImport>>,
    ) {
        let stack_start_idx = lets_haystacks.len();

        // Scope events are in unresolved state of AST, so, there is no need to restore the ownership
        'label: for event in std::mem::take(&mut self.ast.state.scope_events[scope_key]) {
            match event {
                nazmc_ast::ScopeEvent::Let(let_stm_key) => {
                    lets_haystacks.push(let_stm_key);
                }
                nazmc_ast::ScopeEvent::Path(path_no_pkg_key) => {
                    let path_expr = &paths[path_no_pkg_key];
                    let needle_id_key = path_expr.0.id;

                    // Iterate over names_stack in reverse, from stack_start_idx to the end.
                    if let Some(&let_stm_key) =
                        lets_haystacks[stack_start_idx..]
                            .iter()
                            .rev()
                            .find(|&&let_stm_key| {
                                self.ast.state.bound_lets_names[let_stm_key]
                                    .contains_key(&needle_id_key)
                            })
                    {
                        resolved_paths[path_no_pkg_key] = Item::LocalVar {
                            id: needle_id_key,
                            key: let_stm_key,
                        };
                        continue 'label;
                    }

                    // Check if current scope is a lambda expression, and then check if it contains the needle id key
                    if self
                        .ast
                        .state
                        .bound_lambdas_names
                        .get(&scope_key)
                        .is_some_and(|bound_lambda_names| {
                            bound_lambda_names.contains_key(&needle_id_key)
                        })
                    {
                        resolved_paths[path_no_pkg_key] = Item::LambdaParam {
                            id: needle_id_key,
                            scope_key,
                        };
                        continue 'label;
                    }

                    // Iterate over names_stack in reverse, from index `stack_start_idx - 1` to the beginning.
                    if let Some(&let_stm_key) =
                        lets_haystacks[..stack_start_idx]
                            .iter()
                            .rev()
                            .find(|&&let_stm_key| {
                                self.ast.state.bound_lets_names[let_stm_key]
                                    .contains_key(&needle_id_key)
                            })
                    {
                        resolved_paths[path_no_pkg_key] = Item::LocalVar {
                            id: needle_id_key,
                            key: let_stm_key,
                        };
                        continue 'label;
                    }

                    // Searching in fn params
                    if let (Some(fn_key), 0) = (fn_key, stack_start_idx) {
                        if let Some(idx) = self.ast.fns[fn_key].params.iter().position(
                            |FnParam {
                                 ast_id: ASTId { id, .. },
                                 ..
                             }| *id == path_expr.0.id,
                        ) {
                            resolved_paths[path_no_pkg_key] = Item::FnParam {
                                idx: idx as u32,
                                fn_key,
                            };
                            continue 'label;
                        }
                    }

                    resolved_paths[path_no_pkg_key] = self
                        .resolve_item_path_with_no_pkg_path(
                            at,
                            path_expr.0,
                            path_expr.1,
                            &resolved_imports,
                            &resolved_star_imports,
                            |item| {
                                matches!(
                                    item,
                                    Item::Const { .. } | Item::Static { .. } | Item::Fn { .. }
                                )
                            },
                            "عنصر",
                        )
                        .unwrap_or_default();
                }
                nazmc_ast::ScopeEvent::Scope(scope_key) => {
                    self.resolve_paths_in_scope(
                        at,
                        lets_haystacks,
                        fn_key,
                        scope_key,
                        paths,
                        resolved_paths,
                        resolved_imports,
                        resolved_star_imports,
                    );
                }
            }
        }

        lets_haystacks.truncate(stack_start_idx);
    }

    fn resolve_non_pkg_item_path(
        &mut self,
        predicate_kind: impl Fn(Item) -> bool,
        expected_kind: &str,
        at: FileKey,
        item_path: ItemPath,
    ) -> Option<Item> {
        let ASTId {
            span: item_path_span,
            id: item_path_id,
        } = item_path.item;

        let at_span = item_path
            .pkg_path
            .spans
            .first()
            .unwrap_or(&item_path_span)
            .merged_with(&item_path_span);

        let at_pkg_key = item_path.pkg_path.pkg_key;

        let (item_pkg_key, resolved_item) = self.resolve_item_path(item_path)?;

        if !predicate_kind(resolved_item) {
            self.add_unexpected_item_kind_err(
                at,
                item_path_span,
                expected_kind,
                item_kind_to_str(resolved_item),
                resolved_item,
            );
            None
        } else if self.check_resolved_item(
            at,
            at_span,
            at_pkg_key,
            item_pkg_key,
            resolved_item,
            item_path_id,
        ) {
            Some(resolved_item)
        } else {
            None
        }
    }

    fn resolve_item_path_from_local_file(
        &mut self,
        at: FileKey,
        item_path: ItemPath,
        resolved_imports: &TiSlice<FileKey, HashMap<IdKey, ResolvedImport>>,
        resolved_star_imports: &TiSlice<FileKey, ThinVec<ResolvedStarImport>>,
        predicate_kind: impl Fn(Item) -> bool,
        expected_kind: &str,
    ) -> Option<Item> {
        if item_path.pkg_path.ids.is_empty() && item_path.top_pkg_span.is_none() {
            self.resolve_item_path_with_no_pkg_path(
                at,
                item_path.item,
                item_path.pkg_path.pkg_key,
                &resolved_imports,
                &resolved_star_imports,
                predicate_kind,
                expected_kind,
            )
        } else {
            self.resolve_non_pkg_item_path(predicate_kind, expected_kind, at, item_path)
        }
    }

    fn resolve_item_path_with_no_pkg_path(
        &mut self,
        at: FileKey,
        item_ast_id: ASTId,
        item_path_pkg_key: PkgKey,
        resolved_imports: &TiSlice<FileKey, HashMap<IdKey, ResolvedImport>>,
        resolved_star_imports: &TiSlice<FileKey, ThinVec<ResolvedStarImport>>,
        predicate_kind: impl Fn(Item) -> bool,
        expected_kind: &str,
    ) -> Option<Item> {
        if let Some(item) = resolved_imports[at].get(&item_ast_id.id) {
            return Some(item.resolved_item);
        }

        if let Some(item) = self.ast.state.pkgs_to_items[item_path_pkg_key].get(&item_ast_id.id) {
            return if predicate_kind(*item) {
                Some(*item)
            } else {
                self.add_unexpected_item_kind_err(
                    at,
                    item_ast_id.span,
                    expected_kind,
                    item_kind_to_str(*item),
                    *item,
                );
                None
            };
        }

        let resolved_items_with_same_name = resolved_star_imports[at]
            .iter()
            .filter_map(|star_import| {
                self.ast.state.pkgs_to_items[star_import.resolved_pkg_key]
                    .get(&item_ast_id.id)
                    .filter(|item| predicate_kind(**item))
                    .map(|item| (star_import, item))
            })
            .collect::<Vec<_>>();

        let (accessible_items_with_same_name, inaccessible_items_with_same_name): (
            Vec<(&ResolvedStarImport, &Item)>,
            Vec<(&ResolvedStarImport, &Item)>,
        ) = resolved_items_with_same_name.into_iter().partition(
            |(resolved_star_import, resolved_item)| match resolved_item {
                Item::Struct { vis, .. }
                | Item::Const { vis, .. }
                | Item::Static { vis, .. }
                | Item::Fn { vis, .. }
                    if !matches!(vis, nazmc_ast::VisModifier::Default)
                        || resolved_star_import.resolved_pkg_key == item_path_pkg_key =>
                {
                    true
                }
                _ => false,
            },
        );

        if accessible_items_with_same_name.len() == 1 {
            let (resolved_star_import, resolved_item) =
                *accessible_items_with_same_name.first().unwrap();

            let resolved_item = *resolved_item;

            return if !predicate_kind(resolved_item) {
                self.add_unexpected_item_kind_err(
                    at,
                    item_ast_id.span,
                    expected_kind,
                    item_kind_to_str(resolved_item),
                    resolved_item,
                );
                None
            } else if self.check_resolved_item(
                at,
                item_ast_id.span,
                item_path_pkg_key,
                resolved_star_import.resolved_pkg_key,
                resolved_item,
                item_ast_id.id,
            ) {
                Some(resolved_item)
            } else {
                None
            };
        } else if accessible_items_with_same_name.is_empty() {
            if inaccessible_items_with_same_name.is_empty() {
                self.add_unresolved_name_err_with_possible_paths(
                    at,
                    item_ast_id.span,
                    item_ast_id.id,
                    |name| {
                        (
                            format!("لم يتم العثور على {} بالاسم `{}`", expected_kind, name),
                            format!(""),
                        )
                    },
                );
            } else if inaccessible_items_with_same_name.len() == 1 {
                let (star_import, item) = inaccessible_items_with_same_name.first().unwrap();

                let item = **item;

                let mut note_code_window =
                    CodeWindow::new(&self.files_infos[at], star_import.pkg_path_span.start);

                note_code_window.mark_note(star_import.pkg_path_span, vec![]);

                let item_kind_str = item_kind_to_str(item);

                let note = Diagnostic::note(
                    format!(
                        "تم استيراد {} `{}` هنا ضمنياً",
                        item_kind_str, self.id_pool[item_ast_id.id]
                    ),
                    vec![note_code_window],
                );

                let reason = match item {
                    Item::Const { .. } | Item::Static { .. } => "لأنه خاص بالحزمة التابع لها",
                    Item::Fn { .. } => "لأنها خاصة بالحزمة التابعة لها",
                    _ => unreachable!(),
                };

                let mut diagnostic =
                    self.unresolved_name_err(at, item_ast_id.span, item_ast_id.id, |name| {
                        (
                            format!("لا يُمكن الوصول إلى {} `{}` {}", item_kind_str, name, reason),
                            format!(""),
                        )
                    });

                diagnostic.chain(note);

                self.diagnostics.push(diagnostic);
            } else {
                let mut help_code_window = CodeWindow::new(
                    &self.files_infos[at],
                    inaccessible_items_with_same_name
                        .first()
                        .unwrap()
                        .0
                        .pkg_path_span
                        .start,
                );

                for (star_import, _item) in inaccessible_items_with_same_name {
                    help_code_window.mark_help(star_import.pkg_path_span, vec![]);
                }

                let help = Diagnostic::help(
                    format!("تم استيراد ضمنياً عناصر مشابهة من المسارات الآتية ولكنها خاصة بالحزم التابعة لها"),
                    vec![help_code_window],
                );

                let mut diagnostic =
                    self.unresolved_name_err(at, item_ast_id.span, item_ast_id.id, |name| {
                        (
                            format!("لم يتم العثور على {} بالاسم `{}`", expected_kind, name),
                            format!(""),
                        )
                    });

                diagnostic.chain(help);

                self.diagnostics.push(diagnostic);
            }

            return None;
        }

        let name = &self.id_pool[item_ast_id.id];

        let mut code_window = CodeWindow::new(&self.files_infos[at], item_ast_id.span.start);

        code_window.mark_error(
            item_ast_id.span,
            vec!["يوجد أكثر من عنصر بنفس الاسم تم استيرادهم ضمنياً".to_string()],
        );

        let note_msg = match accessible_items_with_same_name.len() {
            2 => {
                format!("تم استيراد عنصرين بنفس الاسم `{}` من المسارات التالية", name)
            }
            n @ 3..=10 => {
                format!(
                    "تم استيراد {} عناصر بنفس الاسم `{}` من المسارات التالية",
                    n, name
                )
            }
            n => {
                format!(
                    "تم استيراد {} عنصر بنفس الاسم `{}` من المسارات التالية",
                    n, name
                )
            }
        };

        let mut note = Diagnostic::note(note_msg, vec![]);

        let mut help_code_window = CodeWindow::new(
            &self.files_infos[at],
            accessible_items_with_same_name
                .first()
                .unwrap()
                .0
                .pkg_path_span
                .start,
        );

        for (resolved_star_import, _resolved_item) in accessible_items_with_same_name {
            help_code_window.mark_note(resolved_star_import.pkg_path_span, vec!["".to_string()]);
        }

        note.push_code_window(help_code_window);

        let msg = format!(
            "الاسم `{}` قد تكرر في الملف ضمنياً، فلا يمكن تحديد أي عنصر يجب استخدامه",
            name
        );

        let mut diagnostic = Diagnostic::error(msg, vec![code_window]);

        diagnostic.chain(note);

        self.diagnostics.push(diagnostic);

        None
    }

    fn resolve_item_path(
        &mut self,
        ItemPath {
            pkg_path,
            item: item_ast_id,
            top_pkg_span: _,
        }: ItemPath,
    ) -> Option<(PkgKey, Item)> {
        let empty_path = pkg_path.ids.is_empty();

        let file_key = pkg_path.file_key;

        let item_pkg_key = self.resolve_pkg_path(pkg_path)?;

        if let Some(item) = self.ast.state.pkgs_to_items[item_pkg_key].get(&item_ast_id.id) {
            Some((item_pkg_key, *item))
        } else {
            self.add_unresolved_name_err_with_possible_paths(
                file_key,
                item_ast_id.span,
                item_ast_id.id,
                |name| {
                    if empty_path {
                        (format!("لم يتم العثور على الاسم `{name}`"), format!(""))
                    } else {
                        (
                            format!("لم يتم العثور على الاسم `{name}` في المسار"),
                            format!("هذا الاسم غير موجود داخل المسار المحدد"),
                        )
                    }
                },
            );
            None
        }
    }

    fn resolve_pkg_path(&mut self, pkg_path: PkgPath) -> Option<PkgKey> {
        match self.pkgs.get(&pkg_path.ids) {
            Some(item_pkg_key) => Some((*item_pkg_key).into()),
            None => {
                self.add_unresolved_name_pkg_path_err(pkg_path);
                None
            }
        }
    }

    fn check_resolved_item(
        &mut self,
        at: FileKey,
        at_span: Span,
        at_pkg_key: PkgKey,
        item_pkg_key: PkgKey,
        resolved_item: Item,
        item_id: IdKey,
    ) -> bool {
        match resolved_item {
            Item::Pkg => {
                self.add_pkgs_cannot_be_imported_err(at, at_span);
                false
            }
            Item::Struct { vis, .. }
            | Item::Const { vis, .. }
            | Item::Static { vis, .. }
            | Item::Fn { vis, .. }
                if matches!(vis, VisModifier::Default) && item_pkg_key != at_pkg_key =>
            {
                self.add_encapsulation_err(at, at_span, resolved_item, item_id);
                false
            }
            _ => true,
        }
    }

    fn add_unexpected_item_kind_err(
        &mut self,
        at: FileKey,
        at_span: Span,
        expected_kind: &str,
        found_kind: &str,
        item: Item,
    ) {
        let msg = format!("يُتوقع {} ولكن تم العثور على {}", expected_kind, found_kind);

        let file_info = &self.files_infos[at];
        let mut code_window = CodeWindow::new(file_info, at_span.start);
        code_window.mark_error(at_span, vec![]);

        let mut diagnostic = Diagnostic::error(msg, vec![code_window]);

        if !matches!(
            item,
            Item::Pkg
                | Item::LocalVar { .. }
                | Item::FnParam { .. }
                | nazmc_ast::Item::LambdaParam { .. }
        ) {
            let help = self.help_diagnostic_to_find_item(item);
            diagnostic.chain(help);
        }

        self.diagnostics.push(diagnostic);
    }

    fn unresolved_name_err(
        &mut self,
        at: FileKey,
        at_span: Span,
        id: IdKey,
        fmt_msg_and_label: impl Fn(&String) -> (String, String),
    ) -> Diagnostic<'a> {
        let file_info = &self.files_infos[at];
        let name = &self.id_pool[id];
        let (msg, label) = fmt_msg_and_label(name);

        let mut code_window = CodeWindow::new(file_info, at_span.start);

        code_window.mark_error(at_span, vec![label]);

        let diagnostic = Diagnostic::error(msg, vec![code_window]);

        diagnostic
    }

    fn add_unresolved_name_err_with_possible_paths(
        &mut self,
        at: FileKey,
        at_span: Span,
        id: IdKey,
        fmt_msg_and_label: impl Fn(&String) -> (String, String),
    ) {
        let mut diagnostic = self.unresolved_name_err(at, at_span, id, fmt_msg_and_label);

        let mut possible_paths = vec![];

        for (pkg_key, pkg_to_items) in self.ast.state.pkgs_to_items.iter_enumerated() {
            if let Some(found_item) = pkg_to_items.get(&id) {
                if matches!(found_item, Item::Pkg) {
                    continue;
                }
                let found_item = *found_item;
                let item_info = self.get_item_info(found_item);
                let item_file = &self.files_infos[item_info.file_key];
                let item_span_cursor = item_info.id_span.start;
                let item_kind_str = item_kind_to_str(found_item);

                let pkg_name = self.fmt_pkg_name(pkg_key);
                let name = &self.id_pool[id];
                let item_path = format!(
                    "{}:{}:{}",
                    &item_file.path,
                    item_span_cursor.line + 1,
                    item_span_cursor.col + 1
                );
                let path = format!(
                    "\t- {} {}::{} في {}",
                    item_kind_str, pkg_name, name, item_path
                );

                possible_paths.push(path);
            }
        }

        if !possible_paths.is_empty() {
            let mut help = Diagnostic::help(
                format!("تم العثور على عناصر مشابهة بنفس الاسم في المسارات التالية:"),
                vec![],
            );

            for t in possible_paths {
                help.chain_free_text(t);
            }

            diagnostic.chain(help);
        }

        self.diagnostics.push(diagnostic);
    }

    fn add_unresolved_name_pkg_path_err(
        &mut self,
        PkgPath {
            pkg_key: _,
            file_key,
            mut ids,
            mut spans,
        }: PkgPath,
    ) {
        while let Some(first_invalid_seg_id) = ids.pop() {
            let first_invalid_seg_span = spans.pop().unwrap();

            if self.pkgs.contains_key(&ids) {
                self.add_unresolved_name_err_with_possible_paths(
                    file_key,
                    first_invalid_seg_span,
                    first_invalid_seg_id,
                    |name| {
                        (
                            format!("لم يتم العثور على الاسم `{name}` في المسار"),
                            format!("هذا الاسم غير موجود داخل المسار المحدد"),
                        )
                    },
                );
                return;
            }
        }
    }

    fn add_encapsulation_err(
        &mut self,
        at: FileKey,
        at_span: Span,
        resolved_item: Item,
        name: IdKey,
    ) {
        let file_info = &self.files_infos[at];
        let name = &self.id_pool[name];
        let msg = match resolved_item {
            Item::Struct { .. } => {
                format!(
                    "لا يمكن الوصول إلى الهيكل `{}` لأنه خاص بالحزمة التابع لها",
                    name
                )
            }
            Item::Const { .. } => {
                format!(
                    "لا يمكن الوصول إلى الثابت `{}` لأنه خاص بالحزمة التابع لها",
                    name
                )
            }
            Item::Static { .. } => {
                format!(
                    "لا يمكن الوصول إلى المشترك `{}` لأنه خاص بالحزمة التابع لها",
                    name
                )
            }
            Item::Fn { .. } => format!(
                "لا يمكن الوصول إلى الدالة `{}` لأنها خاصة بالحزمة التابعة لها",
                name
            ),
            _ => {
                unreachable!()
            }
        };

        let mut code_window = CodeWindow::new(file_info, at_span.start);
        code_window.mark_error(at_span, vec![]);
        let help = self.help_diagnostic_to_find_item(resolved_item);

        let mut diagnostic = Diagnostic::error(msg, vec![code_window]);
        diagnostic.chain(help);
        self.diagnostics.push(diagnostic);
    }

    fn add_pkgs_cannot_be_imported_err(&mut self, at: FileKey, at_span: Span) {
        let file_info = &self.files_infos[at];
        let msg = format!("الحزم لا يمكن إستيرادها");
        let mut code_window = CodeWindow::new(file_info, at_span.start);
        code_window.mark_error(
            at_span,
            vec!["يجب أن يؤول المسار إلى عنصر (دالة أو هيكل) وليس حزمة".to_string()],
        );
        let diagnostic = Diagnostic::error(msg, vec![code_window]);
        self.diagnostics.push(diagnostic);
    }

    fn help_diagnostic_to_find_item(&self, item: Item) -> Diagnostic<'a> {
        let item_kind_str = item_kind_to_str(item);
        let help_msg = format!("تم العثور على ال{} هنا", item_kind_str);
        let resolved_item_info = self.get_item_info(item);
        let file_of_resolved_item = &self.files_infos[resolved_item_info.file_key];
        let mut help_code_window =
            CodeWindow::new(file_of_resolved_item, resolved_item_info.id_span.start);
        help_code_window.mark_help(resolved_item_info.id_span, vec![]);
        Diagnostic::help(help_msg, vec![help_code_window])
    }

    fn get_item_info(&self, item: Item) -> ItemInfo {
        match item {
            Item::Struct { key, .. } => self.ast.structs[key].info,
            Item::Const { key, .. } => self.ast.consts[key].info,
            Item::Static { key, .. } => self.ast.statics[key].info,
            Item::Fn { key, .. } => self.ast.fns[key].info,
            Item::Pkg
            | Item::LocalVar { .. }
            | Item::FnParam { .. }
            | nazmc_ast::Item::LambdaParam { .. } => {
                unreachable!()
            }
        }
    }

    fn fmt_pkg_name(&self, pkg_key: PkgKey) -> String {
        self.pkgs_names[pkg_key]
            .iter()
            .map(|id| self.id_pool[*id].as_str())
            .collect::<Vec<_>>()
            .join("::")
    }
}

#[inline]
fn item_kind_to_str(item: Item) -> &'static str {
    match item {
        Item::Pkg => "حزمة",
        Item::Struct { .. } => "هيكل",
        Item::Const { .. } => "ثابت",
        Item::Static { .. } => "مشترك",
        Item::Fn { .. } => "دالة",
        Item::LocalVar { .. } | Item::FnParam { .. } | nazmc_ast::Item::LambdaParam { .. } => {
            unreachable!()
        }
    }
}
