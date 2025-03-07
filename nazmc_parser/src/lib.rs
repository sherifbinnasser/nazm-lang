pub use ast_validator::ASTValidator;
use error::*;
use nazmc_data_pool::{FileKey, PkgKey};
use nazmc_diagnostics::{
    file_info::FileInfo, fmt_diagnostics, span::SpanCursor, CodeWindow, Diagnostic,
};
use nazmc_lexer::*;
use syntax::File;

mod ast_validator;
pub(crate) mod parse_methods;
pub(crate) mod syntax;
pub(crate) mod tokens_iter;
pub(crate) use nazmc_diagnostics::span::Span;
pub(crate) use nazmc_parse_derive::*;
pub(crate) use parse_methods::*;
pub(crate) use syntax::*;
pub(crate) use tokens_iter::TokensIter;

pub fn parse(
    tokens: Vec<Token>,
    file_info: &FileInfo,
    file_content: &str,
    lexer_errors: Vec<LexerError>,
    ast_validator: &mut ASTValidator,
    pkg_key: PkgKey,
    file_key: FileKey,
) -> Result<(), String> {
    let mut reporter = ParseErrorsReporter {
        file_info,
        file_content,
        tokens: &tokens,
        diagnostics: vec![],
    };

    reporter.report_lexer_errors(&lexer_errors);

    let mut tokens_iter = TokensIter::new(&tokens, &file_content);

    tokens_iter.next_non_space_or_comment(); // To init recent()

    let file = ParseResult::<File>::parse(&mut tokens_iter).unwrap();

    reporter.check_file_items(&file.content.items);

    if reporter.diagnostics.is_empty() {
        ast_validator.pkg_key = pkg_key;
        ast_validator.file_key = file_key;
        ast_validator.lower_file(file);

        Ok(())
    } else {
        Err(fmt_diagnostics(reporter.diagnostics))
    }
}

struct ParseErrorsReporter<'a> {
    tokens: &'a [Token],
    file_info: &'a FileInfo,
    file_content: &'a str,
    diagnostics: Vec<Diagnostic<'a>>,
}

impl<'a> ParseErrorsReporter<'a> {
    fn report(
        &mut self,
        msg: String,
        span: Span,
        primary_label: String,
        secondary_labels: Vec<(Span, Vec<String>)>,
    ) {
        let mut code_window = CodeWindow::new(self.file_info, span.start);

        code_window.mark_error(span, vec![primary_label]);

        for (span, multiline_label) in secondary_labels {
            code_window.mark_secondary(span, multiline_label);
        }

        let diagnostic = Diagnostic::error(msg, vec![code_window]);

        self.diagnostics.push(diagnostic);
    }

    fn report_lexer_errors(&mut self, lexer_errors: &[LexerError]) {
        for err in lexer_errors {
            let token_span = self.tokens[err.token_idx].span;

            let err_span = if err.len > 0 {
                Span {
                    start: SpanCursor {
                        line: token_span.start.line,
                        col: err.col,
                    },
                    end: SpanCursor {
                        line: token_span.end.line,
                        col: err.col + err.len,
                    },
                }
            } else {
                token_span
            };

            match &err.kind {
                LexerErrorKind::UnknownToken => {
                    self.report(
                        "رمز غير مدعوم".to_string(),
                        err_span,
                        "".to_string(),
                        vec![],
                    );
                }
                LexerErrorKind::UnclosedStr => {
                    self.report(
                        "علامة تنصيص مفقودة".to_string(),
                        err_span,
                        "قٌم بإضافة `\"`".to_string(),
                        vec![(
                            Span {
                                start: token_span.start,
                                end: SpanCursor {
                                    line: token_span.start.line,
                                    col: token_span.start.col + 1,
                                },
                            },
                            vec!["لم يتم إغلاق علامة التنصيص هذه".to_string()],
                        )],
                    );
                }
                LexerErrorKind::UnclosedChar => {
                    self.report(
                        "علامة تنصيص مفقودة".to_string(),
                        err_span,
                        "قٌم بإضافة `\'`".to_string(),
                        vec![(
                            Span {
                                start: token_span.start,
                                end: SpanCursor {
                                    line: token_span.start.line,
                                    col: token_span.start.col + 1,
                                },
                            },
                            vec!["لم يتم إغلاق علامة التنصيص هذه".to_string()],
                        )],
                    );
                }
                LexerErrorKind::UnclosedDelimitedComment => self.report(
                    "لم يتم إغلاق التعليق".to_string(),
                    err_span,
                    "تم بدء التعليق هنا".to_string(),
                    vec![],
                ),
                LexerErrorKind::ZeroChars => self.report(
                    "لا يوجد حروف ولكن يُتوقع حرف واحد بين علامتي التنصيص".to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::ManyChars => self.report(
                    "يوجد أكثر من حرف ولكن يُتوقع حرف واحد بين علامتي التنصيص".to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::KufrOrInvalidChar => self.report(
                    "يحتوي على رمز كُفر أو رمز غير مدعوم".to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::UnicodeCodePointHexDigitOnly => self.report(
                    "رمز اليونيكود يجب أن يحتوي فقط على أرقام بالنظام العددي السُداسي عشر"
                        .to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::InvalidUnicodeCodePoint => self.report(
                    "رمز يونيكود غير صالح".to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::UnknownEscapeSequence => self.report(
                    "حرف تسلسل غير صالح".to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::MissingDigitsAfterBasePrefix => self.report(
                    "يُتوقع أرقام بعد رمز النظام العددي".to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::MissingDigitsAfterExponent => self.report(
                    "يُتوقع أرقام الأس".to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::InvalidIntBasePrefix => self.report(
                    "نظام عددي غير مدعوم".to_string(),
                    err_span,
                    "".to_string(),
                    vec![],
                ),
                LexerErrorKind::InvalidNumSuffix => {
                    self.report(
                        "لاحقة غير صحيحة للعدد".to_string(),
                        err_span,
                        "".to_string(),
                        vec![],
                    );

                    self.diagnostics.last_mut().unwrap().chain(Diagnostic::help(
                        "اللاحقات الصالحة للعدد هى (ص، ص1، ص2، ص4، ص8، ط، ط1، ط2، ط4، ط8، ع4، ع8)"
                            .to_string(),
                        vec![],
                    ));
                }
                LexerErrorKind::InvalidFloatSuffix => {
                    self.report(
                        "لاحقة غير صحيحة للعدد العشري".to_string(),
                        err_span,
                        "".to_string(),
                        vec![],
                    );

                    self.diagnostics.last_mut().unwrap().chain(Diagnostic::help(
                        "اللاحقات الصالحة للعدد العشري هى (ع4، ع8)".to_string(),
                        vec![],
                    ));
                }
                LexerErrorKind::InvalidIntSuffix => {
                    self.report(
                        "لاحقة غير صالحة للعدد الصحيح".to_string(),
                        err_span,
                        "".to_string(),
                        vec![],
                    );

                    self.diagnostics.last_mut().unwrap().chain(Diagnostic::help(
                        "اللاحقات الصالحة للعدد الصحيح هى (ص، ص1، ص2، ص4، ص8، ط، ط1، ط2، ط4، ط8)"
                            .to_string(),
                        vec![],
                    ));
                }
                LexerErrorKind::InvalidDigitForBase(base) => {
                    let base_str = match base {
                        crate::Base::Bin => "الثُنائي",
                        crate::Base::Oct => "الثُماني",
                        crate::Base::Dec => "العَشري",
                        crate::Base::Hex => "السُداسي عشر",
                    };
                    self.report(
                        format!("رقم غير صالح في النظام العددي {}", base_str),
                        err_span,
                        "".to_string(),
                        vec![],
                    )
                }
                LexerErrorKind::NumIsOutOfRange(num_kind) => {
                    self.report(
                        "قيمة العدد خارج النطاق المسموح به".to_string(),
                        err_span,
                        "".to_string(),
                        vec![],
                    );

                    let max_num_str = match num_kind {
                        NumKind::F4(_) => f32::MAX.to_string(),
                        NumKind::F8(_) | NumKind::UnspecifiedFloat(_) => f64::MAX.to_string(),
                        NumKind::I(_) => isize::MAX.to_string(),
                        NumKind::I1(_) => i8::MAX.to_string(),
                        NumKind::I2(_) => i16::MAX.to_string(),
                        NumKind::I4(_) => i32::MAX.to_string(),
                        NumKind::I8(_) => i64::MAX.to_string(),
                        NumKind::U(_) => usize::MAX.to_string(),
                        NumKind::U1(_) => u8::MAX.to_string(),
                        NumKind::U2(_) => u16::MAX.to_string(),
                        NumKind::U4(_) => u32::MAX.to_string(),
                        NumKind::U8(_) | NumKind::UnspecifiedInt(_) => u64::MAX.to_string(),
                    };

                    self.diagnostics.last_mut().unwrap().chain(Diagnostic::help(
                        format!("أكبر قيمة من نفس نوع العدد هى `{}`", max_num_str),
                        vec![],
                    ));
                }
                LexerErrorKind::DigitsEndWithCommma => {
                    let (msg, label) = if err.len > 1 {
                        (
                            "تم العثور على فواصل `,` بعد الأرقام",
                            "قُم بإزالة هذه الفواصل",
                        )
                    } else {
                        (
                            "تم العثور على فاصلة `,` بعد الأرقام",
                            "قُم بإزالة هذه الفاصلة",
                        )
                    };
                    self.report(msg.to_string(), err_span, label.to_string(), vec![]);
                }
            };
        }
    }

    fn report_expected(
        &mut self,
        expected: &str,
        err: &ParseErr,
        secondary_labels: Vec<(Span, Vec<String>)>,
    ) {
        let (found_token_span, found_token_val, primary_label) =
            if err.found_token_index < self.tokens.len() {
                let token = &self.tokens[err.found_token_index];
                (
                    token.span,
                    &self.file_content[token.start_byte..token.end_byte],
                    "رمز غير متوقع".to_string(),
                )
            } else {
                let last_span = self.tokens[self.tokens.len() - 1].span;
                (
                    Span::len_after(&last_span, 1),
                    "نهاية الملف",
                    "تم الوصول إلى نهاية الملف".to_string(),
                )
            };

        let msg = format!(
            "يُتوقع {}، ولكن تم العثور على `{}`",
            expected, found_token_val
        );

        self.report(msg, found_token_span, primary_label, secondary_labels);
    }

    fn report_expected_comma_or_item(
        &mut self,
        expected: &str,
        err: &ParseErr,
        secondary_labels: Vec<(Span, Vec<String>)>,
    ) {
        // Here we try to find if the error was occured as the comma is not found (so display that comma is expected)
        // or the comma is found but the the item after it is missing (so display that item is expected)
        let comma_err = 'label: {
            if err.found_token_index < self.tokens.len() {
                if let TokenKind::Symbol(SymbolKind::Comma) =
                    self.tokens[err.found_token_index].kind
                {
                    let mut i = err.found_token_index + 1;
                    while i < self.tokens.len() {
                        match &self.tokens[i].kind {
                            TokenKind::Eol
                            | TokenKind::DelimitedComment
                            | TokenKind::LineComment
                            | TokenKind::Space => i += 1,
                            _ => break,
                        }
                    }

                    break 'label ParseErr {
                        found_token_index: i,
                    };
                }
                err.clone()
            } else {
                err.clone()
            }
        };

        let expected = if comma_err.found_token_index > err.found_token_index {
            expected
        } else {
            "فاصلة `،`"
        };

        self.report_expected(expected, &comma_err, secondary_labels);
    }

    fn report_unclosed_delimiter(&mut self, open_delim_span: Span) {
        self.report(
            "لم يتم إغلاق القوس".to_string(),
            open_delim_span,
            "يجب إغلاق هذا القوس".to_string(),
            vec![],
        );
    }

    fn check_import_stm(&mut self, import_stm: &ImportStm) {
        let mut last_star_symbol_span = None;

        match &import_stm.sec {
            Ok(a) => match &a.seg {
                Ok(b) => {
                    if let PathSegInImportStm::Star(s) = b {
                        last_star_symbol_span = Some(s.span)
                    }
                }
                Err(err) => self.report_expected("اسم أو `*`", err, vec![]),
            },
            Err(err) => {
                if let Some(id) = &import_stm.top {
                    self.report(
                        "يُتوقع `::` ثم اسم عنصر أو `*` بعد الحزمة".to_string(),
                        id.span,
                        "قُم بعدها بإضافة `::` ثم اسم عنصر أو `*`".to_string(),
                        vec![],
                    );
                } else {
                    self.report_expected("اسم أو `::`", err, vec![])
                }

                return;
            }
        }

        for seg in &import_stm.segs {
            match &seg.seg {
                Ok(a) => {
                    if let PathSegInImportStm::Star(s) = a {
                        if let Some(span) = last_star_symbol_span {
                            self.report(
                                "الرمز `*` يجب أن يكون في آخر المسار".to_string(),
                                span,
                                "".to_string(),
                                vec![],
                            );
                            return;
                        }
                        last_star_symbol_span = Some(s.span)
                    }
                }
                Err(err) => {
                    self.report_expected("اسم أو `*`", err, vec![]);
                    return;
                }
            }
        }

        if let Some(alias) = &import_stm.alias {
            if last_star_symbol_span.is_some() {
                self.report(
                    "يُتوقع فاصلة منقوطة `؛`، ولكن تم العثور على `على`".to_string(),
                    alias.on.span,
                    "رمز غير متوقع".to_string(),
                    vec![],
                );
                return;
            }

            if let Err(err) = &alias.id {
                self.report_expected("مُعرِّف", err, vec![]);
            }
        }

        self.check_semicolon_result(&import_stm.semicolon);
    }

    fn check_file_items(&mut self, items: &[ParseResult<FileItem>]) {
        let expected = "عنصر ملف (دالة أو هيكل)";
        for item in items {
            let node = match item {
                Ok(node) => node,
                Err(err) => {
                    self.report_expected(expected, err, vec![]);
                    continue;
                }
            };

            let item = match node {
                FileItem::ImportStm(import_stm) => {
                    self.check_import_stm(import_stm);
                    continue;
                }
                FileItem::WithVisModifier(ItemWithVisibility { visibility, item }) => match item {
                    Ok(item) => item,
                    Err(_) => {
                        self.report(
                            "يُتوقع عنصر ملف (دالة أو هيكل) بعد مُعامِل الوصول".to_string(),
                            visibility.span,
                            "مُعامِل الوصول".to_string(),
                            vec![],
                        );
                        continue;
                    }
                },
                FileItem::WithoutModifier(item) => item,
            };

            match item {
                Item::Const(_const) => self.check_const_static_stm_body(&_const.body),
                Item::Static(_static) => self.check_const_static_stm_body(&_static.body),
                Item::Struct(s) => self.check_struct(s),
                Item::Fn(f) => self.check_fn(f),
            }
        }
    }

    fn check_const_static_stm_body(&mut self, body: &ParseResult<ConstStaticStmBody>) {
        let body = match body {
            Ok(body) => body,
            Err(err) => {
                self.report_expected("مُعرِّف", err, vec![]);
                return;
            }
        };

        if let Err(err) = &body.colon {
            self.report_expected("`:`", err, vec![]);
            return;
        }

        self.check_type_result(&body.typ);

        if let Err(err) = &body.equal {
            self.report_expected("`=`", err, vec![]);
            return;
        }

        self.check_expr_result(&body.expr);

        self.check_semicolon_result(&body.semicolon);
    }

    fn check_struct(&mut self, s: &Struct) {
        let Struct {
            struct_keyword,
            name,
            kind,
        } = s;

        let missing_name = name.is_err();
        let missing_decl = kind.is_err();

        if missing_name && missing_decl {
            self.report(
                "لم يتم تعريف الهيكل".to_string(),
                struct_keyword.span,
                "".to_string(),
                vec![],
            );
            return;
        }

        if missing_name {
            self.report(
                "يجب إعطاء اسم للهيكل".to_string(),
                struct_keyword.span,
                "".to_string(),
                vec![],
            );
        }

        let kind = match kind {
            Ok(kind) => kind,
            Err(err) => {
                self.report_expected("بعد الهيكل `؛` أو `{` أو `(`", err, vec![]);
                return;
            }
        };

        match kind {
            StructKind::Unit(_) => {}
            StructKind::Tuple(TupleStructFields {
                open_delim,
                items,
                close_delim,
            }) => {
                if let Some(PunctuatedTupleStructField {
                    first_item,
                    rest_items,
                    trailing_comma: _,
                }) = items
                {
                    match first_item {
                        Ok(TupleStructField { visibility: _, typ }) => self.check_type_result(typ),
                        Err(err) => {
                            self.report_expected("نوع", err, vec![]);
                        }
                    }

                    for field in rest_items {
                        match field {
                            Ok(CommaWithTupleStructField {
                                comma: _,
                                item: TupleStructField { visibility: _, typ },
                            }) => self.check_type_result(typ),
                            Err(err) => {
                                self.report_expected_comma_or_item("نوع", err, vec![]);
                            }
                        }
                    }
                }
                if close_delim.is_err() {
                    self.report_unclosed_delimiter(open_delim.span);
                }
            }
            StructKind::Fields(StructFields {
                open_delim,
                items,
                close_delim,
            }) => {
                if let Some(PunctuatedStructField {
                    first_item,
                    rest_items,
                    trailing_comma: _,
                }) = &items
                {
                    match first_item {
                        Ok(StructField { typ, .. }) => match typ {
                            Ok(ColonWithType { colon: _, typ }) => self.check_type_result(typ),
                            Err(err) => self.report_expected("`:` ثم نوع الحقل", err, vec![]),
                        },
                        Err(err) => {
                            self.report_expected("حقل", err, vec![]);
                        }
                    }

                    for field in rest_items {
                        match field {
                            Ok(CommaWithStructField {
                                item: StructField { typ, .. },
                                ..
                            }) => match typ {
                                Ok(ColonWithType { colon: _, typ }) => self.check_type_result(typ),
                                Err(err) => self.report_expected("`:` ثم نوع الحقل", err, vec![]),
                            },
                            Err(err) => self.report_expected_comma_or_item("حقل", err, vec![]),
                        }
                    }
                }

                if close_delim.is_err() {
                    self.report_unclosed_delimiter(open_delim.span);
                }
            }
        }
    }

    fn check_fn(&mut self, f: &Fn) {
        let Fn {
            fn_keyword,
            name,
            params_decl,
            return_type,
            body,
        } = f;

        let missing_name = name.is_err();
        let missing_params = params_decl.is_err();
        let no_return_type = return_type.is_none();
        let missing_body = body.is_err();

        if missing_name && missing_params && no_return_type && missing_body {
            self.report(
                "لم يتم تعريف الدالة".to_string(),
                fn_keyword.span,
                "".to_string(),
                vec![],
            );
            return;
        }

        if missing_name {
            self.report(
                "يجب إعطاء اسم للدالة".to_string(),
                fn_keyword.span,
                "".to_string(),
                vec![],
            );
        }

        match params_decl {
            Ok(FnParams {
                open_delim,
                items,
                close_delim,
            }) => {
                if let Some(PunctuatedFnParam {
                    first_item,
                    rest_items,
                    trailing_comma: _,
                }) = items
                {
                    match first_item {
                        Ok(param) => match &param.typ {
                            Ok(node) => self.check_type_result(&node.typ),
                            Err(err) => {
                                self.report_expected("`:` ثم نوع مُعامِل الدالة", err, vec![])
                            }
                        },
                        Err(err) => self.report_expected("مُعامِل دالة", err, vec![]),
                    }

                    let mut last_was_ok = true; // To not report errors that are next to each other

                    for param in rest_items {
                        match param {
                            Ok(node) => {
                                match &node.item.typ {
                                    Ok(node) => self.check_type_result(&node.typ),
                                    Err(err) => {
                                        self.report_expected("نوع لمُعامِل الدالة", err, vec![])
                                    }
                                };
                                last_was_ok = true;
                            }
                            Err(err) if last_was_ok => {
                                self.report_expected_comma_or_item("مُعامِل دالة", err, vec![]);
                                last_was_ok = false;
                            }
                            _ => {}
                        }
                    }
                }

                if close_delim.is_err() {
                    self.report_unclosed_delimiter(open_delim.span);
                }
            }
            Err(err) if !missing_name => {
                self.report_expected("مُعامِلات الدالة", err, vec![]);
            }
            _ => {}
        };

        if let Some(node) = return_type {
            self.check_type_result(&node.typ);
        }

        match body {
            Ok(body) => {
                let Some(lambda_arrow) = &body.lambda_arrow else {
                    self.check_block(body);
                    return;
                };

                let span = match lambda_arrow {
                    LambdaArrow::NoParams(r_arrow) => r_arrow.span,
                    LambdaArrow::WithParams(LambdaParams {
                        first,
                        rest,
                        trailing_comma,
                        r_arrow,
                    }) => {
                        let first_span = match &first.kind {
                            BindingKind::Id(terminal) => terminal.span,
                            BindingKind::MutId(mut_id_binding) => mut_id_binding.mut_keyword.span,
                            BindingKind::Destructed(destructed_tuple) => {
                                destructed_tuple.open_delim.span
                            }
                        };

                        let start = first_span.start;

                        let end = if let Ok(Terminal { span, .. }) = r_arrow {
                            span.end
                        } else if let Some(Terminal { span, .. }) = trailing_comma {
                            span.end
                        } else if !rest.is_empty() {
                            match &rest[rest.len() - 1].item.kind {
                                BindingKind::Id(terminal) => terminal.span.end,
                                BindingKind::MutId(mut_id_binding) => match &mut_id_binding.id {
                                    Ok(id) => id.span.end,
                                    Err(_) => mut_id_binding.mut_keyword.span.end,
                                },
                                BindingKind::Destructed(destructed_tuple) => {
                                    destructed_tuple.open_delim.span.end
                                }
                            }
                        } else {
                            first_span.end
                        };

                        Span { start, end }
                    }
                };

                self.report(
                    "يُتوقع محتوى الدالة وليس مُعاملات لامدا".to_string(),
                    span,
                    "قٌم بإزالة هذا".to_string(),
                    vec![],
                );
            }
            Err(err) if !missing_params || !no_return_type => {
                self.report_expected("محتوى الدالة", err, vec![]);
            }
            _ => {}
        }
    }

    fn check_type_result(&mut self, typ: &ParseResult<Type>) {
        match typ {
            Ok(typ) => self.check_type(typ),
            Err(err) => self.report_expected("نوع", err, vec![]),
        }
    }

    fn check_type(&mut self, typ: &Type) {
        match typ {
            Type::Path(simple_path) => self.check_simple_path(simple_path),
            Type::Ptr(ptr_type) => self.check_type_result(&ptr_type.typ),
            Type::Ref(ref_type) => self.check_type_result(&ref_type.typ),
            Type::Slice(slice_type) => {
                self.check_type_result(&slice_type.typ);
                if let Some(ArraySizeExpr { semicolon: _, expr }) = &slice_type.array_size {
                    self.check_expr_result(expr);
                }
                if slice_type.close_bracket.is_err() {
                    self.report_unclosed_delimiter(slice_type.open_bracket.span);
                }
            }
            Type::Paren(paren_type) => {
                self.check_tuple_type(&paren_type.tuple);

                if let Some(LambdaType { r_arrow: _, typ }) = &paren_type.lambda {
                    self.check_type_result(typ);
                }
            }
        }
    }

    fn check_tuple_type(&mut self, tuple_type: &TupleType) {
        if let Some(PunctuatedType {
            first_item,
            rest_items,
            trailing_comma: _,
        }) = &tuple_type.items
        {
            self.check_type_result(first_item);

            for param in rest_items {
                match param {
                    Ok(node) => self.check_type(&node.item),
                    Err(err) => self.report_expected_comma_or_item("نوع", err, vec![]),
                }
            }
        }

        if tuple_type.close_delim.is_err() {
            self.report_unclosed_delimiter(tuple_type.open_delim.span);
        }
    }

    fn check_simple_path(&mut self, simple_path: &SimplePath) {
        for SimpleInnerPath {
            double_colons: _,
            inner,
        } in &simple_path.inners
        {
            if let Err(err) = inner {
                self.report_expected("مسار", err, vec![]);
            }
        }
    }

    fn check_binding(&mut self, binding: &Binding) {
        self.check_binding_kind(&binding.kind);
        if let Some(ColonWithType { colon: _, typ }) = &binding.typ {
            self.check_type_result(typ);
        }
    }

    fn check_binding_kind(&mut self, binding_kind: &BindingKind) {
        if let BindingKind::MutId(MutIdBinding { mut_keyword: _, id }) = binding_kind {
            if let Err(err) = id {
                self.report_expected("مُعرِّف", err, vec![]);
                return;
            }
        }
        if let BindingKind::Destructed(destructed_tuple) = binding_kind {
            if let Some(PunctuatedBindingKind {
                first_item,
                rest_items,
                trailing_comma: _,
            }) = &destructed_tuple.items
            {
                match first_item {
                    Ok(binding_kind) => self.check_binding_kind(binding_kind),
                    Err(err) => self.report_expected("مُعرِّف", err, vec![]),
                }

                for result in rest_items {
                    match result {
                        Ok(CommaWithBindingKind { comma: _, item }) => {
                            self.check_binding_kind(item)
                        }
                        Err(err) => self.report_expected_comma_or_item("مُعرِّف", err, vec![]),
                    }
                }
            }
            if destructed_tuple.close_delim.is_err() {
                self.report_unclosed_delimiter(destructed_tuple.open_delim.span);
            }
        }
    }

    fn check_block(&mut self, lambda: &LambdaExpr) {
        let LambdaExpr {
            open_curly,
            lambda_arrow: _,
            stms,
            last_expr,
            close_curly,
        } = lambda;

        for stm_result in stms {
            match stm_result {
                Ok(stm) => match stm {
                    Stm::Semicolon(_) => {}
                    Stm::Let(LetStm {
                        let_keyword: _,
                        binding,
                        let_assign,
                        semicolon,
                    }) => {
                        match binding {
                            Ok(binding) => self.check_binding(binding),
                            Err(err) => self.report_expected("مُعرِّف", err, vec![]),
                        }

                        if let Some(LetAssign { equal: _, expr }) = let_assign {
                            self.check_expr_result(expr);
                            if expr.is_ok() {
                                self.check_semicolon_result(semicolon);
                            }
                        } else {
                            self.check_semicolon_result(semicolon);
                        }
                    }
                    Stm::While(while_stm) => {
                        match &while_stm.conditional_block.condition {
                            Ok(expr) => self.check_expr(expr),
                            Err(err) => {
                                self.report_expected("تعبير برمجي (شرط `طالما`)", err, vec![])
                            }
                        }

                        match &while_stm.conditional_block.block {
                            Ok(block) => self.check_block(block),
                            Err(err) => self.report_expected("محتوى `طالما`", err, vec![]),
                        }
                    }
                    Stm::If(if_expr) => self.check_if_expr(if_expr),
                    Stm::When(when_expr) => self.check_when_expr(when_expr),
                    Stm::Expr(ExprStm { expr, semicolon }) => {
                        self.check_expr(expr);
                        self.check_semicolon_result(semicolon);
                    }
                },
                Err(err) => self.report_expected("جملة برمجية", err, vec![]),
            }
        }

        if let Some(expr) = last_expr {
            self.check_expr(expr);
        }

        if close_curly.is_err() {
            self.report_unclosed_delimiter(open_curly.span);
        }
    }

    fn check_semicolon_result(&mut self, semicolon: &ParseResult<SemicolonSymbol>) {
        if let Err(err) = semicolon {
            let mut i = err.found_token_index - 1;
            while let TokenKind::Eol
            | TokenKind::DelimitedComment
            | TokenKind::LineComment
            | TokenKind::Space = &self.tokens[i].kind
            {
                i -= 1;
            }

            let (found_token_span, found_token_val, secondary_label) =
                if err.found_token_index < self.tokens.len() {
                    let token = &self.tokens[err.found_token_index];
                    (
                        token.span,
                        &self.file_content[token.start_byte..token.end_byte],
                        "رمز غير متوقع".to_string(),
                    )
                } else {
                    let last_span = self.tokens[self.tokens.len() - 1].span;
                    (
                        Span::len_after(&last_span, 1),
                        "نهاية الملف",
                        "تم الوصول إلى نهاية الملف".to_string(),
                    )
                };

            let msg = format!(
                "يُتوقع فاصلة منقوطة `؛`، ولكن تم العثور على `{}`",
                found_token_val
            );

            self.report(
                msg,
                Span::len_after(&self.tokens[i].span, 1),
                "قُم هنا بإضافة فاصلة منقوطة `؛`".to_string(),
                vec![(found_token_span, vec![secondary_label.to_string()])],
            );
        }
    }

    fn check_expr_result(&mut self, expr: &ParseResult<Expr>) {
        match expr {
            Ok(expr) => self.check_expr(expr),
            Err(err) => self.report_expected("تعبير برمجي", err, vec![]),
        }
    }

    fn check_expr(&mut self, expr: &Expr) {
        self.check_primary_expr(&expr.left);
        for bin_expr in &expr.bin {
            match &bin_expr.right {
                Ok(expr) => self.check_primary_expr(expr),
                Err(err) => self.report_expected("تعبير برمجي", err, vec![]),
            }
        }
    }

    fn check_primary_expr(&mut self, expr: &PrimaryExpr) {
        match &expr.kind {
            PrimaryExprKind::Unary(unary_expr) => match &unary_expr.expr {
                Ok(expr) => self.check_primary_expr(expr),
                Err(err) => self.report_expected("تعبير برمجي", err, vec![]),
            },
            PrimaryExprKind::Atomic(expr) => self.check_atomic_expr(expr),
        }

        self.check_post_ops(&expr.post_ops);

        for InnerAccessExpr {
            dot: _,
            field,
            post_ops,
        } in &expr.inner_access
        {
            if let Err(err) = field {
                self.report_expected("مُعرِّف", err, vec![]);
            }

            self.check_post_ops(post_ops);
        }
    }

    fn check_post_ops(&mut self, post_ops: &[PostOpExpr]) {
        for post_op_expr in post_ops {
            match post_op_expr {
                PostOpExpr::Invoke(paren_expr) => self.check_paren_expr(paren_expr),
                PostOpExpr::Lambda(lambda_expr) => self.check_lambda_expr(lambda_expr),
                PostOpExpr::Index(IdxExpr {
                    open_bracket,
                    expr,
                    close_bracket,
                }) => {
                    self.check_expr_result(expr);

                    if close_bracket.is_err() {
                        self.report_unclosed_delimiter(open_bracket.span);
                    }
                }
            }
        }
    }

    fn check_atomic_expr(&mut self, expr: &AtomicExpr) {
        match expr {
            AtomicExpr::Literal(_)
            | AtomicExpr::On(_)
            | AtomicExpr::Continue(_)
            | AtomicExpr::Break(_) => {}
            AtomicExpr::Paren(paren_expr) => self.check_paren_expr(paren_expr),
            AtomicExpr::Path(simple_path) => self.check_simple_path(simple_path),
            AtomicExpr::Lambda(lambda_expr) => self.check_lambda_expr(lambda_expr),
            AtomicExpr::If(if_expr) => self.check_if_expr(if_expr),
            AtomicExpr::When(when_expr) => self.check_when_expr(when_expr),
            AtomicExpr::Return(ReturnExpr {
                return_keyword: _,
                expr,
            }) => match &expr {
                Some(expr) => self.check_expr(expr),
                None => {}
            },
            AtomicExpr::Array(ArrayExpr {
                open_bracket,
                expr_kind,
                close_bracket,
            }) => {
                if close_bracket.is_err() {
                    self.report_unclosed_delimiter(open_bracket.span);
                }

                match expr_kind {
                    Some(ArrayExprKind::ExplicitSize(ExplicitSizeArrayExpr {
                        repeated_expr,
                        semicolon: _,
                        size_expr,
                    })) => {
                        self.check_expr_result(repeated_expr);
                        self.check_expr_result(size_expr);
                    }
                    Some(ArrayExprKind::Elements(ElementsArrayExpr {
                        first,
                        rest,
                        trailing_comma: _,
                    })) => {
                        self.check_expr_result(first);

                        for result in rest {
                            match result {
                                Ok(CommaWithExpr { comma: _, item }) => self.check_expr(item),
                                Err(err) => {
                                    self.report_expected_comma_or_item("تعبير برمجي", err, vec![])
                                }
                            }
                        }
                    }
                    None => {}
                }
            }
            AtomicExpr::Struct(StructExpr { dot: _, path, init }) => {
                match path {
                    Ok(simple_path) => self.check_simple_path(simple_path),
                    Err(err) => self.report_expected("اسم هيكل أو مساره", err, vec![]),
                }

                match init {
                    Some(StructInit::Fields(StructFieldsInitExpr {
                        open_delim,
                        items,
                        close_delim,
                    })) => {
                        if close_delim.is_err() {
                            self.report_unclosed_delimiter(open_delim.span);
                        }

                        if let Some(PunctuatedStructFieldInitExpr {
                            first_item,
                            rest_items,
                            trailing_comma: _,
                        }) = items
                        {
                            match first_item {
                                Ok(node) => match &node.expr {
                                    Some(node) => self.check_expr_result(&node.expr),
                                    None => {}
                                },
                                Err(err) => self.report_expected("مُعرِّف", err, vec![]),
                            }

                            for result in rest_items {
                                match result {
                                    Ok(CommaWithStructFieldInitExpr { comma: _, item }) => {
                                        match &item.expr {
                                            Some(node) => self.check_expr_result(&node.expr),
                                            None => {}
                                        }
                                    }
                                    Err(err) => {
                                        self.report_expected_comma_or_item("مُعرِّف", err, vec![])
                                    }
                                }
                            }
                        }
                    }
                    Some(StructInit::Tuple(paren_expr)) => self.check_paren_expr(paren_expr),
                    None => {}
                }
            }
        }
    }

    fn check_if_expr(&mut self, if_expr: &IfExpr) {
        match &if_expr.conditional_block.condition {
            Ok(expr) => self.check_expr(expr),
            Err(err) => self.report_expected("تعبير برمجي (شرط `لو`)", err, vec![]),
        }

        match &if_expr.conditional_block.block {
            Ok(block) => self.check_block(block),
            Err(err) => self.report_expected("محتوى `لو`", err, vec![]),
        }

        for ElseIfClause {
            conditional_block, ..
        } in &if_expr.else_ifs
        {
            match &conditional_block.condition {
                Ok(expr) => self.check_expr(expr),
                Err(err) => self.report_expected("تعبير برمجي (شرط `وإلا لو`)", err, vec![]),
            }

            match &conditional_block.block {
                Ok(block) => self.check_block(block),
                Err(err) => self.report_expected("محتوى `وإلا لو`", err, vec![]),
            }
        }

        if let Some(ElseClause {
            else_keyword: _,
            block,
        }) = &if_expr.else_cluase
        {
            match block {
                Ok(block) => self.check_block(block),
                Err(err) => self.report_expected("محتوى `وإلا`", err, vec![]),
            }
        }
    }

    fn check_when_expr(&mut self, _when_expr: &WhenExpr) {
        // TODO
        todo!()
    }

    fn check_lambda_expr(&mut self, lambda: &LambdaExpr) {
        if let Some(LambdaArrow::WithParams(LambdaParams {
            first,
            rest,
            trailing_comma: _,
            r_arrow,
        })) = &lambda.lambda_arrow
        {
            self.check_binding(first);

            for CommaWithBinding { comma: _, item } in rest {
                self.check_binding(item);
            }

            if let Err(err) = r_arrow {
                self.report_expected("`->`", err, vec![]);
            }
        }

        self.check_block(lambda);
    }

    fn check_paren_expr(
        &mut self,
        ParenExpr {
            open_delim,
            items,
            close_delim,
        }: &ParenExpr,
    ) {
        if let Some(PunctuatedExpr {
            first_item,
            rest_items,
            trailing_comma: _,
        }) = items
        {
            self.check_expr_result(first_item);

            for result in rest_items {
                match result {
                    Ok(CommaWithExpr { comma: _, item }) => self.check_expr(item),
                    Err(err) => self.report_expected_comma_or_item("تعبير برمجي", err, vec![]),
                }
            }
        }

        if close_delim.is_err() {
            self.report_unclosed_delimiter(open_delim.span);
        }
    }
}
