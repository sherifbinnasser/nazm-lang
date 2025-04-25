use super::*;
use nazmc_data_pool::IdKey;
use paste::paste;
use std::fmt::Debug;

mod private {
    pub trait Sealed {}
}

pub(crate) trait TerminalGuard: private::Sealed + Debug {}

#[derive(Debug)]
pub(crate) struct Terminal<T>
where
    T: TerminalGuard,
{
    pub(crate) span: Span,
    pub(crate) data: T,
}

macro_rules! create_keyword_parser {
    ($keyword: ident) => {
        paste! {

            #[derive(Debug)]
            pub(crate) struct [<$keyword KeywordToken>];

            impl private::Sealed for [<$keyword KeywordToken>] {}

            impl TerminalGuard for [<$keyword KeywordToken>] {}

            pub(crate) type [<$keyword Keyword>] = Terminal<[<$keyword KeywordToken>]>;

            impl NazmcParse for ParseResult<[<$keyword Keyword>]>{

                fn parse(iter: &mut TokensIter) -> Self {

                    match iter.recent() {
                        Some(Token { span, kind: TokenKind::Keyword(KeywordKind::$keyword), .. }) => {
                            let ok = Ok(Terminal {
                                span: *span,
                                data: [<$keyword KeywordToken>],
                            });
                            iter.next_non_space_or_comment();
                            ok
                        }
                        Some(_) => Err(ParseErr {
                            found_token_index: iter.peek_idx - 1,
                        }),
                        None => ParseErr::eof(),
                    }
                }
            }
        }
    };
}

macro_rules! create_symbol_parser {
    ($symbol: ident) => {
        paste! {

            #[derive(Debug)]
            pub(crate) struct [<$symbol SymbolToken>];

            impl private::Sealed for [<$symbol SymbolToken>] {}

            impl TerminalGuard for [<$symbol SymbolToken>] {}

            pub(crate) type [<$symbol Symbol>] = Terminal<[<$symbol SymbolToken>]>;

            impl NazmcParse for ParseResult<[<$symbol Symbol>]>{

                fn parse(iter: &mut TokensIter) -> Self {

                    match iter.recent() {
                        Some(Token { span, kind: TokenKind::Symbol(SymbolKind::$symbol), .. }) => {
                            let ok = Ok(Terminal {
                                span: *span,
                                data: [<$symbol SymbolToken>],
                            });
                            iter.next_non_space_or_comment();
                            ok
                        }
                        Some(_) => Err(ParseErr {
                            found_token_index: iter.peek_idx - 1,
                        }),
                        None => ParseErr::eof(),
                    }
                }
            }
        }
    };
}

create_keyword_parser!(Fn);
create_keyword_parser!(Let);
create_keyword_parser!(Mut);
create_keyword_parser!(Const);
create_keyword_parser!(Static);
create_keyword_parser!(Struct);
create_keyword_parser!(Enum);
create_keyword_parser!(Public);
create_keyword_parser!(Private);
create_keyword_parser!(On);
create_keyword_parser!(If);
create_keyword_parser!(Else);
create_keyword_parser!(When);
create_keyword_parser!(While);
create_keyword_parser!(Do);
create_keyword_parser!(Break);
create_keyword_parser!(Continue);
create_keyword_parser!(Return);
create_keyword_parser!(Import);
create_keyword_parser!(Extern);
create_keyword_parser!(Null);

create_symbol_parser!(Comma);
create_symbol_parser!(Semicolon);
create_symbol_parser!(QuestionMark);
create_symbol_parser!(OpenParenthesis);
create_symbol_parser!(CloseParenthesis);
create_symbol_parser!(OpenCurlyBrace);
create_symbol_parser!(CloseCurlyBrace);
create_symbol_parser!(OpenSquareBracket);
create_symbol_parser!(CloseSquareBracket);
create_symbol_parser!(Dot);
create_symbol_parser!(OpenAngleBracketOrLess);
create_symbol_parser!(CloseAngleBracketOrGreater);
create_symbol_parser!(Star);
create_symbol_parser!(Slash);
create_symbol_parser!(Plus);
create_symbol_parser!(Minus);
create_symbol_parser!(BitOr);
create_symbol_parser!(BitAnd);
create_symbol_parser!(Modulo);
create_symbol_parser!(BitNot);
create_symbol_parser!(Xor);
create_symbol_parser!(ExclamationMark);
create_symbol_parser!(Colon);
create_symbol_parser!(Equal);

#[derive(Debug)]
pub(crate) struct IdToken {
    pub(crate) val: IdKey,
}

#[derive(Debug)]
pub(crate) struct DoubleColonsSymbolToken;

#[derive(Debug)]
pub(crate) struct RArrowSymbolToken;

#[derive(Debug)]
pub(crate) struct VarargSymbolToken;

#[derive(Debug)]
/// The parse method is written by hand to avoid backtracking
pub(crate) enum BinOpToken {
    LOr,
    LAnd,
    EqualEqual,
    NotEqual,
    GE,
    GT,
    LE,
    LT,
    OpenOpenRange,
    CloseOpenRange,
    OpenCloseRange,
    CloseCloseRange,
    BOr,
    Xor,
    BAnd,
    Shr,
    Shl,
    Plus,
    Minus,
    Times,
    Div,
    Mod,
    Assign,
    PlusAssign,
    MinusAssign,
    TimesAssign,
    DivAssign,
    ModAssign,
    BAndAssign,
    BOrAssign,
    XorAssign,
    ShlAssign,
    ShrAssign,
}

#[derive(Debug)]
/// The parse method is written by hand to avoid backtracking
///
/// Note that there is no unary plus operator
pub(crate) enum UnaryOpToken {
    Minus,
    LNot,
    BNot,
    Deref,
    Borrow,
    BorrowMut,
}

#[derive(Debug)]
/// The parse method is written by hand to avoid backtracking
pub(crate) enum VisModifierToken {
    Public,
    Private,
}

#[derive(Debug)]
pub(crate) struct EOFToken;

impl private::Sealed for IdToken {}
impl private::Sealed for DoubleColonsSymbolToken {}
impl private::Sealed for RArrowSymbolToken {}
impl private::Sealed for VarargSymbolToken {}
impl private::Sealed for BinOpToken {}
impl private::Sealed for UnaryOpToken {}
impl private::Sealed for LiteralKind {}
impl private::Sealed for VisModifierToken {}
impl private::Sealed for EOFToken {}
impl private::Sealed for usize {}

impl TerminalGuard for IdToken {}
impl TerminalGuard for DoubleColonsSymbolToken {}
impl TerminalGuard for RArrowSymbolToken {}
impl TerminalGuard for VarargSymbolToken {}
impl TerminalGuard for BinOpToken {}
impl TerminalGuard for UnaryOpToken {}
impl TerminalGuard for LiteralKind {}
impl TerminalGuard for VisModifierToken {}
impl TerminalGuard for EOFToken {}
impl TerminalGuard for usize {}

pub(crate) type Id = Terminal<IdToken>;
pub(crate) type DoubleColonsSymbol = Terminal<DoubleColonsSymbolToken>;
pub(crate) type RArrowSymbol = Terminal<RArrowSymbolToken>;
pub(crate) type VarargSymbol = Terminal<VarargSymbolToken>;
pub(crate) type BinOp = Terminal<BinOpToken>;
pub(crate) type UnaryOp = Terminal<UnaryOpToken>;
pub(crate) type LiteralExpr = Terminal<LiteralKind>;
pub(crate) type VisModifier = Terminal<VisModifierToken>;
pub(crate) type Eof = Terminal<EOFToken>;
pub(crate) type TupleIdx = Terminal<usize>;

macro_rules! match_peek_symbols {
    ($iter:ident, $symbol0:ident, $symbol1:ident, $symbol2:ident) => {
        match_peek_symbols!($iter, 0, $symbol0)
            && match_peek_symbols!($iter, 1, $symbol1)
            && match_peek_symbols!($iter, 2, $symbol2)
    };
    ($iter:ident, $symbol0:ident, $symbol1:ident) => {
        match_peek_symbols!($iter, 0, $symbol0) && match_peek_symbols!($iter, 1, $symbol1)
    };
    ($iter:ident, $symbol:ident) => {
        match_peek_symbols!($iter, 0, $symbol)
    };
    ($iter:ident, $nth: literal, $symbol:ident) => {
        matches!(
            $iter.peek_nth($nth),
            Some(Token {
                kind: TokenKind::Symbol(SymbolKind::$symbol),
                ..
            })
        )
    };
}

impl NazmcParse for ParseResult<Id> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(Token {
                span,
                kind: TokenKind::Id(val),
                ..
            }) => {
                let ok = Ok(Terminal {
                    span: *span,
                    data: IdToken { val: *val },
                });
                iter.next_non_space_or_comment();
                ok
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

impl NazmcParse for ParseResult<DoubleColonsSymbol> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(
                token @ Token {
                    kind: TokenKind::Symbol(SymbolKind::Colon),
                    ..
                },
            ) if match_peek_symbols!(iter, Colon) => {
                let mut span = token.span;
                span.end.col += 1;
                iter.peek_idx += 1; // Eat next colon
                iter.next_non_space_or_comment();
                Ok(Terminal {
                    span,
                    data: DoubleColonsSymbolToken,
                })
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

impl NazmcParse for ParseResult<RArrowSymbol> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(
                token @ Token {
                    kind: TokenKind::Symbol(SymbolKind::Minus),
                    ..
                },
            ) if match_peek_symbols!(iter, CloseAngleBracketOrGreater) => {
                let mut span = token.span;
                span.end.col += 1;
                iter.peek_idx += 1; // Eat next '>'
                iter.next_non_space_or_comment();
                Ok(Terminal {
                    span,
                    data: RArrowSymbolToken,
                })
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

impl NazmcParse for ParseResult<VarargSymbol> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(
                token @ Token {
                    kind: TokenKind::Symbol(SymbolKind::Dot),
                    ..
                },
            ) if match_peek_symbols!(iter, Dot, Dot) => {
                let mut span = token.span;
                span.end.col += 2;
                iter.peek_idx += 2; // Eat next '..'
                iter.next_non_space_or_comment();
                Ok(Terminal {
                    span,
                    data: VarargSymbolToken,
                })
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

impl NazmcParse for ParseResult<BinOp> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(
                token @ Token {
                    kind: TokenKind::Symbol(symbol_kind),
                    ..
                },
            ) => {
                let mut span = token.span;
                let (op_kind, peek_inc) = match symbol_kind {
                    SymbolKind::OpenAngleBracketOrLess
                        if match_peek_symbols!(iter, Dot, Dot, OpenAngleBracketOrLess) =>
                    {
                        (BinOpToken::OpenOpenRange, 3)
                    }
                    SymbolKind::OpenAngleBracketOrLess if match_peek_symbols!(iter, Dot, Dot) => {
                        (BinOpToken::OpenCloseRange, 2)
                    }
                    SymbolKind::OpenAngleBracketOrLess
                        if match_peek_symbols!(iter, OpenAngleBracketOrLess, Equal) =>
                    {
                        (BinOpToken::ShrAssign, 2)
                    }
                    SymbolKind::OpenAngleBracketOrLess
                        if match_peek_symbols!(iter, OpenAngleBracketOrLess) =>
                    {
                        (BinOpToken::Shr, 1)
                    }
                    SymbolKind::OpenAngleBracketOrLess if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::LE, 1)
                    }
                    SymbolKind::OpenAngleBracketOrLess => (BinOpToken::LT, 0),

                    SymbolKind::CloseAngleBracketOrGreater
                        if match_peek_symbols!(iter, CloseAngleBracketOrGreater, Equal) =>
                    {
                        (BinOpToken::ShlAssign, 2)
                    }
                    SymbolKind::CloseAngleBracketOrGreater
                        if match_peek_symbols!(iter, CloseAngleBracketOrGreater) =>
                    {
                        (BinOpToken::Shl, 1)
                    }
                    SymbolKind::CloseAngleBracketOrGreater if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::GE, 1)
                    }
                    SymbolKind::CloseAngleBracketOrGreater => (BinOpToken::GT, 0),

                    SymbolKind::Dot if match_peek_symbols!(iter, Dot, OpenAngleBracketOrLess) => {
                        (BinOpToken::CloseOpenRange, 2)
                    }
                    SymbolKind::Dot if match_peek_symbols!(iter, Dot) => {
                        (BinOpToken::CloseCloseRange, 1)
                    }

                    SymbolKind::Equal if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::EqualEqual, 1)
                    }
                    SymbolKind::Equal => (BinOpToken::Assign, 0),
                    SymbolKind::ExclamationMark if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::NotEqual, 1)
                    }

                    SymbolKind::BitOr if match_peek_symbols!(iter, BitOr) => (BinOpToken::LOr, 1),
                    SymbolKind::BitOr if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::BOrAssign, 1)
                    }
                    SymbolKind::BitOr => (BinOpToken::BOr, 0),

                    SymbolKind::Xor if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::XorAssign, 1)
                    }
                    SymbolKind::Xor => (BinOpToken::Xor, 0),

                    SymbolKind::BitAnd if match_peek_symbols!(iter, BitAnd) => {
                        (BinOpToken::LAnd, 1)
                    }
                    SymbolKind::BitAnd if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::BAndAssign, 1)
                    }
                    SymbolKind::BitAnd => (BinOpToken::BAnd, 0),

                    SymbolKind::Plus if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::PlusAssign, 1)
                    }
                    SymbolKind::Plus => (BinOpToken::Plus, 0),

                    SymbolKind::Minus if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::MinusAssign, 1)
                    }
                    SymbolKind::Minus => (BinOpToken::Minus, 0),

                    SymbolKind::Star if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::TimesAssign, 1)
                    }
                    SymbolKind::Star => (BinOpToken::Times, 0),

                    SymbolKind::Slash if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::DivAssign, 1)
                    }
                    SymbolKind::Slash => (BinOpToken::Div, 0),

                    SymbolKind::Modulo if match_peek_symbols!(iter, Equal) => {
                        (BinOpToken::ModAssign, 1)
                    }
                    SymbolKind::Modulo => (BinOpToken::Mod, 0),

                    _ => {
                        return Err(ParseErr {
                            found_token_index: iter.peek_idx - 1,
                        });
                    }
                };

                iter.peek_idx += peek_inc;
                span.end.col += peek_inc;
                iter.next_non_space_or_comment();

                Ok(Terminal {
                    span,
                    data: op_kind,
                })
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

impl NazmcParse for ParseResult<UnaryOp> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(Token {
                span,
                kind: TokenKind::Symbol(symbol_kind),
                ..
            }) => {
                let mut span = *span;

                let op_kind = match symbol_kind {
                    SymbolKind::Minus if !match_peek_symbols!(iter, Equal) => UnaryOpToken::Minus,
                    SymbolKind::ExclamationMark if !match_peek_symbols!(iter, Equal) => {
                        UnaryOpToken::LNot
                    }
                    SymbolKind::BitNot if !match_peek_symbols!(iter, Equal) => UnaryOpToken::BNot,
                    SymbolKind::Star if !match_peek_symbols!(iter, Equal) => UnaryOpToken::Deref,
                    SymbolKind::Xor => {
                        let peek_idx = iter.peek_idx;
                        iter.next_non_space_or_comment();
                        if let Some(Token {
                            span: mut_keyword_span,
                            kind: TokenKind::Keyword(KeywordKind::Mut),
                            ..
                        }) = iter.recent()
                        {
                            span = span.merged_with(mut_keyword_span);
                            UnaryOpToken::BorrowMut
                        } else {
                            iter.peek_idx = peek_idx;
                            UnaryOpToken::Borrow
                        }
                    }
                    _ => {
                        return Err(ParseErr {
                            found_token_index: iter.peek_idx - 1,
                        });
                    }
                };
                iter.next_non_space_or_comment();
                Ok(Terminal {
                    span,
                    data: op_kind,
                })
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

impl NazmcParse for ParseResult<LiteralExpr> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(Token {
                span,
                kind: TokenKind::Literal(literal_kind),
                ..
            }) => {
                let ok = Ok(Terminal {
                    span: *span,
                    data: literal_kind.clone(),
                });
                iter.next_non_space_or_comment();
                ok
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

impl NazmcParse for ParseResult<VisModifier> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(Token {
                span,
                kind: TokenKind::Keyword(KeywordKind::Public),
                ..
            }) => {
                let ok = Ok(Terminal {
                    span: *span,
                    data: VisModifierToken::Public,
                });
                iter.next_non_space_or_comment();
                ok
            }
            Some(Token {
                span,
                kind: TokenKind::Keyword(KeywordKind::Private),
                ..
            }) => {
                let ok = Ok(Terminal {
                    span: *span,
                    data: VisModifierToken::Private,
                });
                iter.next_non_space_or_comment();
                ok
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

impl NazmcParse for ParseResult<Eof> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => Ok(Eof {
                span: Span::default(),
                data: EOFToken,
            }),
        }
    }
}

impl NazmcParse for ParseResult<TupleIdx> {
    fn parse(iter: &mut TokensIter) -> Self {
        match iter.recent() {
            Some(Token {
                span,
                kind:
                    TokenKind::Literal(LiteralKind::Num(nazmc_lexer::NumKind::UnspecifiedInt(int))),
                start_byte,
                end_byte,
            }) if iter.content[*start_byte..*end_byte]
                .chars()
                .all(|c| c.is_ascii_digit()) =>
            {
                let ok = Ok(Terminal {
                    span: *span,
                    data: *int as usize,
                });
                iter.next_non_space_or_comment();
                ok
            }
            Some(_) => Err(ParseErr {
                found_token_index: iter.peek_idx - 1,
            }),
            None => ParseErr::eof(),
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::LexerIter;

    use super::*;

    #[test]
    fn test() {
        let content = "دالة البداية(/* تعليق */){}";
        let mut id_pool = DataPool::new();
        let mut str_pool = DataPool::new();
        let lexer = LexerIter::new(content, &mut id_pool, &mut str_pool);

        let (tokens, ..) = lexer.collect_all();
        let mut iter = TokensIter::new(&tokens, &content);
        iter.next(); // Initialize the value of recent

        let _fn = ParseResult::<FnKeyword>::parse(&mut iter);
        let _id = ParseResult::<Id>::parse(&mut iter);
        let _open_paren = ParseResult::<OpenParenthesisSymbol>::parse(&mut iter);
        let _close_paren = ParseResult::<CloseParenthesisSymbol>::parse(&mut iter);
        let _open_curly = ParseResult::<OpenCurlyBraceSymbol>::parse(&mut iter);
        let _close_curly = ParseResult::<CloseCurlyBraceSymbol>::parse(&mut iter);

        assert!(!_fn.unwrap().is_broken());
        assert!(!_id.unwrap().is_broken());
        assert!(!_open_paren.unwrap().is_broken());
        assert!(!_close_paren.unwrap().is_broken());
        assert!(!_open_curly.unwrap().is_broken());
        assert!(!_close_curly.unwrap().is_broken());
    }

    #[test]
    fn test_fail() {
        let content = "دالة البداية(عدد: ص8){}";
        let mut id_pool = DataPool::new();
        let mut str_pool = DataPool::new();
        let lexer = LexerIter::new(content, &mut id_pool, &mut str_pool);

        let (tokens, ..) = lexer.collect_all();
        let mut iter = TokensIter::new(&tokens, &content);
        iter.next(); // Initialize the value of recent

        let _fn = ParseResult::<FnKeyword>::parse(&mut iter);
        let _id = ParseResult::<Id>::parse(&mut iter);
        let _open_paren = ParseResult::<OpenParenthesisSymbol>::parse(&mut iter);
        let _close_paren = ParseResult::<CloseParenthesisSymbol>::parse(&mut iter);

        assert!(!_fn.unwrap().is_broken());
        assert!(!_id.unwrap().is_broken());
        assert!(!_open_paren.unwrap().is_broken());
        assert!(matches!(
            iter.nth(_close_paren.unwrap_err().found_token_index),
            Some(Token {
                kind: TokenKind::Id,
                ..
            })
        ));
    }
}
