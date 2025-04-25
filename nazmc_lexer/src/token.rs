use documented::DocumentedVariants;
use nazmc_data_pool::{IdKey, StrKey};
use nazmc_diagnostics::span::*;
use strum::EnumIter;

#[derive(Clone, PartialEq, Debug, Default)]
pub struct Token {
    // pub val: &'a str,
    pub span: Span,
    pub kind: TokenKind,
    pub start_byte: usize,
    pub end_byte: usize,
}

#[derive(Clone, PartialEq, Debug, Default)]
pub enum TokenKind {
    #[default]
    Eof,
    Eol,
    Space,
    LineComment,
    DelimitedComment,
    Literal(LiteralKind),
    Id(IdKey),
    Symbol(SymbolKind),
    Keyword(KeywordKind),
}

#[derive(Clone, PartialEq, Debug)]
pub enum LiteralKind {
    Str(StrKey),
    Char(char),
    Bool(bool),
    Num(NumKind),
}

#[derive(Clone, PartialEq, Debug)]
pub enum NumKind {
    F4(f32),
    F8(f64),
    I(isize),
    I1(i8),
    I2(i16),
    I4(i32),
    I8(i64),
    U(usize),
    U1(u8),
    U2(u16),
    U4(u32),
    U8(u64),
    UnspecifiedInt(u64),
    UnspecifiedFloat(f64),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Base {
    Bin = 2,
    Oct = 8,
    Dec = 10,
    Hex = 16,
}

#[derive(Clone, PartialEq, Debug, DocumentedVariants, EnumIter)]
pub enum SymbolKind {
    /// ،
    Comma,
    /// ؛
    Semicolon,
    /// ؟
    QuestionMark,
    /// (
    OpenParenthesis,
    /// )
    CloseParenthesis,
    /// {
    OpenCurlyBrace,
    /// }
    CloseCurlyBrace,
    /// [
    OpenSquareBracket,
    /// ]
    CloseSquareBracket,
    /// .
    Dot,
    /// <
    OpenAngleBracketOrLess,
    /// >
    CloseAngleBracketOrGreater,
    /// *
    Star,
    /// /
    Slash,
    /// +
    Plus,
    /// -
    Minus,
    /// |
    BitOr,
    /// &
    BitAnd,
    /// %
    Modulo,
    /// ~
    BitNot,
    /// ^
    Xor,
    /// !
    ExclamationMark,
    /// :
    Colon,
    /// =
    Equal,
}

#[derive(DocumentedVariants, Debug, Clone, PartialEq, EnumIter)]
pub enum KeywordKind {
    /// دالة
    Fn,
    /// احجز
    Let,
    /// متغير
    Mut,
    /// ثابت
    Const,
    /// مشترك
    Static,
    /// هيكل
    Struct,
    /// تصنيف
    Enum,
    /// تصدير
    Public,
    /// تخصيص
    Private,
    /// على
    On,
    /// لو
    If,
    /// وإلا
    Else,
    /// عندما
    When,
    /// طالما
    While,
    /// افعل
    Do,
    /// قطع
    Break,
    /// وصل
    Continue,
    /// أرجع
    Return,
    /// استيراد
    Import,
    /// ربط
    Extern,
    /// صفر
    Null,
}
