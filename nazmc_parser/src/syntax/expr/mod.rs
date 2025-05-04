use super::*;

mod array;
mod control_flow;
mod lambda;

pub(crate) use array::*;
pub(crate) use control_flow::*;
pub(crate) use lambda::*;

#[derive(NazmcParse, Debug)]
/// The wrapper for all valid expressions syntax in the language
pub(crate) struct Expr {
    pub(crate) left: Box<PrimaryExpr>,
    pub(crate) rights: Vec<BinExpr>,
}

/// This will parse the valid syntax of binary operators and will not parse their precedences
///
/// The precedence parsing will be when constructiong the HIR by the shunting-yard algorithm
/// as we want it here to be simple
///
#[derive(NazmcParse, Debug)]
pub(crate) enum BinExpr {
    Cast(CastExpr),
    Normal(NormalBinExpr),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct CastExpr {
    pub(crate) as_keyword: AsKeyword,
    pub(crate) typ: ParseResult<Type>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct NormalBinExpr {
    pub(crate) op: BinOp,
    pub(crate) right: ParseResult<PrimaryExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct PrimaryExpr {
    pub(crate) kind: PrimaryExprKind,
    pub(crate) post_ops: Vec<PostOpExpr>,
    pub(crate) inner_access: Vec<InnerAccessExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) enum PrimaryExprKind {
    Unary(Box<UnaryExpr>),
    Atomic(AtomicExpr),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct UnaryExpr {
    pub(crate) op: UnaryOp,
    pub(crate) expr: ParseResult<PrimaryExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) enum PostOpExpr {
    Invoke(ParenExpr),
    Lambda(LambdaExpr),
    Index(IdxExpr),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct InnerAccessExpr {
    pub(crate) dot: DotSymbol,
    pub(crate) field: ParseResult<InnerAccessField>,
    pub(crate) post_ops: Vec<PostOpExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) enum InnerAccessField {
    Id(Id),
    TupleIdx(TupleIdx),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct IdxExpr {
    pub(crate) open_bracket: OpenSquareBracketSymbol,
    pub(crate) expr: ParseResult<Expr>,
    pub(crate) close_bracket: ParseResult<CloseSquareBracketSymbol>,
}

#[derive(NazmcParse, Debug)]
/// It's the atom in constructing an expression
pub(crate) enum AtomicExpr {
    Array(ArrayExpr),
    Paren(ParenExpr),
    Struct(StructExpr),
    Path(SimplePath),
    Literal(LiteralExpr),
    On(OnKeyword),
    Null(NullKeyword),
    Lambda(LambdaExpr),
    Break(BreakKeyword),
    Continue(ContinueKeyword),
    Return(ReturnExpr),
    If(IfExpr),
    When(WhenExpr),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct StructExpr {
    pub(crate) dot: DotSymbol,
    pub(crate) path: ParseResult<SimplePath>,
    pub(crate) init: ParseResult<StructInitExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct FieldInitExpr {
    pub(crate) name: Id,
    pub(crate) expr: Option<FieldInitExplicitExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct FieldInitExplicitExpr {
    pub(crate) equal: EqualSymbol,
    pub(crate) expr: ParseResult<Expr>,
}

generatePunctuatedItem!(FieldInitExpr);

generateDelimitedPunctuated!(
    StructInitExpr,
    OpenCurlyBraceSymbol,
    FieldInitExpr,
    CloseCurlyBraceSymbol
);

generatePunctuatedItem!(Expr);

// Could be used for tuples, function calls and and nodrma paren expressions
generateDelimitedPunctuated!(
    ParenExpr,
    OpenParenthesisSymbol,
    Expr,
    CloseParenthesisSymbol
);
