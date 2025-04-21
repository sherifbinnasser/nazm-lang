use super::*;

#[derive(NazmcParse, Debug)]
pub(crate) enum Type {
    Path(Box<SimplePath>),
    Ptr(Box<PtrType>),
    Slice(Box<SliceType>),
    Paren(Box<ParenType>),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct PtrType {
    pub(crate) star: StarSymbol,
    pub(crate) mut_keyword: Option<MutKeyword>,
    pub(crate) typ: ParseResult<Type>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct SliceType {
    pub(crate) open_bracket: OpenSquareBracketSymbol,
    pub(crate) typ: ParseResult<Type>,
    pub(crate) array_size: Option<ArraySizeExpr>,
    pub(crate) close_bracket: ParseResult<CloseSquareBracketSymbol>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ArraySizeExpr {
    pub(crate) semicolon: SemicolonSymbol,
    pub(crate) expr: ParseResult<Expr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ParenType {
    pub(crate) tuple: TupleType,
    pub(crate) lambda: Option<LambdaType>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct LambdaType {
    pub(crate) r_arrow: RArrowSymbol,
    pub(crate) typ: ParseResult<Type>,
}

generatePunctuatedItem!(Type);

generateDelimitedPunctuated!(
    TupleType,
    OpenParenthesisSymbol,
    Type,
    CloseParenthesisSymbol
);
