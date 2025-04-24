use super::*;

#[derive(NazmcParse, Debug)]
pub(crate) enum Type {
    Path(Box<SimplePath>),
    Ptr(Box<PtrType>),
    Slice(Box<SliceType>),
    FnPtr(Box<FnPtrType>),
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
    pub(crate) mut_keyword: Option<MutKeyword>,
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
pub(crate) struct FnPtrType {
    pub(crate) fn_keyword: FnKeyword,
    pub(crate) params: ParseResult<FnPtrParams>,
    pub(crate) return_type: ParseResult<LambdaType>,
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

#[derive(NazmcParse, Debug)]
pub(crate) enum FnPtrParam {
    Varag(VarargSymbol),
    Real(Type),
}

generatePunctuatedItem!(Type);

generatePunctuatedItem!(FnPtrParam);

generateDelimitedPunctuated!(
    TupleType,
    OpenParenthesisSymbol,
    Type,
    CloseParenthesisSymbol
);

generateDelimitedPunctuated!(
    FnPtrParams,
    OpenParenthesisSymbol,
    FnPtrParam,
    CloseParenthesisSymbol
);
