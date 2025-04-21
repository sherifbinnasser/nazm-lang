use crate::*;

#[derive(Clone, Default)]
pub struct TypesExprs {
    pub all: TiVec<TypeExprKey, TypeExpr>,
    pub paths: TiVec<PathTypeExprKey, ItemPath>,
    pub parens: TiVec<ParenTypeExprKey, ParenTypeExpr>,
    pub slices: TiVec<SliceTypeExprKey, SliceTypeExpr>,
    pub ptrs: TiVec<PtrTypeExprKey, PtrTypeExpr>,
    pub ptrs_mut: TiVec<PtrMutTypeExprKey, PtrMutTypeExpr>,
    pub tuples: TiVec<TupleTypeExprKey, TupleTypeExpr>,
    pub arrays: TiVec<ArrayTypeExprKey, ArrayTypeExpr>,
    pub lambdas: TiVec<LambdaTypeExprKey, LambdaTypeExpr>,
}

#[derive(Clone, Copy)]
pub enum TypeExpr {
    Path(PathTypeExprKey),
    Paren(ParenTypeExprKey),
    Slice(SliceTypeExprKey),
    Ptr(PtrTypeExprKey),
    PtrMut(PtrMutTypeExprKey),
    Tuple(TupleTypeExprKey),
    Array(ArrayTypeExprKey),
    Lambda(LambdaTypeExprKey),
}

#[derive(Clone)]
pub struct ParenTypeExpr {
    pub underlying_typ: TypeExprKey,
    pub file_key: FileKey,
    pub span: Span,
}

#[derive(Clone)]
pub struct SliceTypeExpr {
    pub underlying_typ: TypeExprKey,
    pub file_key: FileKey,
    pub span: Span,
}

#[derive(Clone)]
pub struct PtrTypeExpr {
    pub underlying_typ: TypeExprKey,
    pub file_key: FileKey,
    pub span: Span,
}

#[derive(Clone)]
pub struct PtrMutTypeExpr {
    pub underlying_typ: TypeExprKey,
    pub file_key: FileKey,
    pub span: Span,
}

#[derive(Clone)]
pub struct TupleTypeExpr {
    pub types: ThinVec<TypeExprKey>,
    pub file_key: FileKey,
    pub span: Span,
}

#[derive(Clone)]
pub struct ArrayTypeExpr {
    pub underlying_typ: TypeExprKey,
    pub size_expr_scope_key: ScopeKey,
    pub file_key: FileKey,
    pub span: Span,
}

#[derive(Clone)]
pub struct LambdaTypeExpr {
    pub params_types: ThinVec<TypeExprKey>,
    pub return_type: TypeExprKey,
    pub file_key: FileKey,
    pub params_span: Span,
    pub arrow_span: Span,
}
