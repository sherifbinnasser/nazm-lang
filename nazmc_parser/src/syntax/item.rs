use super::*;

#[derive(NazmcParse, Debug)]
pub(crate) enum FileItem {
    ImportStm(ImportStm),
    WithVisModifier(ItemWithVisibility),
    WithoutModifier(Item),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ImportStm {
    pub(crate) import_keyword: ImportKeyword,
    pub(crate) top: Option<Id>,
    pub(crate) sec: ParseResult<DoubleColonsWithPathSegInImportStm>,
    pub(crate) segs: Vec<DoubleColonsWithPathSegInImportStm>,
    pub(crate) alias: Option<ImportAlias>,
    pub(crate) semicolon: ParseResult<SemicolonSymbol>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct DoubleColonsWithPathSegInImportStm {
    pub(crate) double_colons: DoubleColonsSymbol,
    pub(crate) seg: ParseResult<PathSegInImportStm>,
}

#[derive(NazmcParse, Debug)]
pub(crate) enum PathSegInImportStm {
    Id(Id),
    Star(StarSymbol),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ImportAlias {
    pub(crate) as_keyword: AsKeyword,
    pub(crate) id: ParseResult<Id>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ItemWithVisibility {
    pub(crate) visibility: VisModifier,
    pub(crate) item: ParseResult<Item>,
}

#[derive(NazmcParse, Debug)]
pub(crate) enum Item {
    ExternConst(ExternConst),
    ExternStatic(ExternStatic),
    Const(ConstStm),
    Static(StaticStm),
    Struct(Struct),
    Fn(Fn),
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ExternDecl {
    pub(crate) extern_keyword: ExternKeyword,
    pub(crate) link_name: Option<LiteralExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ExternConst {
    pub(crate) extern_decl: ExternDecl,
    pub(crate) const_keyword: ConstKeyword,
    pub(crate) id: ParseResult<Id>,
    pub(crate) colon: ParseResult<ColonSymbol>,
    pub(crate) typ: ParseResult<Type>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ExternStatic {
    pub(crate) extern_decl: ExternDecl,
    pub(crate) static_keyword: StaticKeyword,
    pub(crate) id: ParseResult<Id>,
    pub(crate) colon: ParseResult<ColonSymbol>,
    pub(crate) typ: ParseResult<Type>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ConstStm {
    pub(crate) const_keyword: ConstKeyword,
    pub(crate) body: ParseResult<ConstStaticStmBody>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct StaticStm {
    pub(crate) static_keyword: StaticKeyword,
    pub(crate) body: ParseResult<ConstStaticStmBody>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ConstStaticStmBody {
    pub(crate) id: Id,
    pub(crate) colon: ParseResult<ColonSymbol>,
    pub(crate) typ: ParseResult<Type>,
    pub(crate) equal: ParseResult<EqualSymbol>,
    pub(crate) expr: ParseResult<Expr>,
    pub(crate) semicolon: ParseResult<SemicolonSymbol>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct Struct {
    pub(crate) struct_keyword: StructKeyword,
    pub(crate) name: ParseResult<Id>,
    pub(crate) fields: ParseResult<StructFields>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct StructField {
    pub(crate) visibility: Option<VisModifier>,
    pub(crate) name: Id,
    pub(crate) typ: ParseResult<ColonWithType>,
}

generatePunctuatedItem!(StructField);

generateDelimitedPunctuated!(
    StructFields,
    OpenCurlyBraceSymbol,
    StructField,
    CloseCurlyBraceSymbol
);

#[derive(NazmcParse, Debug)]
pub(crate) struct Fn {
    pub(crate) extern_decl: Option<ExternDecl>,
    pub(crate) fn_keyword: FnKeyword,
    pub(crate) name: ParseResult<Id>,
    pub(crate) params_decl: ParseResult<FnParams>,
    pub(crate) return_type: Option<LambdaType>,
    /// This must be checked that it doesn't have a lambda arrow
    pub(crate) body: ParseResult<LambdaExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct RealFnParam {
    pub(crate) mut_keyword: Option<MutKeyword>,
    pub(crate) name: Id,
    pub(crate) typ: ParseResult<ColonWithType>,
}

#[derive(NazmcParse, Debug)]
pub(crate) enum FnParam {
    Varag(VarargSymbol),
    Real(RealFnParam),
}

generatePunctuatedItem!(FnParam);

generateDelimitedPunctuated!(
    FnParams,
    OpenParenthesisSymbol,
    FnParam,
    CloseParenthesisSymbol
);
