use derive_more::{From, Into};
pub use item::*;
use nazmc_data_pool::{
    new_data_pool_key,
    typed_index_collections::{ti_vec, TiVec},
    DataPoolBuilder, FileKey, IdKey, ItemInfo, PkgKey, StrKey,
};
use nazmc_diagnostics::span::{Span, SpanCursor};
use std::collections::HashMap;
use thin_vec::ThinVec;
pub use typ::*;
mod item;
mod typ;

new_data_pool_key! { StructPathKey }
new_data_pool_key! { PathNoPkgKey }
new_data_pool_key! { PathWithPkgKey }
new_data_pool_key! { TypeExprKey }
new_data_pool_key! { PathTypeExprKey }
new_data_pool_key! { ParenTypeExprKey }
new_data_pool_key! { SliceTypeExprKey }
new_data_pool_key! { SliceMutTypeExprKey }
new_data_pool_key! { PtrTypeExprKey }
new_data_pool_key! { PtrMutTypeExprKey }
new_data_pool_key! { FnPtrTypeExprKey }
new_data_pool_key! { TupleTypeExprKey }
new_data_pool_key! { ArrayTypeExprKey }
new_data_pool_key! { LambdaTypeExprKey }

new_data_pool_key! { StructKey }
new_data_pool_key! { ConstKey }
new_data_pool_key! { StaticKey }
new_data_pool_key! { FnKey }
new_data_pool_key! { ScopeKey }
new_data_pool_key! { LetStmKey }
new_data_pool_key! { ExprKey }

pub type PkgPoolBuilder = DataPoolBuilder<PkgKey, ThinVec<IdKey>>;

#[derive(Default)]
pub struct Unresolved {
    /// The list of maps of items names and their kind, visibility and index
    pub pkgs_to_items: TiVec<PkgKey, HashMap<IdKey, Item>>,
    /// All paths that should be resolved
    pub paths: ASTPaths,
    /// All scope events
    pub scope_events: TiVec<ScopeKey, ThinVec<ScopeEvent>>,
    /// All bound names in all let stms
    pub bound_lets_names: TiVec<LetStmKey, HashMap<IdKey, Span>>,
    /// All bound params names in all lambda expressions scopes
    pub bound_lambdas_names: HashMap<ScopeKey, HashMap<IdKey, Span>>,
}

/// Holds resolved paths
#[derive(Default)]
pub struct Resolved {
    /// The list of all fields struct expressions paths
    pub structs_paths_exprs: TiVec<StructPathKey, StructKey>,
    /// The list of all paths expressions that have no leading pkgs paths
    /// which point only to local vars, statics, consts and fns
    pub paths_no_pkgs_exprs: TiVec<PathNoPkgKey, Item>,
    /// The list of all paths expressions that have leading pkgs paths
    /// which point only to statics, consts and fns
    pub paths_with_pkgs_exprs: TiVec<PathWithPkgKey, Item>,
    /// The list of resolved types paths expressions
    /// which point only to resolved structs
    pub types_paths: TiVec<PathTypeExprKey, (Item, Span)>,
}

#[derive(Default)]
pub struct AST<S> {
    /// The state of AST: may be `Unresolved` or `Resolved`
    pub state: S,
    /// All types exprs
    pub types_exprs: TypesExprs,
    /// All consts
    pub consts: TiVec<ConstKey, Const>,
    /// All statics
    pub statics: TiVec<StaticKey, Static>,
    /// All fields structs
    pub structs: TiVec<StructKey, Struct>,
    /// All fns
    pub fns: TiVec<FnKey, Fn>,
    /// All scopes
    pub scopes: TiVec<ScopeKey, Scope>,
    /// All let stms
    pub lets: TiVec<LetStmKey, LetStm>,
    /// All expressions
    pub exprs: TiVec<ExprKey, Expr>,
}

impl AST<Unresolved> {
    pub fn new(pkgs_len: usize, files_len: usize) -> Self {
        let state = Unresolved {
            pkgs_to_items: ti_vec![HashMap::new(); pkgs_len],
            paths: ASTPaths {
                imports: ti_vec![ThinVec::new(); files_len],
                star_imports: ti_vec![ThinVec::new(); files_len],
                ..Default::default()
            },
            ..Default::default()
        };

        Self {
            state,
            ..Default::default()
        }
    }
}

#[derive(Default)]
pub struct ASTPaths {
    /// The list of imports stms for each file
    pub imports: TiVec<FileKey, ThinVec<ImportStm>>,
    /// The list of star imports for each file
    pub star_imports: TiVec<FileKey, ThinVec<StarImportStm>>,
    /// The list of all struct expressions paths
    pub structs_paths_exprs: TiVec<StructPathKey, ItemPath>,
    /// The list of all paths expressions that have no leading pkgs paths. The PkgKey here represent where this path is loctaed
    pub paths_no_pkgs_exprs: TiVec<PathNoPkgKey, (ASTId, PkgKey)>,
    /// The list of all paths expressions that have leading pkgs paths
    pub paths_with_pkgs_exprs: TiVec<PathWithPkgKey, ItemPath>,
}

#[derive(Clone)]
pub struct PkgPath {
    /// The pkg idx where this path is located
    pub pkg_key: PkgKey,
    /// The file idx where this path is located
    pub file_key: FileKey,
    /// The segmentes of the path
    pub ids: ThinVec<IdKey>,
    /// The spans of the segments of the path
    pub spans: ThinVec<Span>,
}

#[derive(Clone)]
pub struct ItemPath {
    pub top_pkg_span: Option<Span>,
    pub pkg_path: PkgPath,
    pub item: ASTId,
}

impl ItemPath {
    pub fn get_span(&self) -> Span {
        if let Some(span) = self.top_pkg_span {
            span.merged_with(&self.item.span)
        } else if let Some(span) = self.pkg_path.spans.first() {
            span.merged_with(&self.item.span)
        } else {
            self.item.span
        }
    }
}

#[derive(Clone)]
pub struct StarImportStm {
    pub top_pkg_span: Option<Span>,
    pub pkg_path: PkgPath,
}

#[derive(Clone)]
pub struct ImportStm {
    pub item_path: ItemPath,
    pub alias: ASTId,
}

#[derive(Clone, Copy, Default, Debug)]
pub struct ASTId {
    pub span: Span,
    pub id: IdKey,
}

#[derive(Default, Clone, Debug)]
pub struct Binding {
    pub kind: BindingKind,
    pub typ: Option<TypeExprKey>,
}

#[derive(Clone, Debug)]
pub enum BindingKind {
    Id(ASTId),
    MutId { id: ASTId, mut_span: Span },
    Tuple(ThinVec<BindingKind>, Span),
}

impl Default for BindingKind {
    fn default() -> Self {
        Self::Tuple(ThinVec::default(), Span::default())
    }
}

impl BindingKind {
    pub fn get_span(&self) -> Span {
        match self {
            BindingKind::Id(astid) => astid.span,
            BindingKind::MutId { id, mut_span: _ } => id.span,
            BindingKind::Tuple(_, span) => *span,
        }
    }
}

#[derive(Clone, Copy, Default, Debug)]
pub enum VisModifier {
    #[default]
    Default,
    Public,
    Private,
}

#[derive(Clone, Default)]
pub struct Const {
    pub info: ItemInfo,
    pub typ: TypeExprKey,
    pub expr_scope_key: ScopeKey,
}

#[derive(Clone, Default)]
pub struct Static {
    pub info: ItemInfo,
    pub typ: TypeExprKey,
    pub expr_scope_key: ScopeKey,
}

#[derive(Clone, Default)]
pub struct Struct {
    pub info: ItemInfo,
    pub fields: ThinVec<FieldInfo>,
}

#[derive(Clone, Default)]
pub struct FieldInfo {
    pub vis: VisModifier,
    pub id: ASTId,
    pub typ: TypeExprKey,
}

#[derive(Clone, Default)]
pub struct Fn {
    pub info: ItemInfo,
    pub params: ThinVec<FnParam>,
    pub return_type: Option<TypeExprKey>,
    pub linkage: FnLinkage,
}
#[derive(Clone, Copy)]
pub enum FnLinkage {
    ExternWithSameId { is_vararg: bool },
    Extern { name: StrKey, is_vararg: bool },
    Local(ScopeKey),
}

impl Default for FnLinkage {
    fn default() -> Self {
        Self::ExternWithSameId { is_vararg: false }
    }
}

#[derive(Clone, Copy, Default)]
pub struct FnParam {
    pub ast_id: ASTId,
    pub is_mut: bool,
    pub type_expr_key: TypeExprKey,
}

#[derive(Clone, Default)]
pub struct Scope {
    pub stms: ThinVec<Stm>,
    pub return_expr: Option<ExprKey>,
    pub span: Span,
}

#[derive(Clone)]
pub enum ScopeEvent {
    Let(LetStmKey),
    Path(PathNoPkgKey),
    Scope(ScopeKey),
}

#[derive(Clone)]
pub enum Stm {
    Let(LetStmKey),
    While(Box<WhileStm>),
    Expr(ExprKey),
}

#[derive(Default, Clone)]
pub struct LetStm {
    pub binding: Binding,
    pub assign: Option<ExprKey>,
}

#[derive(Clone)]
pub struct WhileStm {
    pub while_keyword_span: Span,
    pub cond_expr_key: ExprKey,
    pub scope_key: ScopeKey,
}

#[derive(Clone, Default)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Default, Debug)]
pub enum ExprKind {
    #[default]
    Unit,
    Null,
    Literal(LiteralExpr),
    PathNoPkg(PathNoPkgKey),
    PathInPkg(PathWithPkgKey),
    Call(Box<CallExpr>),
    Struct(Box<StructExpr>),
    Field(Box<FieldExpr>),
    Idx(Box<IdxExpr>),
    TupleIdx(Box<TupleIdxExpr>),
    Tuple(ThinVec<ExprKey>),
    ArrayElements(ThinVec<ExprKey>),
    ArrayRepeated(Box<ArrayRepeatedExpr>),
    If(Box<IfExpr>),
    Lambda(Box<LambdaExpr>),
    UnaryOp(Box<UnaryOpExpr>),
    BinaryOp(Box<BinaryOpExpr>),
    Return(Box<ReturnExpr>),
    Break(ScopeKey),
    Continue(ScopeKey),
    On,
}

#[derive(Clone, Copy, Debug)]
pub enum LiteralExpr {
    Str(StrKey),
    Char(char),
    Bool(bool),
    Num(NumKind),
}

#[derive(Clone, Copy, Debug)]
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

#[derive(Clone, Debug)]
pub struct CallExpr {
    pub on: ExprKey,
    pub args: ThinVec<ExprKey>,
    pub parens_span: Span,
}

#[derive(Clone, Debug)]
pub struct StructExpr {
    pub path_key: StructPathKey,
    pub fields: ThinVec<(ASTId, ExprKey)>,
}

#[derive(Clone, Debug)]
pub struct FieldExpr {
    pub on: ExprKey,
    pub name: ASTId,
}

#[derive(Clone, Debug)]
pub struct TupleIdxExpr {
    pub on: ExprKey,
    pub idx: u32,
    pub idx_span: Span,
}

#[derive(Clone, Debug)]
pub struct IdxExpr {
    pub on: ExprKey,
    pub idx: ExprKey,
    pub brackets_span: Span,
}

#[derive(Clone, Debug)]
pub struct ArrayRepeatedExpr {
    pub repeat: ExprKey,
    pub size: ExprKey,
}

#[derive(Clone, Debug)]
pub struct IfExpr {
    pub if_: (Span, ExprKey, ScopeKey),
    pub else_ifs: ThinVec<(Span, ExprKey, ScopeKey)>,
    pub else_: Option<(Span, ScopeKey)>,
}

#[derive(Clone, Debug)]
pub struct LambdaExpr {
    pub params: ThinVec<Binding>,
    pub body: ScopeKey,
}

#[derive(Clone, Debug)]
pub struct ReturnExpr {
    pub return_scope: ScopeKey,
    pub return_keyword_span: Span,
    pub expr: Option<ExprKey>,
}

#[derive(Clone, Debug)]
pub struct UnaryOpExpr {
    pub op: UnaryOp,
    pub op_span: Span,
    pub expr: ExprKey,
}

#[derive(Clone, Debug)]
pub enum UnaryOp {
    Minus,
    LNot,
    BNot,
    Deref,
    Borrow,
    BorrowMut,
}

#[derive(Clone, Debug)]
pub struct BinaryOpExpr {
    pub op: BinOp,
    pub op_span_cursor: SpanCursor,
    pub left: ExprKey,
    pub right: ExprKey,
}

#[derive(Clone, Copy, Debug)]
pub enum BinOp {
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
    BOrAssign,
    XorAssign,
    BAndAssign,
    ShrAssign,
    ShlAssign,
}
