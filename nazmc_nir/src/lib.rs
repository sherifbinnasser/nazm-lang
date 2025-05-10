use derive_more::{From, Into};
use nazmc_data_pool::typed_index_collections::TiSlice;
use nazmc_data_pool::{new_data_pool_key, typed_index_collections::TiVec, IdKey, ItemInfo, StrKey};
use nazmc_data_pool::{FileKey, PkgKey};
use nazmc_diagnostics::file_info::FileInfo;
use nazmc_diagnostics::span::Span;
use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use thin_vec::ThinVec;
pub mod fmt;
pub mod nir_analyzer;

new_data_pool_key! { BasicBlockKey }
new_data_pool_key! { BranchKey }
new_data_pool_key! { StructKey }
new_data_pool_key! { StaticKey }
new_data_pool_key! { FnKey }
new_data_pool_key! { ArgKey }
new_data_pool_key! { BindingKey }
new_data_pool_key! { TypeKey }
new_data_pool_key! { ArrayTypeKey }
new_data_pool_key! { TupleTypeKey }
new_data_pool_key! { LambdaTypeKey }
new_data_pool_key! { FnPtrTypeKey }
new_data_pool_key! { TempKey }
new_data_pool_key! { LValueKey }
new_data_pool_key! { ConstKey }

/// NIR, the Nazm Intermediate Representation
#[derive(Default)]
pub struct NIR<'a> {
    pub types: TiVec<TypeKey, Type>,
    pub array_types: TiVec<ArrayTypeKey, ArrayType>,
    pub tuple_types: TiVec<TupleTypeKey, TupleType>,
    pub lambda_types: TiVec<LambdaTypeKey, LambdaType>,
    pub fn_ptr_types: TiVec<FnPtrTypeKey, FnPtrType>,
    pub structs: HashMap<StructKey, Struct>,
    pub statics: TiVec<StaticKey, Static>,
    pub fns: TiVec<FnKey, Fn>,
    pub files_infos: &'a TiSlice<FileKey, FileInfo>,
    pub files_to_pkgs: &'a TiSlice<FileKey, PkgKey>,
    pub pkgs_names: &'a TiSlice<PkgKey, &'a ThinVec<IdKey>>,
    pub id_pool: &'a TiSlice<IdKey, String>,
    pub str_pool: TiVec<StrKey, String>,
    pub consts: HashMap<ConstKey, NamedConst>,
}

#[derive(Default, Debug, Clone)]
pub struct RcValue {
    pub data: Rc<RefCell<Value>>,
}

impl RcValue {
    pub fn new(value: Value) -> Self {
        Self {
            data: Rc::new(RefCell::new(value)),
        }
    }

    pub fn copy(&self) -> Self {
        let data = match &*self.borrow() {
            Value::Agg(elements) => Value::Agg(Rc::new(
                elements.iter().map(|element| element.copy()).collect(),
            )),
            data => data.clone(),
        };
        Self {
            data: Rc::new(RefCell::new(data)),
        }
    }

    pub fn borrow(&self) -> Ref<'_, Value> {
        self.data.borrow()
    }

    pub fn inner(&self) -> Value {
        self.borrow().clone()
    }
}

#[derive(Default, Debug, Clone)]
pub enum Value {
    #[default]
    Unit,
    Int(i64),
    UInt(u64),
    Float(f64),
    Bool(bool),
    Char(char),
    FnPtr(FnKey),
    Ptr(RcValue),
    Agg(Rc<Vec<RcValue>>),
}

#[derive(Default)]
pub struct Struct {
    pub info: ItemInfo,
    pub fields: ThinVec<Field>,
}

pub struct Field {
    pub id: IdKey,
    pub typ: TypeKey,
}

pub struct NamedConst {
    pub info: ItemInfo,
    pub typ: TypeKey,
    pub value: RcValue,
}

pub struct Static {
    pub info: ItemInfo,
    pub typ: TypeKey,
    pub cfg: CFG,
}

pub struct Fn {
    pub info: ItemInfo,
    pub args: TiVec<ArgKey, Arg>,
    pub fn_ptr_type: TypeKey,
    pub return_type: TypeKey,
    pub linkage: FnLinkage,
}

#[derive(Default)]
pub enum FnLinkage {
    #[default]
    ExternWithSameId,
    Extern(StrKey),
    Local(Box<CFG>),
}

impl BasicBlockKey {
    pub const END_BASIC_BLOCK: BasicBlockKey = BasicBlockKey(0);

    pub const START_BASIC_BLOCK: BasicBlockKey = BasicBlockKey(1);
}

#[derive(Default)]
/// A control flow graph of a function or an execution block
pub struct CFG {
    /// The end has a key of 0 and the start block has a key of 1
    pub basic_blocks: HashMap<BasicBlockKey, BasicBlock>,
    /// All branches between basic blocks
    pub branches: HashMap<BranchKey, Branch>,
    /// All lvalues
    pub lvalues: TiVec<LValueKey, LValue>,
    /// All presented bindings
    pub bindings: TiVec<BindingKey, Binding>,
    /// All mutable bindings
    pub mut_bindings: HashMap<BindingKey, ()>,
    /// All temporaries, they are all mutable
    pub temps: TiVec<TempKey, Temp>,
}

pub struct Arg {
    pub id_key: IdKey,
    pub id_span: Span,
    pub typ: TypeKey,
    pub is_mut: bool,
}

pub struct Binding {
    pub id_key: IdKey,
    pub id_span: Span,
    pub typ: TypeKey,
}

pub struct Temp {
    pub typ: TypeKey,
    pub assign_stm_idx: u32,
}

#[derive(Default)]
pub struct BasicBlock {
    pub incoming: HashMap<BranchKey, ()>,
    pub conditional_goto: Option<BranchKey>,
    pub goto: Option<BranchKey>,
    pub stms: ThinVec<Stm>,
}

pub struct Branch {
    pub from: BasicBlockKey,
    pub to: BasicBlockKey,
    pub kind: BranchKind,
}

pub enum BranchKind {
    Straight,
    If(Operand),
    Else,
}

#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    #[default]
    Unit,
    I,
    I1,
    I2,
    I4,
    I8,
    U,
    U1,
    U2,
    U4,
    U8,
    F4,
    F8,
    Bool,
    Char,
    Struct(StructKey),
    Slice(TypeKey),
    MutSlice(TypeKey),
    Ptr(TypeKey),
    MutPtr(TypeKey),
    Array(ArrayTypeKey),
    Tuple(TupleTypeKey),
    Lambda(LambdaTypeKey),
    FnPtr(FnPtrTypeKey),
}

#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArrayType {
    pub underlying_typ: TypeKey,
    pub size: u32,
}

#[derive(Default, Clone, PartialEq, Eq, Hash)]
pub struct TupleType {
    pub types: ThinVec<TypeKey>,
}

#[derive(Default, Clone, PartialEq, Eq, Hash)]
pub struct LambdaType {
    pub params_types: ThinVec<TypeKey>,
    pub return_type: TypeKey,
}

#[derive(Default, Clone, PartialEq, Eq, Hash)]
pub struct FnPtrType {
    pub params_types: ThinVec<TypeKey>,
    pub return_type: TypeKey,
    pub is_vararg: bool,
}

#[derive(Debug)]
pub enum Stm {
    Assign {
        lhs: LValueKey,
        rhs: RValue,
        typ: TypeKey,
    },
    Phi {
        lhs: LValueKey,
        cases: ThinVec<(BasicBlockKey, OperandKind)>,
        typ: TypeKey,
    },
    Return {
        rvalue: RValue,
        typ: TypeKey,
    },
    Drop(LValueKey),
}

#[derive(Clone, Copy, Debug)]
pub struct Operand {
    pub typ: TypeKey,
    pub kind: OperandKind,
}

#[derive(Clone, Copy, Debug)]
pub enum OperandKind {
    LValue(LValueKey),
    Const(Const),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LValue {
    pub typ: TypeKey,
    pub kind: LValueKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LValueKind {
    Binding(BindingKey),
    Arg(ArgKey),
    Static(StaticKey),
    Const(ConstKey),
    Temp(TempKey),
    Deref(LValueKey),
    Field {
        on: LValueKey,
        idx: u32,
    },
    ArrayIdx {
        on: LValueKey,
        idx: LValueKey,
    },
    ArrayConstIdx {
        on: LValueKey,
        idx: u32,
    },
    /// Comes from a mutable lvalue
    MutDeref(LValueKey),
    /// Comes from a mutable lvalue
    MutField {
        on: LValueKey,
        idx: u32,
    },
    /// Comes from a mutable lvalue
    MutArrayIdx {
        on: LValueKey,
        idx: LValueKey,
    },
    /// Comes from a mutable lvalue
    MutArrayConstIdx {
        on: LValueKey,
        idx: u32,
    },
}

#[derive(Debug)]
pub enum RValue {
    Use(Operand),
    Str(StrKey),
    Ref(LValueKey),
    RefMut(LValueKey),
    Tuple(ThinVec<Operand>),
    ArrayElements(ThinVec<Operand>),
    ArrayRepeated {
        repeated: Operand,
        size: u32,
    },
    Struct {
        struct_key: StructKey,
        fields: ThinVec<(u32, Operand)>,
    },
    Cast {
        val: Operand,
        kind: CastKind,
    },
    BinOp {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
    },
    UnaryOp {
        op: UnaryOp,
        operand: Operand,
    },
    Call {
        on: Operand,
        args: ThinVec<Operand>,
    },
}

#[derive(Clone, Debug, Copy)]
pub enum Const {
    Unit,
    Null,
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
    F4(f32),
    F8(f64),
    Bool(bool),
    Char(char),
    Fn(FnKey),
}

impl PartialEq for Const {
    fn eq(&self, other: &Self) -> bool {
        use Const::*;

        match (self, other) {
            (Unit, Unit) => true,
            (I(a), I(b)) => a == b,
            (I1(a), I1(b)) => a == b,
            (I2(a), I2(b)) => a == b,
            (I4(a), I4(b)) => a == b,
            (I8(a), I8(b)) => a == b,
            (U(a), U(b)) => a == b,
            (U1(a), U1(b)) => a == b,
            (U2(a), U2(b)) => a == b,
            (U4(a), U4(b)) => a == b,
            (U8(a), U8(b)) => a == b,
            (F4(a), F4(b)) => a.to_bits() == b.to_bits(), // Handle NaN correctly
            (F8(a), F8(b)) => a.to_bits() == b.to_bits(),
            (Bool(a), Bool(b)) => a == b,
            (Char(a), Char(b)) => a == b,
            (Fn(a), Fn(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Const {}

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    EqualEqual,
    NotEqual,
    GE,
    GT,
    LE,
    LT,
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
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
    LNot,
    BNot,
    Minus,
}

#[derive(Debug, Clone, Copy)]
pub enum CastKind {
    U1ToChar,
    F4ToF8,
    F8ToF4,
    /// Must have same inner type
    ArrayToSlice {
        len: u32,
    },

    // Pointers and addresses
    /// This is like no-op.
    ///
    /// It is used when casting a slice of pointers to another slice of pointers, or array of pointers to another array (same length) of pointers
    PtrToPtr,
    /// Cast only from unsigned ptr-sized integers
    UIntToPtr {
        int_size: Size,
    },
    /// Cast only to unsigned ptr-sized integers
    PtrToUInt {
        int_size: Size,
    },

    // Primtives to integers
    F4ToInt {
        int_size: Size,
    },
    F4ToUInt {
        int_size: Size,
    },
    F8ToInt {
        int_size: Size,
    },
    F8ToUInt {
        int_size: Size,
    },
    BoolToInt {
        int_size: Size,
    },
    BoolToUInt {
        int_size: Size,
    },
    CharToInt {
        int_size: Size,
    },
    CharToUInt {
        int_size: Size,
    },

    // Integers to primitves
    IntToInt {
        int1_size: Size,
        int2_size: Size,
    },
    IntToUInt {
        int1_size: Size,
        int2_size: Size,
    },
    IntToF4 {
        int_size: Size,
    },
    IntToF8 {
        int_size: Size,
    },
    UIntToInt {
        int1_size: Size,
        int2_size: Size,
    },
    UIntToUInt {
        int1_size: Size,
        int2_size: Size,
    },
    UIntToF4 {
        int_size: Size,
    },
    UIntToF8 {
        int_size: Size,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum Size {
    Ptr = 0,
    Byte = 1,
    Word = 2,
    DWord = 4,
    QWord = 8,
}
