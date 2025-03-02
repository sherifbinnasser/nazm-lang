use std::collections::HashMap;

use derive_more::{From, Into};
use nazmc_data_pool::{new_data_pool_key, typed_index_collections::TiVec, IdKey, ItemInfo, StrKey};
use nazmc_diagnostics::span::Span;
use thin_vec::ThinVec;

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

/// NIR, the Nazm Intermediate Representation
pub struct NIR {
    pub types: TiVec<TypeKey, Type>,
    pub array_types: TiVec<ArrayTypeKey, ArrayType>,
    pub tuple_types: TiVec<TupleTypeKey, TupleType>,
    pub lambda_types: TiVec<LambdaTypeKey, LambdaType>,
    pub fn_ptr_types: TiVec<FnPtrTypeKey, FnPtrType>,
    pub structs: TiVec<StructKey, Struct>,
    pub statics: TiVec<StaticKey, Static>,
    pub fns: TiVec<FnKey, Fn>,
}

pub struct Struct {
    pub info: ItemInfo,
    pub fields: HashMap<IdKey, TypeKey>,
}

pub struct Static {
    pub info: ItemInfo,
    pub typ: TypeKey,
    pub cfg: CFG,
}

pub struct Fn {
    pub info: ItemInfo,
    pub args: TiVec<ArgKey, Arg>,
    pub cfg: CFG,
}

pub const START_BASIC_BLOCK: BasicBlockKey = BasicBlockKey(0);

pub const END_BASIC_BLOCK: BasicBlockKey = BasicBlockKey(1);

#[derive(Default)]
/// A control flow graph of a function or an execution block
pub struct CFG {
    /// The start has a key of 0 and the end block has a key of 1
    pub basic_blocks: TiVec<BasicBlockKey, BasicBlock>,
    /// All branches between basic blocks
    pub branches: TiVec<BranchKey, Branch>,
    /// All lvalues
    pub lvalues: TiVec<LValueKey, LValue>,
    /// All presented bindings
    pub bindings: TiVec<BindingKey, Binding>,
    /// All mutable bindings
    pub mut_bindings: HashMap<BindingKey, ()>,
    /// All temporaries
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
}

pub struct BasicBlock {
    pub incoming: ThinVec<BranchKey>,
    pub conditional_goto: Option<BranchKey>,
    pub goto: BranchKey,
    pub stms: ThinVec<Stm>,
}

pub struct Branch {
    pub from: BasicBlockKey,
    pub to: BasicBlockKey,
    pub kind: BranchKind,
}

pub enum BranchKind {
    Straight,
    JZ,
    JNZ,
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
}

pub enum Stm {
    Assign { lhs: LValueKey, rhs: RValue },
    Drop(LValueKey),
}

pub enum LValue {
    ReturnPtr,
    Binding(BindingKey),
    Temp(TempKey),
    Arg(ArgKey),
    Static(StaticKey),
    Fn(FnKey),
    Deref(LValueKey),
    Field { on: LValueKey, field_id: IdKey },
    TupleIdx { on: LValueKey, idx: u32 },
    ArrayIdx { on: LValueKey, idx: LValueKey },
}

pub enum RValue {
    Const(Const),
    Use(LValueKey),
    Ref(LValueKey),
    RefMut(LValueKey),
    Tuple(ThinVec<LValueKey>),
    Struct(ThinVec<(IdKey, LValueKey)>),
    ArrayElements(ThinVec<LValueKey>),
    Array {
        repeated: LValueKey,
        size: u32,
    },
    Cast {
        val: LValueKey,
        to: TypeKey,
    },
    BinOp {
        op: BinOp,
        lhs: LValueKey,
        rhs: LValueKey,
    },
    UnaryOp {
        op: UnaryOp,
        operand: LValueKey,
    },
    Call {
        on: LValueKey,
        args: ThinVec<LValueKey>,
    },
}

pub enum Const {
    Unit,
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
    Str(StrKey),
    Struct(ThinVec<Const>),
    Tuple(ThinVec<Const>),
    Array(ThinVec<Const>),
}

pub enum BinOp {
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
}

pub enum UnaryOp {
    LNot,
    BNot,
    Minus,
}

use std::fs::File;
use std::io::{self, Write};

impl CFG {
    pub fn write_dot(&self, filename: &str) -> io::Result<()> {
        let mut file = File::create(filename)?;

        writeln!(file, "digraph CFG {{")?;
        writeln!(file, "    node [shape=rect];")?;

        // Write basic blocks
        for (bb_key, _) in self.basic_blocks.iter_enumerated() {
            let label = if bb_key == START_BASIC_BLOCK {
                "Start"
            } else if bb_key == END_BASIC_BLOCK {
                "End"
            } else {
                &format!("BB {:?}", bb_key)
            };
            writeln!(file, "    {:?} [label=\"{}\", style=bold];", bb_key, label)?;
        }

        // Write edges
        for branch in &self.branches {
            let label = match branch.kind {
                BranchKind::Straight => "",
                BranchKind::JZ => "JZ",
                BranchKind::JNZ => "JNZ",
            };
            writeln!(
                file,
                "    {:?} -> {:?} [label=\"{}\"]",
                branch.from, branch.to, label
            )?;
        }

        writeln!(file, "}}")?;
        Ok(())
    }
}
