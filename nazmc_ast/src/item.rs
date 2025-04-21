use nazmc_data_pool::IdKey;

use crate::{ConstKey, FnKey, LetStmKey, ScopeKey, StaticKey, StructKey, VisModifier};

#[derive(Clone, Copy, Default, Debug)]
pub enum Item {
    #[default]
    Pkg,
    Struct {
        vis: VisModifier,
        key: StructKey,
    },
    Const {
        vis: VisModifier,
        key: ConstKey,
    },
    Static {
        vis: VisModifier,
        key: StaticKey,
    },
    Fn {
        vis: VisModifier,
        key: FnKey,
    },
    LocalVar {
        id: IdKey,
        key: LetStmKey,
    },
    FnParam {
        idx: u32,
        fn_key: FnKey,
    },
    LambdaParam {
        id: IdKey,
        scope_key: ScopeKey,
    },
}
