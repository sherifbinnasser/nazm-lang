use derive_more::{From, Into};
use nazmc_diagnostics::span::Span;
use std::{collections::HashMap, hash::Hash, marker::PhantomData, usize};
pub use typed_index_collections;
use typed_index_collections::TiVec;

#[macro_export]
macro_rules! new_data_pool_key {
    ($name: ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default, Ord, PartialOrd, From, Into)]
        pub struct $name(pub u32);

        impl From<usize> for $name {
            fn from(value: usize) -> Self {
                Self(value as u32)
            }
        }

        impl From<$name> for usize {
            fn from(value: $name) -> Self {
                value.0 as Self
            }
        }
    };
}

new_data_pool_key! { IdKey }
new_data_pool_key! { StrKey }
new_data_pool_key! { PkgKey }
new_data_pool_key! { FileKey }

#[derive(Clone, Copy, Default)]
pub struct ItemInfo {
    pub file_key: FileKey,
    pub id_key: IdKey,
    pub id_span: Span,
}

pub type IdPoolBuilder = DataPoolBuilder<IdKey, String>;

pub type StrPoolBuilder = DataPoolBuilder<StrKey, String>;

pub struct DataPoolBuilder<K, V>
where
    K: From<usize> + Into<usize>,
    V: Eq + Hash + Clone,
{
    pub map: HashMap<V, usize>,
    phantom_data: PhantomData<K>,
}

impl<K, V> DataPoolBuilder<K, V>
where
    K: From<usize> + Into<usize>,
    V: Eq + Hash + Clone,
{
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            phantom_data: PhantomData,
        }
    }

    pub fn get_key(&mut self, val: &V) -> K {
        match self.map.get(val) {
            Some(index) => (*index).into(),
            None => {
                let index = self.map.len();
                self.map.insert(val.clone(), index);
                index.into()
            }
        }
    }

    pub fn build(self) -> TiVec<K, V> {
        let len = self.map.len();

        let mut data = TiVec::with_capacity(len);

        let ptr: *mut V = data.as_mut_ptr();

        for (val, index) in self.map {
            unsafe {
                ptr.add(index).write(val);
            }
        }

        unsafe {
            data.set_len(len);
        }

        data
    }

    pub fn build_ref(&self) -> TiVec<K, &V> {
        let len = self.map.len();

        let mut data = TiVec::with_capacity(len);

        let ptr: *mut &V = data.as_mut_ptr();

        for (val, index) in &self.map {
            unsafe {
                ptr.add(*index).write(val);
            }
        }

        unsafe {
            data.set_len(len);
        }

        data
    }
}

impl<K, V> Default for DataPoolBuilder<K, V>
where
    K: From<usize> + Into<usize>,
    V: Eq + Hash + Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

pub type IdPool = TiVec<IdKey, String>;

pub type StrPool = TiVec<StrKey, String>;

impl PkgKey {
    pub const TOP: Self = Self(0);
}

impl IdKey {
    pub const EMPTY: Self = Self(0);
    pub const UNIT: Self = Self(1); // "()"
    pub const MAIN: Self = Self(2); // "البداية"
    pub const IMPLICIT_LAMBDA_PARAM: Self = Self(3); // "س"
    pub const I_TYPE: Self = Self(4); // "ص"
    pub const I1_TYPE: Self = Self(5); // "1ص"
    pub const I2_TYPE: Self = Self(6); // "2ص"
    pub const I4_TYPE: Self = Self(7); // "4ص"
    pub const I8_TYPE: Self = Self(8); // "8ص"
    pub const U_TYPE: Self = Self(9); // "ط"
    pub const U1_TYPE: Self = Self(10); // "1ط"
    pub const U2_TYPE: Self = Self(11); // "2ط"
    pub const U4_TYPE: Self = Self(12); // "4ط"
    pub const U8_TYPE: Self = Self(13); // "8ط"
    pub const F4_TYPE: Self = Self(14); // "4ع"
    pub const F8_TYPE: Self = Self(15); // "ع8"
    pub const BOOL_TYPE: Self = Self(16); // "شرط"
    pub const CHAR_TYPE: Self = Self(17); // "حرف"
}

impl IdPoolBuilder {
    pub fn register_defined_ids(&mut self) {
        self.get_key(&"".to_string());
        self.get_key(&"()".to_string());
        self.get_key(&"البداية".to_string());
        self.get_key(&"س".to_string());

        self.get_key(&"ص".to_string());
        self.get_key(&"ص1".to_string());
        self.get_key(&"ص2".to_string());
        self.get_key(&"ص4".to_string());
        self.get_key(&"ص8".to_string());

        self.get_key(&"ط".to_string());
        self.get_key(&"ط1".to_string());
        self.get_key(&"ط2".to_string());
        self.get_key(&"ط4".to_string());
        self.get_key(&"ط8".to_string());

        self.get_key(&"ع4".to_string());
        self.get_key(&"ع8".to_string());

        self.get_key(&"شرط".to_string());
        self.get_key(&"حرف".to_string());
    }
}
