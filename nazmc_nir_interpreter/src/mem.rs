use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    hash::{Hash, Hasher},
    rc::Rc,
};

use derive_more::{From, Into};
use nazmc_data_pool::{new_data_pool_key, typed_index_collections::TiVec};
use nazmc_nir::{FnKey, StructKey};
new_data_pool_key! { PtrKey }

pub struct Memory {
    stack: TiVec<PtrKey, u8>,
    structs_layouts: HashMap<StructKey, AggLayout>,
}

struct AggLayout {
    offsets: Vec<u32>,
}

impl Memory {
    pub fn new() -> Self {
        Self {
            stack: TiVec::with_capacity(4096),
            structs_layouts: HashMap::new(),
        }
    }

    fn alloc(&mut self, size: usize) -> PtrKey {
        let ptr = PtrKey(self.stack.len() as u32);
        self.stack.resize(ptr.0 as usize + size, 0);
        ptr
    }

    pub fn push_bytes_at(&mut self, ptr: PtrKey, bytes: &[u8]) {
        let start = ptr.0 as usize;
        self.stack.raw[start..start + bytes.len()].copy_from_slice(bytes);
    }

    pub fn push_bytes(&mut self, bytes: &[u8]) -> PtrKey {
        let ptr = self.alloc(bytes.len());
        self.push_bytes_at(ptr, bytes);
        ptr
    }

    pub fn push_u8(&mut self, value: u8) -> PtrKey {
        self.push_bytes(&value.to_le_bytes())
    }

    pub fn push_u16(&mut self, value: u16) -> PtrKey {
        self.push_bytes(&value.to_le_bytes())
    }

    pub fn push_u32(&mut self, value: u32) -> PtrKey {
        self.push_bytes(&value.to_le_bytes())
    }

    pub fn push_u64(&mut self, value: u64) -> PtrKey {
        self.push_bytes(&value.to_le_bytes())
    }

    pub fn push_f32(&mut self, val: f32) -> PtrKey {
        self.push_bytes(&val.to_le_bytes())
    }

    pub fn push_f64(&mut self, val: f64) -> PtrKey {
        self.push_bytes(&val.to_le_bytes())
    }

    pub fn push_char(&mut self, val: char) -> PtrKey {
        self.push_u32(val as u32)
    }

    pub fn push_bool(&mut self, val: bool) -> PtrKey {
        self.push_u8(if val { 1 } else { 0 })
    }

    pub fn push_ptr(&mut self, val: PtrKey) -> PtrKey {
        self.push_u32(val.0)
    }

    // ======== Pops ========

    pub fn pop_bytes(&mut self, size: usize) -> Option<Vec<u8>> {
        if self.stack.len() < size {
            return None;
        }
        let start = self.stack.len() - size;
        let bytes = self.stack.raw[start..].to_vec();
        self.stack.truncate(start);
        Some(bytes)
    }

    pub fn pop_u8(&mut self) -> Option<u8> {
        self.stack.raw.pop()
    }

    pub fn pop_u16(&mut self) -> Option<u16> {
        if self.stack.len() < 2 {
            return None;
        }
        let start = self.stack.len() - 2;
        let bytes = &self.stack.raw[start..];
        let val = u16::from_le_bytes(bytes.try_into().unwrap());
        self.stack.truncate(start);
        Some(val)
    }

    pub fn pop_u32(&mut self) -> Option<u32> {
        if self.stack.len() < 4 {
            return None;
        }
        let start = self.stack.len() - 4;
        let bytes = &self.stack.raw[start..];
        let val = u32::from_le_bytes(bytes.try_into().unwrap());
        self.stack.truncate(start);
        Some(val)
    }

    pub fn pop_u64(&mut self) -> Option<u64> {
        if self.stack.len() < 8 {
            return None;
        }
        let start = self.stack.len() - 8;
        let bytes = &self.stack.raw[start..];
        let val = u64::from_le_bytes(bytes.try_into().unwrap());
        self.stack.truncate(start);
        Some(val)
    }

    pub fn pop_f32(&mut self) -> Option<f32> {
        if self.stack.len() < 4 {
            return None;
        }
        let start = self.stack.len() - 4;
        let bytes = &self.stack.raw[start..];
        let val = f32::from_le_bytes(bytes.try_into().unwrap());
        self.stack.truncate(start);
        Some(val)
    }

    pub fn pop_f64(&mut self) -> Option<f64> {
        if self.stack.len() < 8 {
            return None;
        }
        let start = self.stack.len() - 8;
        let bytes = &self.stack.raw[start..];
        let val = f64::from_le_bytes(bytes.try_into().unwrap());
        self.stack.truncate(start);
        Some(val)
    }

    pub fn pop_char(&mut self) -> Option<char> {
        let code = self.pop_u32()?;
        std::char::from_u32(code)
    }

    pub fn pop_bool(&mut self) -> Option<bool> {
        self.pop_u8().map(|b| b != 0)
    }

    pub fn pop_ptr(&mut self) -> Option<PtrKey> {
        self.pop_u32().map(PtrKey)
    }
}

#[derive(Default, Debug, Clone)]
pub enum MemValue {
    #[default]
    Unit,
    Int(i64),
    UInt(u64),
    Float(f64),
    Bool(bool),
    Char(char),
    FnPtr(FnKey),
    Ptr(PtrKey),
    /// Add Rc around Vec to avoid deep cloning
    Agg(Rc<Vec<PtrKey>>),
}

// #[derive(Default, Debug, Clone)]
// pub struct RcMemValue {
//     pub data: Rc<RefCell<MemValue>>,
// }

// impl RcMemValue {
//     pub fn new(value: MemValue) -> Self {
//         Self {
//             data: Rc::new(RefCell::new(value)),
//         }
//     }

//     pub fn copy(&self) -> Self {
//         let data = match &*self.borrow() {
//             MemValue::Agg(elements) => MemValue::Agg(Rc::new(
//                 elements.iter().map(|element| element.copy()).collect(),
//             )),
//             data => data.clone(),
//         };
//         Self {
//             data: Rc::new(RefCell::new(data)),
//         }
//     }

//     pub fn borrow(&self) -> Ref<'_, MemValue> {
//         self.data.borrow()
//     }

//     pub fn inner(&self) -> MemValue {
//         self.borrow().clone()
//     }
// }

// impl PartialEq for RcMemValue {
//     fn eq(&self, other: &Self) -> bool {
//         Rc::ptr_eq(&self.data, &other.data)
//     }
// }

// impl Eq for RcMemValue {}

// impl Hash for RcMemValue {
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         Rc::as_ptr(&self.data).hash(state);
//     }
// }
