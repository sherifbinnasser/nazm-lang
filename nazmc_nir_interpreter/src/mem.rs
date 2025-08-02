use bimap::BiMap;
use nazmc_data_pool::typed_index_collections::TiVec;
use nazmc_nir::PtrKey;

pub struct Memory {
    stack: TiVec<PtrKey, u8>,
    const_mem_len: isize,
    pub unproven_ptrs: BiMap<PtrKey, usize>,
}

pub(crate) enum PtrCmp {
    Eq,
    Ne,
    Ge,
    Gt,
    Le,
    Lt,
}

impl Default for Memory {
    fn default() -> Self {
        let mut s = Self {
            stack: TiVec::with_capacity(4096),
            const_mem_len: 0,
            unproven_ptrs: BiMap::new(),
        };
        s.new_unproven_ptr(0);
        s
    }
}

impl Memory {
    pub fn new_unproven_ptr(&mut self, value: usize) -> PtrKey {
        if let Some(ptr) = self.unproven_ptrs.get_by_right(&value) {
            *ptr
        } else {
            let len = self.unproven_ptrs.len() as isize;
            let ptr = PtrKey(-(len + 1));
            self.unproven_ptrs.insert(ptr, value);
            ptr
        }
    }

    pub fn add_ptr_offset(&mut self, ptr: PtrKey, offset: isize) -> PtrKey {
        if ptr.0 < 0 {
            let ptr_addr = *self.unproven_ptrs.get_by_left(&ptr).unwrap() as isize;
            let new_addr = ptr_addr + offset;
            self.new_unproven_ptr(new_addr as usize)
        } else {
            let ptr_addr = ptr.0;
            let mut new_addr = ptr_addr + offset;
            if new_addr < 0 {
                let raw = (ptr.0 as i128 + offset as i128).rem_euclid(isize::MAX as i128 + 1);
                new_addr = raw as isize;
            }
            PtrKey(new_addr)
        }
    }

    pub(crate) fn ptr_cmp(&self, lhs: PtrKey, rhs: PtrKey, cmp: PtrCmp) -> bool {
        let (lhs, rhs) = if lhs.0 < 0 && rhs.0 < 0 {
            let lhs = *self.unproven_ptrs.get_by_left(&lhs).unwrap();
            let rhs = *self.unproven_ptrs.get_by_left(&rhs).unwrap();
            (lhs, rhs)
        } else if lhs.0 >= 0 && rhs.0 >= 0 {
            (lhs.0 as usize, rhs.0 as usize)
        } else {
            return false;
        };
        match cmp {
            PtrCmp::Eq => lhs == rhs,
            PtrCmp::Ne => lhs != rhs,
            PtrCmp::Ge => lhs >= rhs,
            PtrCmp::Gt => lhs > rhs,
            PtrCmp::Le => lhs <= rhs,
            PtrCmp::Lt => lhs < rhs,
        }
    }

    fn get_ptr(&self, slice: &[u8]) -> PtrKey {
        let stack_start = self.stack.raw.as_ptr();
        let slice_start = slice.as_ptr();

        let offset = unsafe { slice_start.offset_from(stack_start) };

        // offset is isize, must be >= 0 and fits in u32
        assert!(offset >= 0, "slice is not inside the stack buffer");
        PtrKey(offset as isize)
    }

    pub fn set_const_mem_len_to_top(&mut self) {
        self.const_mem_len = self.get_top().0;
    }

    pub fn get_const_mem_len(&self) -> isize {
        self.const_mem_len
    }

    pub fn set_top(&mut self, ptr: PtrKey) {
        self.stack.truncate(ptr.0 as usize)
    }

    pub fn get_top(&self) -> PtrKey {
        PtrKey(self.stack.len() as isize)
    }

    pub fn alloc(&mut self, size: usize) -> PtrKey {
        let ptr = self.get_top();
        self.stack.resize(ptr.0 as usize + size, 0);
        ptr
    }

    pub fn get_bytes_at(&self, ptr: PtrKey, size: usize) -> &[u8] {
        let ptr = ptr.0 as usize;
        &self.stack.raw[ptr..ptr + size]
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

    pub fn push_usize(&mut self, value: usize) -> PtrKey {
        self.push_bytes(&value.to_le_bytes())
    }

    pub fn push_ptr(&mut self, val: PtrKey) -> PtrKey {
        self.push_usize(val.0 as usize)
    }
}

/// Helpers for converting &[u8] to primitive types (little-endian)

pub mod bytes {

    use std::convert::TryInto;

    use nazmc_nir::{FnKey, PtrKey};

    pub fn to_u8(bytes: &[u8]) -> Option<u8> {
        bytes.get(0).copied()
    }

    pub fn to_u16(bytes: &[u8]) -> Option<u16> {
        bytes
            .get(..2)
            .and_then(|b| Some(u16::from_le_bytes(b.try_into().ok()?)))
    }

    pub fn to_u32(bytes: &[u8]) -> Option<u32> {
        bytes
            .get(..4)
            .and_then(|b| Some(u32::from_le_bytes(b.try_into().ok()?)))
    }

    pub fn to_u64(bytes: &[u8]) -> Option<u64> {
        bytes
            .get(..8)
            .and_then(|b| Some(u64::from_le_bytes(b.try_into().ok()?)))
    }

    pub fn to_usize(bytes: &[u8]) -> Option<usize> {
        match std::mem::size_of::<usize>() {
            4 => to_u32(bytes).map(|v| v as usize),
            8 => to_u64(bytes).map(|v| v as usize),
            _ => None,
        }
    }

    pub fn to_i8(bytes: &[u8]) -> Option<i8> {
        bytes.get(0).copied().map(|b| b as i8)
    }

    pub fn to_i16(bytes: &[u8]) -> Option<i16> {
        bytes
            .get(..2)
            .and_then(|b| Some(i16::from_le_bytes(b.try_into().ok()?)))
    }

    pub fn to_i32(bytes: &[u8]) -> Option<i32> {
        bytes
            .get(..4)
            .and_then(|b| Some(i32::from_le_bytes(b.try_into().ok()?)))
    }

    pub fn to_i64(bytes: &[u8]) -> Option<i64> {
        bytes
            .get(..8)
            .and_then(|b| Some(i64::from_le_bytes(b.try_into().ok()?)))
    }

    pub fn to_isize(bytes: &[u8]) -> Option<isize> {
        match std::mem::size_of::<isize>() {
            4 => to_i32(bytes).map(|v| v as isize),
            8 => to_i64(bytes).map(|v| v as isize),
            _ => None,
        }
    }

    pub fn to_f32(bytes: &[u8]) -> Option<f32> {
        bytes
            .get(..4)
            .and_then(|b| Some(f32::from_le_bytes(b.try_into().ok()?)))
    }

    pub fn to_f64(bytes: &[u8]) -> Option<f64> {
        bytes
            .get(..8)
            .and_then(|b| Some(f64::from_le_bytes(b.try_into().ok()?)))
    }

    pub fn to_char(bytes: &[u8]) -> Option<char> {
        to_u32(bytes).and_then(std::char::from_u32)
    }

    pub fn to_bool(bytes: &[u8]) -> Option<bool> {
        to_u8(bytes).map(|b| b != 0)
    }

    pub fn to_ptr_key(bytes: &[u8]) -> Option<PtrKey> {
        to_isize(bytes).map(|p| PtrKey(p))
    }

    pub fn to_fn_key(bytes: &[u8]) -> Option<FnKey> {
        to_usize(bytes).map(|p| FnKey(p as u32))
    }
}
