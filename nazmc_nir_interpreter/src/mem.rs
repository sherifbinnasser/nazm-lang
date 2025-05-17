use nazmc_data_pool::typed_index_collections::TiVec;
use nazmc_nir::PtrKey;

pub struct Memory {
    stack: TiVec<PtrKey, u8>,
}

impl Memory {
    pub fn new() -> Self {
        Self {
            stack: TiVec::with_capacity(4096),
        }
    }

    fn get_ptr(&self, slice: &[u8]) -> PtrKey {
        let stack_start = self.stack.raw.as_ptr();
        let slice_start = slice.as_ptr();

        let offset = unsafe { slice_start.offset_from(stack_start) };

        // offset is isize, must be >= 0 and fits in u32
        assert!(offset >= 0, "slice is not inside the stack buffer");
        PtrKey(offset as u32)
    }

    pub fn set_top(&mut self, ptr: PtrKey) {
        self.stack.truncate(ptr.0 as usize)
    }

    pub fn get_top(&self) -> PtrKey {
        PtrKey(self.stack.len() as u32)
    }

    pub fn alloc(&mut self, size: usize) -> PtrKey {
        let ptr = self.get_top();
        self.stack.resize(ptr.0 as usize + size, 0);
        ptr
    }

    pub fn get_bytes_at(&self, ptr: PtrKey) -> &[u8] {
        &self.stack.raw[ptr.0 as usize..]
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
        to_usize(bytes).map(|p| PtrKey(p as u32))
    }

    pub fn to_fn_key(bytes: &[u8]) -> Option<FnKey> {
        to_usize(bytes).map(|p| FnKey(p as u32))
    }
}
