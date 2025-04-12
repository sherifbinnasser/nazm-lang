use crate::*;

pub struct NIRAbiTransformer<'a> {
    nir: NIR<'a>,
    structs_layouts: HashMap<StructKey, TypeLayout>,
    tuples_layouts: HashMap<TupleTypeKey, TypeLayout>,
}

struct TypeLayout {
    size: u32,
    align: u32,
    fields: Vec<FieldLayout>,
}

struct FieldLayout {
    offset: u32,
}

impl<'a> NIRAbiTransformer<'a> {
    const PTR_SIZE: u32 = usize::BITS / 8;
    const ABI_AGG_TYPE_MAX_SIZE: u32 = 16;

    fn calculate_type_size(&mut self, type_key: TypeKey) -> u32 {
        match self.nir.types[type_key] {
            Type::Unit => 0,
            Type::Bool | Type::U1 | Type::I1 => 1,
            Type::I2 | Type::U2 => 2,
            Type::Char | Type::F4 | Type::I4 | Type::U4 => 4,
            Type::F8 | Type::I8 | Type::U8 => 8,
            Type::I | Type::U | Type::Ptr(_) | Type::MutPtr(_) | Type::FnPtr(_) => Self::PTR_SIZE,
            Type::Slice(_) | Type::MutSlice(_) => 2 * Self::PTR_SIZE,
            Type::Struct(struct_key) => {
                self.calculate_struct_layout(struct_key);
                self.get_struct_size(struct_key)
            }
            Type::Tuple(tuple_type_key) => {
                self.calculate_tuple_layout(tuple_type_key);
                self.get_tuple_size(tuple_type_key)
            }
            Type::Array(array_type_key) => self.calculate_array_size(array_type_key),
            Type::Lambda(lambda_type_key) => todo!(),
        }
    }

    fn calculate_type_align(&mut self, type_key: TypeKey) -> u32 {
        match self.nir.types[type_key] {
            Type::Unit | Type::Bool | Type::U1 | Type::I1 => 1,
            Type::I2 | Type::U2 => 2,
            Type::Char | Type::F4 | Type::I4 | Type::U4 => 4,
            Type::F8 | Type::I8 | Type::U8 => 8,
            Type::I
            | Type::U
            | Type::Ptr(_)
            | Type::MutPtr(_)
            | Type::FnPtr(_)
            | Type::Slice(_)
            | Type::MutSlice(_) => Self::PTR_SIZE,
            Type::Struct(struct_key) => {
                self.calculate_struct_layout(struct_key);
                self.get_struct_align(struct_key)
            }
            Type::Tuple(tuple_type_key) => {
                self.calculate_tuple_layout(tuple_type_key);
                self.get_tuple_align(tuple_type_key)
            }
            Type::Array(array_type_key) => self.calculate_array_align(array_type_key),
            Type::Lambda(_) => todo!(),
        }
    }

    fn calculate_layout_from_types(&mut self, types: impl Iterator<Item = TypeKey>) -> TypeLayout {
        let mut offset = 0;
        let mut max_align = 1;
        let mut fields = Vec::new();

        for type_key in types {
            let field_size = self.calculate_type_size(type_key);
            let field_align = self.calculate_type_align(type_key);
            max_align = max_align.max(field_align);

            offset = (offset + field_align - 1) & !(field_align - 1);
            fields.push(FieldLayout { offset });
            offset += field_size;
        }

        let size = (offset + max_align - 1) & !(max_align - 1);
        TypeLayout {
            size,
            align: max_align,
            fields,
        }
    }

    fn calculate_struct_layout(&mut self, struct_key: StructKey) {
        if self.structs_layouts.contains_key(&struct_key) {
            return;
        }
        let _struct = std::mem::take(&mut self.nir.structs[struct_key]);
        let field_types = _struct
            .fields_order
            .iter()
            .map(|&field_id| _struct.fields_types[&field_id]);
        let layout = self.calculate_layout_from_types(field_types);
        self.nir.structs[struct_key] = _struct;
        self.structs_layouts.insert(struct_key, layout);
    }

    fn calculate_tuple_layout(&mut self, tuple_type_key: TupleTypeKey) {
        if self.tuples_layouts.contains_key(&tuple_type_key) {
            return;
        }
        let types = self.nir.tuple_types[tuple_type_key].types.clone();
        let layout = self.calculate_layout_from_types(types.into_iter());
        self.tuples_layouts.insert(tuple_type_key, layout);
    }

    #[inline]
    fn get_struct_size(&self, struct_key: StructKey) -> u32 {
        self.structs_layouts.get(&struct_key).unwrap().size
    }

    #[inline]
    fn get_struct_align(&self, struct_key: StructKey) -> u32 {
        self.structs_layouts.get(&struct_key).unwrap().align
    }

    #[inline]
    fn get_tuple_size(&self, tuple_type_key: TupleTypeKey) -> u32 {
        self.tuples_layouts.get(&tuple_type_key).unwrap().size
    }

    #[inline]
    fn get_tuple_align(&self, tuple_type_key: TupleTypeKey) -> u32 {
        self.tuples_layouts.get(&tuple_type_key).unwrap().align
    }

    fn calculate_array_size(&mut self, array_type_key: ArrayTypeKey) -> u32 {
        let ArrayType {
            underlying_typ,
            size,
        } = self.nir.array_types[array_type_key].clone();
        self.calculate_type_size(underlying_typ) * size
    }

    #[inline]
    fn calculate_array_align(&mut self, array_type_key: ArrayTypeKey) -> u32 {
        self.calculate_type_align(self.nir.array_types[array_type_key].underlying_typ)
    }

    fn is_agg_type(&self, type_key: TypeKey) -> bool {
        match self.nir.types[type_key] {
            Type::Struct(_)
            | Type::Slice(_)
            | Type::MutSlice(_)
            | Type::Array(_)
            | Type::Tuple(_) => true,
            Type::Lambda(lambda_type_key) => todo!(),
            _ => false,
        }
    }

    pub fn transform(&mut self) {
        let mut fns = std::mem::take(&mut self.nir.fns);
        for _fn in &mut fns {
            let mut new_args = TiVec::with_capacity(_fn.args.len());
            let mut args_map: TiVec<ArgKey, ArgKey> = TiVec::with_capacity(_fn.args.len());
            let args = std::mem::take(&mut _fn.args);
            for arg in args {
                if self.is_agg_type(arg.typ) {
                    let arg_type_size = self.calculate_type_size(arg.typ);
                    if arg_type_size > Self::ABI_AGG_TYPE_MAX_SIZE {
                        // Treat it as a pointer
                        let arg_key = new_args.push_and_get_key(arg);
                        args_map.push(arg_key);
                    } else {
                    }
                } else {
                    // Scalar types
                    let arg_key = new_args.push_and_get_key(arg);
                    args_map.push(arg_key);
                }
            }
        }
    }
}
