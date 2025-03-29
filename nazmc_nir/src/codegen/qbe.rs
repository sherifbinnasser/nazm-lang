use crate::*;

pub struct QbeCodegen<'a> {
    lowered_types: HashMap<TypeKey, qbe::Type>,
    fn_names: HashMap<FnKey, String>,
    module: qbe::Module,
    nir: NIR<'a>,
}

impl<'a> QbeCodegen<'a> {
    pub fn new(nir: NIR<'a>) -> Self {
        Self {
            lowered_types: HashMap::with_capacity(nir.types.len()),
            fn_names: HashMap::with_capacity(nir.fns.len()),
            module: qbe::Module::new(),
            nir,
        }
    }

    pub fn lower(mut self) -> qbe::Module {
        self.lower_types();
        // TODO
        self.module
    }

    fn fmt_pkg_name(&self, pkg_key: PkgKey) -> String {
        self.nir.pkgs_names[pkg_key]
            .iter()
            .map(|id| self.nir.id_pool[*id].as_str())
            .collect::<Vec<_>>()
            .join(".")
    }

    fn fmt_item_name(&self, item_info: ItemInfo) -> String {
        let pkg = self.fmt_pkg_name(self.nir.files_to_pkgs[item_info.file_key]);
        let name = &self.nir.id_pool[item_info.id_key];
        if pkg.is_empty() {
            name.to_owned()
        } else {
            format!("{}.{}", pkg, name)
        }
    }

    fn lower_types(&mut self) {
        for ty in self.nir.types.keys() {
            self.lower_type(ty);
        }
    }

    fn lower_type(&mut self, type_key: TypeKey) -> qbe::Type {
        if let Some(ty) = self.lowered_types.get(&type_key) {
            ty.clone()
        } else {
            let qbe_ty = match self.nir.types[type_key] {
                Type::Unit => qbe::Type::Void,
                Type::I | Type::U => qbe::Type::Long,
                Type::Bool | Type::I1 | Type::U1 => qbe::Type::Byte,
                Type::I2 | Type::U2 => qbe::Type::Halfword,
                Type::Char | Type::I4 | Type::U4 => qbe::Type::Word,
                Type::I8 | Type::U8 => qbe::Type::Long,
                Type::F4 => qbe::Type::Single,
                Type::F8 => qbe::Type::Double,
                Type::Ptr(_) | Type::MutPtr(_) | Type::FnPtr(_) => qbe::Type::Long,
                Type::Struct(struct_key) => {
                    let _struct = &self.nir.structs[struct_key];
                    let name = self.fmt_item_name(_struct.info);
                    let items = _struct
                        .fields
                        .clone()
                        .values()
                        .map(|ty| (self.lower_type(*ty), 0))
                        .collect();
                    let type_def = qbe::TypeDef {
                        name,
                        align: None,
                        items,
                    };
                    let type_def = self.module.add_type(type_def);
                    qbe::Type::Aggregate(type_def)
                }
                Type::Tuple(tuple_type_key) => {
                    let tuple = &self.nir.tuple_types[tuple_type_key];
                    let name = format!("Tuple{}", tuple_type_key.0);
                    let items = tuple
                        .types
                        .clone()
                        .iter()
                        .map(|ty| (self.lower_type(*ty), 0))
                        .collect();
                    let type_def = qbe::TypeDef {
                        name,
                        align: None,
                        items,
                    };
                    let type_def = self.module.add_type(type_def);
                    qbe::Type::Aggregate(type_def)
                }
                Type::Slice(type_key) => todo!(),
                Type::MutSlice(type_key) => todo!(),
                Type::Array(array_type_key) => todo!(),
                Type::Lambda(lambda_type_key) => todo!(),
            };
            self.lowered_types.insert(type_key, qbe_ty.clone());
            qbe_ty
        }
    }
}
