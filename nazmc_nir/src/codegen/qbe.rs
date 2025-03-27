use crate::NIR;

pub struct QbeCodegen<'a> {
    module: qbe::Module<'a>,
    nir: NIR<'a>,
}

impl<'a> QbeCodegen<'a> {
    pub fn new(nir: NIR<'a>) -> Self {
        Self {
            module: qbe::Module::new(),
            nir,
        }
    }

    pub fn lower(mut self) -> qbe::Module<'a> {
        // TODO
        self.module
    }
}
