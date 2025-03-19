use std::process::exit;

use nazmc_data_pool::ItemInfo;
use nazmc_diagnostics::{eprint_diagnostics, CodeWindow, Diagnostic};

use crate::{BasicBlockKey, Stm, Type, CFG, NIR};

pub struct NIRAnalyzer<'a, 'b: 'a> {
    pub nir: &'a mut NIR<'b>,
    pub errors: Vec<Diagnostic<'a>>,
}

impl<'a, 'b> NIRAnalyzer<'a, 'b>
where
    'b: 'a,
{
    pub fn analyze(mut self) {
        let mut fns = std::mem::take(&mut self.nir.fns);
        for _fn in &mut fns {
            self.remove_dead_code(&mut _fn.cfg);
            if !matches!(self.nir.types[_fn.return_type], Type::Unit) {
                self.check_all_paths_must_return(&_fn.cfg, &_fn.info);
            }
        }
        self.nir.fns = fns;

        if !self.errors.is_empty() {
            eprint_diagnostics(self.errors);
            exit(1);
        }
    }

    fn remove_dead_code(&mut self, cfg: &mut CFG) {
        loop {
            let mut remove = None;
            for (bb_key, bb) in cfg.basic_blocks.iter() {
                if *bb_key == BasicBlockKey::START_BASIC_BLOCK
                    || *bb_key == BasicBlockKey::END_BASIC_BLOCK
                {
                    continue; // Don’t remove special blocks
                }

                if bb.incoming.is_empty() {
                    remove = Some(*bb_key);
                    break;
                }
            }

            if let Some(bb_key) = remove {
                let bb = cfg.basic_blocks.remove(&bb_key).unwrap();

                if let Some(goto) = bb.goto {
                    let branch = cfg.branches.remove(&goto).unwrap();
                    cfg.basic_blocks
                        .get_mut(&branch.to)
                        .unwrap()
                        .incoming
                        .remove(&goto);
                }

                if let Some(cond_goto) = bb.conditional_goto {
                    let branch = cfg.branches.remove(&cond_goto).unwrap();
                    cfg.basic_blocks
                        .get_mut(&branch.to)
                        .unwrap()
                        .incoming
                        .remove(&cond_goto);
                }
                // TODO: Show warning
            } else {
                break;
            }
        }
    }

    fn check_all_paths_must_return(&mut self, cfg: &CFG, info: &ItemInfo) {
        let end_block = &cfg.basic_blocks[&BasicBlockKey::END_BASIC_BLOCK];
        for incoming_branch_key in end_block.incoming.keys() {
            let incoming_branch = &cfg.branches[incoming_branch_key];
            let incoming_bb = &cfg.basic_blocks[&incoming_branch.from];
            if !matches!(incoming_bb.stms.last(), Some(Stm::Return { .. })) {
                let mut code_window =
                    CodeWindow::new(&self.nir.files_infos[info.file_key], info.id_span.start);
                code_window.mark_error(info.id_span, vec![]);
                // FIXME: This message might be inaccurate for lambda expressions
                let error = Diagnostic::error(
                    "الدالة يجب أن ترجع قيمة من كل المسارات الممكنة".into(),
                    vec![code_window],
                );
                self.errors.push(error);
                return;
            }
        }
    }
}
