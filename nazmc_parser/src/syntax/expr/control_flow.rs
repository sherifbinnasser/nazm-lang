use super::*;

#[derive(NazmcParse, Debug)]
pub(crate) struct IfExpr {
    pub(crate) if_keyword: IfKeyword,
    pub(crate) conditional_block: ConditionalBlock,
    pub(crate) else_ifs: Vec<ElseIfClause>,
    pub(crate) else_cluase: Option<ElseClause>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ElseIfClause {
    pub(crate) else_keyword: ElseKeyword,
    pub(crate) if_keyword: IfKeyword,
    pub(crate) conditional_block: ConditionalBlock,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ElseClause {
    pub(crate) else_keyword: ElseKeyword,
    /// This must be checked that it doesn't have a lambda arrow
    pub(crate) block: ParseResult<LambdaExpr>,
}

#[derive(NazmcParse, Debug)]
pub(crate) struct WhenExpr {
    pub(crate) when_keyword: WhenKeyword,
    pub(crate) expr: ParseResult<Expr>,
    // TODO
}

#[derive(NazmcParse, Debug)]
pub(crate) struct ReturnExpr {
    pub(crate) return_keyword: ReturnKeyword,
    pub(crate) expr: Option<Expr>,
}

#[derive(Debug)]
pub(crate) struct ConditionalBlock {
    pub(crate) condition: ParseResult<Expr>,
    /// This must be checked that it doesn't have a lambda arrow
    pub(crate) block: ParseResult<LambdaExpr>,
}

impl NazmcParse for ParseResult<ConditionalBlock> {
    fn parse(iter: &mut TokensIter) -> Self {
        let mut condition = ParseResult::<Expr>::parse(iter)?;

        let len = condition.rights.len();

        let mut last_primary_ex = if len == 0 {
            &mut condition.left
        } else {
            match &mut condition.rights[len - 1] {
                BinExpr::Normal(NormalBinExpr {
                    right: Ok(ref mut node),
                    ..
                }) => node,
                BinExpr::Normal(NormalBinExpr {
                    right: Err(err), ..
                }) => {
                    return Ok(ConditionalBlock {
                        block: Err(err.clone()), // No expressions found after the bin op (so no lambda block is found after the op) so clone the error
                        condition: Ok(condition),
                    });
                }
                BinExpr::Cast(_) => {
                    // No block is found after type casting
                    let parse_err = match iter.recent() {
                        Some(_) => Err(ParseErr {
                            found_token_index: iter.peek_idx - 1,
                        }),
                        None => ParseErr::eof(),
                    };

                    return Ok(ConditionalBlock {
                        condition: Ok(condition),
                        block: parse_err,
                    });
                }
            }
        };

        loop {
            match &mut last_primary_ex.kind {
                PrimaryExprKind::Unary(unary_expr) => {
                    last_primary_ex = unary_expr.expr.as_mut().unwrap();
                }
                PrimaryExprKind::Atomic(atomic_expr) => break,
            }
        }

        let len = last_primary_ex.inner_access.len();

        let last_post_ops = if len == 0 {
            &mut last_primary_ex.post_ops
        } else {
            &mut last_primary_ex.inner_access[len - 1].post_ops
        };

        match last_post_ops.last() {
            Some(PostOpExpr::Lambda(LambdaExpr {
                lambda_arrow: Option::None, // No '->' in the lambda expression
                ..
            })) => {} // Block is found
            _ => {
                // No block is found (or found a lambda block with '->')
                let parse_err = match iter.recent() {
                    Some(_) => Err(ParseErr {
                        found_token_index: iter.peek_idx - 1,
                    }),
                    None => ParseErr::eof(),
                };
                return Ok(ConditionalBlock {
                    condition: Ok(condition),
                    block: parse_err,
                });
            }
        };

        let Some(PostOpExpr::Lambda(lambda)) = last_post_ops.pop() else {
            unreachable!()
        };

        Ok(ConditionalBlock {
            condition: Ok(condition),
            block: Ok(lambda),
        })
    }
}
