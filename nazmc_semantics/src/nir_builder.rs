use std::{collections::HashMap, usize};

use nazmc_ast::{ExprKey, LetStmKey, ScopeKey};
use nazmc_data_pool::{typed_index_collections::TiVec, DataPoolBuilder, IdKey};
use nazmc_nir::{
    ArrayType, ArrayTypeKey, BasicBlockKey, BindingKey, Const, FnPtrType, FnPtrTypeKey, LValue,
    LambdaType, LambdaTypeKey, RValue, Stm, Struct, StructKey, Temp, TempKey, TupleType,
    TupleTypeKey, Type, TypeKey, CFG,
};

use crate::SemanticsAnalyzer;

#[derive(Default)]
pub(crate) struct NIRBuilder {
    pub(crate) all_types: DataPoolBuilder<TypeKey, Type>,
    pub(crate) all_array_types: DataPoolBuilder<ArrayTypeKey, ArrayType>,
    pub(crate) all_tuple_types: DataPoolBuilder<TupleTypeKey, TupleType>,
    pub(crate) all_lambda_types: DataPoolBuilder<LambdaTypeKey, LambdaType>,
    pub(crate) all_fn_ptr_types: DataPoolBuilder<FnPtrTypeKey, FnPtrType>,
    pub(crate) exprs_types: TiVec<ExprKey, TypeKey>,
}

impl NIRBuilder {
    pub(crate) fn get_unique_type(&mut self, typ: crate::ConcreteType) -> TypeKey {
        let typ = match typ {
            crate::ConcreteType::Composite(composite_type) => match composite_type {
                crate::CompositeType::Slice(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = *underlying_typ else {
                        unreachable!()
                    };
                    Type::Slice(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::Ptr(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = *underlying_typ else {
                        unreachable!()
                    };
                    Type::Ptr(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::PtrMut(underlying_typ) => {
                    let crate::Type::Concrete(underlying_typ) = *underlying_typ else {
                        unreachable!()
                    };
                    Type::Ptr(self.get_unique_type(underlying_typ))
                }
                crate::CompositeType::Ref(underlying_typ) => todo!(),
                crate::CompositeType::RefMut(underlying_typ) => todo!(),
                crate::CompositeType::Array {
                    underlying_typ,
                    size,
                } => {
                    let crate::Type::Concrete(underlying_typ) = *underlying_typ else {
                        unreachable!()
                    };

                    let underlying_typ_key = self.get_unique_type(underlying_typ);

                    let array_typ = ArrayType {
                        underlying_typ: underlying_typ_key,
                        size,
                    };

                    let array_type_key = self.all_array_types.get_key(&array_typ);

                    Type::Array(array_type_key)
                }
                crate::CompositeType::Tuple { types } => {
                    let types = types
                        .into_iter()
                        .map(|typ| {
                            let crate::Type::Concrete(typ) = typ else {
                                unreachable!()
                            };

                            self.get_unique_type(typ)
                        })
                        .collect();

                    let tuple_type = TupleType { types };

                    let tuple_type_key = self.all_tuple_types.get_key(&tuple_type);

                    Type::Tuple(tuple_type_key)
                }
                crate::CompositeType::Lambda {
                    params_types,
                    return_type,
                } => {
                    let params_types = params_types
                        .into_iter()
                        .map(|typ| {
                            let crate::Type::Concrete(typ) = typ else {
                                unreachable!()
                            };

                            self.get_unique_type(typ)
                        })
                        .collect();

                    let crate::Type::Concrete(return_type) = *return_type else {
                        unreachable!()
                    };

                    let return_type = self.get_unique_type(return_type);

                    let lambda_type = LambdaType {
                        params_types,
                        return_type,
                    };

                    let lambda_type_key = self.all_lambda_types.get_key(&lambda_type);

                    Type::Lambda(lambda_type_key)
                }
                crate::CompositeType::FnPtr {
                    params_types,
                    return_type,
                } => {
                    let params_types = params_types
                        .into_iter()
                        .map(|typ| {
                            let crate::Type::Concrete(typ) = typ else {
                                unreachable!()
                            };

                            self.get_unique_type(typ)
                        })
                        .collect();

                    let crate::Type::Concrete(return_type) = *return_type else {
                        unreachable!()
                    };

                    let return_type = self.get_unique_type(return_type);

                    let fn_ptr_type = FnPtrType {
                        params_types,
                        return_type,
                    };

                    let fn_ptr_type_key = self.all_fn_ptr_types.get_key(&fn_ptr_type);

                    Type::FnPtr(fn_ptr_type_key)
                }
            },
            crate::ConcreteType::UnitStruct(unit_struct_key) => todo!(),
            crate::ConcreteType::TupleStruct(tuple_struct_key) => todo!(),
            crate::ConcreteType::FieldsStruct(fields_struct_key) => {
                Type::Struct(StructKey::from(usize::from(fields_struct_key)))
            }
            crate::ConcreteType::Primitive(primitive_type) => match primitive_type {
                crate::type_infer::PrimitiveType::Unit => Type::Unit,
                crate::type_infer::PrimitiveType::I => Type::I,
                crate::type_infer::PrimitiveType::I1 => Type::I1,
                crate::type_infer::PrimitiveType::I2 => Type::I2,
                crate::type_infer::PrimitiveType::I4 => Type::I4,
                crate::type_infer::PrimitiveType::I8 => Type::I8,
                crate::type_infer::PrimitiveType::U => Type::U,
                crate::type_infer::PrimitiveType::U1 => Type::U1,
                crate::type_infer::PrimitiveType::U2 => Type::U2,
                crate::type_infer::PrimitiveType::U4 => Type::U4,
                crate::type_infer::PrimitiveType::U8 => Type::U8,
                crate::type_infer::PrimitiveType::F4 => Type::F4,
                crate::type_infer::PrimitiveType::F8 => Type::F8,
                crate::type_infer::PrimitiveType::Bool => Type::Bool,
                crate::type_infer::PrimitiveType::Char => Type::Char,
                crate::type_infer::PrimitiveType::Str => {
                    Type::Slice(self.all_types.get_key(&Type::U1))
                }
            },
        };

        self.all_types.get_key(&typ)
    }
}

#[derive(Default)]
pub(crate) struct CFGBuilder {
    pub(crate) cfg: CFG,
    pub(crate) locals: HashMap<(LetStmKey, IdKey), BindingKey>,
}

impl<'a> SemanticsAnalyzer<'a> {
    pub(crate) fn lower_scope(&mut self, scope_key: ScopeKey) {
        let stms = std::mem::take(&mut self.ast.scopes[scope_key].stms);
        for stm in stms {
            match stm {
                nazmc_ast::Stm::Let(let_stm_key) => todo!(),
                nazmc_ast::Stm::While(while_stm) => todo!(),
                nazmc_ast::Stm::Expr(expr_key) => {
                    //     let rvalue = self.lower_expr(expr_key);

                    //     let temp_key = self.cfg_builder.cfg.temps.push_and_get_key(Temp {
                    //         typ: self.nir_builder.exprs_types[expr_key],
                    //     });

                    //     let lvalue_key = self
                    //         .cfg_builder
                    //         .cfg
                    //         .lvalues
                    //         .push_and_get_key(LValue::Temp(temp_key));

                    //     let assign = Stm::Assign {
                    //         lhs: lvalue_key,
                    //         rhs: rvalue,
                    //     };
                    //     self.cfg_builder
                    //         .cfg
                    //         .basic_blocks
                    //         .last_mut()
                    //         .unwrap()
                    //         .stms
                    //         .push(assign);
                }
            }
        }
    }

    fn new_temp(&mut self, typ: TypeKey) {
        let temp_key = self.cfg_builder.cfg.temps.push_and_get_key(Temp { typ });
    }

    fn lower_expr(&mut self, expr_key: ExprKey) {
        let typ = self.nir_builder.exprs_types[expr_key];

        let rvalue = match &self.ast.exprs[expr_key].kind {
            nazmc_ast::ExprKind::Unit => RValue::Const(Const::Unit),
            nazmc_ast::ExprKind::Literal(literal_expr) => match *literal_expr {
                nazmc_ast::LiteralExpr::Str(str_key) => RValue::Const(Const::Str(str_key)),
                nazmc_ast::LiteralExpr::Char(ch) => RValue::Const(Const::Char(ch)),
                nazmc_ast::LiteralExpr::Bool(b) => RValue::Const(Const::Bool(b)),
                nazmc_ast::LiteralExpr::Num(num_kind) => match num_kind {
                    nazmc_ast::NumKind::F4(n) => RValue::Const(Const::F4(n)),
                    nazmc_ast::NumKind::F8(n) => RValue::Const(Const::F8(n)),
                    nazmc_ast::NumKind::I(n) => RValue::Const(Const::I(n)),
                    nazmc_ast::NumKind::I1(n) => RValue::Const(Const::I1(n)),
                    nazmc_ast::NumKind::I2(n) => RValue::Const(Const::I2(n)),
                    nazmc_ast::NumKind::I4(n) => RValue::Const(Const::I4(n)),
                    nazmc_ast::NumKind::I8(n) => RValue::Const(Const::I8(n)),
                    nazmc_ast::NumKind::U(n) => RValue::Const(Const::U(n)),
                    nazmc_ast::NumKind::U1(n) => RValue::Const(Const::U1(n)),
                    nazmc_ast::NumKind::U2(n) => RValue::Const(Const::U2(n)),
                    nazmc_ast::NumKind::U4(n) => RValue::Const(Const::U4(n)),
                    nazmc_ast::NumKind::U8(n) => RValue::Const(Const::U8(n)),
                    _ => unreachable!(),
                },
            },
            nazmc_ast::ExprKind::PathNoPkg(path_no_pkg_key) => todo!(),
            nazmc_ast::ExprKind::PathInPkg(path_with_pkg_key) => todo!(),
            nazmc_ast::ExprKind::Call(call_expr) => todo!(),
            nazmc_ast::ExprKind::UnitStruct(unit_struct_path_key) => todo!(),
            nazmc_ast::ExprKind::TupleStruct(tuple_struct_expr) => todo!(),
            nazmc_ast::ExprKind::FieldsStruct(fields_struct_expr) => todo!(),
            nazmc_ast::ExprKind::Field(field_expr) => todo!(),
            nazmc_ast::ExprKind::Idx(idx_expr) => todo!(),
            nazmc_ast::ExprKind::TupleIdx(tuple_idx_expr) => todo!(),
            nazmc_ast::ExprKind::Tuple(thin_vec) => todo!(),
            nazmc_ast::ExprKind::ArrayElemnts(thin_vec) => todo!(),
            nazmc_ast::ExprKind::ArrayElemntsSized(array_elements_sized_expr) => todo!(),
            nazmc_ast::ExprKind::If(if_expr) => todo!(),
            nazmc_ast::ExprKind::Lambda(lambda_expr) => todo!(),
            nazmc_ast::ExprKind::UnaryOp(unary_op_expr) => todo!(),
            nazmc_ast::ExprKind::BinaryOp(binary_op_expr) => todo!(),
            nazmc_ast::ExprKind::Return(return_expr) => todo!(),
            nazmc_ast::ExprKind::Break(scope_key) => todo!(),
            nazmc_ast::ExprKind::Continue(scope_key) => todo!(),
            nazmc_ast::ExprKind::On => todo!(),
        };
    }
}
