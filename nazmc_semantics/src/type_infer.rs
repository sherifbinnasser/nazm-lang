use nazmc_ast::{FieldsStructKey, TupleStructKey, UnitStructKey};
use nazmc_data_pool::typed_index_collections::TiVec;
use thin_vec::ThinVec;

use derive_more::{From, Into};
use nazmc_data_pool::new_data_pool_key;

new_data_pool_key! { TypeVarKey }

#[derive(Debug, Default)]
pub(crate) struct TypeInferenceCtx {
    pub(crate) ty_vars: TiVec<TypeVarKey, TypeVarSubstitution>,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(crate) enum TypeVarSubstitution {
    #[default]
    Any,
    Never,
    Error,
    ConstrainedNumber(NumberConstraints),
    Determined(Type),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum NumberConstraints {
    #[default]
    Any,
    Signed,
    Int,
    SignedInt,
    Float,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    TypeVar(TypeVarKey),
    Concrete(ConcreteType),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConcreteType {
    Composite(CompositeType),
    UnitStruct(UnitStructKey),
    TupleStruct(TupleStructKey),
    FieldsStruct(FieldsStructKey),
    Primitive(PrimitiveType),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompositeType {
    Slice(Box<Type>),
    Ptr(Box<Type>),
    PtrMut(Box<Type>),
    Array {
        underlying_typ: Box<Type>,
        size: u32,
    },
    Tuple {
        types: ThinVec<Type>,
    },
    Lambda {
        params_types: ThinVec<Type>,
        return_type: Box<Type>,
    },
    FnPtr {
        params_types: ThinVec<Type>,
        return_type: Box<Type>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum PrimitiveType {
    #[default]
    Unit,
    I,
    I1,
    I2,
    I4,
    I8,
    U,
    U1,
    U2,
    U4,
    U8,
    F4,
    F8,
    Bool,
    Char,
}

impl NumberConstraints {
    fn get_intersection(
        one: NumberConstraints,
        two: NumberConstraints,
    ) -> Option<NumberConstraints> {
        use NumberConstraints::*;
        match (one, two) {
            // Any intersected with anything is that thing.
            (Any, x) | (x, Any) => Some(x),

            (Signed, Signed) => Some(Signed),
            (Int, Int) => Some(Int),

            (Signed, Int)
            | (Int, Signed)
            | (Signed, SignedInt)
            | (SignedInt, Signed)
            | (Int, SignedInt)
            | (SignedInt, Int)
            | (SignedInt, SignedInt) => Some(SignedInt),

            (Signed, Float) | (Float, Signed) | (Float, Float) => Some(Float),

            (Int, Float) | (Float, Int) | (SignedInt, Float) | (Float, SignedInt) => None,
        }
    }

    fn contains(&self, concrete_ty: &ConcreteType) -> bool {
        use NumberConstraints::*;
        use PrimitiveType::*;

        // We only handle Primitive types.
        let ConcreteType::Primitive(prim_ty) = concrete_ty else {
            return false;
        };
        match self {
            Any => matches!(
                prim_ty,
                I | I1 | I2 | I4 | I8 | U | U1 | U2 | U4 | U8 | F4 | F8
            ),
            Signed => matches!(prim_ty, I | I1 | I2 | I4 | I8 | F4 | F8),
            Int => matches!(prim_ty, I | I1 | I2 | I4 | I8 | U | U1 | U2 | U4 | U8),
            SignedInt => matches!(prim_ty, I | I1 | I2 | I4 | I8),
            Float => matches!(prim_ty, F4 | F8),
        }
    }
}

impl Type {
    fn occurs_check(&self, of: TypeVarKey) -> bool {
        match self {
            Type::TypeVar(type_var_key) => *type_var_key == of,
            Type::Concrete(concrete_typ) => concrete_typ.occurs_check(of),
        }
    }
}

impl ConcreteType {
    fn occurs_check(&self, of: TypeVarKey) -> bool {
        match self {
            ConcreteType::Composite(composite_typ) => composite_typ.occurs_check(of),
            _ => false,
        }
    }
}

impl CompositeType {
    pub fn occurs_check(&self, of: TypeVarKey) -> bool {
        match self {
            CompositeType::Slice(underlying_typ)
            | CompositeType::Ptr(underlying_typ)
            | CompositeType::PtrMut(underlying_typ)
            | CompositeType::Array {
                underlying_typ,
                size: _,
            } => underlying_typ.occurs_check(of),
            CompositeType::Tuple { types } => types.iter().any(|ty| ty.occurs_check(of)),
            CompositeType::Lambda {
                params_types,
                return_type,
            }
            | CompositeType::FnPtr {
                params_types,
                return_type,
            } => params_types.iter().any(|ty| ty.occurs_check(of)) || return_type.occurs_check(of),
        }
    }
}

impl Type {
    /// Create a new `TyVar` type with the given key.
    pub fn type_var(ty_var_key: TypeVarKey) -> Self {
        Self::TypeVar(ty_var_key)
    }

    pub fn composite(composite_type: CompositeType) -> Self {
        Self::Concrete(ConcreteType::Composite(composite_type))
    }

    pub fn unit_struct(unit_struct_key: UnitStructKey) -> Self {
        Self::Concrete(ConcreteType::UnitStruct(unit_struct_key))
    }

    pub fn fields_struct(fields_struct_key: FieldsStructKey) -> Self {
        Self::Concrete(ConcreteType::FieldsStruct(fields_struct_key))
    }

    pub fn primitive(primitive_type: PrimitiveType) -> Self {
        Self::Concrete(ConcreteType::Primitive(primitive_type))
    }

    /// Create a `Slice` type.
    pub fn slice(inner: Type) -> Self {
        Self::composite(CompositeType::Slice(Box::new(inner)))
    }

    /// Create a `Ptr` type.
    pub fn ptr(inner: Type) -> Self {
        Self::composite(CompositeType::Ptr(Box::new(inner)))
    }

    /// Create a `PtrMut` type.
    pub fn ptr_mut(inner: Type) -> Self {
        Self::composite(CompositeType::PtrMut(Box::new(inner)))
    }

    /// Create a `Array` type.
    pub fn array(underlying_typ: Type, size: u32) -> Self {
        Self::composite(CompositeType::Array {
            underlying_typ: Box::new(underlying_typ),
            size,
        })
    }

    /// Create a `Tuple` type.
    pub fn tuple(types: impl IntoIterator<Item = Type>) -> Self {
        Self::composite(CompositeType::Tuple {
            types: types.into_iter().collect(),
        })
    }

    /// Create a `Lambda` type.
    pub fn lambda(params: impl IntoIterator<Item = Type>, return_type: Type) -> Self {
        Self::composite(CompositeType::Lambda {
            params_types: params.into_iter().collect(),
            return_type: Box::new(return_type),
        })
    }

    /// Create a `FnPtr` type.
    pub fn fn_ptr(params: impl IntoIterator<Item = Type>, return_type: Type) -> Self {
        Self::composite(CompositeType::FnPtr {
            params_types: params.into_iter().collect(),
            return_type: Box::new(return_type),
        })
    }

    /// Create a `ConcreteType::Unit` type.
    pub fn unit() -> Self {
        Self::primitive(PrimitiveType::Unit)
    }

    /// Create a `ConcreteType::I` type.
    pub fn i() -> Self {
        Self::primitive(PrimitiveType::I)
    }

    /// Create a `ConcreteType::I1` type.
    pub fn i1() -> Self {
        Self::primitive(PrimitiveType::I1)
    }

    /// Create a `ConcreteType::I2` type.
    pub fn i2() -> Self {
        Self::primitive(PrimitiveType::I2)
    }

    /// Create a `ConcreteType::I4` type.
    pub fn i4() -> Self {
        Self::primitive(PrimitiveType::I4)
    }

    /// Create a `ConcreteType::I8` type.
    pub fn i8() -> Self {
        Self::primitive(PrimitiveType::I8)
    }
    /// Create a `ConcreteType::U` type.
    pub fn u() -> Self {
        Self::primitive(PrimitiveType::U)
    }

    /// Create a `ConcreteType::U1` type.
    pub fn u1() -> Self {
        Self::primitive(PrimitiveType::U1)
    }

    /// Create a `ConcreteType::U2` type.
    pub fn u2() -> Self {
        Self::primitive(PrimitiveType::U2)
    }

    /// Create a `ConcreteType::U4` type.
    pub fn u4() -> Self {
        Self::primitive(PrimitiveType::U4)
    }

    /// Create a `ConcreteType::U8` type.
    pub fn u8() -> Self {
        Self::primitive(PrimitiveType::U8)
    }

    /// Create a `ConcreteType::F4` type.
    pub fn f4() -> Self {
        Self::primitive(PrimitiveType::F4)
    }

    /// Create a `ConcreteType::F8` type.
    pub fn f8() -> Self {
        Self::primitive(PrimitiveType::F8)
    }

    /// Create a `ConcreteType::Bool` type.
    pub fn boolean() -> Self {
        Self::primitive(PrimitiveType::Bool)
    }

    /// Create a `ConcreteType::Char` type.
    pub fn character() -> Self {
        Self::primitive(PrimitiveType::Char)
    }
}

impl Default for Type {
    fn default() -> Self {
        Self::unit()
    }
}

impl TypeInferenceCtx {
    pub(crate) fn new_ty_var(&mut self) -> Type {
        let ty_var_key = self.ty_vars.push_and_get_key(TypeVarSubstitution::Any);
        Type::type_var(ty_var_key)
    }

    pub(crate) fn new_never_ty_var(&mut self) -> Type {
        let ty_var_key = self.ty_vars.push_and_get_key(TypeVarSubstitution::Never);
        Type::type_var(ty_var_key)
    }

    pub(crate) fn new_int_ty_var(&mut self) -> Type {
        let ty_var_key = self
            .ty_vars
            .push_and_get_key(TypeVarSubstitution::ConstrainedNumber(
                NumberConstraints::Int,
            ));
        Type::type_var(ty_var_key)
    }

    pub(crate) fn new_float_ty_var(&mut self) -> Type {
        let ty_var_key = self
            .ty_vars
            .push_and_get_key(TypeVarSubstitution::ConstrainedNumber(
                NumberConstraints::Float,
            ));
        Type::type_var(ty_var_key)
    }

    pub(crate) fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Concrete(concrete_type) => Type::Concrete(self.apply_on_concrete(concrete_type)),

            // Replace a type variable if it has a substitution
            Type::TypeVar(type_var_key) => {
                let substitution = &self.ty_vars[*type_var_key];

                match substitution {
                    TypeVarSubstitution::Determined(rc_cell) => self.apply(&rc_cell),
                    TypeVarSubstitution::Any
                    | TypeVarSubstitution::Never
                    | TypeVarSubstitution::Error
                    | TypeVarSubstitution::ConstrainedNumber(_) => ty.clone(),
                }
            }
        }
    }

    pub(crate) fn apply_on_concrete(&self, concrete_type: &ConcreteType) -> ConcreteType {
        match concrete_type {
            ConcreteType::Composite(composite_type) => {
                ConcreteType::Composite(self.apply_on_composite(composite_type))
            }
            concrete_type @ _ => concrete_type.clone(),
        }
    }

    pub(crate) fn apply_on_composite(&self, composite_type: &CompositeType) -> CompositeType {
        match composite_type {
            // Recursively apply substitutions to concrete types
            CompositeType::Slice(inner) => {
                CompositeType::Slice(Box::new(self.apply(inner.as_ref())))
            }
            CompositeType::Ptr(inner) => CompositeType::Ptr(Box::new(self.apply(inner))),
            CompositeType::PtrMut(inner) => CompositeType::PtrMut(Box::new(self.apply(inner))),
            CompositeType::Array {
                underlying_typ,
                size,
            } => CompositeType::Array {
                underlying_typ: Box::new(self.apply(underlying_typ)),
                size: *size,
            },

            CompositeType::Tuple { types } => CompositeType::Tuple {
                types: types.iter().map(|inner| self.apply(inner)).collect(),
            },

            CompositeType::Lambda {
                params_types,
                return_type,
            } => CompositeType::Lambda {
                params_types: params_types.iter().map(|param| self.apply(param)).collect(),
                return_type: Box::new(self.apply(return_type)),
            },

            CompositeType::FnPtr {
                params_types,
                return_type,
            } => CompositeType::FnPtr {
                params_types: params_types.iter().map(|param| self.apply(param)).collect(),
                return_type: Box::new(self.apply(return_type)),
            },
        }
    }

    pub(crate) fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), ()> {
        let t1 = self.apply(t1);
        let t2 = self.apply(t2);

        match (t1, t2) {
            // If both are concrete types, compare them recursively
            (Type::Concrete(c1), Type::Concrete(c2)) => self.unify_concrete(&c1, &c2),

            // If both are the same type variable, they're already unified
            (Type::TypeVar(key1), Type::TypeVar(key2)) if key1 == key2 => Ok(()),

            (Type::TypeVar(key1), Type::TypeVar(key2)) => {
                match (&self.ty_vars[key1], &self.ty_vars[key2]) {
                    (TypeVarSubstitution::Error, _)
                    | (
                        TypeVarSubstitution::ConstrainedNumber(_),
                        TypeVarSubstitution::Any | TypeVarSubstitution::Never,
                    ) => {
                        self.ty_vars[key2] = TypeVarSubstitution::Determined(Type::type_var(key1));
                        Ok(())
                    }
                    (_, TypeVarSubstitution::Error)
                    | (
                        TypeVarSubstitution::Any | TypeVarSubstitution::Never,
                        TypeVarSubstitution::Any | TypeVarSubstitution::Never,
                    )
                    | (
                        TypeVarSubstitution::Any | TypeVarSubstitution::Never,
                        TypeVarSubstitution::ConstrainedNumber(_),
                    ) => {
                        self.ty_vars[key1] = TypeVarSubstitution::Determined(Type::type_var(key2));
                        Ok(())
                    }
                    (
                        TypeVarSubstitution::ConstrainedNumber(constraints1),
                        TypeVarSubstitution::ConstrainedNumber(constraints2),
                    ) => {
                        if let Some(intersection) =
                            NumberConstraints::get_intersection(*constraints1, *constraints2)
                        {
                            // More than one possibility remains: update one variable with the intersected constraint.
                            self.ty_vars[key1] =
                                TypeVarSubstitution::ConstrainedNumber(intersection);

                            // Link the other variable to key1.
                            self.ty_vars[key2] =
                                TypeVarSubstitution::Determined(Type::type_var(key1));

                            Ok(())
                        } else {
                            Err(())
                        }
                    }
                    // Should not reach here if Determined states are fully applied via `apply`.
                    _ => Err(()),
                }
            }

            (Type::TypeVar(key), Type::Concrete(concrete_ty))
            | (Type::Concrete(concrete_ty), Type::TypeVar(key)) => {
                // Ensure we do not introduce an infinite type.
                if concrete_ty.occurs_check(key) {
                    return Err(());
                }

                match &self.ty_vars[key] {
                    TypeVarSubstitution::Error => Ok(()), // Just unify, and it will be reported
                    TypeVarSubstitution::Any | TypeVarSubstitution::Never => {
                        // No constraints; simply substitute.
                        self.ty_vars[key] =
                            TypeVarSubstitution::Determined(Type::Concrete(concrete_ty));
                        Ok(())
                    }
                    TypeVarSubstitution::ConstrainedNumber(constraints) => {
                        // Check if the concrete type is one of the allowed costraints.
                        if constraints.contains(&concrete_ty) {
                            self.ty_vars[key] =
                                TypeVarSubstitution::Determined(Type::Concrete(concrete_ty));
                            Ok(())
                        } else {
                            // The concrete type does not satisfy the constraints.
                            Err(())
                        }
                    }
                    TypeVarSubstitution::Determined(_) => unreachable!(),
                }
            }
        }
    }

    pub(crate) fn unify_concrete(
        &mut self,
        c1: &ConcreteType,
        c2: &ConcreteType,
    ) -> Result<(), ()> {
        match (c1, c2) {
            (ConcreteType::Composite(c1), ConcreteType::Composite(c2)) => {
                self.unify_composite(c1, c2)
            }
            (ConcreteType::UnitStruct(k1), ConcreteType::UnitStruct(k2)) if k1 == k2 => Ok(()),
            (ConcreteType::TupleStruct(k1), ConcreteType::TupleStruct(k2)) if k1 == k2 => Ok(()),
            (ConcreteType::FieldsStruct(k1), ConcreteType::FieldsStruct(k2)) if k1 == k2 => Ok(()),
            (ConcreteType::Primitive(p1), ConcreteType::Primitive(p2)) if p1 == p2 => Ok(()),
            _ => Err(()),
        }
    }

    pub(crate) fn unify_composite(
        &mut self,
        c1: &CompositeType,
        c2: &CompositeType,
    ) -> Result<(), ()> {
        match (c1, c2) {
            (CompositeType::Slice(t1), CompositeType::Slice(t2))
            | (CompositeType::Ptr(t1), CompositeType::Ptr(t2))
            | (CompositeType::PtrMut(t1), CompositeType::PtrMut(t2)) => self.unify(&t1, &t2),

            (
                CompositeType::Array {
                    underlying_typ: t1,
                    size: s1,
                },
                CompositeType::Array {
                    underlying_typ: t2,
                    size: s2,
                },
            ) if s1 == s2 => self.unify(&t1, &t2),

            (CompositeType::Tuple { types: t1 }, CompositeType::Tuple { types: t2 })
                if t1.len() == t2.len() =>
            {
                for (t1, t2) in t1.iter().zip(t2.iter()) {
                    self.unify(t1, t2)?;
                }
                Ok(())
            }

            (
                CompositeType::Lambda {
                    params_types: params_types1,
                    return_type: return_type1,
                },
                CompositeType::Lambda {
                    params_types: params_types2,
                    return_type: return_type2,
                },
            )
            | (
                CompositeType::FnPtr {
                    params_types: params_types1,
                    return_type: return_type1,
                },
                CompositeType::FnPtr {
                    params_types: params_types2,
                    return_type: return_type2,
                },
            ) if params_types1.len() == params_types2.len() => {
                for (t1, t2) in params_types1.iter().zip(params_types2.iter()) {
                    self.unify(t1, t2)?;
                }
                self.unify(return_type1, return_type2)?;
                Ok(())
            }
            _ => Err(()),
        }
    }

    /// Constrain the given type variable (or type) to the allowed set of concrete types.
    /// Returns Ok(()) if the constraint is compatible, or Err(()) if the determined type
    /// is not among the allowed alternatives or the intersection is empty.
    pub fn constrain_type_var(
        &mut self,
        ty: &Type,
        constraints: NumberConstraints,
    ) -> Result<(), ()> {
        // First, apply all substitutions to get the current “resolved” type.
        let applied = self.apply(ty);

        let result = match applied {
            // If we have a type variable…
            Type::TypeVar(key) => {
                let substitution = self.ty_vars[key].clone();

                match substitution {
                    TypeVarSubstitution::Error => Ok(()), // The error will be reported
                    // If unconstrained, just set the allowed set.
                    TypeVarSubstitution::Any | TypeVarSubstitution::Never => {
                        self.ty_vars[key] = TypeVarSubstitution::ConstrainedNumber(constraints);
                        Ok(())
                    }
                    // If already constrained, intersect the new allowed set with the existing one.
                    TypeVarSubstitution::ConstrainedNumber(existing_constraints) => {
                        if let Some(intersection) =
                            NumberConstraints::get_intersection(constraints, existing_constraints)
                        {
                            // More than one possibility remains: update one variable with the intersected constraint.
                            self.ty_vars[key] =
                                TypeVarSubstitution::ConstrainedNumber(intersection);
                            Ok(())
                        } else {
                            Err(())
                        }
                    }
                    // If already determined, check that the concrete type is one of the allowed alternatives.
                    TypeVarSubstitution::Determined(determined) => match determined {
                        Type::Concrete(c) if constraints.contains(&c) => Ok(()),
                        _ => Err(()),
                    },
                }
            }
            // If the type is already concrete, verify that it is one of the allowed alternatives.
            Type::Concrete(c) if constraints.contains(&c) => Ok(()),

            _ => Err(()),
        };

        result
    }

    pub(crate) fn make_ty_var_error(&mut self, key: TypeVarKey) -> bool {
        if matches!(
            self.ty_vars[key],
            TypeVarSubstitution::Determined(_) | TypeVarSubstitution::ConstrainedNumber(_)
        ) {
            false
        } else {
            self.ty_vars[key] = TypeVarSubstitution::Error;
            true
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_simple() {
        let mut ctx = TypeInferenceCtx::default();

        let t0 = ctx.new_ty_var();
        let t1 = ctx.new_ty_var();
        let t2 = ctx.new_ty_var();
        let t3 = ctx.new_ty_var();
        let expected_ty = Type::i4();

        assert!(ctx.unify(&t0, &t3).is_ok());
        assert!(ctx.unify(&t1, &t2).is_ok());
        assert!(ctx.unify(&t3, &t1).is_ok());

        assert!(ctx.constrain_type_var(&t0, NumberConstraints::Int).is_ok());

        assert!(ctx.unify(&expected_ty, &t1).is_ok());

        assert_eq!(ctx.apply(&t0), expected_ty);
        assert_eq!(ctx.apply(&t1), expected_ty);
        assert_eq!(ctx.apply(&t2), expected_ty);
        assert_eq!(ctx.apply(&t3), expected_ty);
    }
}
