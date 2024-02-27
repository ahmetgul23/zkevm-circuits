use halo2_base::utils::fe_to_biguint;
use halo2_ecc::{
    bigint::CRTInteger,
    fields::{
        fp::{FpConfig, FpStrategy},
        FieldChip,
    },
    halo2_base::{AssignedValue, Context},
};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    halo2curves::{bls12_381::Scalar, bn256::Fr, ff::PrimeField},
};
use std::ops::{Add, Div, Mul, Sub};

#[derive(Clone)]
pub enum ScalarFieldElement {
    Constant(Scalar),
    Private(Scalar),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Div(Box<Self>, Box<Self>),
    Carry(Box<Self>),
}

impl ScalarFieldElement {
    pub fn constant(x: Scalar) -> Self {
        Self::Constant(x)
    }

    pub fn private(x: Scalar) -> Self {
        Self::Private(x)
    }

    pub fn carry(self) -> Self {
        Self::Carry(Box::new(self))
    }

    pub fn resolve(&self, ctx: &mut Context<Fr>, config: &FpConfig<Fr, Scalar>) -> CRTInteger<Fr> {
        match self {
            Self::Constant(x) => config.load_constant(ctx, fe_to_biguint(x)),
            Self::Private(x) => config.load_private(ctx, Value::known(fe_to_biguint(x).into())),
            Self::Add(x, y) => {
                let x = x.resolve(ctx, config);
                let y = y.resolve(ctx, config);
                config.add_no_carry(ctx, &x, &y)
            }
            Self::Sub(x, y) => {
                let x = x.resolve(ctx, config);
                let y = y.resolve(ctx, config);
                config.sub_no_carry(ctx, &x, &y)
            }
            Self::Mul(x, y) => {
                let x = x.resolve(ctx, config);
                let y = y.resolve(ctx, config);
                config.mul(ctx, &x, &y)
            }
            Self::Div(x, y) => {
                let x = x.resolve(ctx, config);
                let y = y.resolve(ctx, config);
                config.divide(ctx, &x, &y)
            }
            Self::Carry(x) => {
                let x = x.resolve(ctx, config);
                config.carry_mod(ctx, &x)
            }
        }
    }
}

impl Add for ScalarFieldElement {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self::Add(Box::new(self), Box::new(other))
    }
}

impl Sub for ScalarFieldElement {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self::Sub(Box::new(self), Box::new(other))
    }
}

impl Mul for ScalarFieldElement {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self::Mul(Box::new(self), Box::new(other))
    }
}

impl Div for ScalarFieldElement {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        Self::Div(Box::new(self), Box::new(other))
    }
}