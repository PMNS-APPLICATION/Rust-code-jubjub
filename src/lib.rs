//! This crate provides an implementation of the **Jubjub** elliptic curve and its associated
//! field arithmetic. See [`README.md`](https://github.com/zkcrypto/jubjub/blob/master/README.md) for more details about Jubjub.
//!
//! # API
//!
//! * `AffinePoint` / `ExtendedPoint` which are implementations of Jubjub group arithmetic
//! * `AffineNielsPoint` / `ExtendedNielsPoint` which are pre-processed Jubjub points
//! * `Fq`, which is the base field of Jubjub
//! * `Fr`, which is the scalar field of Jubjub
//! * `batch_normalize` for converting many `ExtendedPoint`s into `AffinePoint`s efficiently.
//!
//! # Constant Time
//!
//! All operations are constant time unless explicitly noted; these functions will contain
//! "vartime" in their name and they will be documented as variable time.
//!
//! This crate uses the `subtle` crate to perform constant-time operations.

#![no_std]
// Catch documentation errors caused by code changes.
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]
// This lint is described at
// https://rust-lang.github.io/rust-clippy/master/index.html#suspicious_arithmetic_impl
// In our library, some of the arithmetic will necessarily involve various binary
// operators, and so this lint is triggered unnecessarily.
#![allow(clippy::suspicious_arithmetic_impl)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(test)]
#[macro_use]
extern crate std;

use num_bigint::{BigInt, BigUint};
use num_traits::{FromBytes, FromPrimitive, Num, ToBytes};
const PHI_LOG2: usize = 64;
const POLY_DEG: usize = 4;
const NB_COEFF: usize = 5;
const CONVBASE_LOG2: usize = 51;
const CONV_MASK: u64 = 2251799813685247;

const POLYS_P: [[i64; NB_COEFF]; NB_COEFF] = [
    [
        0x343dce4dc22b8,
        -0x7f0faf2471e4,
        0xf96bb2aff6ca,
        -0x2ccac09fe482,
        0xbbe6ea9dc3eb,
    ],
    [
        -0x39f90eb5db33b,
        -0x8deb5d9587df,
        -0x2a3922ecda803,
        0x384d76e8056bb,
        0x220b59be37eaf,
    ],
    [
        0x12b607b9cdabb,
        0x481a97c5e9e8,
        -0x1cb5ab91c6482,
        -0x51b118b86bc8,
        -0x19879db0689bb,
    ],
    [
        -0x4c0ab46c344f,
        -0x17ff8935b5e9c,
        -0x16026a6a4d92d,
        0x2250f5296fb39,
        -0x1f38024eb6b37,
    ],
    [
        0x1cdffc45856fe,
        0x2096679021067,
        -0x6b3980a4bf6d,
        -0x405cdeb8fcaa6,
        -0x3845f71830cae,
    ],
];

use bitvec::{order::Lsb0, view::AsBits};
use core::borrow::Borrow;
use core::fmt;
use core::iter::Sum;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use ff::{BatchInverter, Field};
use group::{
    cofactor::{CofactorCurve, CofactorCurveAffine, CofactorGroup},
    prime::PrimeGroup,
    Curve, Group, GroupEncoding,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[cfg(feature = "alloc")]
use group::WnafGroup;

#[macro_use]
mod util;

mod fr;
pub use bls12_381::Scalar as Fq;
pub use fr::Fr;

/// Represents an element of the base field $\mathbb{F}_q$ of the Jubjub elliptic curve
/// construction.
pub type Base = Fq;

/// Represents an element of the scalar field $\mathbb{F}_r$ of the Jubjub elliptic curve
/// construction.
pub type Scalar = Fr;

const FR_MODULUS_BYTES: [u8; 32] = [
    183, 44, 247, 214, 94, 14, 151, 208, 130, 16, 200, 204, 147, 32, 104, 166, 0, 59, 52, 1, 1, 59,
    103, 6, 169, 175, 51, 101, 234, 180, 125, 14,
];

fn num_as_u256(bytes: &[u8; 32]) -> num_bigint::BigUint {
    num_bigint::BigUint::from_bytes_le(bytes)
}

fn u256_as_bytes(num: num_bigint::BigUint) -> [u8; 32] {
    let mut bytes = num.to_bytes_le();
    bytes.resize(32, 0);
    bytes.try_into().expect("Failed to convert to [u8; 32]")
}

fn add_lpoly(
    mut rop: [i128; NB_COEFF],
    pa: &[i128; NB_COEFF],
    pb: &[i128; NB_COEFF],
) -> [i128; NB_COEFF] {
    for j in 0..NB_COEFF {
        rop[j] = pa[j] + pb[j];
    }

    rop
}

fn scalar_mult_lpoly(
    mut rop: [i128; NB_COEFF],
    op: &[i64; NB_COEFF],
    scalar: u64,
) -> [i128; NB_COEFF] {
    for j in 0..NB_COEFF {
        rop[j] = (op[j] as i128) * (scalar as i128);
    }
    rop
}

fn internal_reduction(mut rop: [i64; NB_COEFF], op: &[i128; NB_COEFF]) -> [i64; NB_COEFF] {
    let mut tmp_q = [0; 5];
    let mut tmp_zero = [0; 5];

    tmp_q[0] = (((((op[0] as i64).wrapping_mul(0x3335f4b862bc6966))
        .wrapping_add((op[1] as i64).wrapping_mul(0x2a41f8dc459d4f6)))
    .wrapping_add((op[2] as i64).wrapping_mul(0x5f8d7ff8a90e370e)))
    .wrapping_add((op[3] as i64).wrapping_mul(0x5b2216c166abe72d)))
    .wrapping_add((op[4] as i64).wrapping_mul(0x41426512ac1d4624));
    tmp_q[1] = (((((op[0] as i64).wrapping_mul(0x5f5ecd76a9f15cee))
        .wrapping_add((op[1] as i64).wrapping_mul(-0x3335f4b862bc6966)))
    .wrapping_add((op[2] as i64).wrapping_mul(-0x2a41f8dc459d4f6)))
    .wrapping_add((op[3] as i64).wrapping_mul(-0x5f8d7ff8a90e370e)))
    .wrapping_add((op[4] as i64).wrapping_mul(-0x5b2216c166abe72d));
    tmp_q[2] = (((((op[0] as i64).wrapping_mul(0x317403f2d8e76b15))
        .wrapping_add((op[1] as i64).wrapping_mul(0x2deac983d109f1d9)))
    .wrapping_add((op[2] as i64).wrapping_mul(-0x6120be3c33c65b3f)))
    .wrapping_add((op[3] as i64).wrapping_mul(0x5e7c9eae6f6c8649)))
    .wrapping_add((op[4] as i64).wrapping_mul(0x41f5e158e78542a9));
    tmp_q[3] = (((((op[0] as i64).wrapping_mul(0x7287b68385e7d719))
        .wrapping_add((op[1] as i64).wrapping_mul(0x5fea77acd1a7412)))
    .wrapping_add((op[2] as i64).wrapping_mul(0x6040fc3ee4763393)))
    .wrapping_add((op[3] as i64).wrapping_mul(0x579e35365301ea8b)))
    .wrapping_add((op[4] as i64).wrapping_mul(-0x683047013a828016));
    tmp_q[4] = (((((op[0] as i64).wrapping_mul(-0x341823809d41400b))
        .wrapping_add((op[1] as i64).wrapping_mul(0x7287b68385e7d719)))
    .wrapping_add((op[2] as i64).wrapping_mul(0x5fea77acd1a7412)))
    .wrapping_add((op[3] as i64).wrapping_mul(0x6040fc3ee4763393)))
    .wrapping_add((op[4] as i64).wrapping_mul(0x579e35365301ea8b));

    tmp_zero[0] = (tmp_q[0] as i128) * -0x2577d3a698c81
        + (tmp_q[1] as i128) * 0xc89ec0c92cb8
        + (tmp_q[2] as i128) * -0x58d62d4dd747b
        + (tmp_q[3] as i128) * -0x46bb184bc1177
        + (tmp_q[4] as i128) * -0x56f92e43c6a01;
    tmp_zero[1] = (tmp_q[0] as i128) * 0x51a2b7c2858e2
        + (tmp_q[1] as i128) * 0x2577d3a698c81
        + (tmp_q[2] as i128) * 0x733758b51b99
        + (tmp_q[3] as i128) * 0x55676814111f
        + (tmp_q[4] as i128) * -0x4c118ecd02296;
    tmp_zero[2] = (tmp_q[0] as i128) * 0xfb322cd8bd3e
        + (tmp_q[1] as i128) * -0x51a2b7c2858e2
        + (tmp_q[2] as i128) * -0x16e69858dd8d7
        + (tmp_q[3] as i128) * 0x3c5e6bff76558
        + (tmp_q[4] as i128) * -0x3707f57e35439;
    tmp_zero[3] = (tmp_q[0] as i128) * 0x4fc8a2cccc2f9
        + (tmp_q[1] as i128) * -0xfb322cd8bd3e
        + (tmp_q[2] as i128) * -0x38e20a73eea22
        + (tmp_q[3] as i128) * -0x18c0ad4e96ec0
        + (tmp_q[4] as i128) * 0x551f194e0d418;
    tmp_zero[4] = (tmp_q[0] as i128) * -0x644f6064965c
        + (tmp_q[1] as i128) * -0x4fc8a2cccc2f9
        + (tmp_q[2] as i128) * 0x3f27007a3807e
        + (tmp_q[3] as i128) * -0x4eda2347c3dbc
        + (tmp_q[4] as i128) * 0x361975f92cefc;

    for j in 0..NB_COEFF {
        let tmp = (op[j] + tmp_zero[j]) >> PHI_LOG2;
        rop[j] = tmp as i64;
    }

    rop
}

/// Multiplication of polynôme in the Field
pub fn mult_mod_poly(pa: &[i64; NB_COEFF], pb: &[i64; NB_COEFF]) -> [i64; NB_COEFF] {
    let mut tmp_prod_result = [0; NB_COEFF];

    tmp_prod_result[0] = (pa[0] as i128) * (pb[0] as i128)
        + (((pa[1] as i128) * (pb[4] as i128)
            + (pa[2] as i128) * (pb[3] as i128)
            + (pa[3] as i128) * (pb[2] as i128)
            + (pa[4] as i128) * (pb[1] as i128))
            << 1);
    tmp_prod_result[1] = (pa[0] as i128) * (pb[1] as i128)
        + (pa[1] as i128) * (pb[0] as i128)
        + (((pa[2] as i128) * (pb[4] as i128)
            + (pa[3] as i128) * (pb[3] as i128)
            + (pa[4] as i128) * (pb[2] as i128))
            << 1);
    tmp_prod_result[2] = (pa[0] as i128) * (pb[2] as i128)
        + (pa[1] as i128) * (pb[1] as i128)
        + (pa[2] as i128) * (pb[0] as i128)
        + (((pa[3] as i128) * (pb[4] as i128) + (pa[4] as i128) * (pb[3] as i128)) << 1);
    tmp_prod_result[3] = (pa[0] as i128) * (pb[3] as i128)
        + (pa[1] as i128) * (pb[2] as i128)
        + (pa[2] as i128) * (pb[1] as i128)
        + (pa[3] as i128) * (pb[0] as i128)
        + (((pa[4] as i128) * (pb[4] as i128)) << 1);
    tmp_prod_result[4] = (pa[0] as i128) * (pb[4] as i128)
        + (pa[1] as i128) * (pb[3] as i128)
        + (pa[2] as i128) * (pb[2] as i128)
        + (pa[3] as i128) * (pb[1] as i128)
        + (pa[4] as i128) * (pb[0] as i128);

    let rop = [0; NB_COEFF];

    internal_reduction(rop, &tmp_prod_result)
}

fn from_mont_domain(rop: &[i64; NB_COEFF], op: &[i64; NB_COEFF]) -> [i64; NB_COEFF] {
    let mut tmp = [0; NB_COEFF];

    for i in 0..NB_COEFF {
        tmp[i] = op[i] as i128;
    }

    internal_reduction(*rop, &tmp)
}

fn init_data() -> [Fq; POLY_DEG] {
    let mut gama_pow = [Fq::zero(); POLY_DEG];

    gama_pow[0] = Fq::from_raw([
        4235394399895601960,
        14536224357504730555,
        6186625576835806626,
        2734561097847123134,
    ]);

    for i in 1..POLY_DEG {
        gama_pow[i] = &gama_pow[i - 1] * &gama_pow[0];
    }

    gama_pow
}

/// Translation from Fq to PMNS
pub fn from_int_to_pmns(op: Fq) -> [i64; NB_COEFF] {
    let mut tmp_poly = [0; NB_COEFF];
    let mut tmp_sum = [0; NB_COEFF];

    let mut tmp = op.clone();

    let mut rop = [0; NB_COEFF];

    if tmp == Fq::zero() {
        return rop;
    }

    let mut i = 0;

    while tmp != Fq::zero() && i < NB_COEFF {
        let t0 = tmp.to_bytes();

        let bigint = num_as_u256(&t0);
        let mask = BigUint::from_u64(CONV_MASK).unwrap();
        let scalar_big = bigint & mask;
        let scalar = scalar_big.to_u64_digits().get(0).copied().unwrap_or(0); // & ((1 << 51) - 1);

        tmp_poly = scalar_mult_lpoly(tmp_poly, &POLYS_P[i], scalar);

        tmp_sum = add_lpoly(tmp_sum, &tmp_sum, &tmp_poly);

        let mut bigint = num_as_u256(&t0);
        bigint >>= CONVBASE_LOG2;
        let shifted_bytes = u256_as_bytes(bigint);
        tmp = Fq::from_bytes(&shifted_bytes).unwrap();

        i += 1;
    }

    rop = internal_reduction(rop, &tmp_sum);

    rop
}

/// Translation from PMNS to Fq
pub fn from_pmns_to_int(op: &[i64; NB_COEFF]) -> Fq {
    let gama_pow = init_data();

    let mut gama_pow_big = [BigInt::ZERO; 4];
    for k in 0..POLY_DEG {
        let t0 = gama_pow[k].to_bytes();
        gama_pow_big[k] = BigInt::from_le_bytes(&t0);
    }

    let mut tmp_conv = [0; NB_COEFF];

    tmp_conv = from_mont_domain(&tmp_conv, op);

    let mut rop = BigInt::from(tmp_conv[0]);

    for i in 0..POLY_DEG {
        let tmp_sum = &gama_pow_big[i] * BigInt::from(tmp_conv[i + 1]);
        rop = rop + tmp_sum;
    }

    rop = rop
        % BigInt::from_str_radix(
            "52435875175126190479447740508185965837690552500527637822603658699938581184513",
            10,
        )
        .unwrap();

    if rop < BigInt::ZERO {
        rop = rop
            + BigInt::from_str_radix(
                "52435875175126190479447740508185965837690552500527637822603658699938581184513",
                10,
            )
            .unwrap();
    }

    let mut bytes = rop.to_le_bytes();
    if bytes.len() < 64 {
        bytes.resize(64, 0);
    } else if bytes.len() > 64 {
        panic!("Value too large to fit in a 32-byte scalar field.");
    }

    let res = Fq::from_bytes_wide(&<[u8; 64]>::try_from(bytes).unwrap());

    res
}

fn add_poly(pa: &[i64; NB_COEFF], pb: &[i64; NB_COEFF]) -> [i64; NB_COEFF] {
    let mut rop = [0i64; NB_COEFF];

    for j in 0..NB_COEFF {
        rop[j] = pa[j] + pb[j];
    }

    rop
}

fn sub_poly(pa: &[i64; NB_COEFF], pb: &[i64; NB_COEFF]) -> [i64; NB_COEFF] {
    let mut rop = [0i64; NB_COEFF];

    for j in 0..NB_COEFF {
        rop[j] = pa[j] - pb[j];
    }

    rop
}

fn square_mod_poly(pa: &[i64; NB_COEFF]) -> [i64; NB_COEFF] {
    let mut tmp_prod_result = [0; NB_COEFF];

    tmp_prod_result[0] = (pa[0] as i128) * (pa[0] as i128)
        + (((pa[3] as i128) * (pa[2] as i128) + (pa[4] as i128) * (pa[1] as i128)) << 2);
    tmp_prod_result[1] = (((pa[1] as i128) * (pa[0] as i128)) << 1)
        + (((((pa[4] as i128) * (pa[2] as i128)) << 1) + (pa[3] as i128) * (pa[3] as i128)) << 1);
    tmp_prod_result[2] = (((pa[2] as i128) * (pa[0] as i128)) << 1)
        + (pa[1] as i128) * (pa[1] as i128)
        + (((pa[4] as i128) * (pa[3] as i128)) << 2);
    tmp_prod_result[3] = (((pa[2] as i128) * (pa[1] as i128) + (pa[3] as i128) * (pa[0] as i128))
        << 1)
        + (((pa[4] as i128) * (pa[4] as i128)) << 1);
    tmp_prod_result[4] = (((pa[3] as i128) * (pa[1] as i128) + (pa[4] as i128) * (pa[0] as i128))
        << 1)
        + (pa[2] as i128) * (pa[2] as i128);

    let rop = [0i64; NB_COEFF];

    internal_reduction(rop, &tmp_prod_result)
}

fn double_poly_coeffs(op: &[i64; NB_COEFF]) -> [i64; NB_COEFF] {
    let mut rop = [0i64; NB_COEFF];

    for j in 0..NB_COEFF {
        rop[j] = op[j] << 1;
    }

    rop
}

/// This represents a Jubjub point in the affine `(u, v)`
/// coordinates but as polynome representation.
#[derive(Clone, Copy, Debug)]
pub struct AffinePointPmns {
    u: [i64; NB_COEFF],
    v: [i64; NB_COEFF],
}

impl fmt::Display for AffinePointPmns {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

const EDWARDS_D2_PMNS: [i64; NB_COEFF] = [
    716704370704232,
    392398987777065,
    -316121651967027,
    493130060369054,
    50837045442663,
];

impl AffinePointPmns {
    /// Constructs an AffinePoint given `u` and `v` without checking
    /// that the point is on the curve.
    pub const fn from_raw_unchecked(u: [i64; NB_COEFF], v: [i64; NB_COEFF]) -> AffinePointPmns {
        AffinePointPmns { u, v }
    }

    /// Returns the `u`-coordinate of this point.
    pub fn get_u(&self) -> [i64; NB_COEFF] {
        self.u
    }

    /// Returns the `v`-coordinate of this point.
    pub fn get_v(&self) -> [i64; NB_COEFF] {
        self.v
    }

    /// Returns an `ExtendedPoint` for use in arithmetic operations.
    pub const fn to_extended(&self) -> ExtendedPointPmns {
        ExtendedPointPmns {
            u: self.u,
            v: self.v,
            z: [
                152610824437994,
                184148993060356,
                1070594867965611,
                -69557245777675,
                -227161848554867,
            ],
            t1: self.u,
            t2: self.v,
        }
    }

    /// Doc
    pub fn to_niels(&self) -> AffineNielsPointPmns {
        AffineNielsPointPmns {
            v_plus_u: add_poly(&self.v, &self.u),
            v_minus_u: sub_poly(&self.v, &self.u),
            t2d: mult_mod_poly(&&mult_mod_poly(&self.u, &self.v), &EDWARDS_D2_PMNS),
        }
    }
}

/// This represents a Jubjub point as an Exatended
/// point with polynome representation.
#[derive(Clone, Copy, Debug)]
pub struct ExtendedPointPmns {
    u: [i64; NB_COEFF],
    v: [i64; NB_COEFF],
    z: [i64; NB_COEFF],
    t1: [i64; NB_COEFF],
    t2: [i64; NB_COEFF],
}

impl fmt::Display for ExtendedPointPmns {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ExtendedPointPmns {
    /// Constructs an extended point from the neutral element `(0, 1)`.
    pub const fn identity() -> Self {
        ExtendedPointPmns {
            u: [0, 0, 0, 0, 0],
            v: [
                152610824437994,
                184148993060356,
                1070594867965611,
                -69557245777675,
                -227161848554867,
            ],
            z: [
                152610824437994,
                184148993060356,
                1070594867965611,
                -69557245777675,
                -227161848554867,
            ],
            t1: [0, 0, 0, 0, 0],
            t2: [0, 0, 0, 0, 0],
        }
    }

    /// doc
    pub fn get_u(&self) -> [i64; NB_COEFF] {
        self.u
    }

    /// doc
    pub fn get_v(&self) -> [i64; NB_COEFF] {
        self.v
    }

    /// doc
    pub fn get_z(&self) -> [i64; NB_COEFF] {
        self.z
    }

    /// doc
    pub fn get_t1(&self) -> [i64; NB_COEFF] {
        self.t1
    }

    /// doc
    pub fn get_t2(&self) -> [i64; NB_COEFF] {
        self.t2
    }

    /// Computes the doubling of a point more efficiently than a point can
    /// be added to itself.
    pub fn double(&self) -> ExtendedPointPmns {
        let uu = square_mod_poly(&self.u);
        let vv = square_mod_poly(&self.v);
        let tmp = square_mod_poly(&self.z);
        let zz2 = double_poly_coeffs(&tmp);
        let tmp2 = add_poly(&self.u, &self.v);
        let uv2 = square_mod_poly(&tmp2);
        let vv_plus_uu = add_poly(&vv, &uu);
        let vv_minus_uu = sub_poly(&vv, &uu);

        // The remaining arithmetic is exactly the process of converting
        // from a completed point to an extended point.
        CompletedPointPmns {
            u: sub_poly(&uv2, &vv_plus_uu),
            v: vv_plus_uu,
            z: vv_minus_uu,
            t: sub_poly(&zz2, &vv_minus_uu),
        }
        .into_extended()
    }
}

/// This is a pre-processed version of an affine point `(u, v)`
/// in the form `(v + u, v - u, u * v * 2d)`. but as pmns.
#[derive(Clone, Copy, Debug)]
pub struct AffineNielsPointPmns {
    v_plus_u: [i64; NB_COEFF],
    v_minus_u: [i64; NB_COEFF],
    t2d: [i64; NB_COEFF],
}

fn conditional_select(a: &[i64; NB_COEFF], b: &[i64; NB_COEFF], choice: Choice) -> [i64; NB_COEFF] {
    let mut res = [0; NB_COEFF];
    for i in 0..NB_COEFF {
        res[i] = i64::conditional_select(&a[i], &b[i], choice)
    }
    res
}

impl ConditionallySelectable for AffineNielsPointPmns {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        AffineNielsPointPmns {
            v_plus_u: conditional_select(&a.v_plus_u, &b.v_plus_u, choice),
            v_minus_u: conditional_select(&a.v_minus_u, &b.v_minus_u, choice),
            t2d: conditional_select(&a.t2d, &b.t2d, choice),
        }
    }
}

impl AffineNielsPointPmns {
    /// doc
    pub const fn identity() -> Self {
        AffineNielsPointPmns {
            v_plus_u: [
                152610824437994,
                184148993060356,
                1070594867965611,
                -69557245777675,
                -227161848554867,
            ],
            v_minus_u: [
                152610824437994,
                184148993060356,
                1070594867965611,
                -69557245777675,
                -227161848554867,
            ],
            t2d: [0, 0, 0, 0, 0],
        }
    }

    // CETTE FONCTION QU'ON VERIFIE !!
    #[inline]
    fn multiply(&self, by: &[u8; 32]) -> ExtendedPointPmns {
        let zero = AffineNielsPointPmns::identity();

        let mut acc = ExtendedPointPmns::identity();

        for bit in by
            .as_bits::<Lsb0>()
            .iter()
            .rev()
            .skip(4)
            .map(|bit| Choice::from(if *bit { 1 } else { 0 }))
        {
            acc = acc.double(); //
            let tmp = AffineNielsPointPmns::conditional_select(&zero, self, bit);
            acc += tmp;
        }

        acc
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a AffineNielsPointPmns {
    type Output = ExtendedPointPmns;

    fn mul(self, other: &'b Fr) -> ExtendedPointPmns {
        self.multiply(&other.to_bytes())
    }
}

////////////////////////////////////////////////////////////////////////////////

impl_binops_multiplicative_mixed!(AffineNielsPointPmns, Fr, ExtendedPointPmns);

/// This is a "completed" point produced during a point doubling or
/// addition routine. These points exist in the `(U:Z, V:T)` model
/// of the curve. This is not exposed in the API because it is
/// an implementation detail.
struct CompletedPointPmns {
    u: [i64; NB_COEFF],
    v: [i64; NB_COEFF],
    z: [i64; NB_COEFF],
    t: [i64; NB_COEFF],
}

impl CompletedPointPmns {
    #[inline]
    fn into_extended(self) -> ExtendedPointPmns {
        ExtendedPointPmns {
            u: mult_mod_poly(&self.u, &self.t),
            v: mult_mod_poly(&self.v, &self.z),
            z: mult_mod_poly(&self.z, &self.t),
            t1: self.u,
            t2: self.v,
        }
    }
}

impl<'a, 'b> Add<&'b AffineNielsPointPmns> for &'a ExtendedPointPmns {
    type Output = ExtendedPointPmns;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, other: &'b AffineNielsPointPmns) -> ExtendedPointPmns {
        let a = mult_mod_poly(&sub_poly(&self.v, &self.u), &other.v_minus_u);
        let b = mult_mod_poly(&add_poly(&self.v, &self.u), &other.v_plus_u);
        let c = mult_mod_poly(&mult_mod_poly(&self.t1, &self.t2), &other.t2d);
        let d = double_poly_coeffs(&self.z);

        CompletedPointPmns {
            u: sub_poly(&b, &a),
            v: add_poly(&b, &a),
            z: add_poly(&d, &c),
            t: sub_poly(&d, &c),
        }
        .into_extended()
    }
}

impl<'a, 'b> Sub<&'b AffineNielsPointPmns> for &'a ExtendedPointPmns {
    type Output = ExtendedPointPmns;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, other: &'b AffineNielsPointPmns) -> ExtendedPointPmns {
        let a = mult_mod_poly(&sub_poly(&self.v, &self.u), &other.v_plus_u);
        let b = mult_mod_poly(&add_poly(&self.v, &self.u), &other.v_minus_u);
        let c = mult_mod_poly(&mult_mod_poly(&self.t1, &self.t2), &other.t2d);
        let d = double_poly_coeffs(&self.z);

        CompletedPointPmns {
            u: sub_poly(&b, &a),
            v: add_poly(&b, &a),
            z: sub_poly(&d, &c),
            t: add_poly(&d, &c),
        }
        .into_extended()
    }
}

impl_binops_additive!(ExtendedPointPmns, AffineNielsPointPmns);

/// This represents a Jubjub point in the affine `(u, v)`
/// coordinates.
#[derive(Clone, Copy, Debug, Eq)]
pub struct AffinePoint {
    u: Fq,
    v: Fq,
}

impl fmt::Display for AffinePoint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Neg for AffinePoint {
    type Output = AffinePoint;

    /// This computes the negation of a point `P = (u, v)`
    /// as `-P = (-u, v)`.
    #[inline]
    fn neg(self) -> AffinePoint {
        AffinePoint {
            u: -self.u,
            v: self.v,
        }
    }
}

impl ConstantTimeEq for AffinePoint {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.u.ct_eq(&other.u) & self.v.ct_eq(&other.v)
    }
}

impl PartialEq for AffinePoint {
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl ConditionallySelectable for AffinePoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        AffinePoint {
            u: Fq::conditional_select(&a.u, &b.u, choice),
            v: Fq::conditional_select(&a.v, &b.v, choice),
        }
    }
}

/// This represents an extended point `(U, V, Z, T1, T2)`
/// with `Z` nonzero, corresponding to the affine point
/// `(U/Z, V/Z)`. We always have `T1 * T2 = UV/Z`.
///
/// You can do the following things with a point in this
/// form:
///
/// * Convert it into a point in the affine form.
/// * Add it to an `ExtendedPoint`, `AffineNielsPoint` or `ExtendedNielsPoint`.
/// * Double it using `double()`.
/// * Compare it with another extended point using `PartialEq` or `ct_eq()`.

#[derive(Clone, Copy, Debug, Eq)]
pub struct ExtendedPoint {
    u: Fq,
    v: Fq,
    z: Fq,
    t1: Fq,
    t2: Fq,
}

impl fmt::Display for ExtendedPoint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ConstantTimeEq for ExtendedPoint {
    fn ct_eq(&self, other: &Self) -> Choice {
        (self.u * other.z).ct_eq(&(other.u * self.z))
            & (self.v * other.z).ct_eq(&(other.v * self.z))
    }
}

impl ConditionallySelectable for ExtendedPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        ExtendedPoint {
            u: Fq::conditional_select(&a.u, &b.u, choice),
            v: Fq::conditional_select(&a.v, &b.v, choice),
            z: Fq::conditional_select(&a.z, &b.z, choice),
            t1: Fq::conditional_select(&a.t1, &b.t1, choice),
            t2: Fq::conditional_select(&a.t2, &b.t2, choice),
        }
    }
}

impl PartialEq for ExtendedPoint {
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl<T> Sum<T> for ExtendedPoint
where
    T: Borrow<ExtendedPoint>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl Neg for ExtendedPoint {
    type Output = ExtendedPoint;

    /// Computes the negation of a point `P = (U, V, Z, T)`
    /// as `-P = (-U, V, Z, -T1, T2)`. The choice of `T1`
    /// is made without loss of generality.
    #[inline]
    fn neg(self) -> ExtendedPoint {
        ExtendedPoint {
            u: -self.u,
            v: self.v,
            z: self.z,
            t1: -self.t1,
            t2: self.t2,
        }
    }
}

impl From<AffinePoint> for ExtendedPoint {
    fn from(affine: AffinePoint) -> ExtendedPoint {
        ExtendedPoint {
            u: affine.u,
            v: affine.v,
            z: Fq::one(),
            t1: affine.u,
            t2: affine.v,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////

impl<'a> From<&'a ExtendedPoint> for AffinePoint {
    /// Constructs an affine point from an extended point
    /// using the map `(U, V, Z, T1, T2) => (U/Z, V/Z)`
    /// as Z is always nonzero. **This requires a field inversion
    /// and so it is recommended to perform these in a batch
    /// using [`batch_normalize`](crate::batch_normalize) instead.**
    fn from(extended: &'a ExtendedPoint) -> AffinePoint {
        let zinv = extended.z.invert().unwrap();

        AffinePoint {
            u: extended.u * zinv,
            v: extended.v * zinv,
        }
    }
}

impl From<ExtendedPoint> for AffinePoint {
    fn from(extended: ExtendedPoint) -> AffinePoint {
        AffinePoint::from(&extended)
    }
}

/// This is a pre-processed version of an affine point `(u, v)`
/// in the form `(v + u, v - u, u * v * 2d)`. This can be added to an
/// [`ExtendedPoint`](crate::ExtendedPoint).
#[derive(Clone, Copy, Debug)]
pub struct AffineNielsPoint {
    v_plus_u: Fq,
    v_minus_u: Fq,
    t2d: Fq,
}

impl AffineNielsPoint {
    /// Constructs this point from the neutral element `(0, 1)`.
    pub const fn identity() -> Self {
        AffineNielsPoint {
            v_plus_u: Fq::one(),
            v_minus_u: Fq::one(),
            t2d: Fq::zero(),
        }
    }
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // CETTE FONCTION QU'ON VERIFIE !!
    #[inline]
    fn multiply(&self, by: &[u8; 32]) -> ExtendedPoint {
        let zero = AffineNielsPoint::identity();

        let mut acc = ExtendedPoint::identity();

        // This is a simple double-and-add implementation of point
        // multiplication, moving from most significant to least
        // significant bit of the scalar.
        //
        // We skip the leading four bits because they're always
        // unset for Fr.
        for bit in by
            .as_bits::<Lsb0>()
            .iter()
            .rev()
            .skip(4)
            .map(|bit| Choice::from(if *bit { 1 } else { 0 }))
        {
            acc = acc.double(); 
            acc += AffineNielsPoint::conditional_select(&zero, self, bit);
        }

        acc
    }

    /// Multiplies this point by the specific little-endian bit pattern in the
    /// given byte array, ignoring the highest four bits.
    pub fn multiply_bits(&self, by: &[u8; 32]) -> ExtendedPoint {
        self.multiply(by)
    }
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

impl<'a, 'b> Mul<&'b Fr> for &'a AffineNielsPoint {
    type Output = ExtendedPoint;

    fn mul(self, other: &'b Fr) -> ExtendedPoint {
        self.multiply(&other.to_bytes())
    }
}

////////////////////////////////////////////////////////////////////////////////

impl_binops_multiplicative_mixed!(AffineNielsPoint, Fr, ExtendedPoint);

////////////////////////////////////////////////////////////////////////////////

impl ConditionallySelectable for AffineNielsPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        AffineNielsPoint {
            v_plus_u: Fq::conditional_select(&a.v_plus_u, &b.v_plus_u, choice),
            v_minus_u: Fq::conditional_select(&a.v_minus_u, &b.v_minus_u, choice),
            t2d: Fq::conditional_select(&a.t2d, &b.t2d, choice),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////

/// This is a pre-processed version of an extended point `(U, V, Z, T1, T2)`
/// in the form `(V + U, V - U, Z, T1 * T2 * 2d)`.
#[derive(Clone, Copy, Debug)]
pub struct ExtendedNielsPoint {
    v_plus_u: Fq,
    v_minus_u: Fq,
    z: Fq,
    t2d: Fq,
}

impl ConditionallySelectable for ExtendedNielsPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        ExtendedNielsPoint {
            v_plus_u: Fq::conditional_select(&a.v_plus_u, &b.v_plus_u, choice),
            v_minus_u: Fq::conditional_select(&a.v_minus_u, &b.v_minus_u, choice),
            z: Fq::conditional_select(&a.z, &b.z, choice),
            t2d: Fq::conditional_select(&a.t2d, &b.t2d, choice),
        }
    }
}

impl ExtendedNielsPoint {
    /// Constructs this point from the neutral element `(0, 1)`.
    pub const fn identity() -> Self {
        ExtendedNielsPoint {
            v_plus_u: Fq::one(),
            v_minus_u: Fq::one(),
            z: Fq::one(),
            t2d: Fq::zero(),
        }
    }

    #[inline]
    fn multiply(&self, by: &[u8; 32]) -> ExtendedPoint {
        let zero = ExtendedNielsPoint::identity();

        let mut acc = ExtendedPoint::identity();

        // This is a simple double-and-add implementation of point
        // multiplication, moving from most significant to least
        // significant bit of the scalar.
        //
        // We skip the leading four bits because they're always
        // unset for Fr.
        for bit in by
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
            .skip(4)
        {
            acc = acc.double();
            acc += ExtendedNielsPoint::conditional_select(&zero, self, bit);
        }

        acc
    }

    /// Multiplies this point by the specific little-endian bit pattern in the
    /// given byte array, ignoring the highest four bits.
    pub fn multiply_bits(&self, by: &[u8; 32]) -> ExtendedPoint {
        self.multiply(by)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a ExtendedNielsPoint {
    type Output = ExtendedPoint;

    fn mul(self, other: &'b Fr) -> ExtendedPoint {
        self.multiply(&other.to_bytes())
    }
}

impl_binops_multiplicative_mixed!(ExtendedNielsPoint, Fr, ExtendedPoint);

////////////////////////////////////////////////////////////////////////////////

// `d = -(10240/10241)`
const EDWARDS_D: Fq = Fq::from_raw([
    0x0106_5fd6_d634_3eb1,
    0x292d_7f6d_3757_9d26,
    0xf5fd_9207_e6bd_7fd4,
    0x2a93_18e7_4bfa_2b48,
]);

// `2*d`
const EDWARDS_D2: Fq = Fq::from_raw([
    0x020c_bfad_ac68_7d62,
    0x525a_feda_6eaf_3a4c,
    0xebfb_240f_cd7a_ffa8,
    0x5526_31ce_97f4_5691,
]);

impl AffinePoint {
    /// Constructs the neutral element `(0, 1)`.

    ////////////////////////////////////////////////////////////////////////////////

    pub const fn identity() -> Self {
        AffinePoint {
            u: Fq::zero(),
            v: Fq::one(),
        }
    }

    /// Determines if this point is the identity.
    pub fn is_identity(&self) -> Choice {
        ExtendedPoint::from(*self).is_identity()
    }

    /// Multiplies this point by the cofactor, producing an
    /// `ExtendedPoint`
    pub fn mul_by_cofactor(&self) -> ExtendedPoint {
        ExtendedPoint::from(*self).mul_by_cofactor()
    }

    /// Determines if this point is of small order.
    pub fn is_small_order(&self) -> Choice {
        ExtendedPoint::from(*self).is_small_order()
    }

    /// Determines if this point is torsion free and so is
    /// in the prime order subgroup.
    pub fn is_torsion_free(&self) -> Choice {
        ExtendedPoint::from(*self).is_torsion_free()
    }

    /// Determines if this point is prime order, or in other words that
    /// the smallest scalar multiplied by this point that produces the
    /// identity is `r`. This is equivalent to checking that the point
    /// is both torsion free and not the identity.
    pub fn is_prime_order(&self) -> Choice {
        let extended = ExtendedPoint::from(*self);
        extended.is_torsion_free() & (!extended.is_identity())
    }

    /// Converts this element into its byte representation.
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut tmp = self.v.to_bytes();
        let u = self.u.to_bytes();

        // Encode the sign of the u-coordinate in the most
        // significant bit.
        tmp[31] |= u[0] << 7;

        tmp
    }

    /// Attempts to interpret a byte representation of an
    /// affine point, failing if the element is not on
    /// the curve or non-canonical.
    pub fn from_bytes(b: [u8; 32]) -> CtOption<Self> {
        Self::from_bytes_inner(b, 1.into())
    }

    /// Attempts to interpret a byte representation of an affine point, failing if the
    /// element is not on the curve.
    ///
    /// Most non-canonical encodings will also cause a failure. However, this API
    /// preserves (for use in consensus-critical protocols) a bug in the parsing code that
    /// caused two non-canonical encodings to be **silently** accepted:
    ///
    /// - (0, 1), which is the identity;
    /// - (0, -1), which is a point of order two.
    ///
    /// Each of these has a single non-canonical encoding in which the value of the sign
    /// bit is 1.
    ///
    /// See [ZIP 216](https://zips.z.cash/zip-0216) for a more detailed description of the
    /// bug, as well as its fix.
    pub fn from_bytes_pre_zip216_compatibility(b: [u8; 32]) -> CtOption<Self> {
        Self::from_bytes_inner(b, 0.into())
    }

    fn from_bytes_inner(mut b: [u8; 32], zip_216_enabled: Choice) -> CtOption<Self> {
        // Grab the sign bit from the representation
        let sign = b[31] >> 7;

        // Mask away the sign bit
        b[31] &= 0b0111_1111;

        // Interpret what remains as the v-coordinate
        Fq::from_bytes(&b).and_then(|v| {
            // -u^2 + v^2 = 1 + d.u^2.v^2
            // -u^2 = 1 + d.u^2.v^2 - v^2    (rearrange)
            // -u^2 - d.u^2.v^2 = 1 - v^2    (rearrange)
            // u^2 + d.u^2.v^2 = v^2 - 1     (flip signs)
            // u^2 (1 + d.v^2) = v^2 - 1     (factor)
            // u^2 = (v^2 - 1) / (1 + d.v^2) (isolate u^2)
            // We know that (1 + d.v^2) is nonzero for all v:
            //   (1 + d.v^2) = 0
            //   d.v^2 = -1
            //   v^2 = -(1 / d)   No solutions, as -(1 / d) is not a square

            let v2 = v.square();

            ((v2 - Fq::one()) * ((Fq::one() + EDWARDS_D * v2).invert().unwrap_or(Fq::zero())))
                .sqrt()
                .and_then(|u| {
                    // Fix the sign of `u` if necessary
                    let flip_sign = Choice::from((u.to_bytes()[0] ^ sign) & 1);
                    let u_negated = -u;
                    let final_u = Fq::conditional_select(&u, &u_negated, flip_sign);

                    // If u == 0, flip_sign == sign_bit. We therefore want to reject the
                    // encoding as non-canonical if all of the following occur:
                    // - ZIP 216 is enabled
                    // - u == 0
                    // - flip_sign == true
                    let u_is_zero = u.ct_eq(&Fq::zero());
                    CtOption::new(
                        AffinePoint { u: final_u, v },
                        !(zip_216_enabled & u_is_zero & flip_sign),
                    )
                })
        })
    }

    /// Attempts to interpret a batch of byte representations of affine points.
    ///
    /// Returns None for each element if it is not on the curve, or is non-canonical
    /// according to ZIP 216.
    #[cfg(feature = "alloc")]
    pub fn batch_from_bytes(items: impl Iterator<Item = [u8; 32]>) -> Vec<CtOption<Self>> {
        use ff::BatchInvert;

        #[derive(Clone, Copy, Default)]
        struct Item {
            sign: u8,
            v: Fq,
            numerator: Fq,
            denominator: Fq,
        }

        impl ConditionallySelectable for Item {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                Item {
                    sign: u8::conditional_select(&a.sign, &b.sign, choice),
                    v: Fq::conditional_select(&a.v, &b.v, choice),
                    numerator: Fq::conditional_select(&a.numerator, &b.numerator, choice),
                    denominator: Fq::conditional_select(&a.denominator, &b.denominator, choice),
                }
            }
        }

        let items: Vec<_> = items
            .map(|mut b| {
                // Grab the sign bit from the representation
                let sign = b[31] >> 7;

                // Mask away the sign bit
                b[31] &= 0b0111_1111;

                // Interpret what remains as the v-coordinate
                Fq::from_bytes(&b).map(|v| {
                    // -u^2 + v^2 = 1 + d.u^2.v^2
                    // -u^2 = 1 + d.u^2.v^2 - v^2    (rearrange)
                    // -u^2 - d.u^2.v^2 = 1 - v^2    (rearrange)
                    // u^2 + d.u^2.v^2 = v^2 - 1     (flip signs)
                    // u^2 (1 + d.v^2) = v^2 - 1     (factor)
                    // u^2 = (v^2 - 1) / (1 + d.v^2) (isolate u^2)
                    // We know that (1 + d.v^2) is nonzero for all v:
                    //   (1 + d.v^2) = 0
                    //   d.v^2 = -1
                    //   v^2 = -(1 / d)   No solutions, as -(1 / d) is not a square

                    let v2 = v.square();

                    Item {
                        v,
                        sign,
                        numerator: (v2 - Fq::one()),
                        denominator: Fq::one() + EDWARDS_D * v2,
                    }
                })
            })
            .collect();

        let mut denominators: Vec<_> = items
            .iter()
            .map(|item| item.map(|item| item.denominator).unwrap_or(Fq::zero()))
            .collect();
        denominators.iter_mut().batch_invert();

        items
            .into_iter()
            .zip(denominators.into_iter())
            .map(|(item, inv_denominator)| {
                item.and_then(
                    |Item {
                         v, sign, numerator, ..
                     }| {
                        (numerator * inv_denominator).sqrt().and_then(|u| {
                            // Fix the sign of `u` if necessary
                            let flip_sign = Choice::from((u.to_bytes()[0] ^ sign) & 1);
                            let u_negated = -u;
                            let final_u = Fq::conditional_select(&u, &u_negated, flip_sign);

                            // If u == 0, flip_sign == sign_bit. We therefore want to reject the
                            // encoding as non-canonical if all of the following occur:
                            // - u == 0
                            // - flip_sign == true
                            let u_is_zero = u.ct_eq(&Fq::zero());
                            CtOption::new(AffinePoint { u: final_u, v }, !(u_is_zero & flip_sign))
                        })
                    },
                )
            })
            .collect()
    }

    /// Returns the `u`-coordinate of this point.
    pub fn get_u(&self) -> Fq {
        self.u
    }

    /// Returns the `v`-coordinate of this point.
    pub fn get_v(&self) -> Fq {
        self.v
    }

    /// Returns an `ExtendedPoint` for use in arithmetic operations.
    pub const fn to_extended(&self) -> ExtendedPoint {
        ExtendedPoint {
            u: self.u,
            v: self.v,
            z: Fq::one(),
            t1: self.u,
            t2: self.v,
        }
    }

    /// Performs a pre-processing step that produces an `AffineNielsPoint`
    /// for use in multiple additions.
    pub const fn to_niels(&self) -> AffineNielsPoint {
        AffineNielsPoint {
            v_plus_u: Fq::add(&self.v, &self.u),
            v_minus_u: Fq::sub(&self.v, &self.u),
            t2d: Fq::mul(&Fq::mul(&self.u, &self.v), &EDWARDS_D2),
        }
    }

    /// Constructs an AffinePoint given `u` and `v` without checking
    /// that the point is on the curve.
    pub const fn from_raw_unchecked(u: Fq, v: Fq) -> AffinePoint {
        AffinePoint { u, v }
    }

    /// This is only for debugging purposes and not
    /// exposed in the public API. Checks that this
    /// point is on the curve.
    // #[cfg(test)]
    pub fn is_on_curve_vartime(&self) -> bool {
        let u2 = self.u.square();
        let v2 = self.v.square();

        v2 - u2 == Fq::one() + EDWARDS_D * u2 * v2
    }
}

////////////////////////////////////////////////////////////////////////////////

impl ExtendedPoint {
    /// Constructs an extended point from the neutral element `(0, 1)`.
    pub const fn identity() -> Self {
        ExtendedPoint {
            u: Fq::zero(),
            v: Fq::one(),
            z: Fq::one(),
            t1: Fq::zero(),
            t2: Fq::zero(),
        }
    }

    ////////////////////////////////////////////////////////////////////////////////

    /// Determines if this point is the identity.
    pub fn is_identity(&self) -> Choice {
        // If this point is the identity, then
        //     u = 0 * z = 0
        // and v = 1 * z = z
        self.u.ct_eq(&Fq::zero()) & self.v.ct_eq(&self.z)
    }

    /// Determines if this point is of small order.
    pub fn is_small_order(&self) -> Choice {
        // We only need to perform two doublings, since the 2-torsion
        // points are (0, 1) and (0, -1), and so we only need to check
        // that the u-coordinate of the result is zero to see if the
        // point is small order.
        self.double().double().u.ct_eq(&Fq::zero())
    }

    /// Determines if this point is torsion free and so is contained
    /// in the prime order subgroup.
    pub fn is_torsion_free(&self) -> Choice {
        self.multiply(&FR_MODULUS_BYTES).is_identity()
    }

    /// Determines if this point is prime order, or in other words that
    /// the smallest scalar multiplied by this point that produces the
    /// identity is `r`. This is equivalent to checking that the point
    /// is both torsion free and not the identity.
    pub fn is_prime_order(&self) -> Choice {
        self.is_torsion_free() & (!self.is_identity())
    }

    /// Multiplies this element by the cofactor `8`.
    pub fn mul_by_cofactor(&self) -> ExtendedPoint {
        self.double().double().double()
    }

    /// Performs a pre-processing step that produces an `ExtendedNielsPoint`
    /// for use in multiple additions.
    pub fn to_niels(&self) -> ExtendedNielsPoint {
        ExtendedNielsPoint {
            v_plus_u: self.v + self.u,
            v_minus_u: self.v - self.u,
            z: self.z,
            t2d: self.t1 * self.t2 * EDWARDS_D2,
        }
    }

    //  A MODIFIER CELLE LA POUR L'ARITHMETIQUE PMNS

    /// Computes the doubling of a point more efficiently than a point can
    /// be added to itself.
    pub fn double(&self) -> ExtendedPoint {
        let uu = self.u.square();
        let vv = self.v.square();
        let zz2 = self.z.square().double();
        let uv2 = (self.u + self.v).square();
        let vv_plus_uu = vv + uu;
        let vv_minus_uu = vv - uu;

        // The remaining arithmetic is exactly the process of converting
        // from a completed point to an extended point.
        CompletedPoint {
            u: uv2 - vv_plus_uu,
            v: vv_plus_uu,
            z: vv_minus_uu,
            t: zz2 - vv_minus_uu,
        }
        .into_extended()
    }

    #[inline]
    fn multiply(self, by: &[u8; 32]) -> Self {
        self.to_niels().multiply(by)
    }

    /// Converts a batch of projective elements into affine elements.
    ///
    /// This function will panic if `p.len() != q.len()`.
    ///
    /// This costs 5 multiplications per element, and a field inversion.
    fn batch_normalize(p: &[Self], q: &mut [AffinePoint]) {
        assert_eq!(p.len(), q.len());

        for (p, q) in p.iter().zip(q.iter_mut()) {
            // We use the `u` field of `AffinePoint` to store the z-coordinate being
            // inverted, and the `v` field for scratch space.
            q.u = p.z;
        }

        BatchInverter::invert_with_internal_scratch(q, |q| &mut q.u, |q| &mut q.v);

        for (p, q) in p.iter().zip(q.iter_mut()).rev() {
            let tmp = q.u;

            // Set the coordinates to the correct value
            q.u = p.u * tmp; // Multiply by 1/z
            q.v = p.v * tmp; // Multiply by 1/z
        }
    }

    // /// This is only for debugging purposes and not
    // /// exposed in the public API. Checks that this
    // /// point is on the curve.
    // #[cfg(test)]
    // fn is_on_curve_vartime(&self) -> bool {
    //     let affine = AffinePoint::from(*self);

    //     self.z != Fq::zero()
    //         && affine.is_on_curve_vartime()
    //         && (affine.u * affine.v * self.z == self.t1 * self.t2)
    // }

    /// Constructs an AffinePoint given `u` and `v` without checking
    /// that the point is on the curve.
    pub const fn from_raw_unchecked(u: Fq, v: Fq, z: Fq, t1: Fq, t2: Fq) -> ExtendedPoint {
        ExtendedPoint { u, v, z, t1, t2 }
    }

    ////////////////////////////////////////////////////////////////////////////////
}

////////////////////////////////////////////////////////////////////////////////

impl<'a, 'b> Mul<&'b Fr> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    fn mul(self, other: &'b Fr) -> ExtendedPoint {
        self.multiply(&other.to_bytes())
    }
}

impl_binops_multiplicative!(ExtendedPoint, Fr);

impl<'a, 'b> Add<&'b ExtendedNielsPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, other: &'b ExtendedNielsPoint) -> ExtendedPoint {
        // We perform addition in the extended coordinates. Here we use
        // a formula presented by Hisil, Wong, Carter and Dawson in
        // "Twisted Edward Curves Revisited" which only requires 8M.
        //
        // A = (V1 - U1) * (V2 - U2)
        // B = (V1 + U1) * (V2 + U2)
        // C = 2d * T1 * T2
        // D = 2 * Z1 * Z2
        // E = B - A
        // F = D - C
        // G = D + C
        // H = B + A
        // U3 = E * F
        // Y3 = G * H
        // Z3 = F * G
        // T3 = E * H

        let a = (self.v - self.u) * other.v_minus_u;
        let b = (self.v + self.u) * other.v_plus_u;
        let c = self.t1 * self.t2 * other.t2d;
        let d = (self.z * other.z).double();

        // The remaining arithmetic is exactly the process of converting
        // from a completed point to an extended point.
        CompletedPoint {
            u: b - a,
            v: b + a,
            z: d + c,
            t: d - c,
        }
        .into_extended()
    }
}

impl<'a, 'b> Sub<&'b ExtendedNielsPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, other: &'b ExtendedNielsPoint) -> ExtendedPoint {
        let a = (self.v - self.u) * other.v_plus_u;
        let b = (self.v + self.u) * other.v_minus_u;
        let c = self.t1 * self.t2 * other.t2d;
        let d = (self.z * other.z).double();

        CompletedPoint {
            u: b - a,
            v: b + a,
            z: d - c,
            t: d + c,
        }
        .into_extended()
    }
}

impl_binops_additive!(ExtendedPoint, ExtendedNielsPoint);

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/////// A voir
impl<'a, 'b> Add<&'b AffineNielsPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, other: &'b AffineNielsPoint) -> ExtendedPoint {
        // This is identical to the addition formula for `ExtendedNielsPoint`,
        // except we can assume that `other.z` is one, so that we perform
        // 7 multiplications.

        let a = (self.v - self.u) * other.v_minus_u;
        let b = (self.v + self.u) * other.v_plus_u;
        let c = self.t1 * self.t2 * other.t2d;
        let d = self.z.double();

        // The remaining arithmetic is exactly the process of converting
        // from a completed point to an extended point.
        CompletedPoint {
            u: b - a,
            v: b + a,
            z: d + c,
            t: d - c,
        }
        .into_extended()
    }
}

impl<'a, 'b> Sub<&'b AffineNielsPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, other: &'b AffineNielsPoint) -> ExtendedPoint {
        let a = (self.v - self.u) * other.v_plus_u;
        let b = (self.v + self.u) * other.v_minus_u;
        let c = self.t1 * self.t2 * other.t2d;
        let d = self.z.double();

        CompletedPoint {
            u: b - a,
            v: b + a,
            z: d - c,
            t: d + c,
        }
        .into_extended()
    }
}

impl_binops_additive!(ExtendedPoint, AffineNielsPoint);

impl<'a, 'b> Add<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn add(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        self + other.to_niels()
    }
}

impl<'a, 'b> Sub<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn sub(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        self - other.to_niels()
    }
}

impl_binops_additive!(ExtendedPoint, ExtendedPoint);

impl<'a, 'b> Add<&'b AffinePoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn add(self, other: &'b AffinePoint) -> ExtendedPoint {
        self + other.to_niels()
    }
}

impl<'a, 'b> Sub<&'b AffinePoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn sub(self, other: &'b AffinePoint) -> ExtendedPoint {
        self - other.to_niels()
    }
}

impl_binops_additive!(ExtendedPoint, AffinePoint);

/// This is a "completed" point produced during a point doubling or
/// addition routine. These points exist in the `(U:Z, V:T)` model
/// of the curve. This is not exposed in the API because it is
/// an implementation detail.
struct CompletedPoint {
    u: Fq,
    v: Fq,
    z: Fq,
    t: Fq,
}

impl CompletedPoint {
    /// This converts a completed point into an extended point by
    /// homogenizing:
    ///
    /// (u/z, v/t) = (u/z * t/t, v/t * z/z) = (ut/zt, vz/zt)
    ///
    /// The resulting T coordinate is utvz/zt = uv, and so
    /// T1 = u, T2 = v, without loss of generality.
    #[inline]
    fn into_extended(self) -> ExtendedPoint {
        ExtendedPoint {
            u: self.u * self.t,
            v: self.v * self.z,
            z: self.z * self.t,
            t1: self.u,
            t2: self.v,
        }
    }
}

impl Default for AffinePoint {
    /// Returns the identity.
    fn default() -> AffinePoint {
        AffinePoint::identity()
    }
}

impl Default for ExtendedPoint {
    /// Returns the identity.
    fn default() -> ExtendedPoint {
        ExtendedPoint::identity()
    }
}

/// This takes a mutable slice of `ExtendedPoint`s and "normalizes" them using
/// only a single inversion for the entire batch. This normalization results in
/// all of the points having a Z-coordinate of one. Further, an iterator is
/// returned which can be used to obtain `AffinePoint`s for each element in the
/// slice.
///
/// This costs 5 multiplications per element, and a field inversion.
pub fn batch_normalize(v: &mut [ExtendedPoint]) -> impl Iterator<Item = AffinePoint> + '_ {
    // We use the `t1` field of `ExtendedPoint` for scratch space.
    BatchInverter::invert_with_internal_scratch(v, |p| &mut p.z, |p| &mut p.t1);

    for p in v.iter_mut() {
        let mut q = *p;
        let tmp = q.z;

        // Set the coordinates to the correct value
        q.u *= &tmp; // Multiply by 1/z
        q.v *= &tmp; // Multiply by 1/z
        q.z = Fq::one(); // z-coordinate is now one
        q.t1 = q.u;
        q.t2 = q.v;

        *p = q;
    }

    // All extended points are now normalized, but the type
    // doesn't encode this fact. Let us offer affine points
    // to the caller.

    v.iter().map(|p| AffinePoint { u: p.u, v: p.v })
}

impl<'a, 'b> Mul<&'b Fr> for &'a AffinePoint {
    type Output = ExtendedPoint;

    fn mul(self, other: &'b Fr) -> ExtendedPoint {
        self.to_niels().multiply(&other.to_bytes())
    }
}

impl_binops_multiplicative_mixed!(AffinePoint, Fr, ExtendedPoint);

/// This represents a point in the prime-order subgroup of Jubjub, in extended
/// coordinates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SubgroupPoint(ExtendedPoint);

impl From<SubgroupPoint> for ExtendedPoint {
    fn from(val: SubgroupPoint) -> ExtendedPoint {
        val.0
    }
}

impl<'a> From<&'a SubgroupPoint> for &'a ExtendedPoint {
    fn from(val: &'a SubgroupPoint) -> &'a ExtendedPoint {
        &val.0
    }
}

impl fmt::Display for SubgroupPoint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ConditionallySelectable for SubgroupPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        SubgroupPoint(ExtendedPoint::conditional_select(&a.0, &b.0, choice))
    }
}

impl SubgroupPoint {
    /// Constructs an AffinePoint given `u` and `v` without checking that the point is on
    /// the curve or in the prime-order subgroup.
    ///
    /// This should only be used for hard-coding constants (e.g. fixed generators); in all
    /// other cases, use [`SubgroupPoint::from_bytes`] instead.
    ///
    /// [`SubgroupPoint::from_bytes`]: SubgroupPoint#impl-GroupEncoding
    pub const fn from_raw_unchecked(u: Fq, v: Fq) -> Self {
        SubgroupPoint(AffinePoint::from_raw_unchecked(u, v).to_extended())
    }
}

impl<T> Sum<T> for SubgroupPoint
where
    T: Borrow<SubgroupPoint>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl Neg for SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn neg(self) -> SubgroupPoint {
        SubgroupPoint(-self.0)
    }
}

impl Neg for &SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn neg(self) -> SubgroupPoint {
        SubgroupPoint(-self.0)
    }
}

impl<'a, 'b> Add<&'b SubgroupPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn add(self, other: &'b SubgroupPoint) -> ExtendedPoint {
        self + other.0
    }
}

impl<'a, 'b> Sub<&'b SubgroupPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn sub(self, other: &'b SubgroupPoint) -> ExtendedPoint {
        self - other.0
    }
}

impl_binops_additive!(ExtendedPoint, SubgroupPoint);

impl<'a, 'b> Add<&'b SubgroupPoint> for &'a SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn add(self, other: &'b SubgroupPoint) -> SubgroupPoint {
        SubgroupPoint(self.0 + other.0)
    }
}

impl<'a, 'b> Sub<&'b SubgroupPoint> for &'a SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn sub(self, other: &'b SubgroupPoint) -> SubgroupPoint {
        SubgroupPoint(self.0 - other.0)
    }
}

impl_binops_additive!(SubgroupPoint, SubgroupPoint);

impl<'a, 'b> Mul<&'b Fr> for &'a SubgroupPoint {
    type Output = SubgroupPoint;

    fn mul(self, other: &'b Fr) -> SubgroupPoint {
        SubgroupPoint(self.0.multiply(&other.to_bytes()))
    }
}

impl_binops_multiplicative!(SubgroupPoint, Fr);

impl Group for ExtendedPoint {
    type Scalar = Fr;

    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let v = Fq::random(&mut rng);
            let flip_sign = rng.next_u32() % 2 != 0;

            // See AffinePoint::from_bytes for details.
            let v2 = v.square();
            let p = ((v2 - Fq::one())
                * ((Fq::one() + EDWARDS_D * v2).invert().unwrap_or(Fq::zero())))
            .sqrt()
            .map(|u| AffinePoint {
                u: if flip_sign { -u } else { u },
                v,
            });

            if p.is_some().into() {
                let p = p.unwrap().to_curve();

                if bool::from(!p.is_identity()) {
                    return p;
                }
            }
        }
    }

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        AffinePoint::generator().into()
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    #[must_use]
    fn double(&self) -> Self {
        self.double()
    }
}

impl Group for SubgroupPoint {
    type Scalar = Fr;

    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let p = ExtendedPoint::random(&mut rng).clear_cofactor();

            if bool::from(!p.is_identity()) {
                return p;
            }
        }
    }

    fn identity() -> Self {
        SubgroupPoint(ExtendedPoint::identity())
    }

    fn generator() -> Self {
        ExtendedPoint::generator().clear_cofactor()
    }

    fn is_identity(&self) -> Choice {
        self.0.is_identity()
    }

    #[must_use]
    fn double(&self) -> Self {
        SubgroupPoint(self.0.double())
    }
}

#[cfg(feature = "alloc")]
impl WnafGroup for ExtendedPoint {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        // Copied from bls12_381::g1, should be updated.
        const RECOMMENDATIONS: [usize; 12] =
            [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

impl PrimeGroup for SubgroupPoint {}

impl CofactorGroup for ExtendedPoint {
    type Subgroup = SubgroupPoint;

    fn clear_cofactor(&self) -> Self::Subgroup {
        SubgroupPoint(self.mul_by_cofactor())
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(SubgroupPoint(self), self.is_torsion_free())
    }

    fn is_torsion_free(&self) -> Choice {
        self.is_torsion_free()
    }
}

/*
A GARDER LE TO_AFFINE
*/
impl Curve for ExtendedPoint {
    type AffineRepr = AffinePoint;

    fn batch_normalize(p: &[Self], q: &mut [Self::AffineRepr]) {
        Self::batch_normalize(p, q);
    }

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl CofactorCurve for ExtendedPoint {
    type Affine = AffinePoint;
}

impl CofactorCurveAffine for AffinePoint {
    type Scalar = Fr;
    type Curve = ExtendedPoint;

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        // The point with the lowest positive v-coordinate and positive u-coordinate.
        AffinePoint {
            u: Fq::from_raw([
                0xe4b3_d35d_f1a7_adfe,
                0xcaf5_5d1b_29bf_81af,
                0x8b0f_03dd_d60a_8187,
                0x62ed_cbb8_bf37_87c8,
            ]),
            v: Fq::from_raw([
                0x0000_0000_0000_000b,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
            ]),
        }
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    fn to_curve(&self) -> Self::Curve {
        (*self).into()
    }
}

impl GroupEncoding for ExtendedPoint {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        AffinePoint::from_bytes(*bytes).map(Self::from)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        // We can't avoid curve checks when parsing a compressed encoding.
        AffinePoint::from_bytes(*bytes).map(Self::from)
    }

    fn to_bytes(&self) -> Self::Repr {
        AffinePoint::from(self).to_bytes()
    }
}

impl GroupEncoding for SubgroupPoint {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        ExtendedPoint::from_bytes(bytes).and_then(|p| p.into_subgroup())
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        ExtendedPoint::from_bytes_unchecked(bytes).map(SubgroupPoint)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.0.to_bytes()
    }
}

impl GroupEncoding for AffinePoint {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(*bytes)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(*bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.to_bytes()
    }
}
