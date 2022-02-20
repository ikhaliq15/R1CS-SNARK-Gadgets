extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use std::cmp::max;
use std::collections::HashMap;
use curve25519_dalek::scalar::Scalar;
use crate::bit_helpers::{get_pow_2};

pub fn get_var_index(
    var: String,
    vars: &mut HashMap<String, usize>
) -> usize {
    if !vars.contains_key(var.as_str()) {
        vars.insert(var.clone(), vars.len());
    }
    *vars.get(var.as_str()).unwrap()
}

pub fn add_mult_constraint(
    x: String,
    y: String,
    z: String,
    constraint_id: &mut usize,
    num_non_zero: &mut usize,
    variables: &mut HashMap<String, usize>,
    A: &mut Vec<(usize, usize, [u8; 32])>,
    B: &mut Vec<(usize, usize, [u8; 32])>,
    C: &mut Vec<(usize, usize, [u8; 32])>
) {
    A.push((*constraint_id, get_var_index(x, variables), Scalar::one().to_bytes()));
    B.push((*constraint_id, get_var_index(y, variables), Scalar::one().to_bytes()));
    C.push((*constraint_id, get_var_index(z, variables), Scalar::one().to_bytes()));
    *num_non_zero += 1;
    *constraint_id += 1;
}

pub fn add_mult_scalar_constraint(
    x: String,
    y: Scalar,
    z: String,
    constraint_id: &mut usize,
    num_non_zero: &mut usize,
    variables: &mut HashMap<String, usize>,
    A: &mut Vec<(usize, usize, [u8; 32])>,
    B: &mut Vec<(usize, usize, [u8; 32])>,
    C: &mut Vec<(usize, usize, [u8; 32])>
) {
    A.push((*constraint_id, get_var_index(x, variables), Scalar::one().to_bytes()));
    B.push((*constraint_id, get_var_index("one".to_string(), variables), y.to_bytes()));
    C.push((*constraint_id, get_var_index(z, variables), Scalar::one().to_bytes()));
    *num_non_zero += 1;
    *constraint_id += 1;
}

pub fn add_addition_constraint(
    x: String,
    y: String,
    z: String,
    constraint_id: &mut usize,
    num_non_zero: &mut usize,
    variables: &mut HashMap<String, usize>,
    A: &mut Vec<(usize, usize, [u8; 32])>,
    B: &mut Vec<(usize, usize, [u8; 32])>,
    C: &mut Vec<(usize, usize, [u8; 32])>
) {
    A.push((*constraint_id, get_var_index(x, variables), Scalar::one().to_bytes()));
    A.push((*constraint_id, get_var_index(y, variables), Scalar::one().to_bytes()));
    B.push((*constraint_id, get_var_index("one".to_string(), variables), Scalar::one().to_bytes()));
    C.push((*constraint_id, get_var_index(z, variables), Scalar::one().to_bytes()));
    *num_non_zero += 2;
    *constraint_id += 1;
}

pub fn add_subtraction_constraint(
    x: String,
    y: String,
    z: String,
    constraint_id: &mut usize,
    num_non_zero: &mut usize,
    variables: &mut HashMap<String, usize>,
    A: &mut Vec<(usize, usize, [u8; 32])>,
    B: &mut Vec<(usize, usize, [u8; 32])>,
    C: &mut Vec<(usize, usize, [u8; 32])>
) {
    A.push((*constraint_id, get_var_index(x, variables), Scalar::one().to_bytes()));
    A.push((*constraint_id, get_var_index(y, variables), (-Scalar::one()).to_bytes()));
    B.push((*constraint_id, get_var_index("one".to_string(), variables), Scalar::one().to_bytes()));
    C.push((*constraint_id, get_var_index(z, variables), Scalar::one().to_bytes()));
    *num_non_zero += 2;
    *constraint_id += 1;
}

pub fn add_is_bit_constraint(
    x: String,
    constraint_id: &mut usize,
    num_non_zero: &mut usize,
    variables: &mut HashMap<String, usize>,
    A: &mut Vec<(usize, usize, [u8; 32])>,
    B: &mut Vec<(usize, usize, [u8; 32])>,
    _C: &mut Vec<(usize, usize, [u8; 32])>
) {
    A.push((*constraint_id, get_var_index(x.clone(), variables), Scalar::one().to_bytes()));
    B.push((*constraint_id, get_var_index(x.clone(), variables), Scalar::one().to_bytes()));
    B.push((*constraint_id, get_var_index("one".to_string(), variables), (-Scalar::one()).to_bytes()));
    *num_non_zero += 2;
    *constraint_id += 1;
}

pub fn add_equality_scalar_constraint(
    x: String,
    y: Scalar,
    constraint_id: &mut usize,
    num_non_zero: &mut usize,
    variables: &mut HashMap<String, usize>,
    A: &mut Vec<(usize, usize, [u8; 32])>,
    B: &mut Vec<(usize, usize, [u8; 32])>,
    C: &mut Vec<(usize, usize, [u8; 32])>
) {
    A.push((*constraint_id, get_var_index("one".to_string(), variables), y.to_bytes()));
    B.push((*constraint_id, get_var_index("one".to_string(), variables), Scalar::one().to_bytes()));
    C.push((*constraint_id, get_var_index(x.clone(), variables), Scalar::one().to_bytes()));
    *num_non_zero += 1;
    *constraint_id += 1;
}

pub fn add_equality_constraint(
    x: String,
    y: String,
    constraint_id: &mut usize,
    num_non_zero: &mut usize,
    variables: &mut HashMap<String, usize>,
    A: &mut Vec<(usize, usize, [u8; 32])>,
    B: &mut Vec<(usize, usize, [u8; 32])>,
    C: &mut Vec<(usize, usize, [u8; 32])>
) {
    A.push((*constraint_id, get_var_index(x.clone(), variables), Scalar::one().to_bytes()));
    B.push((*constraint_id, get_var_index("one".to_string(), variables), Scalar::one().to_bytes()));
    C.push((*constraint_id, get_var_index(y.clone(), variables), Scalar::one().to_bytes()));
    *num_non_zero += 1;
    *constraint_id += 1;
}

pub fn add_twos_complement_decomposition_constraint (
    x: String,
    N: usize,
    constraint_id: &mut usize,
    num_non_zero: &mut usize,
    variables: &mut HashMap<String, usize>,
    A: &mut Vec<(usize, usize, [u8; 32])>,
    B: &mut Vec<(usize, usize, [u8; 32])>,
    C: &mut Vec<(usize, usize, [u8; 32])>
) {
    for i in 0..N {
        if i == N - 1 {
            A.push((*constraint_id, get_var_index(format!("{:}_bit{:}", x, i), variables), (-get_pow_2(i)).to_bytes()))
        } else {
            A.push((*constraint_id, get_var_index(format!("{:}_bit{:}", x, i), variables), get_pow_2(i).to_bytes()))
        }
    }

    B.push((*constraint_id, get_var_index("one".to_string(), variables), Scalar::one().to_bytes()));
    C.push((*constraint_id, get_var_index(x.clone(), variables), Scalar::one().to_bytes()));

    *num_non_zero += max(N, 1);
    *constraint_id += 1;

    for i in 0..N {
        add_is_bit_constraint(format!("{:}_bit{:}", x, i), constraint_id, num_non_zero, variables, A, B, C);
    }
}