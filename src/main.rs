#![allow(non_snake_case)]

mod r1cs_helpers;
mod bit_helpers;

extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use r1cs_helpers::*;
use std::collections::HashMap;
use std::ops::Neg;
use curve25519_dalek::scalar::Scalar;
use libspartan::{InputsAssignment, Instance, SNARKGens, VarsAssignment, SNARK};
use merlin::Transcript;
use r1cs::num::pow;
use crate::bit_helpers::sum_last_n_bits;

fn main() {
    // produce a tiny instance
    let (
        num_cons,
        num_vars,
        num_inputs,
        num_non_zero_entries,
        inst,
        assignment_vars,
        assignment_inputs,
    ) = produce_range_r1cs(
        Scalar::from(pow(2, 23  ) + 325013u32),
        Scalar::from(pow(2, 16) as u32),
        Scalar::from(pow(2, 25) as u32),
        100
    );

    // produce public parameters
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_non_zero_entries);

    // create a commitment to the R1CS instance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a proof of satisfiability
    let mut prover_transcript = Transcript::new(b"snark_example");
    let proof = SNARK::prove(
        &inst,
        &decomm,
        assignment_vars,
        &assignment_inputs,
        &gens,
        &mut prover_transcript,
    );

    let custom_inputs = vec![Scalar::zero().to_bytes(); num_inputs];
    let custom_assignment_inputs = InputsAssignment::new(&custom_inputs).unwrap();

    // verify the proof of satisfiability
    let mut verifier_transcript = Transcript::new(b"snark_example");
    assert!(proof
        .verify(&comm, &custom_assignment_inputs, &mut verifier_transcript, &gens)
        .is_ok());

    println!("proof verification successful!");
}


fn produce_range_r1cs(x: Scalar, a: Scalar, b: Scalar, n: usize) -> (
    usize,
    usize,
    usize,
    usize,
    Instance,
    VarsAssignment,
    InputsAssignment,
) {
    /* Build a rank 1 constraint system so that x \in [A, B] */
    let zero = Scalar::zero();
    let one = Scalar::one();
    let two: Scalar = Scalar::from(2u32);

    let mut variables: HashMap<String, usize> = HashMap::new();

    let mut vars: Vec<(usize, [u8; 32])> = Vec::new();
    vars.push((get_var_index("one".to_string(), &mut variables), one.to_bytes()));
    vars.push((get_var_index("A".to_string(), &mut variables), a.to_bytes()));
    vars.push((get_var_index("B".to_string(), &mut variables), b.to_bytes()));
    vars.push((get_var_index("x".to_string(), &mut variables), x.to_bytes()));

    let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
    let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
    let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

    let mut num_cons = 0;

    /* verify that A is the agreed lower bound */
    add_equality_scalar_constraint("A".to_string(), a, &mut num_cons, &mut variables, &mut A, &mut B, &mut C);

    /* verify that B is the agreed upper bound */
    add_equality_scalar_constraint("B".to_string(), b, &mut num_cons, &mut variables, &mut A, &mut B, &mut C);

    /* verify y == (a - x) * (x - b) */
    let y: Scalar = (a - x) * (x - b);
    let bits_in_y: usize = 2 * n + 2;

    // this should detect overflow if bits in y is less than approx 250
    let y_is_neg: bool = sum_last_n_bits(y.to_bytes(), 8) != 0;

    add_subtraction_constraint(
        "A".to_string(),
        "x".to_string(),
        "t1".to_string(),
        &mut num_cons, &mut variables, &mut A, &mut B, &mut C
    );
    add_subtraction_constraint(
        "x".to_string(),
        "B".to_string(),
        "t2".to_string(),
        &mut num_cons, &mut variables, &mut A, &mut B, &mut C
    );
    add_mult_constraint(
        "t1".to_string(),
        "t2".to_string(),
        "y".to_string(),
        &mut num_cons, &mut variables, &mut A, &mut B, &mut C
    );
    vars.push((get_var_index("t1".to_string() , &mut variables), (a - x).to_bytes()));
    vars.push((get_var_index("t2".to_string() , &mut variables), (x - b).to_bytes()));
    vars.push((get_var_index("y".to_string() , &mut variables), y.to_bytes()));

    /* construct the necessary powers of two for bit-decomposition */
    let mut power: Scalar = one;

    // verify our powers of two begin with 2^0 = 1
    add_equality_scalar_constraint("power_0".to_string(), power, &mut num_cons, &mut variables, &mut A, &mut B, &mut C);
    vars.push((get_var_index("power_0".to_string(), &mut variables), power.to_bytes()));

    // construct 2^i for i \in [1..|y|-1] where |y| is size of y in bits
    for i in 0..(bits_in_y-1) {
        add_mult_scalar_constraint(
            format!("power_{:}", i),
            two,
            format!("power_{:}", i + 1),
            &mut num_cons,
            &mut variables,
            &mut A,
            &mut B,
            &mut C
        );
        power = power * two;
        vars.push((get_var_index(format!("power_{:}", i + 1), &mut variables), power.to_bytes()));
    }

    // construct -2^i for i = |y| - 1
    add_mult_scalar_constraint(
        format!("power_{:}", bits_in_y - 1),
        -one, format!("-power_{:}", bits_in_y - 1),
        &mut num_cons, &mut variables, &mut A, &mut B, &mut C
    );
    vars.push((get_var_index(format!("-power_{:}", bits_in_y - 1), &mut variables), (-power).to_bytes()));

    /* verify that each y_i is a bit (\forall i, y_i \in \{0, 1\})
       also verify that -2^{n-1} * y_{n-1} + \sum_{i=0}^{n-2} 2^i * y_i = y
       essentially, verify that the bits y_i form two's complement of y */
    let mut total: Scalar = zero;
    power = one;

    // verify that our summations begins at 0
    add_equality_scalar_constraint("total_0".to_string(), total, &mut num_cons, &mut variables, &mut A, &mut B, &mut C);
    vars.push((get_var_index("total_0".to_string(), &mut variables), total.to_bytes()));

    // construct bit decomposition constraints
    let y_bits = if y_is_neg { y.neg().to_bytes() } else { y.to_bytes() };
    let mut carry: u8 = 1;
    for i in 0..bits_in_y {
        // determine what the i-th bit of y is in two's complement representation
        let mut u_bit = (y_bits[i / 8] >> (i % 8)) & 1;
        if y_is_neg {
            u_bit = (1 - u_bit) + carry;
            carry = if u_bit > 1 { 1 } else { 0 };
            u_bit = u_bit % 2;
        }
        let b = if u_bit == 1 { one } else { zero };

        // add constraints to check y_i is a bit
        // also generate witness for y_i
        add_is_bit_constraint(format!("y_{:?}", i), &mut num_cons, &mut variables, &mut A, &mut B, &mut C);
        vars.push((get_var_index(format!("y_{:?}", i), &mut variables), b.to_bytes()));

        // do part of the summation that ensures that y_i form two's complement of y
        // also generate our witness for intermediary results of the summation
        if i == bits_in_y - 1 {
            add_mult_constraint(
                format!("y_{:?}", i),
                format!("-power_{:?}", i),
                format!("temp_{:?}", i),
                &mut num_cons, &mut variables, &mut A, &mut B, &mut C
            );
            vars.push((get_var_index(format!("temp_{:?}", i), &mut variables), (b * -power).to_bytes()));
            vars.push((get_var_index(format!("total_{:?}", i + 1), &mut variables), (total - (b * power)).to_bytes()));
        } else {
            add_mult_constraint(
                format!("y_{:?}", i),
                format!("power_{:?}", i),
                format!("temp_{:?}", i),
                &mut num_cons, &mut variables, &mut A, &mut B, &mut C)
            ;
            vars.push((get_var_index(format!("temp_{:?}", i), &mut variables), (b * power).to_bytes()));
            vars.push((get_var_index(format!("total_{:?}", i + 1), &mut variables), (total + b * power).to_bytes()));
        }
        add_addition_constraint(
            format!("total_{:?}", i),
            format!("temp_{:?}", i),
            format!("total_{:?}", i + 1),
            &mut num_cons, &mut variables, &mut A, &mut B, &mut C
        );
        total += b * power;
        power *= two;
    }

    // verify that y_i are two's complement representation of y
    add_equality_constraint(
        "y".to_string(),
        format!("total_{:?}", bits_in_y),
        &mut num_cons, &mut variables, &mut A, &mut B, &mut C
    );

    // verify y > 0 (if y_i form two's complement of y, then just check MSB == 0)
    add_equality_scalar_constraint(
        format!("y_{:}", bits_in_y - 1),
        zero,
        &mut num_cons, &mut variables, &mut A, &mut B, &mut C
    );

    /* Post setup so that one and inputs are put in front of variables. */

    // one = 1 * 1
    A.push((num_cons, get_var_index("one".to_string(), &mut variables), one.to_bytes()));
    B.push((num_cons, get_var_index("one".to_string(), &mut variables), one.to_bytes()));
    C.push((num_cons, variables.len(), one.to_bytes()));
    num_cons += 1;

    /* Construct r1cs instance. */
    let num_vars = variables.len();
    let num_inputs = 0;
    let num_non_zero_entries = variables.len().next_power_of_two() + 0;
    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C).unwrap();

    // compute the final witness
    let mut final_vars = vec![zero.to_bytes(); vars.len()];
    for (i, v) in vars.iter() {
        final_vars[*i] = *v;
    }
    let assignment_vars = VarsAssignment::new(&final_vars).unwrap();

    let inputs = vec![zero.to_bytes(); num_inputs];
    let assignment_inputs = InputsAssignment::new(&inputs).unwrap();

    // check if the instance we created is satisfiable
    let res = inst.is_sat(&assignment_vars, &assignment_inputs);
    assert!(res.unwrap());

    (
        num_cons,
        num_vars,
        num_inputs,
        num_non_zero_entries,
        inst,
        assignment_vars,
        assignment_inputs,
    )
}
