extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use std::cmp::min;
use std::collections::HashMap;
use std::ops::Neg;
use curve25519_dalek::scalar::Scalar;
use libspartan::{InputsAssignment, Instance, VarsAssignment};
use crate::bit_helpers::{get_bit, sum_last_n_bits};
use crate::r1cs_helpers::*;

pub fn produce_range_r1cs(x: Scalar, a: Scalar, b: Scalar) -> (
    usize,
    usize,
    usize,
    usize,
    Instance,
    VarsAssignment,
    InputsAssignment,
    bool
) {
    /* Build a rank 1 constraint system so that x \in [A, B] */
    let zero = Scalar::zero();
    let one = Scalar::one();

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
    let mut num_non_zero_entries = 0;

    /* verify that A is the agreed lower bound */
    add_equality_scalar_constraint(
        "A".to_string(), a,
        &mut num_cons, &mut num_non_zero_entries, &mut variables,
        &mut A, &mut B, &mut C
    );

    /* verify that B is the agreed upper bound */
    add_equality_scalar_constraint(
        "B".to_string(), b,
        &mut num_cons, &mut num_non_zero_entries, &mut variables,
        &mut A, &mut B, &mut C);

    /* verify y == (a - x) * (x - b) */
    let y: Scalar = (a - x) * (x - b);
    let bits_in_y: usize = 202;

    // this should detect overflow if bits in y is less than approx 250
    let y_is_neg: bool = sum_last_n_bits(y.to_bytes(), 8) != 0;

    add_subtraction_constraint(
        "A".to_string(),
        "x".to_string(),
        "t1".to_string(),
        &mut num_cons, &mut num_non_zero_entries, &mut variables,
        &mut A, &mut B, &mut C
    );
    add_subtraction_constraint(
        "x".to_string(),
        "B".to_string(),
        "t2".to_string(),
        &mut num_cons, &mut num_non_zero_entries, &mut variables,
        &mut A, &mut B, &mut C
    );
    add_mult_constraint(
        "t1".to_string(),
        "t2".to_string(),
        "y".to_string(),
        &mut num_cons, &mut num_non_zero_entries, &mut variables,
        &mut A, &mut B, &mut C
    );
    vars.push((get_var_index("t1".to_string() , &mut variables), (a - x).to_bytes()));
    vars.push((get_var_index("t2".to_string() , &mut variables), (x - b).to_bytes()));
    vars.push((get_var_index("y".to_string() , &mut variables), y.to_bytes()));

    /* verify that each y_i is a bit (\forall i, y_i \in \{0, 1\})
       also verify that -2^{n-1} * y_{n-1} + \sum_{i=0}^{n-2} 2^i * y_i = y
       essentially, verify that the bits y_i form two's complement of y */
    add_twos_complement_decomposition_constraint(
        "y".to_string(),
        bits_in_y,
        &mut num_cons, &mut num_non_zero_entries, &mut variables,
        &mut A, &mut B, &mut C
    );

    let y_bits = if y_is_neg { y.neg().to_bytes() } else { y.to_bytes() };
    let mut carry: u8 = 1;
    for i in 0..bits_in_y {
        // determine what the i-th bit of y is in two's complement representation
        let mut u_bit = get_bit(y_bits, i);
        if y_is_neg {
            u_bit = (1 - u_bit) + carry;
            carry = if u_bit > 1 { 1 } else { 0 };
            u_bit = u_bit & 1;
        }
        let b = if u_bit == 1 { one } else { zero };
        vars.push((get_var_index(format!("y_bit{:}", i), &mut variables), b.to_bytes()));
    }

    // verify y > 0 (if y_i form two's complement of y, then just check MSB == 0)
    add_equality_scalar_constraint(
        format!("y_bit{:}", bits_in_y - 1),
        zero,
        &mut num_cons, &mut num_non_zero_entries, &mut variables,
        &mut A, &mut B, &mut C
    );

    /* Post setup so that one and inputs are put in front of variables. */

    // one = 1 * 1
    A.push((num_cons, variables.len(), one.to_bytes()));
    B.push((num_cons, variables.len(), one.to_bytes()));
    C.push((num_cons, get_var_index("one".to_string(), &mut variables), one.to_bytes()));
    num_non_zero_entries += 1;
    num_cons += 1;

    /* Construct r1cs instance. */
    let num_vars = variables.len();
    let num_inputs = 0;
    num_non_zero_entries = min(num_non_zero_entries, num_vars.next_power_of_two() + 1);
    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C).unwrap();

    // compute the final witness
    let mut final_vars = vec![zero.to_bytes(); vars.len()];
    for (i, v) in vars.iter() {
        final_vars[*i] = *v;
    }
    let assignment_vars = VarsAssignment::new(&final_vars).unwrap();
    let assignment_inputs = InputsAssignment::new(&vec![zero.to_bytes(); 0]).unwrap();

    // check if the instance we created is satisfiable
    let witness_satisfies_instance: bool = inst
        .is_sat(&assignment_vars, &assignment_inputs)
        .unwrap_or(false);

    (
        num_cons,
        num_vars,
        num_inputs,
        num_non_zero_entries,
        inst,
        assignment_vars,
        assignment_inputs,
        witness_satisfies_instance
    )
}

#[cfg(test)]
mod range_proof_tests {
    use curve25519_dalek::scalar::Scalar;
    use libspartan::{InputsAssignment, SNARK, SNARKGens};
    use merlin::Transcript;
    use crate::{get_pow_2, produce_range_r1cs};

    fn range_proof_test_helper(x: Scalar, a: Scalar, b: Scalar) {
        // produce a range proof
        let (
            num_cons,
            num_vars,
            num_inputs,
            num_non_zero_entries,
            inst,
            assignment_vars,
            assignment_inputs,
            _
        ) = produce_range_r1cs(x, a, b);

        // produce public parameters
        let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_non_zero_entries);

        // create a commitment to the R1CS instance
        let (comm, decomm) = SNARK::encode(&inst, &gens);

        // produce a proof of satisfiability
        let mut prover_transcript = Transcript::new(b"range_proof_test");
        let proof = SNARK::prove(
            &inst,
            &decomm,
            assignment_vars,
            &assignment_inputs,
            &gens,
            &mut prover_transcript,
        );

        // generate inputs, if any
        let custom_inputs = vec![Scalar::zero().to_bytes(); num_inputs];
        let custom_assignment_inputs = InputsAssignment::new(&custom_inputs).unwrap();

        // verify the proof of satisfiability
        let mut verifier_transcript = Transcript::new(b"range_proof_test");
        assert!(
            proof
                .verify(&comm, &custom_assignment_inputs, &mut verifier_transcript, &gens)
                .is_ok(),
            "testing range proof"
        );
    }

    #[test]
    fn range_proof_small_in_range_test() {
        let a: Scalar = Scalar::from(2u32);
        let b: Scalar = Scalar::from(5u32);
        range_proof_test_helper(Scalar::from(2u32), a, b);
        range_proof_test_helper(Scalar::from(3u32), a, b);
        range_proof_test_helper(Scalar::from(4u32), a, b);
        range_proof_test_helper(Scalar::from(4u32), a, b);
    }

    #[test]
    #[should_panic]
    fn range_proof_small_out_of_range_1_test() {
        let a: Scalar = Scalar::from(2u32);
        let b: Scalar = Scalar::from(5u32);
        range_proof_test_helper(-Scalar::one(), a, b);
    }

    #[test]
    #[should_panic]
    fn range_proof_small_out_of_range_2_test() {
        let a: Scalar = Scalar::from(2u32);
        let b: Scalar = Scalar::from(5u32);
        range_proof_test_helper(Scalar::zero(), a, b);
    }

    #[test]
    #[should_panic]
    fn range_proof_small_out_of_range_3_test() {
        let a: Scalar = Scalar::from(2u32);
        let b: Scalar = Scalar::from(5u32);
        range_proof_test_helper(Scalar::one(), a, b);
    }


    #[test]
    #[should_panic]
    fn range_proof_small_out_of_range_4_test() {
        let a: Scalar = Scalar::from(2u32);
        let b: Scalar = Scalar::from(5u32);
        range_proof_test_helper(Scalar::from(6u32), a, b);
    }

    #[test]
    #[should_panic]
    fn range_proof_small_out_of_range_5_test() {
        let a: Scalar = Scalar::from(2u32);
        let b: Scalar = Scalar::from(5u32);
        range_proof_test_helper(Scalar::from(7u32), a, b);
    }

    #[test]
    fn range_proof_large_in_range_test() {
        let a: Scalar = get_pow_2(88);
        let b: Scalar = get_pow_2(97);
        range_proof_test_helper(get_pow_2(88), a, b);
        range_proof_test_helper(get_pow_2(97), a, b);
        range_proof_test_helper(get_pow_2(88) + Scalar::one(), a, b);
        range_proof_test_helper(get_pow_2(92), a, b);
    }

    #[test]
    #[should_panic]
    fn range_proof_large_out_of_range_1_test() {
        let a: Scalar = get_pow_2(88);
        let b: Scalar = get_pow_2(97);
        range_proof_test_helper(Scalar::one(), a, b);
    }

    #[test]
    #[should_panic]
    fn range_proof_large_out_of_range_2_test() {
        let a: Scalar = get_pow_2(88);
        let b: Scalar = get_pow_2(97);
        range_proof_test_helper(get_pow_2(97) + Scalar::one(), a, b);
    }

    #[test]
    #[should_panic]
    fn range_proof_large_out_of_range_3_test() {
        let a: Scalar = get_pow_2(88);
        let b: Scalar = get_pow_2(97);
        range_proof_test_helper(get_pow_2(88) + -Scalar::one(), a, b);
    }


    #[test]
    #[should_panic]
    fn range_proof_large_out_of_range_4_test() {
        let a: Scalar = get_pow_2(88);
        let b: Scalar = get_pow_2(97);
        range_proof_test_helper(get_pow_2(98), a, b);
    }

    #[test]
    #[should_panic]
    fn range_proof_large_out_of_range_5_test() {
        let a: Scalar = get_pow_2(88);
        let b: Scalar = get_pow_2(97);
        range_proof_test_helper(get_pow_2(65), a, b);
    }
}