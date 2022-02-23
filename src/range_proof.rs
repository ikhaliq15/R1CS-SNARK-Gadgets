extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use std::ops::Neg;
use curve25519_dalek::scalar::Scalar;
use libspartan::{InputsAssignment, Instance, VarsAssignment};
use crate::bit_helpers::{get_bit, sum_last_n_bits};
use crate::r1cs::*;

/*  Generates a R1CS instance for a proof that X is the range
    between A and B (both are inclusive).  */
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

    let mut r1cs: R1CS = R1CS::new(&Vec::from([("A", a), ("B", b)]));
    r1cs.new_range_constraint("A", "B", "x");

    let mut vars: Vec<(usize, [u8; 32])> = Vec::new();
    vars.push((r1cs.get_var_index("one"), one.to_bytes()));
    vars.push((r1cs.get_var_index("A"), a.to_bytes()));
    vars.push((r1cs.get_var_index("B"), b.to_bytes()));
    vars.push((r1cs.get_var_index("x"), x.to_bytes()));

    // this should detect overflow if bits in y is less than approx 250 bits
    let y: Scalar = (a - x) * (x - b);
    let y_is_neg: bool = sum_last_n_bits(y.to_bytes(), 8) != 0;
    let y_bits = if y_is_neg { y.neg().to_bytes() } else { y.to_bytes() };
    let bits_in_y: usize = 202;

    vars.push((r1cs.get_var_index("y"), y.to_bytes()));

    /* get the values of y_biti that are used in the range proof constraint. */
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
        vars.push((r1cs.get_var_index(&*format!("y_bit{:}", i)), b.to_bytes()));
    }

    // build our r1cs instance
    let (inst, num_cons, num_vars, num_inputs, num_non_zero_entries) = r1cs.build_instance();

    // compute the final witness
    let mut final_vars = vec![zero.to_bytes(); vars.len()];
    for (i, v) in vars.iter() {
        final_vars[*i] = *v;
    }
    let assignment_vars = VarsAssignment::new(&final_vars).unwrap();
    let assignment_inputs = InputsAssignment::new(&vec![zero.to_bytes(); 0]).unwrap();

    // check if the instance we created is satisfied by our witness
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