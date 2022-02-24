extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use curve25519_dalek::scalar::Scalar;
use libspartan::{InputsAssignment, Instance, VarsAssignment};
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
    let mut r1cs: R1CS = R1CS::new(&Vec::from([("A", a), ("B", b)]));

    // generate constraints for a range proof
    r1cs.new_range_constraint("A", "B", "x");

    // generate a witness to satisfy these constraints
    r1cs.add_witness_var_assignment("x", x);
    r1cs.generate_witness_range("A", "B", "x", a, b, x);

    // build our r1cs instance
    let (inst, num_cons, num_vars, num_inputs, num_non_zero_entries) = r1cs.build_instance();

    // build our witness
    let (assignment_vars, assignment_inputs) = r1cs.build_witness();

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

    fn range_proof_test_helper(x: Scalar, a: Scalar, b: Scalar, expected_to_verify: bool) {
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
        assert_eq!(
            expected_to_verify,
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
        range_proof_test_helper(Scalar::from(2u32), a, b, true);
        range_proof_test_helper(Scalar::from(3u32), a, b, true);
        range_proof_test_helper(Scalar::from(4u32), a, b, true);
        range_proof_test_helper(Scalar::from(4u32), a, b, true);
    }

    #[test]
    fn range_proof_small_out_of_range_test() {
        let a: Scalar = Scalar::from(2u32);
        let b: Scalar = Scalar::from(5u32);
        range_proof_test_helper(-Scalar::one(), a, b, false);
        range_proof_test_helper(Scalar::zero(), a, b, false);
        range_proof_test_helper(Scalar::one(), a, b, false);
        range_proof_test_helper(Scalar::from(6u32), a, b, false);
        range_proof_test_helper(Scalar::from(7u32), a, b, false);
    }

    #[test]
    fn range_proof_large_in_range_test() {
        let a: Scalar = get_pow_2(88);
        let b: Scalar = get_pow_2(97);
        range_proof_test_helper(get_pow_2(88), a, b, true);
        range_proof_test_helper(get_pow_2(97), a, b, true);
        range_proof_test_helper(get_pow_2(88) + Scalar::one(), a, b, true);
        range_proof_test_helper(get_pow_2(92), a, b, true);
    }

    #[test]
    fn range_proof_large_out_of_range_test() {
        let a: Scalar = get_pow_2(88);
        let b: Scalar = get_pow_2(97);
        range_proof_test_helper(Scalar::one(), a, b, false);
        range_proof_test_helper(get_pow_2(97) + Scalar::one(), a, b, false);
        range_proof_test_helper(get_pow_2(88) + -Scalar::one(), a, b, false);
        range_proof_test_helper(get_pow_2(98), a, b, false);
        range_proof_test_helper(get_pow_2(65), a, b, false);
    }
}