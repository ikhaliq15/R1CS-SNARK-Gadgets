extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use curve25519_dalek::scalar::Scalar;
use libspartan::{InputsAssignment, Instance, VarsAssignment};
use crate::r1cs::*;

/*  Generates a R1CS instance for a proof that SECRET is in SET.
    SET should not have any repeating values (otherwise it is not a set). */
pub fn produce_set_membership_r1cs(secret: Scalar, set: Vec<Scalar>) -> (
    usize,
    usize,
    usize,
    usize,
    Instance,
    VarsAssignment,
    InputsAssignment,
    bool
) {
    /* Build a rank 1 constraint system so that SECRET \in SET. */
    let set_value_names: Vec<String> = (0..set.len()).map(|i: usize| format!("set[{}]", i)).collect();
    let input_value_pairs: Vec<(&str, Scalar)> = set_value_names.iter().zip(set.clone()).map(|(k, v)| (k.as_str(), v) ).collect();

    let mut r1cs: R1CS = R1CS::new(&input_value_pairs);

    // generate constraints for a set membership proof
    r1cs.new_set_membership_constraint("secret", set_value_names.iter().map(|s| s.as_str()).collect());

    // generate a witness to satisfy these constraints
    r1cs.add_witness_var_assignment("secret", secret);
    r1cs.generate_witness_set_membership("secret", secret, set);

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
mod set_membership_tests {
    use curve25519_dalek::scalar::Scalar;
    use libspartan::{InputsAssignment, SNARK, SNARKGens};
    use merlin::Transcript;
    use crate::set_membership::produce_set_membership_r1cs;

    fn set_membership_test_helper(secret: Scalar, set: Vec<Scalar>) {
        // produce a set_membership proof
        let (
            num_cons,
            num_vars,
            num_inputs,
            num_non_zero_entries,
            inst,
            assignment_vars,
            assignment_inputs,
            _
        ) = produce_set_membership_r1cs(secret, set);

        // produce public parameters
        let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_non_zero_entries);

        // create a commitment to the R1CS instance
        let (comm, decomm) = SNARK::encode(&inst, &gens);

        // produce a proof of satisfiability
        let mut prover_transcript = Transcript::new(b"set_membership_test");
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
        let mut verifier_transcript = Transcript::new(b"set_membership_test");
        assert!(
            proof
                .verify(&comm, &custom_assignment_inputs, &mut verifier_transcript, &gens)
                .is_ok(),
            "testing set membership proof"
        );
    }

    #[test]
    #[should_panic]
    fn set_membership_empty_set_test() {
        set_membership_test_helper(Scalar::from(156u32), Vec::new());
    }

    #[test]
    fn set_membership_singleton_set_is_member_test() {
        set_membership_test_helper(Scalar::from(1323u32), Vec::from([Scalar::from(1323u32)]));
    }

    #[test]
    fn set_membership_small_set_is_member_test() {
        let set: Vec<Scalar> = Vec::from([
            Scalar::from(1323u32),
            Scalar::from(3u32),
            Scalar::from(0u32),
            Scalar::from(4235u32),
            Scalar::from(13532u32),
            Scalar::from(4892332u32),
        ]);
        for value in set.iter() {
            set_membership_test_helper(*value, set.clone());
        }
    }

    #[test]
    #[should_panic]
    fn set_membership_small_set_is_not_member_test() {
        let set: Vec<Scalar> = Vec::from([
            Scalar::from(1323u32),
            Scalar::from(3u32),
            Scalar::from(0u32),
            Scalar::from(321u32),
            Scalar::from(13532u32),
            Scalar::from(4892332u32),
        ]);
        set_membership_test_helper(Scalar::from(4235u32), set);
    }

    // TODO: add tests for larger sets
}