#![allow(non_snake_case)]

pub mod r1cs_helpers;
pub mod bit_helpers;
pub mod range_proof;

extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use curve25519_dalek::scalar::Scalar;
use libspartan::{InputsAssignment, SNARKGens, SNARK};
use merlin::Transcript;
use crate::bit_helpers::get_pow_2;
use crate::range_proof::produce_range_r1cs;

fn main() {
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
    ) = produce_range_r1cs(
        get_pow_2(20),
        get_pow_2(16),
        get_pow_2(25),
    );

    // produce public parameters
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_non_zero_entries);

    // create a commitment to the R1CS instance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a proof of satisfiability
    let mut prover_transcript = Transcript::new(b"range_proof_example");
    let proof =  SNARK::prove(
        &inst,
        &decomm,
        assignment_vars,
        &assignment_inputs,
        &gens,
        &mut prover_transcript,
    );

    // generate inputs, if any
    let custom_assignment_inputs = InputsAssignment::new(&vec![Scalar::zero().to_bytes(); num_inputs]).unwrap();

    // verify the proof of satisfiability
    let mut verifier_transcript = Transcript::new(b"range_proof_example");

    let success = proof
        .verify(&comm, &custom_assignment_inputs, &mut verifier_transcript, &gens)
        .is_ok();

    if success {
        println!("proof verification successful!");
    } else {
        println!("proof verification failed!");
    }
}
