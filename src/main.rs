#![allow(non_snake_case)]

mod r1cs_helpers;
mod bit_helpers;
mod range_proof;

extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use curve25519_dalek::scalar::Scalar;
use libspartan::{InputsAssignment, SNARKGens, SNARK};
use merlin::Transcript;
use r1cs::num::pow;
use crate::range_proof::produce_range_r1cs;

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
        Scalar::from(pow(2, 23) + 325013u32),
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

    // generate inputs, if any
    let custom_inputs = vec![Scalar::zero().to_bytes(); num_inputs];
    let custom_assignment_inputs = InputsAssignment::new(&custom_inputs).unwrap();

    // verify the proof of satisfiability
    let mut verifier_transcript = Transcript::new(b"snark_example");
    assert!(proof
        .verify(&comm, &custom_assignment_inputs, &mut verifier_transcript, &gens)
        .is_ok());

    println!("proof verification successful!");
}