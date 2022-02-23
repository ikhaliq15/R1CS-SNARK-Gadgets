extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;

use std::cmp::{max, min};
use std::collections::HashMap;
use curve25519_dalek::scalar::Scalar;
use libspartan::{Assignment, InputsAssignment, Instance, VarsAssignment};
use crate::bit_helpers::{get_bit, get_pow_2, sum_last_n_bits};

pub struct R1CS {
    constraint_count: usize,
    num_non_zero: usize,
    variables: HashMap<String, usize>,
    witness_assignments: HashMap<String, Scalar>,
    A: Vec<(usize, usize, [u8; 32])>,
    B: Vec<(usize, usize, [u8; 32])>,
    C: Vec<(usize, usize, [u8; 32])>
}

impl R1CS {
    pub fn new(inputs: &Vec<(&str, Scalar)>) -> R1CS {
        let mut r1cs = R1CS {
            constraint_count: 0,
            num_non_zero: 0,
            variables: HashMap::new(),
            witness_assignments: HashMap::new(),
            A: Vec::new(),
            B: Vec::new(),
            C: Vec::new()
        };

        r1cs.add_witness_var_assignment("one", Scalar::one());

        /* verify inputs are equal to publicly agreed value */
        for (input, value) in inputs {
            r1cs.new_equality_scalar_constraint(input, *value);
            r1cs.add_witness_var_assignment(input, *value);
        }

        r1cs
    }

    /*  Should only be called once, after the entire R1CS has been built.
        Expect undefined behavior if called multiple times. */
    pub fn build_instance(&mut self) -> (Instance, usize, usize, usize, usize) {
        /* add final constraints, including that the "one" variable equals 1  */
        let one_ind = self.get_var_index("one");
        self.A.push((self.constraint_count, self.variables.len(), Scalar::one().to_bytes()));
        self.B.push((self.constraint_count, self.variables.len(), Scalar::one().to_bytes()));
        self.C.push((self.constraint_count, one_ind, Scalar::one().to_bytes()));
        self.num_non_zero += 1;
        self.constraint_count += 1;

        // TODO: add input constraints so that input variables equal

        let num_vars = self.variables.len();
        let num_inputs = 0;
        let num_non_zero_entries = min(self.num_non_zero, num_vars.next_power_of_two() + 1);
        let inst = Instance::new(self.constraint_count, num_vars, num_inputs, &self.A, &self.B, &self.C).unwrap();
        (inst, self.constraint_count, num_vars, num_inputs, num_non_zero_entries)
    }

    /*  Should only be called once, after the entire R1CS has been built.
        Expect undefined behavior if called multiple times. */
    pub fn build_witness(&mut self) -> (Assignment, Assignment) {
        assert_eq!(self.witness_assignments.len(), self.variables.len());
        let mut variables = vec![Scalar::zero().to_bytes(); self.witness_assignments.len()];
        for (var, value) in self.witness_assignments.iter() {
            assert!(self.variables.contains_key(var));
            let var_ind: usize = *self.variables.get(var).unwrap();
            variables[var_ind] = (*value).to_bytes();
        }
        let assignment_vars = VarsAssignment::new(&variables).unwrap();
        let assignment_inputs = InputsAssignment::new(&vec![Scalar::zero().to_bytes(); 0]).unwrap();
        (assignment_vars, assignment_inputs)
    }

    /* Return the next available index in the witness vector for a new variable. */
    fn get_new_var_index(&self) -> usize {
        self.variables.len()
    }

    /* Get the position in the final witness vector that VAR will hold. */
    pub fn get_var_index(&mut self, var: &str) -> usize {
        if !self.variables.contains_key(var) {
            self.variables.insert(var.to_string(), self.get_new_var_index());
        }
        *self.variables.get(var).unwrap()
    }

    /* Set the witness assignment of VAR to VALUE. */
    pub fn add_witness_var_assignment(&mut self, var: &str, value: Scalar) {
        assert!(!self.witness_assignments.contains_key(var));
        self.witness_assignments.insert(var.to_string(), value);
    }

    /*  Add constraint that the the product of X and Y must equal Z.
    That is X * Y == Z. X, Y, and Z are variables. */
    pub fn new_mult_constraint(&mut self, x: &str, y: &str, z: &str) {
        let x_ind = self.get_var_index(x);
        let y_ind = self.get_var_index(y);
        let z_ind = self.get_var_index(z);
        self.A.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.B.push((self.constraint_count, y_ind, Scalar::one().to_bytes()));
        self.C.push((self.constraint_count, z_ind, Scalar::one().to_bytes()));
        self.num_non_zero += 1;
        self.constraint_count += 1;
    }

    pub fn generate_witness_mult(&mut self, x: Scalar, y: Scalar, z: &str) {
        self.add_witness_var_assignment(z, x * y);
    }

    /*  Add constraint that the the product of X and Y must equal Z.
    That is X * Y == Z. X, Z are variables. Y is a scalar. */
    pub fn new_mult_scalar_constraint(&mut self, x: &str, y: Scalar, z: &str) {
        let x_ind = self.get_var_index(x);
        let z_ind = self.get_var_index(z);
        let one_ind = self.get_var_index("one");
        self.A.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.B.push((self.constraint_count, one_ind, y.to_bytes()));
        self.C.push((self.constraint_count, z_ind, Scalar::one().to_bytes()));
        self.num_non_zero += 1;
        self.constraint_count += 1;
    }

    pub fn generate_witness_mult_scalar(&mut self, x: Scalar, y: Scalar, z: &str) {
        self.add_witness_var_assignment(z, x * y);
    }

    /*  Add constraint that the the sum of X and Y must equal Z.
    That is X + Y == Z. X, Y, and Z are variables. */
    pub fn new_addition_constraint(&mut self, x: &str, y: &str, z: &str) {
        let x_ind = self.get_var_index(x);
        let y_ind = self.get_var_index(y);
        let z_ind = self.get_var_index(z);
        let one_ind = self.get_var_index("one");
        self.A.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.A.push((self.constraint_count, y_ind, Scalar::one().to_bytes()));
        self.B.push((self.constraint_count, one_ind, Scalar::one().to_bytes()));
        self.C.push((self.constraint_count, z_ind, Scalar::one().to_bytes()));
        self.num_non_zero += 2;
        self.constraint_count += 1;
    }

    pub fn generate_witness_addition(&mut self, x: Scalar, y: Scalar, z: &str) {
        self.add_witness_var_assignment(z, x + y);
    }

    /*  Add constraint that the the difference of X and Y must equal Z.
    That is X - Y == Z. X, Y, and Z are variables. */
    pub fn new_subtraction_constraint(&mut self, x: &str, y: &str, z: &str) {
        let x_ind = self.get_var_index(x);
        let y_ind = self.get_var_index(y);
        let z_ind = self.get_var_index(z);
        let one_ind = self.get_var_index("one");
        self.A.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.A.push((self.constraint_count, y_ind, (-Scalar::one()).to_bytes()));
        self.B.push((self.constraint_count, one_ind, Scalar::one().to_bytes()));
        self.C.push((self.constraint_count, z_ind, Scalar::one().to_bytes()));
        self.num_non_zero += 2;
        self.constraint_count += 1;
    }

    pub fn generate_witness_addition_scalar(&mut self, x: Scalar, y: Scalar, z: &str) {
        self.add_witness_var_assignment(z, x + y);
    }

    pub fn new_is_bit_constraint(&mut self, x: &str) {
        let x_ind = self.get_var_index(x);
        let one_ind = self.get_var_index("one");
        self.A.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.B.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.B.push((self.constraint_count, one_ind, (-Scalar::one()).to_bytes()));
        self.num_non_zero += 2;
        self.constraint_count += 1;
    }

    pub fn new_equality_constraint(&mut self, x: &str, y: &str) {
        let x_ind = self.get_var_index(x);
        let y_ind = self.get_var_index(y);
        let one_ind = self.get_var_index("one");
        self.A.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.B.push((self.constraint_count, one_ind, Scalar::one().to_bytes()));
        self.C.push((self.constraint_count, y_ind, Scalar::one().to_bytes()));
        self.num_non_zero += 1;
        self.constraint_count += 1;
    }

    pub fn new_equality_scalar_constraint(&mut self, x: &str, y: Scalar) {
        let x_ind = self.get_var_index(x);
        let one_ind = self.get_var_index("one");
        self.A.push((self.constraint_count, one_ind, y.to_bytes()));
        self.B.push((self.constraint_count, one_ind, Scalar::one().to_bytes()));
        self.C.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.num_non_zero += 1;
        self.constraint_count += 1;
    }

    /* creates N new variables of the form X_biti for i in [0, N). Each X_biti is constrained
       to be a bit. For all i, X_biti is constrained to be the i-th bit of X when X is a
       twos complement N bit number.*/
    pub fn new_twos_complement_decomposition_constraint(&mut self, x: &str, N: usize) {
        let x_ind = self.get_var_index(x);
        let one_ind = self.get_var_index("one");

        for i in 0..N {
            self.new_is_bit_constraint(&*format!("{:}_bit{:}", x, i));
        }

        for i in 0..N {
            let y_bit_i = self.get_var_index(&*format!("{:}_bit{:}", x, i));
            if i == N - 1 {
                self.A.push((self.constraint_count, y_bit_i, (-get_pow_2(i)).to_bytes()))
            } else {
                self.A.push((self.constraint_count, y_bit_i, get_pow_2(i).to_bytes()))
            }
        }

        self.B.push((self.constraint_count, one_ind, Scalar::one().to_bytes()));
        self.C.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));

        self.num_non_zero += max(N, 1);
        self.constraint_count += 1;
    }

    pub fn generate_witness_twos_complement_decomposition(&mut self, var: &str, value: Scalar, N: usize) {
        let zero = Scalar::zero();
        let one = Scalar::one();

        let var_is_neg: bool = sum_last_n_bits(value.to_bytes(), 8) != 0;
        let var_bits = if var_is_neg { (-value).to_bytes() } else { value.to_bytes() };

        let mut carry: u8 = 1;
        for i in 0..N {
            // determine what the i-th bit of val is in two's complement representation
            let mut u_bit = get_bit(var_bits, i);
            if var_is_neg {
                u_bit = (1 - u_bit) + carry;
                carry = if u_bit > 1 { 1 } else { 0 };
                u_bit = u_bit & 1;
            }
            let b = if u_bit == 1 { one } else { zero };

            self.add_witness_var_assignment(&*format!("{:}_bit{:}", var, i), b);
        }
    }

    /* Add constraints to verify X \in [A, B] where X, A, and B are 100 bit numbers. */
    pub fn new_range_constraint(&mut self, a: &str, b: &str, x: &str) {
        let helper_var: &str = &*format!("{}_{}_{}_range_helper", x, a, b);

        /* constraint so that y = (a - x) * (x - b) */
        let a_ind = self.get_var_index(a);
        let b_ind = self.get_var_index(b);
        let x_ind = self.get_var_index(x);
        let y_ind = self.get_var_index(helper_var);
        self.A.push((self.constraint_count, a_ind, Scalar::one().to_bytes()));
        self.A.push((self.constraint_count, x_ind, (-Scalar::one()).to_bytes()));
        self.B.push((self.constraint_count, x_ind, Scalar::one().to_bytes()));
        self.B.push((self.constraint_count, b_ind, (-Scalar::one()).to_bytes()));
        self.C.push((self.constraint_count, y_ind, Scalar::one().to_bytes()));
        self.num_non_zero += 2;
        self.constraint_count += 1;

        /*  verify that each y_i is a bit (\forall i, y_i \in \{0, 1\})
            also verify that -2^{n-1} * y_{n-1} + \sum_{i=0}^{n-2} 2^i * y_i = y
            essentially, verify that the bits y_i form two's complement of y */
        self.new_twos_complement_decomposition_constraint(helper_var, 202);

        // verify y > 0 (if y_i form two's complement of y, then just check MSB == 0)
        self.new_equality_scalar_constraint(&*format!("{}_bit{}", helper_var, 201), Scalar::zero());
    }

    pub fn generate_witness_range(&mut self, a: &str, b: &str, x: &str, a_val: Scalar, b_val: Scalar, x_val: Scalar) {
        let helper_var: &str = &*format!("{}_{}_{}_range_helper", x, a, b);
        let helper_var_val: Scalar = (a_val - x_val) * (x_val - b_val);
        self.add_witness_var_assignment(&*helper_var, helper_var_val);
        self.generate_witness_twos_complement_decomposition(helper_var, helper_var_val, 202);
    }
}