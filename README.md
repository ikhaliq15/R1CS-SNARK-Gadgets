# R1CS Gadgets

This repository contains R1CS gadgest I have built using (a slightly modified version of) [Spartan](https://github.com/microsoft/Spartan).

Currently, the two gadgets included are: 

1. a range proof (prove `x` in the interval `[A, B]`)
2. a set membership proof (`x` is in `S`, where `S` is an arbitrary set of field elements).


The repository also contains a framework to easily add more gadgets, as well as an easy method for witness creation.
