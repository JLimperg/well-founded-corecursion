# Integrating well-founded recursion and corecursion

This repository contains work-in-progress experiments in integrating
well-founded recursion and corecursion in Agda. Specifically, the code in
`M.agda` implements a fixed-point combinator (`fixM`) which allows recursive
calls to *either* give the next observation of the constructed coinductive data
structure (as in ordinary corecursive function definitions) *or* decrease a
well-founded relation (as in well-founded recursion). `Generic.agda` implements
a reflection-based variant where the user's coinductive data type needs not be
defined as an M-type but just needs to have a particular structure.

The `Graph/` directory contains a usage example with two implementations of the
same function: With `fixM` in `Graph/M.agda` and without in
`Graph/Direct.agda`. Definitions common to both are in `Graph/Base.agda`.
