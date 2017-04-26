# Integrating well-founded recursion and corecursion

This repository contains work-in-progress experiments in integrating
well-founded recursion and corecursion in Agda. Specifically, the code in
`Coinduction/WellFounded/Indexed.agda` implements a fixed-point combinator
(`cofixWf`) which allows recursive calls to *either* give the next observation
of the constructed coinductive data structure (as in ordinary corecursive
function definitions) *or* decrease a well-founded relation (as in well-founded
recursion).

The `examples` directory contains applications of `cofixWf` to various simple
problems.
