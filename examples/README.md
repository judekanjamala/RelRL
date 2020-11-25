## Examples

This directory contains examples used to evaluate WhyRel.  It is expected that
more will be added soon.  To replay an example, it is sufficient to `cd`
to its directory and run:

```
make
make ide
```

Please consult the `Makefile` in each directory to learn about additional
options.  Replaying the examples may require the following SMT solvers to be
installed on your system: Alt-Ergo, Z3, CVC3, and CVC4.

Included examples are:

- **cell**: Equivalence of two modules implementing boxed integers in
  different ways.
- **swap-calls**: Minimal example of program equivalence: commuting two
  calls to two methods acting on different parts of the heap.
- **listpub**: Information flow case study.  Verifies that a program summing up
  public elements in a list with public and non-public elements does not leak
  information about non-public values.
- **SSSP**: Establishes equivalence of two priority queue modules with different
  internals.  Client program is Dijkstra's single source shortest paths algorithm.

Currently, a few VCs for the client in **SSSP** remain to be verified.  These
relate to WhyRel's encoding of field updates and can be discharged by adding
frame conditions to loop invariants.  To be addressed in the next revision of
WhyRel.
