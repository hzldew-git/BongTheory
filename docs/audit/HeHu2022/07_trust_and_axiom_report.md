# Trust and axiom report

`BongTest.HeHu2022Audit` prints the transitive axioms of every public paper
endpoint, including Corollary 4.6, Theorem 4.7, Theorems 1.1--1.2, the
finite-table cardinality theorems, and literal proper-subset minimality.

The observed dependencies are only Lean's expected foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`. No project-specific `axiom`,
`sorry`, or `opaque` declaration occurs in the scoped source closure.

Deep inputs that were formerly exposed as interfaces—notably diagonal local
classification, the codimension-two representation theorem, and maximal
lattice uniqueness—are discharged by proved repository modules before the
paper endpoints are assembled. The audit therefore does not treat a
paper-specific assumption as a proof of the same paper assertion.

Independent human semantic review remains outside the Lean trust report and
is not self-certified here.
