# Executive summary

- The frozen source is arXiv:2008.10113v2, identified by SHA-256.
- The exact lattice-integrality, universality, scalar-representation,
  maximality, and Witt-index predicates are formalized.
- Lemmas 2.2--2.14, Corollary 2.9, and Theorem 2.1 have checked proof paths.
- Theorem 3.1 is derived for an arbitrary prescribed Jordan decomposition;
  the good BONG and alignment profile are internal witnesses.
- Lemmas 4.1--4.9, all four clauses of Corollary 4.5, and Corollary 4.10 have
  public theorem endpoints.
- Focused axiom reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- No public endpoint accepts a project-specific law, data, or proof-obligation
  parameter.

One source-level issue remains explicit.  In Theorem 3.1(3.2.1--2), the paper
prints coefficient `r_1`, while direct substitution of
`R_2=2r_1-u_1` and `u_1=0` into Theorem 2.1 gives `2r_1`.  Lean proves
the direct criterion unconditionally and the literal printed criterion under
`r_1=0`; it does not assume a general equivalence.

Current status:
**`FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY`** and
**`PROVISIONAL_MATCH`** pending independent mathematical and Lean review.
