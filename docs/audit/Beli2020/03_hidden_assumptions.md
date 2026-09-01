# Hidden assumptions and elaboration report

1. `DyadicContext K` packages a normalized nondiscrete interface for the
   dyadic local field, a uniformizer, and positivity of `ord(2)`.  It does
   not contain a Beli theorem, a Jordan classification conclusion, or a
   universality oracle.
2. `QuadraticSpace K V` is nondegenerate by construction.
   `Lattice K V` is full and finitely generated; its stored ambient basis
   supplies finite dimensionality when a proof needs diagonalization.
3. Good-BONG existence and the BONG/Jordan dictionary are proved in the
   earlier formalization.  Theorem 3.1 chooses a good BONG internally; neither
   it nor an alignment profile is a public hypothesis.
4. Theorem 2.1 uses length `tail+2`, so rank at least two is encoded in the
   type.  The arbitrary-Jordan theorem instead includes the paper's rank
   inequality explicitly and proves that universality itself forces it.
5. Every later Jordan component and every `R_3`, `R_4`, `alpha_3`,
   `f_2`, or `f_3` access has a `Fin` witness.  The paper's convention
   to ignore out-of-range clauses is represented by typed branch guards.
6. `IsUniversal` is exactly `Q(L)=O`.  Ambient line-universality, lattice
   integrality, isotropy, and `n`-universality remain separate predicates.
7. The Section 4 quantification over target carrier types is universe
   polymorphic where the paper quantifies over all lattices.  Rank,
   integrality, maximality, and Witt-index hypotheses are explicit.
8. Classical choice is used for bases, good BONGs, maximal superlattices, and
   square-class representatives.  Its use appears in the kernel axiom report.
9. The printed/direct Theorem 3.1 discrepancy is not hidden as an assumption.
   The unconditional endpoint uses the directly derived exponent; the literal
   printed endpoint requires the separately displayed first-scale-order-zero
   hypothesis.
10. No public endpoint in this paper formalization accepts a project-specific
    `...Laws`, `...Data`, or proof-obligation parameter.
