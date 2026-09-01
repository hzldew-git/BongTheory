# Adversarial review

## Challenges discharged

1. **False completion through a proposition-valued obligation.**
   `universalTheorem21CaseAnalysis_proved` inhabits the obligation and the
   final iff theorem is checked directly.
2. **Out-of-range BONG entries.**  Rank two, rank three, and higher ranks are
   split before every use of `R_3`, `R_4`, or `alpha_3`.
3. **Floor convention.**  Every half-gap uses integer floor division by the
   positive integer two.
4. **Conflated predicates.**  lattice universality, ambient line-universality,
   isotropy, maximality, and Witt index remain distinct.
5. **Theorem 3.1 copied rather than derived.**  The proof chooses and aligns a
   good BONG, proves the geometric prefix transport, translates every branch,
   and eliminates the witnesses.
6. **Dependence on a specially adapted Jordan decomposition.**  Approximation
   and codimension-one cancellation identify the relevant prefixes for the
   actual prescribed decomposition.
7. **Rank-one universal space overlooked.**  A square-class determinant
   argument proves that lattice universality forces ambient rank at least two.
8. **Printed exponent silently repaired.**  Literal and directly derived
   Theorem 3.1 predicates are separate; their unconditional equality is not
   asserted.
9. **Section 4 represented by definitions only.**  Each numbered lemma and
   corollary has a theorem endpoint, and Lemma 4.9 carries the residual
   invariant and prefix-space data used by Corollary 4.10.
10. **Boundary tail omitted.**  Corollary 4.10 includes `tail=0`, exactly the
    paper's `m=n+1` case.

## Remaining review targets

- Obtain author or independent domain confirmation of the coefficient in
  Theorem 3.1(3.2.1--2).
- Compare the distributed packaging of Lemma 2.8/Corollary 2.9 and Lemma 2.11
  with the paper line by line.
- Independently check the universe-polymorphic quantifiers in Lemmas 4.1--4.5
  and the exact-Witt-index convention in Corollary 4.10.
- Run a clean-clone build after the overlay is committed or tagged.
- Obtain independent domain and Lean signatures on the review cards.
