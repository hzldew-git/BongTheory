# Adversarial review

Highest-risk checks are: one-based/zero-based endpoint conversion; parity ranges;
the exceptional `m=n+2=4` branch; coercions from integral orders into
`WithTop ℚ`; and the distinction between ambient-space universality and lattice
universality. A reviewer should also test `n=2`, minimal stable rank `m=n+3`,
and empty `Fin (m-1)` edge cases.

For the Section 4 conversion, separately verify that paper
`alpha_(n+1)` is Lean index `n`, that both neighboring alpha caps become
`2e` in the exceptional equality case, and that the raw defect is used only
when `R_(n+3)-R_(n+2)=2e` and `R_(n+2)=2-2e`. For the now-checked Lemma 4.2,
independently verify the even-rank reparameterization, the final odd-index
order, and the nonsquare product of the `1` and `Delta` test determinants.
For Lemma 4.4, separately inspect the terminal-index cast, the split between
last target order `-2e` and at least `1-2e`, and the use of `I2^E` only in the
higher-order contradiction. The direct Theorem 4.1 endpoint now depends on
the separately checked Lemmas 4.2, 4.4, and 4.5.

For Lemma 5.9, check both determinant square-class transports, the common
hyperbolic prefix in the case-III parity cycle, and the final quantifier. The
proved assertion excludes simultaneous representation and yields failure for
at least one test; it must not be read as proving that both tests separately
fail.

For Lemma 5.10, independently check that its condition (ii) uses one common
sharp witness for the two first-column tests and says "some" rather than
"every" exceptional ternary test.  In the reverse implication, inspect the
terminal-index conversion, the use of Lemma 2.11 in equation (5.5), and both
branches of the parity definition of `G_n`.  The `alpha_n=0` normal-form
composition must point from the target `W_1^n(epsilon)` into the source
`W_1^(n+1)(1 or Delta)` in the direction stated by Lemma 3.14(ii).

For Lemma 5.11, check both valuation-parity constructions of the second test,
the conversion from `ord(c)` to `R_(n+2)-R_(n+1)`, and the determinant sign in
the codimension-two Lemma 3.13 application.  Also inspect that only the
terminal index is eliminated by `I3^O`; every earlier index must descend to
the rank-`n-1` prefix and Lemma 4.5.

For Proposition 3.7, independently inspect the even index-two volume drop,
the `0,-2e`, `0,-2e,0`, and `0,-2e,0,-2e` equality profiles, and the direction
of every same-rank diagonal representation used in the three endpoint
contradictions. Also confirm that the distinguished discriminant class is the
canonical proved instance throughout the Table 1/Table 2 comparison.
