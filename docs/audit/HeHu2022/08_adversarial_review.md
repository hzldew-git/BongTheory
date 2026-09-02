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
higher-order contradiction. The checked assembly theorem must not be mistaken
for the still-open Lemma 4.5.

For Proposition 3.7, independently inspect the even index-two volume drop,
the `0,-2e`, `0,-2e,0`, and `0,-2e,0,-2e` equality profiles, and the direction
of every same-rank diagonal representation used in the three endpoint
contradictions. Also confirm that the distinguished discriminant class is the
canonical proved instance throughout the Table 1/Table 2 comparison.
