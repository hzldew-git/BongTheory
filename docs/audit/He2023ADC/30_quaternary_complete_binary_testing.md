# Complete binary testing for the quaternary boundary candidate

Date: 2026-09-05. Frozen code:
`0aa3848ca5aae079c2944174e687af8c068b9573`. This report covers
`He2023ADCQuaternaryBoundaryNormalization` and
`He2023ADCQuaternaryBoundaryTesting`, their canonical entry imports, and eight
new audit queries. The later explicit proposition naming the published claim is
excluded.

## Exact claim and independent verdict

The actual integral quaternary candidate represents every ambiently relevant
maximal binary lattice and is therefore 2-ADC. The same lattice is not maximal.
Independent source-first and code-second audit found no semantic or trust
blocker in this argument.

The supporting representation theorems are `NO_PAPER_COUNTERPART`. Their
combined consequence is evidence of a `SEMANTIC_MISMATCH` with the `n=2` case
printed in Lemma 6.8(iv). This report does not propose a corrected Theorem 6.2.

## Exhaustion of binary tests

Proposition 3.5(ii) supplies one of the actual two-column maximal models for
every rank-two maximal target. The first column is partitioned into square,
discriminant-square, and nonexceptional classes. In the second column the
square class is excluded by the rank-two definedness predicate; the
discriminant-square and nonexceptional classes remain.

The square first-column test is transported from `N_1^2(1)`. The
discriminant-square first-column target is ambiently impossible because the
candidate's space is the unique completion missing that class. The second
discriminant target is transported from `N_2^2(Delta)`. All nonexceptional
targets use the finite-defect argument after square normalization.

The normalizing square may have negative valuation. The proof first obtains a
quadratic-space isometry and then uses uniqueness of maximal lattices to obtain
an integral isometry. It never assumes that coordinate scaling preserves the
integral lattice.

## Source comparison

The publisher version states Lemma 6.8(iv) for every even `n >= 2`, including
`n=2`. Its proof on pp. 1002--1003 invokes Lemma 6.7(ii), whose own statement
requires `n >= 4` and the unavailable binary square second-column test. The
formal candidate satisfies the printed dyadic, rank, integrality, good-BONG,
2-ADC, and ambient `W_2^4(Delta)` hypotheses but is not the asserted maximal
lattice.

## Trust, universes, and nonvacuity

The two new modules and canonical entry passed local replay. The complete ADC
audit had 203 reports at this checkpoint, and all eight new declarations used
only `propext`, `Classical.choice`, and `Quot.sound`. The focused gate checked
57,753 declarations. An independent traversal visited 80,790 constants and
found no dependency on Lemma 6.8 or Theorem 6.2.

The exported ADC statement is `IsNADC.{u,u,u}`: field, source carrier, and
target carrier share one universe. Every finite-dimensional target has a
coordinate model in that universe, but an arbitrary-universe strengthening is
not separately exported. A concrete `Q_2` probe verifies that the hypotheses
are inhabited.

The checks used existing dependency artifacts. Reproducibility status remains
`PARTIALLY_REPRODUCIBLE` until an exact-revision clean kit and CI run pass.
