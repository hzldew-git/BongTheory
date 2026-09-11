# Actual finite and exceptional binary boundary tests

Date: 2026-09-05. Frozen code:
`442b2d3e0d6592263aa25e22a0a832d2b6a76e31`. This report covers
`He2023ADCQuaternaryBoundaryTests` and
`He2023ADCQuaternaryBoundaryEndpoint`, their canonical entry imports, and
eleven new audit queries. Later normalization and complete testing are excluded.

## Exact scope and verdict

The actual candidate's split head, third coefficient, and full signed defect
are proved rather than supplied. The finite criterion applies for
`0 <= d < 2e`. A separate endpoint proof treats `d = 2e`. It yields actual
integral representations of the named maximal lattices `N_2^2(Delta)` and
`N_1^2(1)` whenever appropriate.

The new declarations are `NO_PAPER_COUNTERPART` supporting results. Independent
AI review detected no semantic discrepancy within this scope. They do not yet
assert 2-ADC, exhaust the maximal binary catalogue, or refute a paper result.

## Mathematical checks

The head is `[1,-pi^(-2e)]`, the third coefficient is literally `pi`, and the
full raw defect is `2e`. The endpoint target has orders `(1,1-2e)` and signed
raw defect `2e`. The first central trigger would require `1 < 1`; the second
uses an explicit ternary-prefix field representation. All four conditions of
the published Theorem 3.6 are then applied before any integral representation
is concluded.

The named-target transports have the required direction. Maximal-lattice
uniqueness supplies actual integral isometries. The square endpoint comes from
the literal half-hyperbolic integral summand with Gram matrix
`[[0,1/2],[1/2,0]]`; it is not confused with the finite discriminant endpoint.

## Trust and reproducibility

Both frozen modules, the canonical entry, and the full ADC audit replayed
successfully. There were 189 axiom reports. Each of the eleven new declarations
uses exactly `propext`, `Classical.choice`, and `Quot.sound`. The focused gate
checked 57,737 declarations. A separate dependency-body traversal visited
80,643 constants and found no dependency on Lemma 6.8 or `IsNADC`.

These were cached local checks. They are not a clean build or CI certificate.
Reproducibility status for this frozen increment: `PARTIALLY_REPRODUCIBLE`.
