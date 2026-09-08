# Non-dyadic table low-rank boundary refinement

## Status

Checkpoint: `ef4fcf4`.

Classification: `CONCRETE_FINITE_DATA_CERTIFICATE` for the published table
domain, with the arithmetic realization and classification boundary from
Report 61 unchanged.

## Source boundary corrected

The two-column display in Lemma 4.7(i), p. 993 of the publisher version,
does not define a second-column lattice in rank one. It also omits
`N_2^2(1)` in rank two. The common catalogue predicate now records both
exceptions literally:

```text
(m != 1 or nu != 2) and (m != 2 or nu != 2 or c != 1).
```

This repairs an internal interface mismatch at the Report 61 checkpoint:
the parity-specific odd predicate already excluded every second-column unary
row, whereas the common predicate encoded only the binary exception. No
published theorem conclusion was weakened or strengthened by the repair.

## Kernel-checked consequences

Lean now proves:

- the common predicate agrees with the odd-table predicate for every
  positive odd rank, including rank one;
- exactly the four first-column square-class rows are defined in rank one;
- exactly seven of the eight column/square-class pairs are defined in rank
  two;
- multiplication of the four symbolic square classes by `Delta` is an
  involution; and
- every general row used by the conditional non-dyadic Theorem 1.10
  catalogue is defined in ranks at least three under the refined predicate.

The canonical He ADC entry and complete audit rebuild successfully. The
relevant build completes all 5,556 jobs with Lean 4.32.1. The focused
endpoints use only the permitted foundational axioms, with the involution
theorem requiring none.

The independent Mathematica check reports:

```text
<|evenRows -> True, oddRows -> True, jordanZeroOne -> True,
  uniformizerJ0Ranks -> True, firstUnitJ0Ranks -> True,
  deltaTwistInvolution -> True, unarySecondColumnOmitted -> True,
  unaryDefinedCount -> True, binaryUndefinedRow -> True,
  binaryDefinedCount -> True|>
```

The comment-aware scanner checks 2,772 tracked Lean sources. All 27 CI
policy and scanner tests pass, every changed Lean line is at most 100
columns, and `git diff --check` passes.

## Unchanged trust boundary

This refinement certifies the finite indexing boundary and symbolic table
arithmetic only. It does not realize the displayed expressions as integral
lattices over arbitrary non-dyadic local fields, prove maximality,
classification, exhaustion, irredundancy, Lemma 4.7(ii), the representation
equivalence in Lemma 4.8, or instantiate `SectionFiveLaws` and
`CatalogueLaws`. Those remain explicit external mathematical obligations.

The exact Review Kit being verified for checkpoint `8ead7f4` contains the
Table 1 certificate through Report 59 and predates both Reports 61--62. It
must not be cited as clean-build evidence for this refinement. A later exact
source kit remains required.
