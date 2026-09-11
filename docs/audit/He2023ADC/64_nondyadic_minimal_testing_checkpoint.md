# Non-dyadic Lemma 4.7(ii) minimal-testing checkpoint

## Status

Checkpoint: `5b2c411`.

Classification: `CONCRETE_FINITE_INDEX_CERTIFICATE` and
`CONDITIONAL_FORMALIZATION` of Lemma 4.7(ii).

## Authoritative source

The statement authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The publisher PDF has SHA-256

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 4.7(ii), on p. 993, states that the non-dyadic maximal-lattice family
is a minimal testing set for rank-`n` universality and cites the published
Proposition 3.2 of reference [16].

## Formal statement and finite family

`HeADC2025NonDyadicTestingIndex n` is the subtype of the eight
column/square-class pairs satisfying the exact common row-definedness
predicate. Thus invalid low-rank expressions are absent from the type rather
than represented by dummy rows. Lean proves its exact cardinalities:

- four rows in rank one;
- seven rows in rank two; and
- eight rows in every rank at least three.

The module defines rank-`n` universality, a universality-testing family, and
literal deletion-minimality directly in the abstract non-dyadic system. The
minimality conclusion quantifies over each displayed row and supplies an
integral witness which misses that row while representing every other row.

## Proved logical deduction

The sufficiency half is no longer an assumed family-level conclusion. Given
an arbitrary integral rank-`n` lattice, Lean:

1. embeds it in a maximal rank-`n` lattice;
2. classifies that maximal lattice by a defined Table 4.7 row;
3. transports representation across the supplied integral isometry; and
4. composes representations.

The deletion-minimality half then uses one explicit deletion witness per
defined row. The theorem `heADC2025Lemma47ii` combines these arguments and
has the publisher's hypothesis `1 <= n`. Neither the universality-testing
conclusion nor the minimal-testing conclusion is a field of a law package.

## Exposed mathematical inputs

The actual local-lattice content remains visible in two places:

- `CatalogueLaws` supplies the maximal-lattice classification; and
- `MinimalTestingLaws` supplies representation composition and transport,
  maximal overlattices, and the cited row-by-row deletion witnesses.

In particular, `deletion_witness` is not proved for concrete non-dyadic
local lattices at this checkpoint. Therefore this result must not be called
an unconditional proof of Lemma 4.7(ii).

## Mechanical evidence

The new module, canonical entry, and focused audit build with Lean 4.32.1.
The full canonical entry completes 5,557 jobs; the focused module/audit build
completes 3,001 jobs. The two logical endpoints depend on no axioms. The
three cardinality endpoints report only the permitted foundational axioms.
The comment-aware scanner checks 2,776 tracked Lean sources, all 27 CI policy
and scanner tests pass, changed Lean lines are at most 100 columns, and
`git diff --check` passes.

An exact clean Review Kit for this checkpoint, concrete instances of the
listed laws, and independent human semantic sign-off remain separate gates.
