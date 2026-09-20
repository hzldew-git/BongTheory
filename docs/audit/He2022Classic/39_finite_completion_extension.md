# Finite-completion extension checkpoint

Status: `PROVED_COMPLETION_EMBEDDING_INFRASTRUCTURE` /
`PARTIAL_LEMMA_8_1`.

Code checkpoint:
`82a2b047f168e6de7a8d0a869bec38ead1f01a8d` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and exact scope

The sole semantic authority remains the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Lemma 8.1 is stated for a finite extension of completed local fields. Report
38 proved the order-scaling formula only for a coefficient in the dense
number-field subfield. This checkpoint constructs the missing field-extension
carrier between the corresponding completions. It does not yet extend the
order formula to an arbitrary nonzero completed-field element.

## Proved completion structure

For a finite extension of number fields `L / K` and height-one primes `P | p`,
the module now constructs

`completionMap : K_p ->+* L_P`.

The definition is the map of uniform completions induced by `K -> L`,
transported through mathlib's finite-place completion equivalences. The
following facts are checked in Lean:

- `completionMap_coe`: the map agrees with `K -> L` on every element of the
  dense number-field subfield;
- `continuous_completionMap`: the completed embedding is continuous;
- scoped `Algebra`, `IsScalarTower`, and `ContinuousSMul` instances for
  `K -> K_p -> L_P`; and
- inference of both `Module.Finite K_p L_P` and
  `FiniteDimensional K_p L_P` from mathlib's finite-completion theorem.

The instances are scoped under `CompletionLiesOver`. This avoids installing a
global instance that could form a diamond if mathlib later exports the same
canonical completion algebra.

## Mechanical evidence

The completion module and focused audit complete a 5,651-job build. The
canonical paper entry and combined Classic audit complete a 5,674-job build.
The audited map-compatibility and continuity theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. All 30 CI policy tests pass, and the
comment-aware scanner checks 2,800 tracked Lean sources without a forbidden
proof token outside comments. The focused imported-closure gate reports
`AXIOM_GATE_PASS: 62830 declarations checked`.

These are incremental checks at the stated code commit. They are not an exact
fresh-extraction Review Kit receipt and provide no GitHub deployment evidence.

## Remaining boundary

The completed embedding and finite-dimensional extension are structural
prerequisites, not the remaining arithmetic conclusions. In particular, this
checkpoint does not prove:

- valuation-order scaling for every element of `K_p^x`;
- a concrete quadratic-defect definition and the defect inequality of Lemma
  8.1(ii);
- scalar extension of an integral lattice, its orthogonal basis, or its good
  BONG in Lemma 8.1(iii); or
- any of the remaining concrete global lattice, localization,
  sum-of-squares, representation-transport, or strong-approximation inputs.

The false unrestricted odd Corollary 6.3 remains unchanged in authoritative
v5. The whole-paper grade remains D, the completion verdict remains
`NOT_COMPLETE`, and GitHub deployment remains disabled.
