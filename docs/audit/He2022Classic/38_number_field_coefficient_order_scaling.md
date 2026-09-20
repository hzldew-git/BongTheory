# Number-field coefficient order scaling

Status: `PROVED_GLOBAL_COEFFICIENT_SPECIALIZATION` /
`PARTIAL_LEMMA_8_1`.

Code checkpoint:
`6d5c434a76afc46bed1904516d33c9c8fd6f811b` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and exact scope

The sole semantic authority remains the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Lemma 8.1(i) is stated for every element of a completed local field
`K_p` inside a finite extension `E_P / K_p`. This checkpoint proves the
specialization needed for a nonzero coefficient already lying in the
underlying number field `K`. It does not silently identify that specialization
with the full completed-field statement.

## Proved arithmetic

For a finite extension of number fields `L / K`, height-one primes `P | p`,
and `x : Kˣ`, the new module defines the additive order by the negative
logarithm of mathlib's multiplicative adic valuation. It then proves:

- `adicOrder_liesOver`, namely
  `ord_P(x) = ord_p(x) * e(P / p)`;
- `relativeRamificationIndex_pos`, the positivity of `e(P / p)`; and
- `absoluteRamificationIndex_tower`, namely
  `e(P / 2) = e(p / 2) * e(P / p)`.

These are derived from the actual prime-ideal valuation and ramification API,
including `valuation_liesOver`,
`ramificationIdx'_eq_ramificationIdx`, and `ramificationIdx_tower`.
No paper-specific arithmetic law is introduced.

`RemainingCoefficientInputs.toLocalExtensionData` specializes the existing
Section 8 interface to `Kˣ`. Its `lemma81Laws` theorem fills the order-scaling,
ramification-tower, and positivity fields from the proved arithmetic. The
caller supplies only quadratic-defect scaling and good-BONG transfer.

## Mechanical evidence

The new module and focused audit complete a 5,651-job build. The canonical
paper entry and combined Classic audit complete a 5,674-job build. All five
audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
All 30 CI policy tests pass, and the comment-aware scanner checks 2,800
tracked Lean sources without a forbidden proof token outside comments.
The focused imported-closure gate reports
`AXIOM_GATE_PASS: 62819 declarations checked`.

These are incremental checks at the stated code commit. An exact source-only
Review Kit for a later documentation commit remains a separate gate.

## Remaining boundary

The following parts of Lemma 8.1 are not proved by this checkpoint:

- extension of the order identity from `Kˣ` to every nonzero element of the
  completion `K_p`;
- a concrete quadratic-defect definition on both completions and the
  inequality in Lemma 8.1(ii); and
- scalar extension of the lattice, its orthogonal basis, and its good BONG in
  Lemma 8.1(iii).

Those obligations remain visible, together with the false unrestricted odd
Corollary 6.3 and the other concrete global instances. The whole-paper grade
remains D and the completion verdict remains `NOT_COMPLETE`.
