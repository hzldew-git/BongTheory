# Lemma 7.14 determinant-parity classification

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint: `6c528031d27cc050a1f10c2ec953500f9b4c3c2c`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 7.14 and its proof occur on p. 1013. The post-publication arXiv
revision remains comparison-only.

## Formal statement

For odd `n=2k+3`, a rank-`n+2` good BONG has `2k+5` entries. The formal
endpoints retain both source ambient columns:

- `heADC2025Lemma714i` proves that an ambient parameter `delta` of valuation
  zero forces the last order to be zero;
- `heADC2025Lemma714ii` proves that the parameter
  `delta * uniformizerPowerUnit K 1` forces the last order to be one.

The unit `delta` remains universally quantified. These two rows are exactly
the paper's normalization `epsilon` and `epsilon*pi`.

## Determinant parity

`heADC2025Lemma714_fullOrderEven_iff` compares the source full prefix product
with the determinant of either ambient diagonal model. In the first column,
the product of these two determinants is a square. In the second column, the
published pair theorem first compares its determinant with the first column.
In both cases, square valuation has even order, so the source full determinant
has the same parity as the parameter.

This argument keeps the two ambient isometry alternatives separate. It does
not assert that the two ambient spaces are isometric.

## Initial prefix and last order

`heADC2025Lemma714_initialPrefixEven` expands the first `n+1` orders using
Theorem 7.4. Its alternating initial row consists of `0` and `-2e`, and its
penultimate entry is even; therefore the prefix sum is even. Subtracting this
from the full determinant order identifies the parity of the last order.

Theorem 7.4 restricts the last order to `0` or `1`. The even parameter row
therefore selects `0`, and the odd parameter row selects `1`. This is the
congruence argument printed immediately after equation (7.3).

## Statement-strength conclusion

The two public endpoints retain the source hypotheses: odd `n`, rank `n+2`,
`n`-ADC, either ambient column, and a valuation-unit parameter. All parity
facts and the last-order dichotomy are derived internally. The result is
therefore `LOGICALLY_EQUIVALENT` after the paper's own parameter
normalization.

## Mechanical trust checks

The Lemma 7.14 module, canonical paper entry, and focused audit compile
directly with Lean 4.32.1. The transitive axiom reports for both public
endpoints contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
The enforcing focused gate reports
`AXIOM_GATE_PASS: 59218 declarations checked`. The comment-aware scanner
checks 2,728 tracked Lean files and finds no forbidden proof token outside
comments. All changed Lean source lines satisfy the 100-column limit, and
`git diff --check` passes.

These are local checks at the stated code commit. Exact-revision Review Kit
CI, release promotion, and independent human sign-off remain separate gates.

## Coverage consequence

Section 7 now has eleven fully formalized numbered items: Theorems 7.1 and
7.4, Lemmas 7.5--7.12, and Lemma 7.14. Lemma 7.13 remains a documented source
quantifier mismatch. Theorem 7.2, Remark 7.3, Lemma 7.15, Definition 7.16,
Remark 7.17, Lemmas 7.18--7.20, and Corollary 7.21 remain pending.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
