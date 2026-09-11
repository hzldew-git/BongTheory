# Formal record of the Lemma 6.8(iv) binary discrepancy

Date: 2026-09-05. Frozen code:
`fe2a459a4152ade94299a61d1c4958fefa646ba0`. Publisher source: Doc. Math.
30 (2025), 981--1022, DOI 10.4171/DM/1003, PDF SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

## Formal result

`HeADC2025Lemma68ivBinaryStatement` records the exact public `n=2` implication:
every 2-ADC rank-four lattice with ambient space `W_2^4(Delta)` is integrally
isometric to `N_2^4(Delta)`. The theorem
`not_heADC2025Lemma68ivBinaryStatement` proves its negation. A separate theorem
shows directly that the actual candidate is not integrally isometric to the
asserted maximal target.

`BongTest.He2023ADCQuaternaryBoundaryQ2` instantiates the argument over
`Q_2`. It checks the actual 2-ADC property, nonmaximality, and negation of the
published binary implication. This rules out vacuity of the abstract dyadic
context.

## Status

Lemma 6.8(iv) is `SEMANTIC_MISMATCH` at `n=2`. The existing theorem
`heADC2025Lemma68iv_of_pos` remains a `PROVISIONAL_MATCH` for `n >= 4`.
The formal refutation is a `NO_PAPER_COUNTERPART` result because the publisher
paper asserts the opposite implication.

This finding invalidates the printed proof route to Theorem 6.2. It does not by
itself decide whether a corrected version of Theorem 6.2 is true, nor identify
a complete replacement list of exceptional lattices.

## Trust and reproducibility

The discrepancy module, canonical paper entry, and concrete `Q_2` module pass
Lean 4.32.1. The full ADC audit contains 205 axiom reports at this checkpoint.
Both discrepancy theorems and the concrete field context use only `propext`,
`Classical.choice`, and `Quot.sound`. The focused enforcing gate checks 57,757
declarations. No proof imports or invokes Lemma 6.8 or Theorem 6.2.

These are cached local checks. Exact-revision clean-kit compilation and GitHub
CI remain required. The theorem-level source verdict is evidence-backed, while
paper-author and independent human expert confirmation remain unsigned.
