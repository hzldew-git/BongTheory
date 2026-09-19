# Theorem 1.9 strong-approximation derivation

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`7c615fcb35e2d8e85d9ab5883019c1505d27f132` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and locator

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Theorem 1.9 is stated at line 235.  Its proof is at lines 1697--1700.  In the
sufficiency direction, the paper fixes a positive definite classic integral
target, checks representation at every archimedean, non-dyadic, and dyadic
place, and invokes strong approximation because the number field is not
totally real.

## Formal change

The former `SectionEightLaws.sumOfSquares_local_to_global` field stored the
whole conclusion that finite-place local universality implies global
universality.  It is replaced by `SumOfSquaresLocalGlobalLaws`, whose inputs
are:

1. global integrality of the sum-of-squares lattice;
2. preservation of rank under localization;
3. localization of integrality; and
4. a strong-approximation representation law after finite-place
   representations and real-place admissibility have been supplied.

`SumOfSquaresLocalGlobalLaws.sumOfSquares_local_to_global` now proves global
`n`-universality.  For an arbitrary globally integral admissible rank-`n`
target, it localizes the target, uses local `n`-universality at each finite
place, and applies the strong-approximation law.  A compatibility theorem in
`SectionEightLaws` delegates to this derivation, so the existing Theorem 1.9
proof consumes no final-conclusion field.

This is a strict trust-boundary reduction.  The concrete strong-approximation
instance and number-field localization operations are still explicit
implementation obligations.

## Mechanical evidence

With Lean 4.32.1, the focused module
`BongTest.He2022ClassicStrongApproximationAudit` completes a 5,000-job build
and runs directly.  The lower derivation and its compatibility endpoint have
empty axiom sets; the full conditional Theorem 1.9 endpoint reports only
`propext`.

The canonical paper and audit modules complete a 5,018-job incremental build.
The focused imported-closure gate reports
`AXIOM_GATE_PASS: 62668 declarations checked`.  All 30 policy tests pass, and
the comment-aware scanner checks 2,792 tracked Lean sources without finding a
forbidden proof token.  These checks reuse local artifacts; exact clean-kit
verification remains a separate gate.

## Fidelity boundary

The derivation formalizes the quantifier flow in the published sufficiency
argument but does not implement strong approximation, archimedean signatures,
or concrete completions of number-field lattices.  Theorem 1.9 therefore
remains conditional.  The whole-paper Grade D and the separate v5
Corollary 6.3/Lemma 8.3 parity defect are unchanged.
