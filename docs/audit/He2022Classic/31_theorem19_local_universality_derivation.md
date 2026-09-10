# Theorem 1.9 finite-place local-universality derivation

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`83aec42841ecb1b75b010ac15fddd72555939d36` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and locator

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Theorem 1.9 is stated at line 235 and proved at lines 1697--1700.  In the
sufficiency direction, line 1700 separates finite places into three cases:

1. a non-dyadic prime, handled by the cited non-dyadic universality results;
2. a dyadic prime with `n >= 2`, handled by Theorem 1.1; and
3. a dyadic prime with `n = 1`, where odd discriminant gives ramification
   index one and the alpha criterion invokes Beli's universal theorem.

## Formal change

The former `SectionEightLaws.sumOfSquares_localUniversal_of_oddDiscriminant`
field supplied the all-places local-universality conclusion directly.  It is
replaced by `SumOfSquaresLocalUniversalityLaws`, whose fields expose the
three source branches and the required odd-discriminant-to-ramification
direction separately.

The theorem
`SumOfSquaresLocalUniversalityLaws.sumOfSquares_localUniversal_of_oddDiscriminant`
now performs the complete case split.  It uses the explicit source hypothesis
`1 <= n`: the `n = 1` branch supplies `4 <= m`, while the complementary branch
derives `2 <= n`.  The finite-place derivation no longer takes the unrelated
`notTotallyReal` hypothesis.  A compatibility theorem in `SectionEightLaws`
retains the public call shape used by the full Theorem 1.9 deduction.

Thus the final quantified local conclusion is a proof term rather than a
field.  The remaining fields are concrete arithmetic implementation
boundaries, not restatements of that conclusion.

## Mechanical evidence

With Lean 4.32.1, the focused
`BongTest.He2022ClassicLocalUniversalityAudit` build completes 5,000 jobs and
runs directly.  The new derivation, its compatibility endpoint, and the full
conditional Theorem 1.9 use only `propext`, `Classical.choice`, and
`Quot.sound`.

The canonical paper and audit modules complete a 5,020-job incremental build.
The focused imported-closure gate reports
`AXIOM_GATE_PASS: 62689 declarations checked`.  All 30 policy tests pass, and
the comment-aware scanner checks 2,794 tracked Lean sources without finding a
forbidden proof token.  These checks reuse local artifacts; exact clean-kit
verification remains separate.

## Fidelity boundary

The branch structure now matches v5 line 1700, but the branch laws still need
concrete number-field/completion instances.  In particular, the present
formalization does not yet connect the abstract localized sum-of-squares
lattice to the proved local BONG Theorem 1.1 or Beli unary criterion.  Report
30's directional discriminant premise is still required for the necessity
direction; its converse is used here as the separately named ramification law
required by the sufficiency proof.  This refines Report 30's earlier broad
description of that converse as unused: it had been hidden inside the former
all-places field.

This derivation does not alter the Grade-D whole-paper verdict, repair the
false odd clause of v5 Corollary 6.3, or supply the missing odd argument in
Lemma 8.3 and Theorem 1.8.
