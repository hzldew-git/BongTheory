# Discriminant and ramification direction

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`46bf941e3edc83b7dc2fb115bdd8b0215a73653f` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and locator

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
The global conclusion of Theorem 1.5 is stated at line 217.  Theorem 1.7 is
stated at line 227 and proved at lines 1675--1679.  Theorem 1.9 is proved at
lines 1697--1700.  These arguments use the implication from ramification
index one at every dyadic prime to odd discriminant, and its contrapositive.

## Formal change

The former `SectionEightLaws.unramified_iff_discriminantOdd` field supplied a
full biconditional, although no formal proof used the reverse implication.
It is replaced by `DiscriminantRamificationLaws`, which contains only:

`(all dyadic ramification indices are one) -> discriminantOdd`.

The theorem
`exists_ramifiedDyadic_of_not_discriminantOdd` derives the contrapositive
existence statement: if the discriminant is not odd, some dyadic place has
ramification index different from one.  Theorem 1.7 combines that witness
with the separate positivity law to obtain ramification index greater than
one.  The global Theorem 1.5 deduction and the necessity direction of Theorem
1.9 consume the same one-way criterion directly.

Thus a stronger unused arithmetic premise has been removed, and the
ramified-place witness is now a proof term rather than a field.

## Mechanical evidence

With Lean 4.32.1,
`BongTest.He2022ClassicDiscriminantRamificationAudit` completes a 5,000-job
focused build and runs directly.  The global Theorem 1.5 endpoint and the
conditional Theorem 1.9 endpoint have empty axiom sets.  The contrapositive
witness and Theorem 1.7 use only `propext`, `Classical.choice`, and
`Quot.sound`.

The canonical paper and audit modules complete a 5,019-job incremental build.
The focused imported-closure gate reports
`AXIOM_GATE_PASS: 62676 declarations checked`.  All 30 policy tests pass, and
the comment-aware scanner checks 2,794 tracked Lean sources without finding a
forbidden proof token.  These checks reuse local artifacts; exact clean-kit
verification remains separate.

## Fidelity boundary

The project still does not instantiate the discriminant/ramification law for
a concrete number field.  Theorem 1.7 also retains the independently
documented missing odd coefficient calculation.  This reduction therefore
does not alter the Grade-D whole-paper verdict or repair the false odd clause
of v5 Corollary 6.3.
