# Proposition 8.2 globalization derivation

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`ea0f9f1516d41d18c87b8c0ee0757fd8d5e58e1b` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and locator

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Proposition 8.2 is stated at lines 1660--1664 and proved at lines 1665--1674.
For a selected finite prime, the proof globalizes each local testing lattice
to a positive definite classic integral global lattice, applies the global
representation hypothesis, localizes the representation, and uses the local
testing theorem.  The dyadic globalization is attributed to O'Meara 81:14;
the unary and non-dyadic testing families are cited separately.

## Formal change

The former `SectionEightLaws.proposition82` field stored the complete local
universality conclusion.  It is replaced by `Proposition82Laws`, whose four
inputs are lower-level arithmetic operations:

1. localization of global integrality;
2. positive-definite integral globalization of an arbitrary integral local
   lattice at the selected finite place, preserving rank up to local
   equivalence;
3. localization of global representation; and
4. transport of local representation across equivalence of the represented
   lattice.

`Proposition82Laws.he2022ClassicProposition82_positive` now proves the first
sentence of Proposition 8.2.  Given an arbitrary integral local rank-`n`
lattice, it obtains the global positive-definite lattice, applies the global
hypothesis, localizes the resulting representation, and transports it to the
original local lattice.  The public `SectionEightLaws` endpoint retains the
source assumption `1 <= n`, although this abstract derivation does not need
positivity of `n`.  The second sentence still follows by converting global
classic universality into the stronger positive-definite premise.

This is a strict reduction of the trust boundary: Proposition 8.2 itself is
no longer a supplied field.  The four concrete arithmetic inputs are not yet
implemented for number-field lattices and therefore remain explicit.

## Mechanical evidence

With Lean 4.32.1, the focused module
`BongTest.He2022ClassicProposition82Audit` completes a 5,000-job build and
runs directly.  The derived positive statement, its compatibility wrapper,
and the second sentence of Proposition 8.2 all report empty axiom sets.

The canonical paper and audit modules complete a 5,016-job incremental build.
The combined imported-closure gate reports
`AXIOM_GATE_PASS: 62655 declarations checked`.  All 30 policy tests pass and
the comment-aware scanner checks 2,790 tracked Lean sources without finding a
forbidden proof token.  These checks reuse local artifacts; an exact clean
Review Kit remains a separate reproducibility gate.

## Fidelity boundary

The formal proof follows the source's globalization/localization logic, but
the repository still lacks a concrete number-field lattice implementation of
O'Meara 81:14 and the local representation-transport facts.  The result is
therefore conditional, not an unconditional formalization of Proposition
8.2 over algebraic number fields.

The Grade-D whole-paper verdict is unchanged.  In particular, this work does
not repair the false unrestricted odd clause of v5 Corollary 6.3 or the
dependent odd branch of Lemma 8.3 and Theorem 1.8.
