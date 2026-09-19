# Lemma 7.10(iii) C-row witness checkpoint

Date: 2026-09-06. Code checkpoint:
`cf2f474d7bb82ad076ba39b92bcba9f7a2de082a`. Lean: 4.32.1. The sole
semantic authority is the 37-page publisher version of record with SHA-256
`51F3626A15692E2FF0BAAE62F0EBCC4B8BEE02052C4D3CB1EA579B02E17480C1`.

## Published statement and proof boundary

Lemma 7.10 on journal pp. 591--592 treats even `n >= 2`. Clause (iii) says
that, for a determinant square class `c` with `d(c) in {0,1}`, the rank
`n+2` lattice `C1(c)` represents every member of the printed rank-`n` table
except `C2(c)`, and conversely the rank-`n+2` lattice `C2(c)` represents
every member except `C1(c)`.

The printed proof first verifies the terminal hypotheses of Lemma 3.15 and
then invokes He--Hu Proposition 3.5(iii) for ambient codimension-two
exactness. Those are separate obligations: ambient representation alone does
not imply integral lattice representation without the Lemma 3.15 hypotheses.

## Formal endpoints

`Bong/Bong/He2022ClassicLemma710.lean` now provides four layers.

- `he2022ClassicLemma710iii_largeC2_missesExactly_C1` and its `C1/C2`
  converse transfer He--Hu Proposition 3.5(iii) to arbitrary compatible
  classic `C1/C2` pairs in ranks `n` and `n+2`.
- `he2022ClassicLemma710iii_C1_represents_of_ambient` and its `C2`
  counterpart verify the actual order, alpha, signed full-defect, and classic
  integrality hypotheses of Lemma 3.15(i).
- `he2022ClassicLemma710iii_largeC1_misses_C2` and its converse prove genuine
  lattice nonrepresentation, not only ambient nonrepresentation.
- `he2022ClassicLemma710iii_largeC1_represents_other` and its converse prove
  integral representation of every classic rank-`n` target outside the
  excluded ambient isometry class.

`He2022ClassicSectionSeven.lean` specializes both directions to every `C` row
actually printed in Definition 2.6: defect-one unit parameters use the
canonical sharp unit, while odd-order parameters use the discriminant-unit
twist. The four specialized miss theorems and four specialized
`represents_other` theorems compile.

## Scope assessment

The mathematical `C`-pair witness mechanism in Lemma 7.10(iii) is
`FULLY_FORMALIZED` at the coefficient-space and exact-lattice levels, with
correspondence status `PROVISIONAL_MATCH`.

The literal finite-table clause remains `PARTIAL_FORMALIZATION`: the generic
endpoint asks for proof that another table row is outside the deleted row's
ambient isometry class. The finite representative system is irredundant, but
the repository still needs the explicit theorem converting inequality of the
nested classic table indices into that nonisometry premise. Clauses (i)--(ii),
which require the exceptional `H`-row witnesses, are also not included here.
Consequently this checkpoint is not a proof of full Lemma 7.10, minimality in
Theorem 1.3, or whole-paper completion.

## Mechanical evidence

At the fixed code checkpoint:

- the new module, `He2022ClassicSectionSeven.lean`, and the canonical paper
  entry compile with warnings treated as errors;
- `BongTest/He2022ClassicAudit.lean` checks the public signatures and reports
  only `propext`, `Classical.choice`, and `Quot.sound` for the new endpoints;
- the focused transitive axiom gate passes on 58,173 declarations;
- the proof-token scanner checks 2,743 tracked Lean sources with no forbidden
  unfinished-proof token;
- all 24 CI helper tests pass.

These local checks do not replace exact-commit GitHub CI, a clean extracted
Review Kit, or independent human semantic approval.
