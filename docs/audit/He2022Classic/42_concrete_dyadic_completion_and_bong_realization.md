# Concrete dyadic completions and actual good-BONG realization

Status: `LEMMA_8_1_I_II_PROVED` /
`LEMMA_8_1_III_PROOF_SUPPORTED_REALIZATION_PROVED` /
`LITERAL_SCALAR_EXTENSION_CARRIER_IDENTIFICATION_OPEN`.

Code checkpoint:
`e3b18be95c813885a421b83fe0a0148d6b561ae0` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority

The sole semantic authority remains the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
The manuscript is author-held and is not redistributed.

V5 Lemma 8.1 occurs at source lines 1632--1659. Parts (i) and (ii) are the
order equality and relative quadratic-defect inequality. Part (iii) names a
preassigned localized scalar-extension lattice `L_P`. Its proof checks the
three He--Hu numerical conditions for the mapped coefficients and then invokes
He--Hu Lemma 2.2. That cited lemma, reproduced at v5 lines 241--250, concludes
only that the orthogonal vectors form a good BONG **for some lattice**.
Neither the citation nor the written proof identifies that lattice with the
preassigned `L_P`.

## Concrete local-field bridge

`Bong.Dyadic.NumberFieldCompletion` now supplies the missing reusable
infrastructure for every finite completion of a number field:

- the residue map from the original number-field integer ring to the residue
  field of the completed valuation ring is proved surjective;
- finiteness of the completed residue field follows from the finite quotient
  by the defining height-one prime;
- the canonical completed valuation ring is a DVR, and the completion is
  proper, locally compact, and an `IsNonarchimedeanLocalField`;
- its normalized additive valuation has a uniformizer of order one; and
- a prime containing two supplies an actual `DyadicContext` for the BONG
  library.

The residue-field surjectivity proof uses density of the number field in its
completion and the Dedekind approximation theorem. No finiteness or local-
compactness assertion is introduced as a paper-specific premise.

## Identification with the BONG normalization

`Bong.Lattice.He2022ClassicNumberFieldBONGBridge` proves that the new concrete
context agrees with both earlier formulations:

- `ramificationIndex_eq_idealRamificationIdx` identifies the BONG absolute
  ramification index with the ideal-theoretic index;
- `ordUnit_eq_completionAdicOrder` identifies the BONG additive order with
  the completed logarithmic order;
- `isQuadraticApproximation_iff_completion` identifies the additive-order and
  valuation-ball square-approximation predicates; and
- `quadraticDefect_eq_completionQuadraticDefect` and
  `defectOrder_eq_completionQuadraticDefectQ` identify the two defect scales,
  including the infinite-defect case.

Thus Reports 40--41 do not merely use parallel numerical definitions: their
orders, defects, and ramification indices are now proved equal to the concrete
BONG library notions.

## Actual realization proved

The following implications are kernel checked:

1. `goodBONG_completionGoodBONGCoefficients` starts with an actual good BONG
   over the lower dyadic completion and derives the exact adjacent and
   two-step He--Hu coefficient criterion.
2. `completionGoodBONGCoefficients_hasGoodBONG` proves the converse at the
   realization level: every coefficient row satisfying that criterion is
   realized by an actual integral lattice with an actual good BONG and exactly
   those values.
3. `completionGoodBONGCoefficients_map_hasGoodBONG` applies the result after a
   finite extension and a prime above the original dyadic prime.
4. `goodBONG_mappedValues_haveRealization` composes the preceding statements:
   every actual lower good BONG has an actual upper good-BONG realization whose
   values are precisely the images of the lower values.

This is the strongest conclusion established by the proof written in v5:

`actual lower good BONG -> actual upper realization with mapped values`.

It is stronger than the coefficient-only checkpoint in Report 41, but it is
still weaker than the literal statement

`the same vectors form a good BONG of the preassigned lattice L_P`.

The latter additionally needs a carrier theorem identifying the constructed
upper realization with the localization/scalar extension of the original
lattice. The source proof does not supply that step, and the Lean development
does not assume it.

## Mechanical evidence

At the stated code checkpoint:

- the focused completion/BONG/audit build completes 5,653 jobs;
- the canonical paper entry and all eight manifest-listed Classic audits
  complete 5,676 jobs;
- all 30 repository policy tests pass;
- the comment-aware scanner checks 2,802 tracked Lean sources without a
  forbidden proof token outside comments;
- the focused imported-closure gate reports
  `AXIOM_GATE_PASS: 62917 declarations checked`; and
- every newly audited declaration uses only `propext`, `Classical.choice`,
  and `Quot.sound`.

These are local code-checkpoint results. Fresh source-only Review Kit
verification and GitHub CI are separate gates.

## Remaining boundary

The literal carrier conclusion of v5 Lemma 8.1(iii) remains unproved. A source
repair can take either of two forms:

1. weaken part (iii) to the actual-existence conclusion proved above; or
2. retain `L_P` and add a lemma proving that the lattice produced by He--Hu
   Lemma 2.2 is the specified localized scalar-extension lattice.

The concrete global lattice/localization model, its place equivalence,
positive-definite globalization, representation transport, local
sum-of-squares branches, and strong approximation also remain open. The
independent obstruction from the false unrestricted odd v5 Corollary 6.3
remains unchanged. Consequently the whole-paper grade stays D, the completion
verdict stays `NOT_COMPLETE`, and GitHub deployment stays disabled.
