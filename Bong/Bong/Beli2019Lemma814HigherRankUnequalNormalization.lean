/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankUnequal

/-!
# Beli (2019), Lemma 8.14: unequal-outer third-pair normalization

After reductions (I) and (II), a large uncapped first-three defect makes the
first left-endpoint inequality strict.  Corollary 8.11 may then normalize
`[a₃,a₄]`; the strict endpoint relation is invariant and automatically
recovers reduction (I) for the new good BONG.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- Data retained after Corollary 8.11 normalizes the third adjacent pair in
the higher-rank unequal-outer branch. -/
structure Beli2019Lemma814ThirdAdjacentNormalForm
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) where
  transformed : GoodBONG q L (N + 4)
  firstOrder_eq : transformed.order (0 : Fin (N + 4)) =
    b.order (0 : Fin 1)
  firstBinaryAlpha_eq : transformed.firstBinaryAlpha =
    (transformed.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  thirdBinaryAlpha_eq : transformed.adjacentBinaryAlpha
      (2 : Fin (N + 3)) =
    (transformed.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
  outer_lt : transformed.order (0 : Fin (N + 4)) <
    transformed.order (2 : Fin (N + 4))
  firstEndpoint_strict :
    (transformed.order (0 : Fin (N + 4)) : ℚ) +
        transformed.alphaValue (0 : Fin (N + 3)) <
      (transformed.order (1 : Fin (N + 4)) : ℚ) +
        transformed.alphaValue (1 : Fin (N + 3))
  conditions : transformed.Lemma813Conditions b
  notExceptional : ¬transformed.Beli2019Lemma814Exceptional b

/-- Corollary 8.11 on `[a₃,a₄]`, with the strict endpoint relation and
all global Lemma 8.14 hypotheses transported to the resulting good BONG. -/
theorem exists_lemma814ThirdAdjacentNormalForm
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hfirst : a.lemma814InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (N + 3)))
    (hsecond : a.lemma814InitialThree.alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin (N + 3)))
    (houter : a.order (0 : Fin (N + 4)) < a.order (2 : Fin (N + 4)))
    (hraw : (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
      defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1)) :
    Nonempty (a.Beli2019Lemma814ThirdAdjacentNormalForm b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have hstrict :=
    a.lemma814_firstEndpoint_strict_of_thirdAlpha_lt_rawDefect b conditions
      hfirst hsecond houter hraw
  rcases a.beli2019Corollary811 (2 : Fin (N + 3)) with ⟨D⟩
  let changed := D.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have hstrict' :
      (changed.order (0 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (0 : Fin (N + 3)) <
        (changed.order (1 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (1 : Fin (N + 3)) := by
    rw [← horders (0 : Fin (N + 4)),
      ← halphas (0 : Fin (N + 3)),
      ← horders (1 : Fin (N + 4)),
      ← halphas (1 : Fin (N + 3))]
    exact hstrict
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  exact ⟨{
    transformed := changed
    firstOrder_eq := by
      rw [← horders (0 : Fin (N + 4))]
      exact horder
    firstBinaryAlpha_eq :=
      changed.firstBinaryAlpha_eq_alpha_of_firstEndpoint_strict hstrict'
    thirdBinaryAlpha_eq := D.adjacentBinaryAlpha_eq
    outer_lt := by
      rw [← horders (0 : Fin (N + 4)),
        ← horders (2 : Fin (N + 4))]
      exact houter
    firstEndpoint_strict := hstrict'
    conditions := hconditions
    notExceptional := fun E ↦ hnotExceptional (hinvariant.mpr E)
  }⟩

/-- The residual hard branch after normalizing `[a₃,a₄]`: the Hilbert
symbol is negative, the unequal-outer bound has been re-established for the
new BONG, and its uncapped first-three defect is still too large for the
direct ternary reduction. -/
structure Beli2019Lemma814UnequalHardData
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) where
  normalForm : a.Beli2019Lemma814ThirdAdjacentNormalForm b
  hilbert_neg_one : hilbertSymbol K
      (normalForm.transformed.lemma814Epsilon b)
      (normalForm.transformed.adjacentProduct (0 : Fin (N + 3))) = -1
  unequalOuterBound : normalForm.transformed.Lemma814UnequalOuterBound b
  thirdAlpha_lt_rawDefect :
    (normalForm.transformed.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1) * normalForm.transformed.prefixProduct 3 * b.prefixProduct 1)

/-- Re-dispatch after the third-pair normalization.  A positive Hilbert
symbol solves the problem on the first binary pair.  A negative symbol first
re-establishes the paper's unequal-outer bound; a small raw defect then uses
the direct ternary reduction, leaving exactly `Beli2019Lemma814UnequalHardData`.
-/
theorem lemma814ThirdAdjacentNormalForm_dispatch
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (T : a.Beli2019Lemma814ThirdAdjacentNormalForm b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) ∨
      Nonempty (a.Beli2019Lemma814UnequalHardData b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let c := T.transformed
  by_cases hone : hilbertSymbol K (c.lemma814Epsilon b)
      (c.adjacentProduct (0 : Fin (N + 3))) = 1
  · left
    rcases c.beli2019Lemma814_binaryBranch b T.firstOrder_eq T.conditions
        T.firstBinaryAlpha_eq hone with ⟨U⟩
    exact ⟨{
      transformed := U.transformed
      firstValue_eq := U.firstValue_eq
    }⟩
  · have hneg : hilbertSymbol K (c.lemma814Epsilon b)
        (c.adjacentProduct (0 : Fin (N + 3))) = -1 := by
      apply (hilbertSymbol_eq_neg_one_iff K _ _).2
      intro hnorm
      exact hone ((hilbertSymbol_eq_one_iff K _ _).2 hnorm)
    rcases c.lemma814_outerCases_of_hilbert_neg_one b T.conditions hneg with
      houterEq | hbound
    · exact (ne_of_lt T.outer_lt houterEq).elim
    · by_cases hraw : defectOrder (K := K)
          ((-1) * c.prefixProduct 3 * b.prefixProduct 1) ≤
        (c.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
      · left
        exact c.beli2019Lemma814_higherRankUnequal_of_raw_le_thirdAlpha
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW)
          original b T.firstOrder_eq T.conditions T.firstBinaryAlpha_eq
            hbound hraw
      · right
        exact ⟨{
          normalForm := T
          hilbert_neg_one := hneg
          unequalOuterBound := hbound
          thirdAlpha_lt_rawDefect := lt_of_not_ge hraw
        }⟩

end BONG.GoodBONG
end Bong
