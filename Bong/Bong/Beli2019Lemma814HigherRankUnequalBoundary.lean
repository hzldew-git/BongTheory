/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankUnequalStrict

/-!
# Beli (2019), Lemma 8.14: the third-alpha half-gap boundary

On the boundary where the third alpha attains its half-gap, the canonical
binary segment `[a₃,a₄]` also has first alpha equal to the ambient third
alpha.  If this binary segment is not exceptional for Lemma 8.8, its scaling
reduces the first-three raw defect exactly as in the strict suffix branch.
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

/-- The canonical binary segment `[a₃,a₄]`. -/
noncomputable def lemma814UnequalThirdPairSegment
    (a : GoodBONG q L (N + 4)) :
    BONG.SegmentWitness a.toBONG 2 2 (by omega) :=
  a.toBONG.segmentWitness 2 2 (by omega)

/-- The canonical binary segment `[a₃,a₄]`, regarded as a good BONG. -/
noncomputable def lemma814UnequalThirdPair
    (a : GoodBONG q L (N + 4)) :
    GoodBONG
      (q.restrict a.lemma814UnequalThirdPairSegment.carrier
        a.lemma814UnequalThirdPairSegment.nondegenerate)
      a.lemma814UnequalThirdPairSegment.lattice 2 :=
  a.lemma814UnequalThirdPairSegment.toGoodBONG a.good

/-- Third-pair normalization identifies the alpha of `[a₃,a₄]` with
the ambient third alpha. -/
theorem lemma814UnequalThirdPair_alpha_eq_thirdAlpha
    (a : GoodBONG q L (N + 4))
    (hbinary : a.adjacentBinaryAlpha (2 : Fin (N + 3)) =
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)) :
    a.lemma814UnequalThirdPair.alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin (N + 3)) := by
  have hsegment := a.adjacentBinaryAlpha_eq_segmentAlpha
    (2 : Fin (N + 3)) a.lemma814UnequalThirdPairSegment
  have htop :
      (a.lemma814UnequalThirdPair.alphaValue (0 : Fin 1) : WithTop ℚ) =
        (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) :=
    hsegment.symm.trans hbinary
  exact_mod_cast htop

/-- The half-gap of `[a₃,a₄]` is the ambient third half-gap. -/
theorem lemma814UnequalThirdPair_halfGap_eq
    (a : GoodBONG q L (N + 4)) :
    a.lemma814UnequalThirdPair.halfGapValue (0 : Fin 1) =
      a.halfGapValue (2 : Fin (N + 3)) := by
  let s := a.lemma814UnequalThirdPair
  let w := a.lemma814UnequalThirdPairSegment
  have horder0 : s.order (0 : Fin 2) = a.order (2 : Fin (N + 4)) := by
    change w.bong.order 0 = a.toBONG.order 2
    rw [w.order_eq]
    congr 1
  have horder1 : s.order (1 : Fin 2) = a.order (3 : Fin (N + 4)) := by
    change w.bong.order 1 = a.toBONG.order 3
    rw [w.order_eq]
    congr 1
  unfold halfGapValue orderGap
  change (((s.order (1 : Fin 2) - s.order (0 : Fin 2) : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ)) =
    (((a.order (3 : Fin (N + 4)) - a.order (2 : Fin (N + 4)) : Int) : ℚ) /
      2 + (ramificationIndex K : ℚ))
  rw [horder0, horder1]

/-- Insert a successful binary Lemma 8.8 transform of `[a₃,a₄]` into
the ambient BONG. -/
theorem lemma814UnequalTailScalingData_of_thirdPairTransform
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (T : a.lemma814UnequalThirdPair.Beli2019FirstValueTransform)
    (halpha : a.lemma814UnequalThirdPair.alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin (N + 3))) :
    Nonempty a.Beli2019Lemma814UnequalTailScalingData := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma814UnequalThirdPairSegment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 4) :=
    ⟨replacement.bong, replacement.good⟩
  have beforeValue_eq (i : Fin (N + 4)) (hi : i.1 < 2) :
      transformed.valueUnit i = a.valueUnit i := by
    apply Units.ext
    change replacement.bong.value i = a.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (replacement.before_eq i hi)
  have hthirdLocal : transformed.valueUnit (2 : Fin (N + 4)) =
      T.transformed.valueUnit (0 : Fin 2) := by
    apply Units.ext
    change replacement.bong.value 2 = T.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 2) =
      q.quadratic (T.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic (replacement.inside_eq (0 : Fin 2))
  have hpairFirst : a.lemma814UnequalThirdPair.valueUnit (0 : Fin 2) =
      a.valueUnit (2 : Fin (N + 4)) := by
    let w := a.lemma814UnequalThirdPairSegment
    change w.bong.valueUnit 0 = a.toBONG.valueUnit 2
    rw [w.valueUnit_eq]
    congr 1
  exact ⟨{
    epsilon := T.epsilon
    epsilon_isValuationUnit := T.epsilon_isValuationUnit
    epsilon_defect := T.epsilon_defect.trans <|
      congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) halpha
    transformed := transformed
    firstValue_eq := beforeValue_eq (0 : Fin (N + 4)) (by norm_num)
    secondValue_eq := beforeValue_eq (1 : Fin (N + 4)) (by norm_num)
    thirdValue_eq := hthirdLocal.trans <| T.firstValue_eq.trans <|
      congrArg (T.epsilon * ·) hpairFirst
  }⟩

/-- A nonexceptional third binary pair supplies the same ambient scaling data
as the strict full-suffix branch. -/
theorem exists_lemma814UnequalTailScalingData_of_thirdPair_notExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (hbinary : a.adjacentBinaryAlpha (2 : Fin (N + 3)) =
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ))
    (hnotExceptional :
      ¬a.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional) :
    Nonempty a.Beli2019Lemma814UnequalTailScalingData := by
  have halpha := a.lemma814UnequalThirdPair_alpha_eq_thirdAlpha hbinary
  rcases a.lemma814UnequalThirdPair.beli2019Lemma88_rankTwo_sufficiency
      hnotExceptional with ⟨T⟩
  exact a.lemma814UnequalTailScalingData_of_thirdPairTransform T halpha

/-- Completion of the half-gap boundary when `[a₃,a₄]` is not
exceptional for Lemma 8.8. -/
theorem beli2019Lemma814_higherRankUnequal_boundary_of_thirdPair_notExceptional
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
    (H : a.Beli2019Lemma814UnequalHardData b)
    (hnotExceptional :
      ¬H.normalForm.transformed.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let c := H.normalForm.transformed
  rcases c.exists_lemma814UnequalTailScalingData_of_thirdPair_notExceptional
      H.normalForm.thirdBinaryAlpha_eq hnotExceptional with ⟨D⟩
  exact beli2019Lemma814_higherRankUnequal_of_tailScalingData
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    a original b H D

/-- The sole remaining boundary package after the binary Lemma 8.8 attempt.
-/
structure Beli2019Lemma814UnequalBoundaryExceptionalData
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) where
  hardData : a.Beli2019Lemma814UnequalHardData b
  thirdAlpha_eq_halfGap :
    hardData.normalForm.transformed.alphaValue (2 : Fin (N + 3)) =
      hardData.normalForm.transformed.halfGapValue (2 : Fin (N + 3))
  thirdPairExceptional :
    hardData.normalForm.transformed.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional

/-- The strict and boundary split after the hard normal form.  All cases are
closed except the explicitly bundled exceptional binary boundary. -/
theorem lemma814UnequalHardData_dispatch
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
    (H : a.Beli2019Lemma814UnequalHardData b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) ∨
      Nonempty (a.Beli2019Lemma814UnequalBoundaryExceptionalData b) := by
  let c := H.normalForm.transformed
  rcases lt_or_eq_of_le (c.alphaValue_le_halfGapValue
      (2 : Fin (N + 3))) with hstrict | hboundary
  · left
    exact beli2019Lemma814_higherRankUnequal_of_thirdAlpha_lt_halfGap
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      a original b H hstrict
  · by_cases hpair : c.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional
    · right
      exact ⟨{
        hardData := H
        thirdAlpha_eq_halfGap := hboundary
        thirdPairExceptional := hpair
      }⟩
    · left
      exact
        beli2019Lemma814_higherRankUnequal_boundary_of_thirdPair_notExceptional
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW)
          a original b H hpair

end BONG.GoodBONG
end Bong
