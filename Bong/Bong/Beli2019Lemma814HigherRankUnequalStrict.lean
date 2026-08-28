/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankUnequalTail

/-!
# Beli (2019), Lemma 8.14: strict third-alpha tail scaling

When the third alpha is strictly below its half-gap, Lemma 8.8 changes the
first value of `[a₃, ..., aₙ]`.  Lemma 4.9(ii) inserts the changed suffix into
the ambient BONG.  The new first-three raw defect is exactly the third alpha,
so the direct ternary reduction completes this branch.
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

/-- Ambient data obtained by inserting a successful Lemma 8.8
transformation of `[a₃, ..., aₙ]`. -/
structure Beli2019Lemma814UnequalTailScalingData
    (a : GoodBONG q L (N + 4)) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect : defectOrder (K := K) epsilon =
    (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
  transformed : GoodBONG q L (N + 4)
  firstValue_eq : transformed.valueUnit (0 : Fin (N + 4)) =
    a.valueUnit (0 : Fin (N + 4))
  secondValue_eq : transformed.valueUnit (1 : Fin (N + 4)) =
    a.valueUnit (1 : Fin (N + 4))
  thirdValue_eq : transformed.valueUnit (2 : Fin (N + 4)) =
    epsilon * a.valueUnit (2 : Fin (N + 4))

/-- Lemma 8.8 on `[a₃, ..., aₙ]`, inserted by Lemma 4.9(ii), in the
strict third-alpha branch. -/
theorem exists_lemma814UnequalTailScalingData_of_thirdAlpha_lt_halfGap
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
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (hbinary : a.adjacentBinaryAlpha (2 : Fin (N + 3)) =
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ))
    (hstrict : a.alphaValue (2 : Fin (N + 3)) <
      a.halfGapValue (2 : Fin (N + 3))) :
    Nonempty a.Beli2019Lemma814UnequalTailScalingData := by
  have halpha := a.lemma814UnequalTail_alpha_zero_eq_thirdAlpha hbinary
  have hhalf := a.lemma814UnequalTail_halfGapValue_zero_eq
  have htailStrict : a.lemma814UnequalTail.alphaValue (0 : Fin (N + 1)) <
      a.lemma814UnequalTail.halfGapValue (0 : Fin (N + 1)) := by
    rw [halpha, hhalf]
    exact hstrict
  have htailNotExceptional :
      ¬a.lemma814UnequalTail.Beli2019Lemma88Exceptional := by
    rintro ⟨hattains, _⟩
    exact (ne_of_lt htailStrict) hattains
  rcases a.lemma814UnequalTail.beli2019Lemma88_sufficiency
      htailNotExceptional with ⟨T⟩
  rcases a.toBONG.beliLemma49_ii a.good a.lemma814UnequalTailSegment
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
      T.transformed.valueUnit (0 : Fin (N + 2)) := by
    apply Units.ext
    change replacement.bong.value 2 = T.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 2) =
      q.quadratic (T.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic (replacement.inside_eq (0 : Fin (N + 2)))
  have htailFirst : a.lemma814UnequalTail.valueUnit (0 : Fin (N + 2)) =
      a.valueUnit (2 : Fin (N + 4)) := by
    have h := a.lemma814UnequalTail_valueUnit_eq (0 : Fin (N + 2))
    convert h using 1
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
      congrArg (T.epsilon * ·) htailFirst
  }⟩

namespace Beli2019Lemma814UnequalTailScalingData

variable {a : GoodBONG q L (N + 4)}

/-- The first-three product is multiplied by the suffix multiplier. -/
theorem prefixProduct_three_eq
    (D : a.Beli2019Lemma814UnequalTailScalingData) :
    D.transformed.prefixProduct 3 = D.epsilon * a.prefixProduct 3 := by
  unfold GoodBONG.prefixProduct
  rw [D.transformed.toBONG.prefixProduct_succ 2 (by omega),
    D.transformed.toBONG.prefixProduct_succ 1 (by omega),
    D.transformed.toBONG.prefixProduct_succ 0 (by omega),
    a.toBONG.prefixProduct_succ 2 (by omega),
    a.toBONG.prefixProduct_succ 1 (by omega),
    a.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul]
  have hfirst := D.firstValue_eq
  change D.transformed.toBONG.valueUnit ⟨0, by omega⟩ =
    a.toBONG.valueUnit ⟨0, by omega⟩ at hfirst
  have hsecond := D.secondValue_eq
  change D.transformed.toBONG.valueUnit ⟨1, by omega⟩ =
    a.toBONG.valueUnit ⟨1, by omega⟩ at hsecond
  have hthird := D.thirdValue_eq
  change D.transformed.toBONG.valueUnit ⟨2, by omega⟩ =
    D.epsilon * a.toBONG.valueUnit ⟨2, by omega⟩ at hthird
  rw [hfirst, hsecond, hthird]
  ac_rfl

/-- If the old first-three raw defect is strictly larger than the third
alpha, the suffix scaling makes the new raw defect exactly the third alpha.
-/
theorem firstThreeRawDefect_eq_thirdAlpha_of_old_gt
    [QuadraticDefectLaws K]
    (D : a.Beli2019Lemma814UnequalTailScalingData)
    (b : GoodBONG r M 1)
    (hraw : (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
      defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1)) :
    defectOrder (K := K)
        ((-1) * D.transformed.prefixProduct 3 * b.prefixProduct 1) =
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := by
  have hproduct :
      (-1 : Kˣ) * D.transformed.prefixProduct 3 * b.prefixProduct 1 =
        D.epsilon * ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
    rw [D.prefixProduct_three_eq]
    ac_rfl
  rw [hproduct,
    defectOrder_mul_eq_left_of_lt_right (K := K) (D.epsilon_defect ▸ hraw),
    D.epsilon_defect]

end Beli2019Lemma814UnequalTailScalingData

/-- Any suffix or third-pair scaling with multiplier defect equal to the
third alpha makes the first-three raw defect small and completes the hard
unequal-outer branch. -/
theorem beli2019Lemma814_higherRankUnequal_of_tailScalingData
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
    (D : H.normalForm.transformed.Beli2019Lemma814UnequalTailScalingData) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let c := H.normalForm.transformed
  let changed := D.transformed
  have horders := c.order_invariant changed
  have halphas := c.alpha_invariant changed
  have horder' : changed.order (0 : Fin (N + 4)) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 4))]
    exact H.normalForm.firstOrder_eq
  have hstrictEndpoint :
      (changed.order (0 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (0 : Fin (N + 3)) <
        (changed.order (1 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (1 : Fin (N + 3)) := by
    rw [← horders (0 : Fin (N + 4)),
      ← halphas (0 : Fin (N + 3)),
      ← horders (1 : Fin (N + 4)),
      ← halphas (1 : Fin (N + 3))]
    exact H.normalForm.firstEndpoint_strict
  have hbinary :=
    changed.firstBinaryAlpha_eq_alpha_of_firstEndpoint_strict hstrictEndpoint
  have hconditions := c.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b
      H.normalForm.firstOrder_eq H.normalForm.conditions
  have hinvariant := c.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  have hnotExceptional : ¬changed.Beli2019Lemma814Exceptional b :=
    fun E ↦ H.normalForm.notExceptional (hinvariant.mpr E)
  have hepsilon : changed.lemma814Epsilon b = c.lemma814Epsilon b := by
    unfold lemma814Epsilon
    rw [D.firstValue_eq]
  have hadjacent : changed.adjacentProduct (0 : Fin (N + 3)) =
      c.adjacentProduct (0 : Fin (N + 3)) := by
    unfold adjacentProduct
    have hfirst : changed.valueUnit (0 : Fin (N + 3)).castSucc =
        c.valueUnit (0 : Fin (N + 3)).castSucc := by
      change D.transformed.valueUnit (0 : Fin (N + 3)).castSucc =
        c.valueUnit (0 : Fin (N + 3)).castSucc
      convert D.firstValue_eq using 1 <;> congr 1
    have hsecond : changed.valueUnit (0 : Fin (N + 3)).succ =
        c.valueUnit (0 : Fin (N + 3)).succ := by
      change D.transformed.valueUnit (0 : Fin (N + 3)).succ =
        c.valueUnit (0 : Fin (N + 3)).succ
      convert D.secondValue_eq using 1 <;> congr 1
    rw [hfirst, hsecond]
  have hhilbert : hilbertSymbol K (changed.lemma814Epsilon b)
      (changed.adjacentProduct (0 : Fin (N + 3))) = -1 := by
    rw [hepsilon, hadjacent]
    exact H.hilbert_neg_one
  have houter : changed.order (0 : Fin (N + 4)) <
      changed.order (2 : Fin (N + 4)) := by
    rw [← horders (0 : Fin (N + 4)),
      ← horders (2 : Fin (N + 4))]
    exact H.normalForm.outer_lt
  have hbound : changed.Lemma814UnequalOuterBound b := by
    rcases changed.lemma814_outerCases_of_hilbert_neg_one b hconditions
        hhilbert with houterEq | hbound
    · exact (ne_of_lt houter houterEq).elim
    · exact hbound
  have hrawOld :=
    D.firstThreeRawDefect_eq_thirdAlpha_of_old_gt b
      H.thirdAlpha_lt_rawDefect
  have hraw : defectOrder (K := K)
        ((-1) * changed.prefixProduct 3 * b.prefixProduct 1) =
      (changed.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := by
    calc
      defectOrder (K := K)
          ((-1) * changed.prefixProduct 3 * b.prefixProduct 1) =
          (c.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := hrawOld
      _ = (changed.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
          (halphas (2 : Fin (N + 3)))
  exact changed.beli2019Lemma814_higherRankUnequal_of_raw_le_thirdAlpha
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b horder' hconditions hbinary hbound hraw.le

/-- Completion of the hard unequal-outer subcase in which the third alpha is
strictly below its half-gap. -/
theorem beli2019Lemma814_higherRankUnequal_of_thirdAlpha_lt_halfGap
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
    (hstrict : H.normalForm.transformed.alphaValue (2 : Fin (N + 3)) <
      H.normalForm.transformed.halfGapValue (2 : Fin (N + 3))) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let c := H.normalForm.transformed
  rcases c.exists_lemma814UnequalTailScalingData_of_thirdAlpha_lt_halfGap
      H.normalForm.thirdBinaryAlpha_eq hstrict with ⟨D⟩
  exact beli2019Lemma814_higherRankUnequal_of_tailScalingData
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    a original b H D

end BONG.GoodBONG
end Bong
