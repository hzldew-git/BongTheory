/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankStrict
import Bong.Bong.Beli2019Lemma814HigherRankEqual
import Bong.Bong.Beli2019Lemma814HigherRankNormalization

/-!
# Beli (2019), Lemma 8.14: higher-rank assembly

The two order branches constructed in the preceding files both replace the
ambient BONG by one whose initial quaternary segment no longer satisfies
exception (c).  This file transports all invariant hypotheses to that BONG,
applies the completed rank-four theorem, and inserts the resulting initial
quaternary transformation back into the original lattice.
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

/-- Once a change of ambient BONG destroys local exception (c), the
rank-four theorem and Lemma 4.9(ii) finish the higher-rank construction. -/
theorem beli2019Lemma814_of_initialFour_exceptionC_killed
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
    [DyadicTernaryRepresentationObstructionLaws K]
    (a a' original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (houterAmbient : a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)))
    (hsecondFourthAmbient : a.order (1 : Fin (N + 5)) <
      a.order (⟨3, by omega⟩ : Fin (N + 5)))
    (hnotC : ¬Beli2019Lemma814ExceptionC
      (a'.lemma814InitialFour (by omega)) b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have horders := a.order_invariant a'
  have halphas := a.alpha_invariant a'
  have horder' : a'.order (0 : Fin (N + 5)) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 5))]
    exact horder
  have hconditions' := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) a' b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) a' b
  have hnotExceptional' : ¬a'.Beli2019Lemma814Exceptional b :=
    fun E ↦ hnotExceptional (hinvariant.mpr E)
  have hhalf := a.halfGapValue_invariant
    (classificationV := classificationV) a'
      (⟨2, by omega⟩ : Fin (N + 4))
  have hthirdHalf : a'.alphaValue
      (⟨2, by omega⟩ : Fin (N + 4)) =
        a'.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) := by
    calc
      a'.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
          a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) :=
        (halphas _).symm
      _ = a.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) :=
        A.third_eq_halfGap
      _ = a'.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) := hhalf
  have hbinary' :=
    a'.adjacentBinaryAlpha_eq_alpha_of_attainsHalfGap
      (⟨2, by omega⟩ : Fin (N + 4)) hthirdHalf
  have hlocalAlphas' :=
    a'.lemma814InitialFour_alphas_eq (by omega) hbinary'
  have hlocalConditions' :=
    a'.lemma814InitialFour_conditions b (by omega)
      hlocalAlphas' hconditions'
  have hnotAB' :=
    a'.lemma814InitialFour_not_exceptionAB b (by omega)
      hlocalAlphas' hnotExceptional'
  have hnotLocalExceptional :
      ¬Beli2019Lemma814Exceptional
        (a'.lemma814InitialFour (by omega)) b := by
    intro E
    rcases E with A' | B' | C'
    · exact hnotAB'.1 A'
    · exact hnotAB'.2 B'
    · exact hnotC C'
  have houter' : a'.order (0 : Fin (N + 5)) =
      a'.order (⟨2, by omega⟩ : Fin (N + 5)) := by
    rw [← horders (0 : Fin (N + 5)),
      ← horders (⟨2, by omega⟩ : Fin (N + 5))]
    exact houterAmbient
  have hsecondFourth' : a'.order (1 : Fin (N + 5)) <
      a'.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    rw [← horders (1 : Fin (N + 5)),
      ← horders (⟨3, by omega⟩ : Fin (N + 5))]
    exact hsecondFourthAmbient
  have hlocalOrder : (a'.lemma814InitialFour (by omega)).order
      (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [a'.lemma814InitialFour_order_eq (by omega)]
    exact horder'
  have hlocalOuter : (a'.lemma814InitialFour (by omega)).order
      (0 : Fin 4) =
        (a'.lemma814InitialFour (by omega)).order (2 : Fin 4) := by
    simp only [a'.lemma814InitialFour_order_eq (by omega)]
    convert houter' using 1 <;> congr 1
  have hlocalSecondFourth :
      (a'.lemma814InitialFour (by omega)).order (1 : Fin 4) <
        (a'.lemma814InitialFour (by omega)).order (3 : Fin 4) := by
    simp only [a'.lemma814InitialFour_order_eq (by omega)]
    convert hsecondFourth' using 1 <;> congr 1
  rcases (a'.lemma814InitialFour (by omega)).beli2019Lemma814_rankFour
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      (a'.lemma814InitialFour (by omega)) b hlocalOrder
        hlocalConditions' hnotLocalExceptional hlocalOuter
          hlocalSecondFourth with ⟨T⟩
  exact a'.prescribedFirstValueTransform_of_firstFourSegment
    original b (by omega) (a'.lemma814InitialFourSegment (by omega)) T

section HigherRankBranches

variable
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
  [DyadicTernaryRepresentationObstructionLaws K]

/-- The `R₃ < R₅` construction destroys local exception (c) and
therefore finishes through the common rank-four assembly. -/
theorem beli2019Lemma814_of_initialFour_exceptionC_third_lt_fifth
    (a original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hraw : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ))
    (houter : a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)))
    (hsecondFourth : a.order (1 : Fin (N + 5)) <
      a.order (⟨3, by omega⟩ : Fin (N + 5)))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) <
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.exists_lemma814TailScalingData_of_third_lt_fifth
      A hthirdFifth with ⟨S⟩
  have hnotC := S.initialFour_not_exceptionC
    A b hresidueTwo hraw
  exact a.beli2019Lemma814_of_initialFour_exceptionC_killed
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    S.transformed original b horder conditions hnotExceptional A houter
      hsecondFourth hnotC

/-- The `R₃ = R₅` construction likewise destroys local exception
(c), now through Corollary 8.9 on the initial five entries. -/
theorem beli2019Lemma814_of_initialFour_exceptionC_third_eq_fifth
    (a original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hraw : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ))
    (hsecondStrict :
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)))
    (houter : a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)))
    (hsecondFourth : a.order (1 : Fin (N + 5)) <
      a.order (⟨3, by omega⟩ : Fin (N + 5)))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.exists_lemma814InitialFiveScalingData
      A hsecondStrict hthirdFifth with ⟨S⟩
  have hnotC := S.initialFour_not_exceptionC
    A b hresidueTwo hraw
  exact a.beli2019Lemma814_of_initialFour_exceptionC_killed
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    S.transformed original b horder conditions hnotExceptional A houter
      hsecondFourth hnotC

/-- Good-BONG two-step monotonicity leaves exactly the strict and equality
branches treated above. -/
theorem beli2019Lemma814_of_initialFour_exceptionC
    (a original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hraw : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ))
    (hsecondStrict :
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)))
    (houter : a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)))
    (hsecondFourth : a.order (1 : Fin (N + 5)) <
      a.order (⟨3, by omega⟩ : Fin (N + 5))) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  have htwoStepRaw := a.orderSequence.twoStep 2 (by omega)
  have htwoStep : a.order (⟨2, by omega⟩ : Fin (N + 5)) ≤
      a.order (⟨4, by omega⟩ : Fin (N + 5)) := by
    simpa only [orderSequence, BeliOrderSequence.entry] using htwoStepRaw
  rcases lt_or_eq_of_le htwoStep with hstrict | hequal
  · exact a.beli2019Lemma814_of_initialFour_exceptionC_third_lt_fifth
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions hnotExceptional A hresidueTwo hraw
        houter hsecondFourth hstrict
  · exact a.beli2019Lemma814_of_initialFour_exceptionC_third_eq_fifth
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions hnotExceptional A hresidueTwo hraw
        hsecondStrict houter hsecondFourth hequal

/-- The second use of Corollary 8.11 in the paper normalizes the first
binary pair of the initial quaternary lattice.  Its ambient insertion
supplies exactly the determinant and adjacent-defect data required by the
strict/equality dispatcher above. -/
theorem beli2019Lemma814_of_initialFour_exceptionC_normalized
    (a original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour (by omega)).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (C : Beli2019Lemma814ExceptionC
      (a.lemma814InitialFour (by omega)) b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.exists_lemma814HigherRankFirstBinaryData
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) b A halphas C with ⟨D⟩
  let changed := D.transformed
  have horders := a.order_invariant changed
  have horder' : changed.order (0 : Fin (N + 5)) =
      b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 5))]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  have hnotExceptional' : ¬changed.Beli2019Lemma814Exceptional b :=
    fun E ↦ hnotExceptional (hinvariant.mpr E)
  have houter : a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)) := by
    have h := C.firstThirdOrders_eq
    simp only [a.lemma814InitialFour_order_eq (by omega)] at h
    have hzero : (⟨(0 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
        (0 : Fin (N + 5)) := by ext; rfl
    have htwo : (⟨(2 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
        (⟨2, by omega⟩ : Fin (N + 5)) := by ext; rfl
    simpa only [hzero, htwo] using h
  have hsecondFourth : a.order (1 : Fin (N + 5)) <
      a.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    have h := C.secondFourthOrders_lt
    simp only [a.lemma814InitialFour_order_eq (by omega)] at h
    have hone : (⟨(1 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
        (1 : Fin (N + 5)) := by ext; rfl
    have hthree : (⟨(3 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
        (⟨3, by omega⟩ : Fin (N + 5)) := by ext; rfl
    simpa only [hone, hthree] using h
  have houter' : changed.order (0 : Fin (N + 5)) =
      changed.order (⟨2, by omega⟩ : Fin (N + 5)) := by
    rw [← horders (0 : Fin (N + 5)),
      ← horders (⟨2, by omega⟩ : Fin (N + 5))]
    exact houter
  have hsecondFourth' : changed.order (1 : Fin (N + 5)) <
      changed.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    rw [← horders (1 : Fin (N + 5)),
      ← horders (⟨3, by omega⟩ : Fin (N + 5))]
    exact hsecondFourth
  exact changed.beli2019Lemma814_of_initialFour_exceptionC
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b horder' hconditions hnotExceptional' D.alphaData C.residueTwo
      D.firstFourRawDefect_eq_secondAlpha
      D.secondAlpha_lt_thirdAdjacentDefect houter' hsecondFourth'

/-- Complete higher-rank reduction in the strict second/fourth-order case.
Corollary 8.11 first realizes the third alpha on `[a₃,a₄]`.  Local
exceptions (a) and (b) contradict ambient nonexceptionality; if (c) remains,
the second normalization and the two high-rank order branches finish it. -/
theorem beli2019Lemma814_higherRank_of_secondFourth_lt
    (a original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)))
    (hsecondFourth : a.order (1 : Fin (N + 5)) <
      a.order (⟨3, by omega⟩ : Fin (N + 5))) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.beli2019Corollary811
      (⟨2, by omega⟩ : Fin (N + 4)) with ⟨D⟩
  let changed := D.transformed
  have horders := a.order_invariant changed
  have horder' : changed.order (0 : Fin (N + 5)) =
      b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 5))]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  have hnotExceptional' : ¬changed.Beli2019Lemma814Exceptional b :=
    fun E ↦ hnotExceptional (hinvariant.mpr E)
  have houter' : changed.order (0 : Fin (N + 5)) =
      changed.order (⟨2, by omega⟩ : Fin (N + 5)) := by
    rw [← horders (0 : Fin (N + 5)),
      ← horders (⟨2, by omega⟩ : Fin (N + 5))]
    exact houter
  have hsecondFourth' : changed.order (1 : Fin (N + 5)) <
      changed.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    rw [← horders (1 : Fin (N + 5)),
      ← horders (⟨3, by omega⟩ : Fin (N + 5))]
    exact hsecondFourth
  have hthirdBinary : changed.adjacentBinaryAlpha
      (⟨2, by omega⟩ : Fin (N + 4)) =
        (changed.alphaValue
          (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) :=
    D.adjacentBinaryAlpha_eq
  have hlocalAlphas :=
    changed.lemma814InitialFour_alphas_eq (by omega) hthirdBinary
  have hlocalConditions :=
    changed.lemma814InitialFour_conditions b (by omega)
      hlocalAlphas hconditions
  have hnotAB :=
    changed.lemma814InitialFour_not_exceptionAB b (by omega)
      hlocalAlphas hnotExceptional'
  by_cases hC : Beli2019Lemma814ExceptionC
      (changed.lemma814InitialFour (by omega)) b
  · have A :=
      changed.lemma814HigherRankAlphaData_of_initialFour_exceptionC
        b (by omega) hlocalAlphas hnotExceptional' hC
    exact changed.beli2019Lemma814_of_initialFour_exceptionC_normalized
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder' hconditions hnotExceptional' A hlocalAlphas hC
  · have hlocalNotExceptional :
        ¬Beli2019Lemma814Exceptional
          (changed.lemma814InitialFour (by omega)) b := by
      rintro (E | E | E)
      · exact hnotAB.1 E
      · exact hnotAB.2 E
      · exact hC E
    have hlocalOrder : (changed.lemma814InitialFour (by omega)).order
        (0 : Fin 4) = b.order (0 : Fin 1) := by
      rw [changed.lemma814InitialFour_order_eq (by omega)]
      exact horder'
    have hlocalOuter : (changed.lemma814InitialFour (by omega)).order
        (0 : Fin 4) =
          (changed.lemma814InitialFour (by omega)).order (2 : Fin 4) := by
      simp only [changed.lemma814InitialFour_order_eq (by omega)]
      have hzero : (⟨(0 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
          (0 : Fin (N + 5)) := by ext; rfl
      have htwo : (⟨(2 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
          (⟨2, by omega⟩ : Fin (N + 5)) := by ext; rfl
      simpa only [hzero, htwo] using houter'
    have hlocalSecondFourth :
        (changed.lemma814InitialFour (by omega)).order (1 : Fin 4) <
          (changed.lemma814InitialFour (by omega)).order (3 : Fin 4) := by
      simp only [changed.lemma814InitialFour_order_eq (by omega)]
      have hone : (⟨(1 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
          (1 : Fin (N + 5)) := by ext; rfl
      have hthree : (⟨(3 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
          (⟨3, by omega⟩ : Fin (N + 5)) := by ext; rfl
      simpa only [hone, hthree] using hsecondFourth'
    rcases (changed.lemma814InitialFour (by omega)).beli2019Lemma814_rankFour
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW)
        (changed.lemma814InitialFour (by omega)) b hlocalOrder
          hlocalConditions hlocalNotExceptional hlocalOuter
            hlocalSecondFourth with ⟨T⟩
    exact changed.prescribedFirstValueTransform_of_firstFourSegment
      original b (by omega) (changed.lemma814InitialFourSegment (by omega)) T

omit prefixChangeV prefixChangeW
  [DiagonalCodimensionOneCancellationLaws K]
  [DiagonalIsometryInvariantLaws K]
  [DyadicQuaternaryComplementLaws K]
  [DyadicDiagonalClassificationLaws K]
  [DyadicTernaryRepresentationObstructionLaws K] in
/-- If `R₂ = R₄`, the initial quaternary segment has alternating
orders and Lemma 8.3 directly changes its first value to the prescribed
unary value.  The preliminary third-pair normalization identifies the local
first alpha with the ambient one. -/
theorem beli2019Lemma814_higherRank_of_secondFourth_eq
    (a original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)))
    (hsecondFourth : a.order (1 : Fin (N + 5)) =
      a.order (⟨3, by omega⟩ : Fin (N + 5))) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.beli2019Corollary811
      (⟨2, by omega⟩ : Fin (N + 4)) with ⟨D⟩
  let changed := D.transformed
  have horders := a.order_invariant changed
  have horder' : changed.order (0 : Fin (N + 5)) =
      b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 5))]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have houter' : changed.order (0 : Fin (N + 5)) =
      changed.order (⟨2, by omega⟩ : Fin (N + 5)) := by
    rw [← horders (0 : Fin (N + 5)),
      ← horders (⟨2, by omega⟩ : Fin (N + 5))]
    exact houter
  have hsecondFourth' : changed.order (1 : Fin (N + 5)) =
      changed.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    rw [← horders (1 : Fin (N + 5)),
      ← horders (⟨3, by omega⟩ : Fin (N + 5))]
    exact hsecondFourth
  have hthirdBinary : changed.adjacentBinaryAlpha
      (⟨2, by omega⟩ : Fin (N + 4)) =
        (changed.alphaValue
          (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) :=
    D.adjacentBinaryAlpha_eq
  have hlocalAlphas :=
    changed.lemma814InitialFour_alphas_eq (by omega) hthirdBinary
  let s := changed.lemma814InitialFour (by omega)
  have halternating : s.HasQuaternaryAlternatingOrders := by
    constructor
    · simp only [s, changed.lemma814InitialFour_order_eq (by omega)]
      have hzero : (⟨(0 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
          (0 : Fin (N + 5)) := by ext; rfl
      have htwo : (⟨(2 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
          (⟨2, by omega⟩ : Fin (N + 5)) := by ext; rfl
      simpa only [hzero, htwo] using houter'
    · simp only [s, changed.lemma814InitialFour_order_eq (by omega)]
      have hone : (⟨(1 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
          (1 : Fin (N + 5)) := by ext; rfl
      have hthree : (⟨(3 : Fin 4).1, by omega⟩ : Fin (N + 5)) =
          (⟨3, by omega⟩ : Fin (N + 5)) := by ext; rfl
      simpa only [hone, hthree] using hsecondFourth'
  let epsilon := changed.lemma814Epsilon b
  have hepsilonUnit : IsValuationUnit K (epsilon : K) :=
    changed.lemma814Epsilon_isValuationUnit b horder'
  have hepsilonDefect : (s.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) epsilon := by
    have hbound := changed.alpha_le_lemma814EpsilonDefect b hconditions
    have hzero : (⟨(0 : Fin 3).1, by omega⟩ : Fin (N + 4)) =
        (0 : Fin (N + 4)) := by ext; rfl
    rw [hlocalAlphas (0 : Fin 3), hzero]
    exact hbound
  rcases s.beli2019Lemma83 halternating epsilon hepsilonUnit
      hepsilonDefect with ⟨c, hc⟩
  have hsFirst : s.valueUnit (0 : Fin 4) =
      changed.valueUnit (0 : Fin (N + 5)) := by
    have h := changed.lemma814InitialFour_valueUnit_eq
      (by omega) (0 : Fin 4)
    convert h using 1
    congr 1
  have hfirst : c.valueUnit (0 : Fin 4) = b.valueUnit (0 : Fin 1) := by
    calc
      c.valueUnit (0 : Fin 4) = epsilon * s.valueUnit (0 : Fin 4) := hc
      _ = epsilon * changed.valueUnit (0 : Fin (N + 5)) :=
        congrArg (epsilon * ·) hsFirst
      _ = b.valueUnit (0 : Fin 1) :=
        changed.lemma814Epsilon_mul_firstValue b
  let T : s.Beli2019PrescribedFirstValueTransform b := {
    transformed := c
    firstValue_eq := hfirst
  }
  exact changed.prescribedFirstValueTransform_of_firstFourSegment
    original b (by omega) (changed.lemma814InitialFourSegment (by omega)) T

/-- Good-BONG two-step monotonicity gives `R₂ ≤ R₄`; the equality
case is Lemma 8.3 and the strict case is the completed high-rank reduction. -/
theorem beli2019Lemma814_higherRank_equalOuter
    (a original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5))) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  have htwoStepRaw := a.orderSequence.twoStep 1 (by omega)
  have htwoStep : a.order (1 : Fin (N + 5)) ≤
      a.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    change a.order ⟨1, by omega⟩ ≤ a.order ⟨1 + 2, by omega⟩ at htwoStepRaw
    convert htwoStepRaw using 1
    congr 1
  rcases lt_or_eq_of_le htwoStep with hstrict | hequal
  · exact a.beli2019Lemma814_higherRank_of_secondFourth_lt
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions hnotExceptional houter hstrict
  · exact a.beli2019Lemma814_higherRank_of_secondFourth_eq
      (classificationV := classificationV)
      (classificationW := classificationW)
      original b horder conditions houter hequal

end HigherRankBranches

end BONG.GoodBONG

end Bong
