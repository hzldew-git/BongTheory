/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Choice
import Bong.Bong.GoodBONGScalarAgreement
import Bong.Bong.Beli2019Lemma93TailAlpha

/-!
# Beli (2019), Lemma 8.8: induction decomposition

The first step of the induction is the exact formula

`α₁(M) = min (α₁([a₁,a₂])) (R₂ - R₁ + α₁(M*))`.

This file identifies the canonical suffix segment in Corollary 2.5(ii) with
the recursive projected tail and then derives that two-term minimum formula.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The full suffix segment beginning with the second BONG vector has the
same scalar sequence as the recursive projected tail. -/
theorem suffixAlphaSegmentWitness_zero_scalarAgreement
    (b : GoodBONG q L (N + 3)) :
    ScalarAgreement
      ((b.suffixAlphaSegmentWitness (n := N + 1)
        (0 : Fin (N + 2)) (by
          show 1 < N + 2
          omega)).toGoodBONG b.good)
      b.tail := by
  let w := b.suffixAlphaSegmentWitness (n := N + 1)
    (0 : Fin (N + 2)) (by
      show 1 < N + 2
      omega)
  refine ⟨?_⟩
  intro i
  change w.bong.valueUnit i = b.tail.valueUnit i
  calc
    w.bong.valueUnit i = b.valueUnit (w.sourceIndex i) := w.valueUnit_eq i
    _ = b.valueUnit i.succ := by
      congr 1
      apply Fin.ext
      change 1 + i.1 = i.1 + 1
      omega
    _ = b.tail.valueUnit i := (b.valueUnit_goodTail i).symm

/-- The suffix term in Corollary 2.5(ii), at the first alpha index, is the
first order gap plus the first alpha of the recursive tail. -/
theorem suffixSegmentAlphaCandidate_zero_eq_orderGap_add_tailAlpha
    (b : GoodBONG q L (N + 3)) :
    b.suffixSegmentAlphaCandidate (n := N + 1)
        (0 : Fin (N + 2)) (by
          show 1 < N + 2
          omega) =
      (((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) : WithTop ℚ) +
        (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
  let i : Fin (N + 2) := 0
  let hi : i.1 + 1 < N + 2 := by
    dsimp [i]
    omega
  let w := b.suffixAlphaSegmentWitness (n := N + 1) i hi
  have hscalar := b.suffixAlphaSegmentWitness_zero_scalarAgreement
  have halpha := hscalar.alphaValue_eq (0 : Fin (N + 1))
  unfold suffixSegmentAlphaCandidate rightCompressionValue
  change
    ((((b.order
        (suffixAlphaLocalizationIndex i hi).pivotFin.castSucc -
          b.order i.castSucc : Int) : ℚ) +
        (w.toGoodBONG b.good).alphaValue
          (suffixAlphaLocalizationIndex i hi).localPivot : ℚ) : WithTop ℚ) =
      ((((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) +
        b.tail.alphaValue (0 : Fin (N + 1)) : ℚ) : WithTop ℚ)
  apply congrArg (fun x : ℚ => (x : WithTop ℚ))
  have hpivot :
      (suffixAlphaLocalizationIndex i hi).pivotFin.castSucc =
        (0 : Fin (N + 2)).succ := by
    apply Fin.ext
    rfl
  have hlocal :
      (suffixAlphaLocalizationIndex i hi).localPivot =
        (0 : Fin (N + 1)) := by
    apply Fin.ext
    rfl
  rw [hpivot, hlocal]
  dsimp [i]
  change
    (((b.order (0 : Fin (N + 2)).succ -
        b.order (0 : Fin (N + 2)).castSucc : Int) : ℚ) +
      (w.toGoodBONG b.good).alphaValue (0 : Fin (N + 1))) = _
  rw [halpha]
  unfold orderGap
  norm_num
  rfl

/-- The exact first-index induction formula used in Lemma 8.8:
the global alpha is the minimum of the first binary alpha and the first order
gap plus the alpha of the projected tail. -/
theorem alpha_zero_eq_min_firstBinary_orderGap_add_tailAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (b : GoodBONG q L (N + 3)) :
    (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) =
      min b.firstBinaryAlpha
        ((((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) : WithTop ℚ) +
          (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ)) := by
  rw [b.coe_alphaValue]
  rw [b.beli2009Corollary25_ii (n := N + 1) (0 : Fin (N + 2))]
  unfold segmentRecursiveAlphaCandidates prefixSegmentAlphaCandidates
    suffixSegmentAlphaCandidates firstBinaryAlpha
  simp [b.suffixSegmentAlphaCandidate_zero_eq_orderGap_add_tailAlpha,
    min_assoc]

/-- If the raw first adjacent defect is no larger than the tail alpha, the
global first alpha is already realized by the first binary segment. -/
theorem firstBinaryAlpha_eq_alpha_of_adjacentDefect_le_tailAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hle : b.adjacentDefect (0 : Fin (N + 2)) ≤
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ)) :
    b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
  have hleft :
      b.leftDefectCandidate (0 : Fin (N + 2)) (0 : Fin (N + 2)) ≤
        (((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) : WithTop ℚ) +
          (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    unfold leftDefectCandidate orderGap
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).2 hle
  have hbinary : b.firstBinaryAlpha ≤
      (((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) : WithTop ℚ) +
        (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) :=
    (min_le_right _ _).trans hleft
  rw [b.alpha_zero_eq_min_firstBinary_orderGap_add_tailAlpha,
    min_eq_left hbinary]

/-- In the strict-tail case, strictness of the global alpha below the
half-gap forces the tail term to be the minimum in the induction formula. -/
theorem alpha_zero_eq_orderGap_add_tailAlpha_of_tailAlpha_lt_adjacentDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (htail :
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
        b.adjacentDefect (0 : Fin (N + 2)))
    (hstrict : b.alphaValue (0 : Fin (N + 2)) <
      b.halfGapValue (0 : Fin (N + 2))) :
    (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) =
      (((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) : WithTop ℚ) +
        (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
  let tailTerm : WithTop ℚ :=
    (((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) : WithTop ℚ) +
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ)
  have htailLeft : tailTerm <
      b.leftDefectCandidate (0 : Fin (N + 2)) (0 : Fin (N + 2)) := by
    dsimp only [tailTerm]
    unfold leftDefectCandidate orderGap
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).2 htail
  have hstrictTop :
      (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
        b.halfGapCandidate (0 : Fin (N + 2)) := by
    rw [← b.coe_halfGapValue]
    exact_mod_cast hstrict
  have htailHalf : tailTerm <
      b.halfGapCandidate (0 : Fin (N + 2)) := by
    by_contra hnot
    have hhalfTail : b.halfGapCandidate (0 : Fin (N + 2)) ≤ tailTerm :=
      le_of_not_gt hnot
    have hhalfLeft : b.halfGapCandidate (0 : Fin (N + 2)) ≤
        b.leftDefectCandidate (0 : Fin (N + 2)) (0 : Fin (N + 2)) :=
      hhalfTail.trans htailLeft.le
    have hbinaryHalf : b.firstBinaryAlpha =
        b.halfGapCandidate (0 : Fin (N + 2)) := by
      unfold firstBinaryAlpha
      rw [min_eq_left hhalfLeft]
    have hformula := b.alpha_zero_eq_min_firstBinary_orderGap_add_tailAlpha
    rw [show
        (((b.orderGap (0 : Fin (N + 2)) : Int) : ℚ) : WithTop ℚ) +
            (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) = tailTerm
          by rfl,
      hbinaryHalf, min_eq_left hhalfTail] at hformula
    exact (ne_of_lt hstrictTop) hformula
  have htailBinary : tailTerm < b.firstBinaryAlpha := by
    unfold firstBinaryAlpha
    exact lt_min htailHalf htailLeft
  rw [b.alpha_zero_eq_min_firstBinary_orderGap_add_tailAlpha]
  change min b.firstBinaryAlpha tailTerm = tailTerm
  exact min_eq_right htailBinary.le

/-- In the first numerical branch of the induction, the first adjacent
defect is no larger than the tail alpha.  Hence the global first alpha is
already binary, and the strict binary theorem supplies the required
first-value transformation. -/
theorem beli2019Lemma88_strict_of_adjacentDefect_le_tailAlpha
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hle : b.adjacentDefect (0 : Fin (N + 2)) ≤
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hstrict : b.alphaValue (0 : Fin (N + 2)) <
      b.halfGapValue (0 : Fin (N + 2))) :
    Nonempty b.Beli2019FirstValueTransform := by
  apply b.beli2019Lemma88_strict_binary
  · exact b.firstBinaryAlpha_eq_alpha_of_adjacentDefect_le_tailAlpha hle
  · exact hstrict

/-- The recursive strict-tail branch of Beli (2019), Lemma 8.8.  A
first-value transformation of the projected tail is lifted with the head
fixed.  Exact defect domination then makes the transformed first binary
alpha equal to the original global alpha, so the strict binary theorem can
be applied once more. -/
theorem beli2019Lemma88_strict_tail_of_tailTransform
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (htail :
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
        b.adjacentDefect (0 : Fin (N + 2)))
    (hstrict : b.alphaValue (0 : Fin (N + 2)) <
      b.halfGapValue (0 : Fin (N + 2)))
    (T : b.tail.Beli2019FirstValueTransform) :
    Nonempty b.Beli2019FirstValueTransform := by
  rcases b.tailReplacementData_of_firstValueTransform T with ⟨D⟩
  have hglobal :=
    b.alpha_zero_eq_orderGap_add_tailAlpha_of_tailAlpha_lt_adjacentDefect
      htail hstrict
  have hbinaryOriginal :=
    D.firstBinaryAlpha_eq_of_strict_tail htail hglobal
  have halphas := b.alpha_invariant D.transformed
  have hbinary : D.transformed.firstBinaryAlpha =
      (D.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    calc
      D.transformed.firstBinaryAlpha =
          (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := hbinaryOriginal
      _ = (D.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) :=
        congrArg (fun x : ℚ => (x : WithTop ℚ))
          (halphas (0 : Fin (N + 2)))
  have horders := b.order_invariant D.transformed
  have hhalf : D.transformed.halfGapValue (0 : Fin (N + 2)) =
      b.halfGapValue (0 : Fin (N + 2)) := by
    unfold halfGapValue orderGap
    rw [← horders (0 : Fin (N + 2)).succ,
      ← horders (0 : Fin (N + 2)).castSucc]
  have hstrictTransformed :
      D.transformed.alphaValue (0 : Fin (N + 2)) <
        D.transformed.halfGapValue (0 : Fin (N + 2)) := by
    rw [← halphas (0 : Fin (N + 2)), hhalf]
    exact hstrict
  rcases D.transformed.beli2019Lemma88_strict_binary hbinary
      hstrictTransformed with ⟨S⟩
  exact ⟨D.compose_firstValueTransform S⟩

end BONG.GoodBONG

end Bong
