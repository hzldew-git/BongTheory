/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalDefect
import Bong.Bong.BeliUniversalEndpoint
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha
import Bong.Dyadic.HilbertNondegeneracyProof

/-!
# The unary defect criterion in Beli's universal-lattice theorem

This file proves Beli's Lemma 2.10.  The auxiliary Case II' is the form used
inside the proof: `alpha_1 = 1` and the adjacent defect has its sharp value.
The ambient line-universality assumption is used only to exclude rank two in
that branch; it is not hidden in the definition of the case.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The temporary alternative II(a') in the proof of Theorem 2.1. -/
def UniversalCaseIIPrime {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  0 < tail ∧
    a.alphaValue (0 : Fin (tail + 1)) = 1 ∧
    a.truncatedPrefixDefect a (-1) 0 2 =
      ((((1 : ℚ) - (a.orderGap (0 : Fin (tail + 1)) : ℚ)) : ℚ) :
        WithTop ℚ)

/-- Condition (ii) of Lemma 2.3 for every unary target of order zero or one. -/
def UniversalUnaryDefectConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  ∀ b : Kˣ, ordUnit K b = 0 ∨ ordUnit K b = 1 →
    a.RepresentationDefectCondition (BONG.unaryModelGoodBONG b)

/-- A binary quadratic space which represents every nonzero line has square
negative determinant.  The proof chooses a Hilbert-symbol obstruction to a
nonsquare determinant and contradicts line universality. -/
theorem firstTwoSignedProduct_isSquare_of_isLineUniversal_rankTwo
    (a : GoodBONG q L 2) (hline : q.IsLineUniversal) :
    IsSquare (-(a.valueUnit 0 * a.valueUnit 1)) := by
  by_contra hnotSquare
  obtain ⟨z, hz⟩ :=
    exists_hilbertSymbol_eq_neg_one_of_not_isSquare_proved
      (-(a.valueUnit 0 * a.valueUnit 1)) hnotSquare
  let b : Kˣ := z * a.valueUnit 0
  have hambient :
      q.Represents
        (QuadraticSpace.rescaleUnit b (QuadraticSpace.line K)) := hline b
  have hdiagonal : DiagonalRepresents
      (BONG.unaryModelBONG b).value a.toBONG.value :=
    a.toBONG.diagonalRepresents_of_ambient (BONG.unaryModelBONG b) hambient
  have hbinary : DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (Fin.cons (a.valueUnit 0 : K)
        (fun _ : Fin 1 ↦ (a.valueUnit 1 : K))) := by
    convert hdiagonal using 1 <;> funext i
    · fin_cases i
      exact (BONG.unaryModelBONG_value b 0).symm
    · fin_cases i <;> rfl
  have hone :=
    (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
      (a.valueUnit 0) (a.valueUnit 1) b).mp hbinary
  have hratio : b * (a.valueUnit 0)⁻¹ = z := by
    dsimp only [b]
    group
  rw [hratio, hilbertSymbol_comm K] at hone
  rw [hz] at hone
  norm_num at hone

/-- A binary quadratic space which represents every nonzero line is
isotropic. -/
theorem firstTwoIsotropic_of_isLineUniversal_rankTwo
    (a : GoodBONG q L 2) (hline : q.IsLineUniversal) :
    a.UniversalFirstTwoIsotropic := by
  have hsquare :=
    a.firstTwoSignedProduct_isSquare_of_isLineUniversal_rankTwo hline
  have hisotropic := diagonalBinary_isotropic_of_isSquare_neg_product
    (a.valueUnit 0) (a.valueUnit 1) hsquare
  change DiagonalIsotropic (a.prefixValues 2 (by omega))
  convert hisotropic using 1
  funext i
  fin_cases i <;> rfl

/-- At rank two both prefix caps are endpoints, so the adjacent capped
defect is the ordinary defect of the negative determinant. -/
theorem rankTwo_adjacentDefect_eq_defectOrder_signedProduct
    (a : GoodBONG q L 2) :
    a.truncatedPrefixDefect a (-1) 0 2 =
      defectOrder (K := K) (-(a.valueUnit 0 * a.valueUnit 1)) := by
  have hzero : a.prefixProduct 0 = 1 := by
    exact a.toBONG.prefixProduct_zero
  have hone : a.prefixProduct 1 = a.valueUnit 0 := by
    calc
      a.prefixProduct 1 =
          a.prefixProduct 0 * a.valueUnit (0 : Fin 2) := by
        exact a.toBONG.prefixProduct_succ 0 (by omega)
      _ = a.valueUnit 0 := by rw [hzero, one_mul]
  have htwo : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    calc
      a.prefixProduct 2 =
          a.prefixProduct 1 * a.valueUnit (1 : Fin 2) := by
        exact a.toBONG.prefixProduct_succ 1 (by omega)
      _ = a.valueUnit 0 * a.valueUnit 1 := by rw [hone]
  have hcap : a.prefixAlphaCap 2 = ⊤ := by
    change a.prefixAlphaCap (1 + 1) = ⊤
    exact a.prefixAlphaCap_last
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_zero, hcap, hzero, htwo]
  simp

/-- The alpha value at the first boundary is either zero or one as soon as
the unit-target defect conditions hold. -/
theorem first_alphaValue_eq_zero_or_one_of_universalUnaryDefectConditions
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (hdefect : a.UniversalUnaryDefectConditions) :
    a.alphaValue (0 : Fin (tail + 1)) = 0 ∨
      a.alphaValue (0 : Fin (tail + 1)) = 1 := by
  have hunit : ∀ b : Kˣ, ordUnit K b = 0 →
      (a.representationAlphaValue (BONG.unaryModelGoodBONG b)
          (unaryRepresentationIndex tail) : WithTop ℚ) ≤
        a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) 1 1 1 := by
    intro b hb
    exact (a.unary_representationDefectCondition_iff b).mp
      (hdefect b (Or.inl hb))
  have halphaLe : a.alphaValue (0 : Fin (tail + 1)) ≤ 1 :=
    (a.universalUnitDefectConditions_iff_alphaValue_le_one hzero).mp hunit
  by_cases halphaZero : a.alphaValue (0 : Fin (tail + 1)) = 0
  · exact Or.inl halphaZero
  · right
    letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
    letI : Beli2009AlphaParityLaws.{u, v} K :=
      beliUniversalAlphaParityLaws
    have halphaOne : (1 : ℚ) ≤ a.alphaValue (0 : Fin (tail + 1)) :=
      a.one_le_alphaValue_of_ne_zero (0 : Fin (tail + 1)) halphaZero
    linarith

/-- With `R_1 = 0`, the sharp adjacent defect makes the unary primary
candidate vanish for every target of order one. -/
theorem unary_representationPrimaryDefect_eq_zero_of_sharp
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (b : Kˣ) (hb : ordUnit K b = 1)
    (hsharp : a.truncatedPrefixDefect a (-1) 0 2 =
      ((((1 : ℚ) - (a.orderGap (0 : Fin (tail + 1)) : ℚ)) : ℚ) :
        WithTop ℚ)) :
    a.representationPrimaryDefect (BONG.unaryModelGoodBONG b)
        (unaryRepresentationIndex tail) = 0 := by
  rw [a.unary_representationPrimaryDefect_eq b, hsharp, hb,
    ← WithTop.coe_add]
  apply WithTop.coe_eq_coe.mpr
  unfold orderGap
  push_cast
  change (a.order 1 : ℚ) - 1 +
    (1 - ((a.order 1 : ℚ) - (a.order 0 : ℚ))) = 0
  rw [hzero]
  ring

/-- Beli, Lemma 2.10.  Under ambient universality and `R_1 = 0`, condition
(ii) for all unary targets of order zero or one is equivalent to I(a) or to
the temporary alternative II(a'). -/
theorem universalUnaryDefectConditions_iff_alphaZero_or_caseIIPrime
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (hline : q.IsLineUniversal) :
    a.UniversalUnaryDefectConditions ↔
      a.alphaValue (0 : Fin (tail + 1)) = 0 ∨
        a.UniversalCaseIIPrime := by
  constructor
  · intro hdefect
    rcases a.first_alphaValue_eq_zero_or_one_of_universalUnaryDefectConditions
      hzero hdefect with halphaZero | halphaOne
    · exact Or.inl halphaZero
    · right
      have hconsequences :=
        a.alphaValue_eq_one_consequences (0 : Fin (tail + 1)) halphaOne
      have hsharp : a.truncatedPrefixDefect a (-1) 0 2 =
          ((((1 : ℚ) -
            (a.orderGap (0 : Fin (tail + 1)) : ℚ)) : ℚ) : WithTop ℚ) := by
        by_contra hnotSharp
        have hendpoint :
            a.orderGap (0 : Fin (tail + 1)) =
              2 - 2 * (ramificationIndex K : Int) := by
          by_contra hnotEndpoint
          exact hnotSharp (hconsequences.2.2.2 hnotEndpoint)
        have hstrict :
            ((((1 : ℚ) -
              (a.orderGap (0 : Fin (tail + 1)) : ℚ)) : ℚ) : WithTop ℚ) <
              a.truncatedPrefixDefect a (-1) 0 2 :=
          lt_of_le_of_ne hconsequences.2.2.1
            (fun h ↦ hnotSharp h.symm)
        let b : Kˣ := uniformizerPowerUnit K (1 : Int)
        have hb : ordUnit K b = 1 := by
          exact ordUnit_uniformizerPowerUnit (K := K) (1 : Int)
        have horder : a.order 0 ≤ ordUnit K b := by
          rw [hzero, hb]
          omega
        have hboundary :=
          (a.unary_representationDefectCondition_iff b).mp
            (hdefect b (Or.inr hb))
        have hcondition :=
          (a.unary_defectCondition_iff_defectOrder b horder).mp hboundary
        have haOrder : ordUnit K (a.valueUnit 0) = 0 := by
          calc
            ordUnit K (a.valueUnit 0) = a.order 0 := by
              simpa only [GoodBONG.order, GoodBONG.valueUnit] using
                (a.toBONG.order_eq_ordUnit (0 : Fin (tail + 2))).symm
            _ = 0 := hzero
        have hproductOdd : Odd (ordUnit K (a.valueUnit 0 * b)) := by
          rw [ordUnit_mul, haOrder, hb, zero_add]
          exact odd_one
        have hrawZero : defectOrder (K := K) (a.valueUnit 0 * b) = 0 := by
          unfold defectOrder
          rw [quadraticDefect_eq_zero_of_odd_ordUnit
            (a.valueUnit 0 * b) hproductOdd]
          rfl
        rw [hrawZero] at hcondition
        have hsecond : a.order 1 =
            2 - 2 * (ramificationIndex K : Int) := by
          calc
            a.order 1 = a.orderGap (0 : Fin (tail + 1)) := by
              unfold orderGap
              change a.order 1 = a.order 1 - a.order 0
              rw [hzero]
              omega
            _ = 2 - 2 * (ramificationIndex K : Int) := hendpoint
        have hpositive : (0 : WithTop ℚ) <
            (a.representationAlphaValue (BONG.unaryModelGoodBONG b)
              (unaryRepresentationIndex tail) : WithTop ℚ) := by
          rw [a.coe_representationAlphaValue,
            a.representationAlpha_eq_min_halfGap_prime,
            a.unary_representationAlphaPrime_eq_primary b,
            a.unary_representationHalfGap_eq b,
            a.unary_representationPrimaryDefect_eq b]
          apply lt_min
          · norm_cast
            rw [hb, hsecond]
            have hcast :
                ((2 - 2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) =
                  1 - 2 * (ramificationIndex K : ℚ) := by
              push_cast
              ring
            simp only [Rat.divInt_eq_div]
            rw [hcast]
            ring_nf
            norm_num
          · have hcancel :
                ((((a.order 1 - ordUnit K b : Int) : ℚ) : WithTop ℚ) +
                    ((((1 : ℚ) -
                      (a.orderGap (0 : Fin (tail + 1)) : ℚ)) : ℚ) :
                        WithTop ℚ)) = 0 := by
                rw [← WithTop.coe_add]
                apply WithTop.coe_eq_coe.mpr
                unfold orderGap
                push_cast
                change (a.order 1 : ℚ) - (ordUnit K b : ℚ) +
                  (1 - ((a.order 1 : ℚ) - (a.order 0 : ℚ))) = 0
                rw [hzero, hb]
                ring
            calc
              (0 : WithTop ℚ) =
                  ((((a.order 1 - ordUnit K b : Int) : ℚ) : WithTop ℚ) +
                    ((((1 : ℚ) -
                      (a.orderGap (0 : Fin (tail + 1)) : ℚ)) : ℚ) :
                        WithTop ℚ)) := hcancel.symm
              _ < ((((a.order 1 - ordUnit K b : Int) : ℚ) : WithTop ℚ) +
                    a.truncatedPrefixDefect a (-1) 0 2) :=
                WithTop.add_lt_add_left WithTop.coe_ne_top hstrict
        exact (not_lt_of_ge hcondition hpositive).elim
      have htail : 0 < tail := by
        by_contra hnotPositive
        have htailZero : tail = 0 := Nat.eq_zero_of_not_pos hnotPositive
        subst tail
        have hsquare :=
          a.firstTwoSignedProduct_isSquare_of_isLineUniversal_rankTwo hline
        rw [a.rankTwo_adjacentDefect_eq_defectOrder_signedProduct,
          defectOrder_eq_top_of_isSquare hsquare] at hsharp
        have hfinite :
            ((((1 : ℚ) - (a.orderGap (0 : Fin (0 + 1)) : ℚ)) : ℚ) :
              WithTop ℚ) ≠ ⊤ := WithTop.coe_ne_top
        exact hfinite hsharp.symm
      exact ⟨htail, halphaOne, hsharp⟩
  · rintro (halphaZero | hcase) b hb
    · have horder : a.order 0 ≤ ordUnit K b := by
        rcases hb with hb | hb
        · rw [hzero, hb]
        · rw [hzero, hb]
          omega
      rw [a.unary_representationDefectCondition_iff,
        a.unary_defectCondition_iff_defectOrder b horder]
      have hA := a.alphaValue_ge_unaryRepresentationAlphaValue b horder
      rw [halphaZero] at hA
      exact (WithTop.coe_le_coe.mpr hA).trans (defectOrder_nonneg _)
    · have horder : a.order 0 ≤ ordUnit K b := by
        rcases hb with hb | hb
        · rw [hzero, hb]
        · rw [hzero, hb]
          omega
      rw [a.unary_representationDefectCondition_iff,
        a.unary_defectCondition_iff_defectOrder b horder]
      rcases hb with hbZero | hbOne
      · have hAeq :=
          a.alphaValue_eq_unaryRepresentationAlphaValue_of_order_eq b
            (hzero.trans hbZero.symm)
        rw [hAeq, hcase.2.1]
        have haOrder : ordUnit K (a.valueUnit 0) = 0 := by
          calc
            ordUnit K (a.valueUnit 0) = a.order 0 := by
              simpa only [GoodBONG.order, GoodBONG.valueUnit] using
                (a.toBONG.order_eq_ordUnit (0 : Fin (tail + 2))).symm
            _ = 0 := hzero
        apply defectOrder_one_le_of_even
        rw [ordUnit_mul, haOrder, hbZero, zero_add]
        exact Even.zero
      · have hprimary :=
          a.unary_representationPrimaryDefect_eq_zero_of_sharp
            hzero b hbOne hcase.2.2
        have hAle :
            (a.representationAlphaValue (BONG.unaryModelGoodBONG b)
              (unaryRepresentationIndex tail) : WithTop ℚ) ≤ 0 := by
          rw [a.coe_representationAlphaValue,
            a.representationAlpha_eq_min_halfGap_prime,
            a.unary_representationAlphaPrime_eq_primary b, hprimary]
          exact min_le_right _ _
        have haOrder : ordUnit K (a.valueUnit 0) = 0 := by
          calc
            ordUnit K (a.valueUnit 0) = a.order 0 := by
              simpa only [GoodBONG.order, GoodBONG.valueUnit] using
                (a.toBONG.order_eq_ordUnit (0 : Fin (tail + 2))).symm
            _ = 0 := hzero
        have hproductOdd : Odd (ordUnit K (a.valueUnit 0 * b)) := by
          rw [ordUnit_mul, haOrder, hbOne, zero_add]
          exact odd_one
        have hrawZero : defectOrder (K := K) (a.valueUnit 0 * b) = 0 := by
          unfold defectOrder
          rw [quadraticDefect_eq_zero_of_odd_ordUnit
            (a.valueUnit 0 * b) hproductOdd]
          rfl
        rw [hrawZero]
        exact hAle

end BONG.GoodBONG

end Bong
