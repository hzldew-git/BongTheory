/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalAlpha
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm
import Bong.Bong.Beli2019UnitDefectSpectrumProof

/-!
# The first unary defect condition in Beli's universal criterion

This file proves Lemmas 2.6 and 2.7 of Beli's paper.  The first result compares
the source invariant `alpha_1` with the representation invariant `A_1`; the
second quantifies over all unary unit targets and identifies the sharp bound
`alpha_1 <= 1`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- At the first unary boundary, the auxiliary representation invariant has
only its primary candidate. -/
theorem unary_representationAlphaPrime_eq_primary
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (b : Kˣ) :
    a.representationAlphaPrime (BONG.unaryModelGoodBONG b)
        (unaryRepresentationIndex tail) =
      a.representationPrimaryDefect (BONG.unaryModelGoodBONG b)
        (unaryRepresentationIndex tail) := by
  apply a.representationAlphaPrime_eq_primary_of_not_interior
  simp [unaryRepresentationIndex]

/-- The capped defect in the first unary primary candidate is the adjacent
source defect occurring in the formula for `alpha_1`. -/
theorem unary_primary_cappedDefect_eq_adjacent
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (b : Kˣ) :
    a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 2 0 =
      a.truncatedPrefixDefect a (-1) 0 2 := by
  rw [a.truncatedPrefixDefect_zero_right_eq_self]
  exact a.truncatedPrefixDefect_comm a (-1) 2 0

/-- Explicit half-gap candidate at the unary boundary. -/
theorem unary_representationHalfGap_eq
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (b : Kˣ) :
    a.representationHalfGap (BONG.unaryModelGoodBONG b)
        (unaryRepresentationIndex tail) =
      (((((a.order 1 - ordUnit K b : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
  unfold representationHalfGap unaryRepresentationIndex
  change
    (((((a.order (1 : Fin (tail + 2)) -
      (BONG.unaryModelGoodBONG b).order (0 : Fin 1) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) = _
  rw [BONG.unaryModelGoodBONG_order]

/-- Explicit primary defect candidate at the unary boundary. -/
theorem unary_representationPrimaryDefect_eq
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (b : Kˣ) :
    a.representationPrimaryDefect (BONG.unaryModelGoodBONG b)
        (unaryRepresentationIndex tail) =
      ((((a.order 1 - ordUnit K b : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) 0 2) := by
  unfold representationPrimaryDefect unaryRepresentationIndex
  change
    ((((a.order (1 : Fin (tail + 2)) -
      (BONG.unaryModelGoodBONG b).order (0 : Fin 1) : Int) : ℚ) :
        WithTop ℚ) +
      a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 2 0) = _
  rw [BONG.unaryModelGoodBONG_order]
  rw [a.unary_primary_cappedDefect_eq_adjacent b]

/-- The local formula for the first source alpha, with all `Fin` casts
normalized to the first two displayed orders. -/
theorem first_alphaValue_formula
    {tail : Nat} (a : GoodBONG q L (tail + 2)) :
    (a.alphaValue 0 : WithTop ℚ) =
      min
        (((((a.order 1 - a.order 0 : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
        ((((a.order 1 - a.order 0 : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a (-1) 0 2) := by
  rw [a.alpha_eq_min_halfGap_add_cappedAdjacent,
    ← a.coe_halfGapValue]
  change min
    (((((a.order (1 : Fin (tail + 2)) - a.order (0 : Fin (tail + 2)) :
      Int) : ℚ) / 2 + (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
    ((((a.order (1 : Fin (tail + 2)) - a.order (0 : Fin (tail + 2)) :
      Int) : ℚ) : WithTop ℚ) + a.truncatedPrefixDefect a (-1) 0 2) = _
  rfl

/-- Beli, Lemma 2.6, first assertion: increasing the unary target order can
only decrease the representation invariant `A_1`. -/
theorem alphaValue_ge_unaryRepresentationAlphaValue
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (b : Kˣ)
    (horder : a.order 0 ≤ ordUnit K b) :
    a.representationAlphaValue (BONG.unaryModelGoodBONG b)
        (unaryRepresentationIndex tail) ≤ a.alphaValue 0 := by
  rw [← WithTop.coe_le_coe]
  rw [a.coe_representationAlphaValue,
    a.representationAlpha_eq_min_halfGap_prime,
    a.unary_representationAlphaPrime_eq_primary b,
    a.unary_representationHalfGap_eq b,
    a.unary_representationPrimaryDefect_eq b,
    a.first_alphaValue_formula]
  apply min_le_min
  · apply WithTop.coe_le_coe.mpr
    push_cast
    have horderQ : (a.order 0 : ℚ) ≤ (ordUnit K b : ℚ) := by
      exact_mod_cast horder
    linarith
  · have hcoefficient :
        ((((a.order 1 - ordUnit K b : Int) : ℚ) : WithTop ℚ)) ≤
          (((a.order 1 - a.order 0 : Int) : ℚ) : WithTop ℚ) := by
      apply WithTop.coe_le_coe.mpr
      exact_mod_cast (sub_le_sub_left horder (a.order 1))
    simpa only [add_comm] using
      add_le_add_right hcoefficient
        (a.truncatedPrefixDefect a (-1) 0 2)

/-- Beli, Lemma 2.6, equality assertion. -/
theorem alphaValue_eq_unaryRepresentationAlphaValue_of_order_eq
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (b : Kˣ)
    (horder : a.order 0 = ordUnit K b) :
    a.representationAlphaValue (BONG.unaryModelGoodBONG b)
        (unaryRepresentationIndex tail) = a.alphaValue 0 := by
  rw [← WithTop.coe_eq_coe]
  rw [a.coe_representationAlphaValue,
    a.representationAlpha_eq_min_halfGap_prime,
    a.unary_representationAlphaPrime_eq_primary b,
    a.unary_representationHalfGap_eq b,
    a.unary_representationPrimaryDefect_eq b,
    a.first_alphaValue_formula]
  congr 1
  · apply WithTop.coe_eq_coe.mpr
    congr 2
    exact_mod_cast (congrArg (fun z : Int ↦ a.order 1 - z) horder).symm
  · congr 1
    apply WithTop.coe_eq_coe.mpr
    exact_mod_cast (congrArg (fun z : Int ↦ a.order 1 - z) horder).symm

/-- Under the order comparison of Lemma 2.6, the capped defect condition is
equivalent to the corresponding uncapped quadratic-defect inequality. -/
theorem unary_defectCondition_iff_defectOrder
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (b : Kˣ)
    (horder : a.order 0 ≤ ordUnit K b) :
    ((a.representationAlphaValue (BONG.unaryModelGoodBONG b)
          (unaryRepresentationIndex tail) : WithTop ℚ) ≤
        a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) 1 1 1) ↔
      ((a.representationAlphaValue (BONG.unaryModelGoodBONG b)
          (unaryRepresentationIndex tail) : WithTop ℚ) ≤
        defectOrder (K := K) (a.valueUnit 0 * b)) := by
  let A := (a.representationAlphaValue (BONG.unaryModelGoodBONG b)
    (unaryRepresentationIndex tail) : WithTop ℚ)
  have hAalpha : A ≤ (a.alphaValue 0 : WithTop ℚ) := by
    change (a.representationAlphaValue (BONG.unaryModelGoodBONG b)
      (unaryRepresentationIndex tail) : WithTop ℚ) ≤
        (a.alphaValue 0 : WithTop ℚ)
    exact WithTop.coe_le_coe.mpr
      (a.alphaValue_ge_unaryRepresentationAlphaValue b horder)
  have htargetCap :
      (BONG.unaryModelGoodBONG b).prefixAlphaCap 1 = ⊤ := by
    exact (BONG.unaryModelGoodBONG b).prefixAlphaCap_last
  change A ≤ min
      (defectOrder (K := K)
        (1 * a.prefixProduct 1 *
          (BONG.unaryModelGoodBONG b).prefixProduct 1))
      (min (a.prefixAlphaCap 1)
        ((BONG.unaryModelGoodBONG b).prefixAlphaCap 1)) ↔
    A ≤ defectOrder (K := K) (a.valueUnit 0 * b)
  rw [htargetCap]
  simp only [min_eq_left le_top]
  have hsourceCap : a.prefixAlphaCap 1 = (a.alphaValue 0 : WithTop ℚ) := by
    apply a.prefixAlphaCap_of_internal <;> omega
  rw [hsourceCap, le_min_iff]
  have hsourceProduct : a.prefixProduct 1 = a.valueUnit 0 := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_zero, one_mul]
    rfl
  have htargetProduct :
      (BONG.unaryModelGoodBONG b).prefixProduct 1 = b := by
    change (BONG.unaryModelBONG b).prefixProduct 1 = b
    rw [(BONG.unaryModelBONG b).prefixProduct_succ 0 (by omega),
      (BONG.unaryModelBONG b).prefixProduct_zero, one_mul,
      BONG.unaryModelBONG_valueUnit]
  rw [hsourceProduct, htargetProduct]
  simp only [one_mul]
  exact and_iff_left hAalpha

/-- Beli, Lemma 2.7: with `R_1 = 0`, condition (ii) for all unary unit
targets is equivalent to `alpha_1 <= 1`. -/
theorem universalUnitDefectConditions_iff_alphaValue_le_one
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) :
    (∀ b : Kˣ, ordUnit K b = 0 →
      (a.representationAlphaValue (BONG.unaryModelGoodBONG b)
          (unaryRepresentationIndex tail) : WithTop ℚ) ≤
        a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) 1 1 1) ↔
      a.alphaValue 0 ≤ 1 := by
  letI : BONG.DyadicUnitDefectSpectrumLaws K :=
    BONG.dyadicUnitDefectSpectrumLawsProved K
  constructor
  · intro h
    obtain ⟨epsilon, hepsilonUnit, hepsilonDefect⟩ :=
      BONG.DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
        (K := K) 1 (by exact ⟨1, odd_one, by norm_num⟩)
        (by norm_num) (by
          have he := ramificationIndex_pos K
          exact_mod_cast (show (1 : Int) < 2 * (ramificationIndex K : Int) by omega))
    let b : Kˣ := (a.valueUnit 0)⁻¹ * epsilon
    have hbOrder : ordUnit K b = 0 := by
      simp only [b, ordUnit_mul, ordUnit_inv]
      have haOrder : ordUnit K (a.valueUnit 0) = 0 := by
        calc
          ordUnit K (a.valueUnit 0) = a.order 0 := by
            simpa only [GoodBONG.order, GoodBONG.valueUnit] using
              (a.toBONG.order_eq_ordUnit (0 : Fin (tail + 2))).symm
          _ = 0 := hzero
      have hepsilonOrder : ordUnit K epsilon = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K epsilon).1 hepsilonUnit
      rw [haOrder, hepsilonOrder, neg_zero, zero_add]
    have hAeq := a.alphaValue_eq_unaryRepresentationAlphaValue_of_order_eq
      b (hzero.trans hbOrder.symm)
    have hcondition := h b hbOrder
    rw [a.unary_defectCondition_iff_defectOrder b (by rw [hzero, hbOrder])]
      at hcondition
    have hproduct : a.valueUnit 0 * b = epsilon := by
      simp [b]
    rw [hAeq, hproduct, hepsilonDefect] at hcondition
    exact_mod_cast hcondition
  · intro halpha b hbOrder
    rw [a.unary_defectCondition_iff_defectOrder b (by rw [hzero, hbOrder])]
    have hAeq := a.alphaValue_eq_unaryRepresentationAlphaValue_of_order_eq
      b (hzero.trans hbOrder.symm)
    rw [hAeq]
    have hproductEven : Even (ordUnit K (a.valueUnit 0 * b)) := by
      have haOrder : ordUnit K (a.valueUnit 0) = 0 := by
        calc
          ordUnit K (a.valueUnit 0) = a.order 0 := by
            simpa only [GoodBONG.order, GoodBONG.valueUnit] using
              (a.toBONG.order_eq_ordUnit (0 : Fin (tail + 2))).symm
          _ = 0 := hzero
      rw [ordUnit_mul, haOrder, hbOrder]
      exact Even.zero
    exact (show (a.alphaValue 0 : WithTop ℚ) ≤ 1 by exact_mod_cast halpha).trans
      (defectOrder_one_le_of_even (a.valueUnit 0 * b) hproductEven)

end BONG.GoodBONG

end Bong
