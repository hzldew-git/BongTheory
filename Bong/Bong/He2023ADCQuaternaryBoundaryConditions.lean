/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryCandidate
import Bong.Bong.He2023ADCPublishedRepresentation
import Bong.Bong.Beli2019OddPrefixDefect
import Bong.Bong.BeliUniversalCentral

/-!
# Representation checks at the unresolved quaternary boundary

These are individual, proved conditions for the order profile `0,-2e,1,3-2e`.
They are not a proof that this profile is 2-ADC: the complete family of relevant
binary maximal tests must still be represented before that conclusion is valid.
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
  {L : Lattice K V} {M : Lattice K W}

/-- The exact order profile under investigation, without any ADC assertion. -/
def HeADCQuaternaryBoundaryOrders (a : GoodBONG q L 4) : Prop :=
  ∀ i, a.order i = (![0, -(2 * (ramificationIndex K : Int)), 1,
    3 - 2 * (ramificationIndex K : Int)] : Fin 4 → Int) i

/-- The constructed candidate has the stated profile. -/
theorem heADCQuaternaryBoundaryCandidate_hasOrders :
    HeADCQuaternaryBoundaryOrders (heADCQuaternaryBoundaryCandidate (K := K)) :=
  heADCQuaternaryBoundaryCandidate_orders

/-- Condition (i) holds for every integral binary target. -/
theorem heADCBoundary_orderCondition (a : GoodBONG q L 4) (b : GoodBONG r M 2)
    (ha : HeADCQuaternaryBoundaryOrders a) (hb : Lattice.IsIntegral r M) :
    a.RepresentationOrderCondition b (by omega) := by
  dsimp only [HeADCQuaternaryBoundaryOrders] at ha
  intro i
  left
  fin_cases i
  · have h := ((b.heHu2022Proposition27i hb).oddIndexed 0 0 le_rfl
      (by decide) (by decide)).1
    simpa [ha] using h
  · have h := ((b.heHu2022Proposition27i hb).evenIndexed 1 1 le_rfl
      (by decide) (by decide)).1
    simpa [ha] using h

/-- The long-prefix trigger is impossible for an integral binary target. -/
theorem heADCBoundary_longConditions (a : GoodBONG q L 4) (b : GoodBONG r M 2)
    (ha : HeADCQuaternaryBoundaryOrders a) (hb : Lattice.IsIntegral r M) :
    a.LongRepresentationConditions b := by
  dsimp only [HeADCQuaternaryBoundaryOrders] at ha
  intro i htrigger
  have hi : i.val = 2 := by have := i.one_lt; have := i.succ_lt_large; omega
  have hzero := ((b.heHu2022Proposition27i hb).oddIndexed 0 0 le_rfl
    (by decide) (by decide)).1
  have h := htrigger.2.1
  simp only [hi, ha] at h
  change b.order 0 + 2 * (ramificationIndex K : Int) <
    3 - 2 * (ramificationIndex K : Int) at h
  have he := ramificationIndex_pos (K := K)
  omega

/-- The first defect inequality follows from its nonpositive half-gap bound. -/
theorem heADCBoundary_firstDefect (a : GoodBONG q L 4) (b : GoodBONG r M 2)
    (ha : HeADCQuaternaryBoundaryOrders a) (hb : Lattice.IsIntegral r M)
    (i : RepresentationIndex 4 2) (hi : i.val = 1) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤ a.truncatedPrefixDefect b 1 1 1 := by
  dsimp only [HeADCQuaternaryBoundaryOrders] at ha
  have hzero := ((b.heHu2022Proposition27i hb).oddIndexed 0 0 le_rfl
    (by decide) (by decide)).1
  rw [coe_representationAlphaValue]
  apply (a.representationAlpha_le_halfGap b i).trans
  apply le_trans (b := (0 : WithTop ℚ))
  · unfold representationHalfGap
    simp only [hi, ha]
    change ((((-(2 * (ramificationIndex K : Int)) - b.order 0 : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤ 0
    apply WithTop.coe_le_coe.mpr
    push_cast
    have hzero' : (0 : ℚ) ≤ b.order 0 := by exact_mod_cast hzero
    linarith
  · exact a.truncatedPrefixDefect_nonneg b 1 1 1

/-- The middle alpha is strictly above `2e`, with its exact half-integral value. -/
theorem heADCBoundary_middleAlpha (a : GoodBONG q L 4)
    (ha : HeADCQuaternaryBoundaryOrders a) :
    a.alphaValue 1 = 2 * (ramificationIndex K : ℚ) + 1 / 2 := by
  dsimp only [HeADCQuaternaryBoundaryOrders] at ha
  have hgap : a.orderGap 1 = 2 * (ramificationIndex K : Int) + 1 := by
    simp [orderGap, ha]
    ring
  rw [(a.heADC2025Proposition33 1).halfGap (Or.inl (by rw [hgap]; omega))]
  simp [halfGapValue, orderGap, ha]
  ring

/-- A target with first order zero gives zero at the terminal previous defect. -/
theorem heADCBoundary_oddMixedPrefix (a : GoodBONG q L 4) (b : GoodBONG r M 2)
    (ha : HeADCQuaternaryBoundaryOrders a) (hb : b.order 0 = 0) :
    a.truncatedPrefixDefect b (-1) 3 1 = 0 := by
  dsimp only [HeADCQuaternaryBoundaryOrders] at ha
  apply a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed b (-1) 3 1
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hneg : ordUnit K (-1 : Kˣ) = 0 := by rw [ordUnit_neg, hone]
  rw [ordUnit_mul, ordUnit_mul, hneg,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum 1 (by omega)]
  simp only [BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_zero,
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 2)]
  change Odd (0 + (0 + a.order 0 + a.order 1 + a.order 2) + (0 + b.order 0))
  rw [ha, ha, ha, hb]
  change Odd (0 + (0 + 0 + -(2 * (ramificationIndex K : Int)) + 1) + (0 + 0))
  exact ⟨-(ramificationIndex K : Int), by ring⟩

/-- With a split head, the second comparison defect retains every finite target defect. -/
theorem heADCBoundary_secondComparisonDefect (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCQuaternaryBoundaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) (d : Nat)
    (hd : d ≤ 2 * ramificationIndex K)
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ)) :
    a.truncatedPrefixDefect b 1 2 2 = (d : ℚ) := by
  have hdom : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) <
      defectOrder (K := K) ((-1 : Kˣ) * a.prefixProduct 2) := by
    rw [hb, defectOrder_eq_top_of_isSquare hsplit]
    exact WithTop.coe_lt_top _
  have hraw := defectOrder_mul_eq_right_of_lt_left hdom
  have hproduct : ((-1 : Kˣ) * a.prefixProduct 2) *
      ((-1 : Kˣ) * b.prefixProduct 2) = a.prefixProduct 2 * b.prefixProduct 2 := by
    simp only [neg_one_mul, neg_mul_neg]
  rw [hproduct, hb] at hraw
  rw [truncatedPrefixDefect, one_mul, hraw, b.prefixAlphaCap_last,
    min_top_right, a.prefixAlphaCap_of_internal (by omega) (by omega)]
  change min ((d : ℚ) : WithTop ℚ) (a.alphaValue 1) = (d : ℚ)
  rw [a.heADCBoundary_middleAlpha ha, min_eq_left]
  apply WithTop.coe_le_coe.mpr
  have hd' : (d : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by exact_mod_cast hd
  linarith

/-- The primary candidate proves the second ordinary inequality for finite-defect tests. -/
theorem heADCBoundary_secondDefect_of_finite (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCQuaternaryBoundaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) (d : Nat)
    (hd : d ≤ 2 * ramificationIndex K)
    (hbzero : b.order 0 = 0) (hbone : b.order 1 = 1 - (d : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ))
    (i : RepresentationIndex 4 2) (hi : i.val = 2) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤ a.truncatedPrefixDefect b 1 2 2 := by
  rw [a.heADCBoundary_secondComparisonDefect b ha hsplit d hd hb,
    coe_representationAlphaValue]
  apply (a.representationAlpha_le_primary b i).trans
  unfold representationPrimaryDefect
  simp only [hi, a.heADCBoundary_oddMixedPrefix b ha hbzero, add_zero]
  have haTwo : a.order 2 = 1 := ha 2
  change (((a.order 2 - b.order 1 : Int) : ℚ) : WithTop ℚ) ≤ (d : ℚ)
  rw [haTwo, hbone]
  norm_num

/-- Strict domination computes the terminal full mixed defect below the endpoint. -/
theorem heADCBoundary_terminalMixedDefect (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (d : Nat) (hd : d < 2 * ramificationIndex K)
    (ha : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ)) :
    a.truncatedPrefixDefect b (-1) 4 2 = (d : ℚ) := by
  have hdom : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) <
      defectOrder (K := K) (a.prefixProduct 4) := by
    rw [ha, hb]
    apply WithTop.coe_lt_coe.mpr
    exact_mod_cast hd
  have hraw := defectOrder_mul_eq_right_of_lt_left hdom
  rw [hb] at hraw
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_last, b.prefixAlphaCap_last, min_self, min_top_right]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw

/-- The terminal central trigger fails for the entire finite-defect numerical family. -/
theorem heADCBoundary_terminalTrigger_not_of_finite (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCQuaternaryBoundaryOrders a)
    (d : Nat) (hd : d < 2 * ramificationIndex K)
    (hbzero : b.order 0 = 0) (hbone : b.order 1 = 1 - (d : Int))
    (hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ))
    (i : CentralRepresentationIndex 4 2) (hi : i.val = 3) :
    ¬ a.centralDefectTrigger b i := by
  intro htrigger
  have h := htrigger.2
  simp only [centralPreviousDefect, centralCurrentDefect, hi,
    a.heADCBoundary_oddMixedPrefix b ha hbzero,
    a.heADCBoundary_terminalMixedDefect b d hd hfull hb, zero_add] at h
  have haThree : a.order 3 = 3 - 2 * (ramificationIndex K : Int) := ha 3
  change (((2 * (ramificationIndex K : ℚ) + (b.order 1 : ℚ) -
    (a.order 3 : ℚ)) : ℚ) : WithTop ℚ) < (d : ℚ) at h
  rw [hbone, haThree] at h
  have h' := WithTop.coe_lt_coe.mp h
  push_cast at h'
  have hd' : (d : ℚ) ≤ 2 * (ramificationIndex K : ℚ) - 1 := by
    have hNat : d + 1 ≤ 2 * ramificationIndex K := hd
    have hRat : (d : ℚ) + 1 ≤ 2 * (ramificationIndex K : ℚ) := by exact_mod_cast hNat
    linarith
  linarith

/-- A split binary head supplies the unary prefix representation for every target. -/
theorem heADCBoundary_firstCentralRepresentation (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) :
    DiagonalRepresents (b.prefixValues 1 (by omega)) (a.prefixValues 2 (by omega)) := by
  have hproduct : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega), BONG.prefixProduct_zero, one_mul]
    rfl
  have hsquare : IsSquare (-(a.valueUnit 0 * a.valueUnit 1)) := by
    simpa only [hproduct, neg_one_mul] using hsplit
  have hisotropic := (diagonalBinary_isotropic_iff_isSquare_neg_product
    (a.valueUnit 0) (a.valueUnit 1)).mpr hsquare
  have hrep := diagonalBinary_represents_of_isotropic
    (a.valueUnit 0) (a.valueUnit 1) (b.valueUnit 0) hisotropic
  convert hrep using 1
  · funext i
    fin_cases i
    rfl
  · funext i
    fin_cases i <;> rfl

/-- All four conditions hold for an actual finite-defect binary target in this family.
The ambient embedding remains an explicit necessary hypothesis; no ADC property is assumed. -/
theorem heADCBoundary_represents_finite (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCQuaternaryBoundaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2))
    (hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (d : Nat) (hd : d < 2 * ramificationIndex K)
    (hbzero : b.order 0 = 0) (hbone : b.order 1 = 1 - (d : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ))
    (ambient : q.Represents r) : Lattice.Represents q r L M := by
  have hintegral : Lattice.IsIntegral r M :=
    b.toBONG.beliUniversalLemma22.mpr (by change 0 ≤ b.order 0; rw [hbzero])
  apply (heADC2025Theorem36Published (by omega) ambient a b).mpr
  refine ⟨a.heADCBoundary_orderCondition b ha hintegral, ?_, ?_,
    a.heADCBoundary_longConditions b ha hintegral⟩
  · intro i
    have hi : i.val = 1 ∨ i.val = 2 := by have := i.pos; have := i.le_small; omega
    rcases hi with hi | hi
    · simpa only [hi] using a.heADCBoundary_firstDefect b ha hintegral i hi
    · simpa only [hi] using a.heADCBoundary_secondDefect_of_finite b ha hsplit d
        hd.le hbzero hbone hb i hi
  · intro i htrigger
    have hi : i.val = 2 ∨ i.val = 3 := by
      have := i.one_lt
      have := i.le_small_succ
      omega
    rcases hi with hi | hi
    · rcases i with ⟨j, hj1, hj2, hj3⟩
      change j = 2 at hi
      subst j
      exact a.heADCBoundary_firstCentralRepresentation b hsplit
    · exact (a.heADCBoundary_terminalTrigger_not_of_finite b ha d hd hbzero hbone
        hfull hb i hi htrigger).elim

end BONG.GoodBONG

end Bong
