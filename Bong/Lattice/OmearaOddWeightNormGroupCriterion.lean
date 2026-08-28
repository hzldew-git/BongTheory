/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009OrthogonalIdealProof

/-!
# Detecting an odd weight ideal from a norm-group bound

O'Meara's low-rank models are checked by showing that every enlarged
quadratic value belongs to `a O^2 + b O`, while `a` is a norm generator
and `b` itself is represented.  If the orders of `a` and `b` have opposite
parity, these facts force the selected weight ideal to be exactly `b O`.

The result below isolates that argument.  It is a consequence of the
concrete construction and uniqueness of Beli's weight ideal and introduces
no local-law interface.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Below the error ideal `b O`, an element of `a O^2 + b O` has the
same valuation parity as `a`. -/
theorem even_order_sub_of_mem_integralSquareCoset_of_ord_lt
    (a b z : Kˣ)
    (hz : (z : K) ∈
      integralSquareCoset (a : K) (principalIdeal (K := K) (b : K)))
    (hlt : ordUnit K z < ordUnit K b) :
    Even (ordUnit K z - ordUnit K a) := by
  rcases hz with ⟨c, y, hy, hzEq⟩
  have hyOrder : ord K (b : K) ≤ ord K y := by
    have hy' := hy
    rw [principalIdeal_eq_powerIdeal, mem_powerIdeal_iff] at hy'
    simpa only [← coe_ordUnit] using hy'
  have hzLtY : ord K (z : K) < ord K y := by
    apply lt_of_lt_of_le _ hyOrder
    rw [← coe_ordUnit, ← coe_ordUnit]
    exact WithTop.coe_lt_coe.mpr hlt
  have htermOrder : ord K ((a : K) * (c : K) ^ 2) =
      ord K (z : K) := by
    have hdom := (ord K).map_sub_eq_of_lt_left hzLtY
    have htermEq : (a : K) * (c : K) ^ 2 = (z : K) - y := by
      rw [hzEq]
      ring
    rw [htermEq]
    exact hdom
  have hcNe : (c : K) ≠ 0 := by
    intro hc
    rw [hc, zero_pow (by norm_num : (2 : Nat) ≠ 0), mul_zero,
      ord_zero, ← coe_ordUnit] at htermOrder
    exact WithTop.top_ne_coe htermOrder
  let cu : Kˣ := Units.mk0 (c : K) hcNe
  have hcOrder : ord K (c : K) =
      (ordUnit K cu : WithTop Int) := by
    simpa only [cu, Units.val_mk0] using (coe_ordUnit K cu).symm
  rw [ord_mul, ord_pow, ← coe_ordUnit, hcOrder,
    ← coe_ordUnit] at htermOrder
  have horder : ordUnit K a + 2 * ordUnit K cu = ordUnit K z := by
    have horder' : ordUnit K a +
        (ordUnit K cu + ordUnit K cu) = ordUnit K z := by
      apply WithTop.coe_injective
      simpa only [two_smul, WithTop.coe_add] using htermOrder
    omega
  exact ⟨ordUnit K cu, by omega⟩

/-- If the norm group is bounded by `a O^2 + b O`, contains the
opposite-parity value `b`, and `b O` contains the ambient `2s` ideal, then
the selected weight ideal is exactly `b O`. -/
theorem weightIdeal_eq_principalIdeal_of_odd_normGroup_bound
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q L a)
    (hbGroup : (b : K) ∈ normGroupSet q L)
    (hodd : Odd (ordUnit K a + ordUnit K b))
    (htwo : twoScaleIdeal q L ≤
      principalIdeal (K := K) (b : K))
    (hbound : normGroupSet q L ⊆
      integralSquareCoset (a : K)
        (principalIdeal (K := K) (b : K))) :
    weightIdeal q L = principalIdeal (K := K) (b : K) := by
  let w : OrderedFractionalIdeal K := Beli2009WeightIdealData.weight q L
  have hgroup : normGroupSet q L =
      integralSquareCoset (a : K) w.carrier :=
    normGroupSet_eq_integralSquareCoset_weightIdeal a ha
  have hoddDiff : Odd (ordUnit K b - ordUnit K a) := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨k - ordUnit K a, ?_⟩
    omega
  have hbWeight : (b : K) ∈ weightIdeal q L := by
    exact oppositeParity_normGroup_mem_candidateWeight
      ha w hgroup hbGroup hoddDiff
  have hbLeWeight : principalIdeal (K := K) (b : K) ≤
      weightIdeal q L := by
    rw [principalIdeal, Submodule.span_singleton_le_iff_mem]
    exact hbWeight
  have hconditions := (beli2009Lemma210 a ha w
    (twoScaleIdeal_le_weightIdeal q L)).mp rfl
  rcases hconditions.2 with hterminal | hweightOdd
  · have hweightTwo : weightIdeal q L = twoScaleIdeal q L := hterminal
    exact le_antisymm
      (by rw [hweightTwo]; exact htwo)
      hbLeWeight
  · have hnotLt : ¬ weightIdealOrder q L < ordUnit K b := by
      intro hlt
      let z : Kˣ := uniformizerPowerUnit K (weightIdealOrder q L)
      have hzWeight : (z : K) ∈ weightIdeal q L := by
        rw [weightIdeal_eq_powerIdeal]
        exact generator_mem_principalIdeal _
      have hzGroup : (z : K) ∈ normGroupSet q L := by
        rw [hgroup]
        exact ⟨0, (z : K), hzWeight, by simp⟩
      have hzBound := hbound hzGroup
      have hzEven :=
        even_order_sub_of_mem_integralSquareCoset_of_ord_lt
          a b z hzBound (by
            dsimp only [z]
            rw [ordUnit_uniformizerPowerUnit]
            exact hlt)
      have hweightOdd' :
          Odd (ordUnit K a + weightIdealOrder q L) := hweightOdd
      have hzOdd : Odd (ordUnit K z - ordUnit K a) := by
        rcases hweightOdd' with ⟨k, hk⟩
        refine ⟨k - ordUnit K a, ?_⟩
        dsimp only [z]
        rw [ordUnit_uniformizerPowerUnit]
        omega
      exact Int.not_even_iff_odd.mpr hzOdd hzEven
    have hweightOrderLe : weightIdealOrder q L ≤ ordUnit K b := by
      rw [weightIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
        powerIdeal_le_iff] at hbLeWeight
      exact hbLeWeight
    have horderEq : weightIdealOrder q L = ordUnit K b := by
      exact le_antisymm hweightOrderLe (le_of_not_gt hnotLt)
    calc
      weightIdeal q L = powerIdeal (K := K) (weightIdealOrder q L) :=
        weightIdeal_eq_powerIdeal q L
      _ = powerIdeal (K := K) (ordUnit K b) := by rw [horderEq]
      _ = principalIdeal (K := K) (b : K) :=
        (principalIdeal_eq_powerIdeal b).symm

/-- Under the preceding hypotheses the whole norm group is the expected
square coset. -/
theorem normGroupSet_eq_integralSquareCoset_principal_of_odd_bound
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q L a)
    (hbGroup : (b : K) ∈ normGroupSet q L)
    (hodd : Odd (ordUnit K a + ordUnit K b))
    (htwo : twoScaleIdeal q L ≤
      principalIdeal (K := K) (b : K))
    (hbound : normGroupSet q L ⊆
      integralSquareCoset (a : K)
        (principalIdeal (K := K) (b : K))) :
    normGroupSet q L =
      integralSquareCoset (a : K)
        (principalIdeal (K := K) (b : K)) := by
  rw [normGroupSet_eq_integralSquareCoset_weightIdeal a ha,
    weightIdeal_eq_principalIdeal_of_odd_normGroup_bound
      a b ha hbGroup hodd htwo hbound]

end Lattice

end Bong
