/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.BeliGroups

/-!
# Factorization in the normalized valuation ring

The Smith normal form used in Beli's prime-index reduction has coefficients
in the valuation ring.  This file puts the elementary DVR factorization into
the exact form needed later: every nonzero coefficient is a power of the
chosen uniformizer times a unit of the valuation ring.
-/

namespace Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The selected uniformizer as an element of the valuation ring. -/
noncomputable def uniformizerInteger : IntegerRing K :=
  ⟨uniformizer K, (mem_integerRing_iff K).2 (by
    rw [IsIntegral, ord_uniformizer]
    norm_num)⟩

@[simp]
theorem coe_uniformizerInteger :
    (uniformizerInteger K : K) = uniformizer K :=
  rfl

theorem uniformizerInteger_ne_zero : uniformizerInteger K ≠ 0 := by
  intro h
  have hK := congrArg (fun x : IntegerRing K => (x : K)) h
  apply uniformizer_ne_zero K
  simpa [uniformizerInteger] using hK

/-- A nonzero integral element is a nonnegative power of the selected
uniformizer times a unit of the valuation ring. -/
theorem exists_eq_uniformizerInteger_pow_mul_unit
    (a : IntegerRing K) (ha : a ≠ 0) :
    ∃ n : Nat, ∃ u : (IntegerRing K)ˣ,
      a = uniformizerInteger K ^ n * (u : IntegerRing K) := by
  have haK : (a : K) ≠ 0 := by
    intro h
    apply ha
    exact Subtype.ext h
  let aK : Kˣ := Units.mk0 (a : K) haK
  let ε : Kˣ := normalizedUnitPart K aK
  have hε : IsValuationUnit K (ε : K) := by
    exact normalizedUnitPart_isValuationUnit K aK
  let εO : IntegerRing K :=
    ⟨(ε : K), (mem_integerRing_iff K).2 (by
      rw [IsIntegral, hε])⟩
  let εInvO : IntegerRing K :=
    ⟨((ε⁻¹ : Kˣ) : K), (mem_integerRing_iff K).2 (by
      rw [IsIntegral, Units.val_inv_eq_inv_val,
        AddValuation.map_inv, hε]
      simp)⟩
  let uO : (IntegerRing K)ˣ := Units.mk εO εInvO (by
    apply Subtype.ext
    simp [εO, εInvO]) (by
    apply Subtype.ext
    simp [εO, εInvO])
  have horder : 0 ≤ ordUnit K aK := by
    have haIntegral := (mem_integerRing_iff K).1 a.property
    change (0 : WithTop Int) ≤ ord K (a : K) at haIntegral
    have hcoe : (ordUnit K aK : WithTop Int) = ord K (a : K) := by
      simpa [aK] using coe_ordUnit K aK
    rw [← hcoe] at haIntegral
    exact_mod_cast haIntegral
  refine ⟨Int.toNat (ordUnit K aK), uO, ?_⟩
  apply Subtype.ext
  have hfactor := uniformizerPower_mul_normalizedUnitPart K aK
  have hcast : ((Int.toNat (ordUnit K aK) : Nat) : Int) =
      ordUnit K aK := Int.toNat_of_nonneg horder
  have hpow :
      (uniformizerPowerUnit K (ordUnit K aK) : K) =
        uniformizer K ^ Int.toNat (ordUnit K aK) := by
    change
      ((uniformizerUnit K ^ ordUnit K aK : Kˣ) : K) =
        uniformizer K ^ Int.toNat (ordUnit K aK)
    rw [← hcast, zpow_natCast]
    simp [max_eq_left horder]
  have hfactorK :
      (uniformizerPowerUnit K (ordUnit K aK) : K) *
          (normalizedUnitPart K aK : K) = (aK : K) := by
    exact congrArg (fun x : Kˣ => (x : K)) hfactor
  rw [hpow] at hfactorK
  simpa [uniformizerInteger, uO, εO, ε, aK] using hfactorK.symm

end Bong.Dyadic
