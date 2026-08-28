/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.HilbertSymbol
import Bong.Dyadic.QuadraticDefectHensel

/-!
# The Hilbert-symbol defect criterion

This proves the positive half of O'Meara's dyadic Hilbert-symbol filtration
criterion directly from quadratic approximation and the local square theorem.
For normalized errors `alpha` and `beta`, the hypothesis makes
`1 - alpha * beta` a square.  The identities

`alpha = 1 - (1 - alpha)` and
`alpha * (1 - beta) = (1 - alpha * beta) - (1 - alpha)`

then exhibit the second normalized square class as a quotient of two norms.
-/

namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

local instance defectLaws : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

private theorem isQuadraticNorm_of_defect_add_gt_two_mul_e
    (a b : Kˣ)
    (h : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K a + quadraticDefect K b) :
    IsQuadraticNorm K a b := by
  by_cases haSquare : IsSquare a
  · exact isQuadraticNorm_of_isSquare_left K haSquare
  by_cases hbSquare : IsSquare b
  · exact isQuadraticNorm_of_isSquare_right K hbSquare
  have haFinite : quadraticDefect K a ≠ ⊤ := by
    intro htop
    exact haSquare ((quadraticDefect_eq_top_iff_isSquare (K := K) a).mp htop)
  have hbFinite : quadraticDefect K b ≠ ⊤ := by
    intro htop
    exact hbSquare ((quadraticDefect_eq_top_iff_isSquare (K := K) b).mp htop)
  let da := (quadraticDefect K a).toNat
  let db := (quadraticDefect K b).toNat
  have hda : quadraticDefect K a = (da : ℕ∞) := by
    simpa only [da] using (ENat.coe_toNat haFinite).symm
  have hdb : quadraticDefect K b = (db : ℕ∞) := by
    simpa only [db] using (ENat.coe_toNat hbFinite).symm
  have hsum : 2 * ramificationIndex K < da + db := by
    rw [hda, hdb] at h
    exact_mod_cast h
  have hdaBound : da ≤ 2 * ramificationIndex K := by
    have hbound := quadraticDefect_le_two_mul_e_of_not_isSquare
      (K := K) haSquare
    rw [hda] at hbound
    exact_mod_cast hbound
  have hdbBound : db ≤ 2 * ramificationIndex K := by
    have hbound := quadraticDefect_le_two_mul_e_of_not_isSquare
      (K := K) hbSquare
    rw [hdb] at hbound
    exact_mod_cast hbound
  have hdaPos : 0 < da := by omega
  have hdbPos : 0 < db := by omega
  have haApprox : IsQuadraticApproximation K a da :=
    (isQuadraticApproximation_iff_le_defect K).2 (by rw [hda])
  have hbApprox : IsQuadraticApproximation K b db :=
    (isQuadraticApproximation_iff_le_defect K).2 (by rw [hdb])
  rcases haApprox with ⟨x, hx⟩
  rcases hbApprox with ⟨y, hy⟩
  have hxNe : x ≠ 0 := by
    intro hxZero
    subst x
    simp only [zero_pow (by omega : 2 ≠ 0), zero_div, sub_zero,
      ord_one] at hx
    have hpos : (0 : WithTop Int) < (da : WithTop Int) := by
      exact_mod_cast hdaPos
    exact (not_lt_of_ge hx) hpos
  have hyNe : y ≠ 0 := by
    intro hyZero
    subst y
    simp only [zero_pow (by omega : 2 ≠ 0), zero_div, sub_zero,
      ord_one] at hy
    have hpos : (0 : WithTop Int) < (db : WithTop Int) := by
      exact_mod_cast hdbPos
    exact (not_lt_of_ge hy) hpos
  let xu : Kˣ := Units.mk0 x hxNe
  let yu : Kˣ := Units.mk0 y hyNe
  let alpha : K := 1 - x ^ 2 / (a : K)
  let beta : K := 1 - y ^ 2 / (b : K)
  let p : Kˣ := xu ^ 2 / a
  let q : Kˣ := yu ^ 2 / b
  have hpVal : (p : K) = 1 - alpha := by
    dsimp only [p, alpha, xu]
    simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      Units.val_mk0]
    ring
  have hqVal : (q : K) = 1 - beta := by
    dsimp only [q, beta, yu]
    simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      Units.val_mk0]
    ring
  have halphaNe : alpha ≠ 0 := by
    intro halpha
    apply haSquare
    refine ⟨xu, ?_⟩
    apply Units.ext
    change (a : K) = x * x
    have hratio : x ^ 2 / (a : K) = 1 := by
      dsimp only [alpha] at halpha
      exact (sub_eq_zero.mp halpha).symm
    field_simp [Units.ne_zero a] at hratio
    simpa [pow_two] using hratio.symm
  have hbetaNe : beta ≠ 0 := by
    intro hbeta
    apply hbSquare
    refine ⟨yu, ?_⟩
    apply Units.ext
    change (b : K) = y * y
    have hratio : y ^ 2 / (b : K) = 1 := by
      dsimp only [beta] at hbeta
      exact (sub_eq_zero.mp hbeta).symm
    field_simp [Units.ne_zero b] at hratio
    simpa [pow_two] using hratio.symm
  have halphaOrder : (da : WithTop Int) ≤ ord K alpha := by
    simpa only [alpha] using hx
  have hbetaOrder : (db : WithTop Int) ≤ ord K beta := by
    simpa only [beta] using hy
  have hproductOrder :
      (((da + db : Nat) : Int) : WithTop Int) ≤ ord K (alpha * beta) := by
    rw [ord_mul]
    have hadd := add_le_add halphaOrder hbetaOrder
    norm_cast at hadd ⊢
  have hdeepProduct :
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) <
        ord K (alpha * beta) := by
    have hcast :
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) <
          (((da + db : Nat) : Int) : WithTop Int) := by
      exact_mod_cast hsum
    exact hcast.trans_le hproductOrder
  have honeSubNe : 1 - alpha * beta ≠ 0 := by
    intro hzero
    have hprod : 1 = alpha * beta := sub_eq_zero.mp hzero
    have horder : ord K (alpha * beta) = 0 := by rw [← hprod, ord_one]
    rw [horder] at hdeepProduct
    have hnonneg :
        (0 : WithTop Int) ≤
          (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
      exact_mod_cast Nat.zero_le (2 * ramificationIndex K)
    exact (not_lt_of_ge hnonneg) hdeepProduct
  let endpoint : Kˣ := Units.mk0 (1 - alpha * beta) honeSubNe
  have hendpointSquare : IsSquare endpoint := by
    apply isSquare_of_ord_sub_one_gt_two_mul_e K endpoint
    simpa only [endpoint, Units.val_mk0, sub_sub_cancel_left, ord_neg] using
      hdeepProduct
  rcases hendpointSquare with ⟨s, hs⟩
  have hsVal : (s : K) ^ 2 = 1 - alpha * beta := by
    have := congrArg (fun z : Kˣ ↦ (z : K)) hs
    simpa only [pow_two, Units.val_mul, endpoint, Units.val_mk0] using this.symm
  let alphaUnit : Kˣ := Units.mk0 alpha halphaNe
  have halphaNorm : IsQuadraticNorm K p alphaUnit := by
    refine ⟨1, 1, ?_⟩
    change 1 ^ 2 - (p : K) * 1 ^ 2 = alpha
    rw [hpVal]
    ring
  have halphaQNorm : IsQuadraticNorm K p (alphaUnit * q) := by
    refine ⟨(s : K), 1, ?_⟩
    change (s : K) ^ 2 - (p : K) * 1 ^ 2 = alpha * (q : K)
    rw [hsVal, hpVal, hqVal]
    ring
  have hqNorm : IsQuadraticNorm K p q := by
    have hmul := IsQuadraticNorm.mul K halphaQNorm
      (IsQuadraticNorm.inv K halphaNorm)
    simpa [mul_assoc] using hmul
  let sa : Kˣ := xu / a
  let sb : Kˣ := yu / b
  have hpForm : p = a * sa ^ 2 := by
    dsimp only [p, sa]
    simp only [div_eq_mul_inv, pow_two]
    calc
      xu * xu * a⁻¹ = (a * a⁻¹) * (xu * xu) * a⁻¹ := by simp
      _ = a * ((xu * a⁻¹) * (xu * a⁻¹)) := by ac_rfl
  have hqForm : q = b * sb ^ 2 := by
    dsimp only [q, sb]
    simp only [div_eq_mul_inv, pow_two]
    calc
      yu * yu * b⁻¹ = (b * b⁻¹) * (yu * yu) * b⁻¹ := by simp
      _ = b * ((yu * b⁻¹) * (yu * b⁻¹)) := by ac_rfl
  have haqNorm : IsQuadraticNorm K a q := by
    apply (isQuadraticNorm_mul_square_left_iff K a q sa).mp
    rwa [← hpForm]
  apply (isQuadraticNorm_mul_square_right_iff K a b sb).mp
  rwa [← hqForm]

theorem hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e_proved
    (a b : Kˣ)
    (h : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K a + quadraticDefect K b) :
    hilbertSymbol K a b = 1 :=
  (hilbertSymbol_eq_one_iff K a b).2
    (isQuadraticNorm_of_defect_add_gt_two_mul_e a b h)

end Bong.Dyadic
