/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma72Proof

/-!
# Integer defect cutoffs used in Beli (2003), Lemma 7.3

Lemma 7.2 states its cutoff in `WithTop ℚ`, while the explicit quadratic
approximations used in Lemma 7.3 are indexed by `ℕ∞`.  The lemmas below
give the exact conversion when the parameter order is even and the cutoff is
nonnegative, including the finite discriminant endpoint.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

theorem enat_le_beliParameterDefect_of_intCast_le_orderQ
    (a : Kˣ) (z : Int) (hz : 0 ≤ z)
    (h : (((z : Int) : ℚ) : WithTop ℚ) ≤
      beliParameterDefectOrderQ (K := K) a) :
    ((z.toNat : Nat) : ℕ∞) ≤ beliParameterDefect K a := by
  cases hd : beliParameterDefect K a with
  | top => simp
  | coe d =>
      unfold beliParameterDefectOrderQ at h
      rw [hd] at h
      change (((z : Int) : ℚ) : WithTop ℚ) ≤
        (((d : Nat) : ℚ) : WithTop ℚ) at h
      norm_cast at h
      exact_mod_cast (show z.toNat ≤ d by omega)

theorem enat_lt_beliParameterDefect_of_intCast_lt_orderQ
    (a : Kˣ) (z : Int) (hz : 0 ≤ z)
    (h : (((z : Int) : ℚ) : WithTop ℚ) <
      beliParameterDefectOrderQ (K := K) a) :
    ((z.toNat : Nat) : ℕ∞) < beliParameterDefect K a := by
  cases hd : beliParameterDefect K a with
  | top => simp
  | coe d =>
      unfold beliParameterDefectOrderQ at h
      rw [hd] at h
      change (((z : Int) : ℚ) : WithTop ℚ) <
        (((d : Nat) : ℚ) : WithTop ℚ) at h
      norm_cast at h
      exact_mod_cast (show z.toNat < d by omega)

theorem lemma72DefectThreshold_eq_intCast_of_even
    (a : Kˣ) (hEven : Even (ordUnit K a)) :
    lemma72DefectThreshold (K := K) a =
      (((ramificationIndex K : Int) - ordUnit K a / 2 : Int) : ℚ) := by
  unfold lemma72DefectThreshold
  rcases hEven with ⟨r, hr⟩
  have hhalf : ordUnit K a / 2 = r := by omega
  rw [hhalf, hr]
  push_cast
  ring

theorem beliParameterDefect_cutoff_le_of_unitCriterion
    (a : Kˣ) (h : SatisfiesLemma72UnitCriterion (K := K) a)
    (hcut : 0 ≤ (ramificationIndex K : Int) - ordUnit K a / 2) :
    ((((ramificationIndex K : Int) - ordUnit K a / 2).toNat : Nat) : ℕ∞) ≤
      beliParameterDefect K a := by
  have hq :
      (((((ramificationIndex K : Int) - ordUnit K a / 2 : Int) : ℚ)) :
          WithTop ℚ) ≤
        beliParameterDefectOrderQ (K := K) a := by
    rw [← lemma72DefectThreshold_eq_intCast_of_even a h.1]
    rcases h.2 with hendpoint | hstrict
    · rcases hendpoint with ⟨horder, hdefect⟩
      have hcutEq :
          (ramificationIndex K : Int) - ordUnit K a / 2 =
            ((2 * ramificationIndex K : Nat) : Int) := by
        rw [horder]
        push_cast
        omega
      rw [lemma72DefectThreshold_eq_intCast_of_even a h.1, hcutEq]
      unfold beliParameterDefectOrderQ
      rw [hdefect]
      rfl
    · exact hstrict.le
  exact enat_le_beliParameterDefect_of_intCast_le_orderQ a _ hcut hq

theorem beliParameterDefect_cutoff_lt_of_unitCriterion_of_not_endpoint
    (a : Kˣ) (h : SatisfiesLemma72UnitCriterion (K := K) a)
    (hnot : ¬IsNegativeDiscriminantQuarterParameter (K := K) a)
    (hcut : 0 ≤ (ramificationIndex K : Int) - ordUnit K a / 2) :
    ((((ramificationIndex K : Int) - ordUnit K a / 2).toNat : Nat) : ℕ∞) <
      beliParameterDefect K a := by
  have hstrict := h.2.resolve_left hnot
  rw [lemma72DefectThreshold_eq_intCast_of_even a h.1] at hstrict
  exact enat_lt_beliParameterDefect_of_intCast_lt_orderQ a _ hcut hstrict

end Dyadic

end Bong
