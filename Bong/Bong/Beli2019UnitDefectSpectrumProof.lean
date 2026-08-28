/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Choice
import Bong.Dyadic.UnitDefectClassification

/-!
# The unit-defect spectrum used in Beli (2019)

O'Meara, Remark 63:6 is specialized to the rational defect-order convention
used by Beli.  The underlying field theorem is proved in
`Bong.Dyadic.UnitDefectClassification`.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Every nonnegative odd integral depth below `2e` is realized by a
valuation unit. -/
noncomputable instance dyadicUnitDefectSpectrumLawsProved :
    DyadicUnitDefectSpectrumLaws K where
  exists_unit_of_odd_rational_defect d hodd hnonnegative hlt := by
    rcases hodd with ⟨z, hzOdd, hd⟩
    have hzNonnegative : 0 ≤ z := by
      have hcast : (0 : ℚ) ≤ (z : ℚ) := by simpa only [hd] using hnonnegative
      exact_mod_cast hcast
    have hzPositive : 0 < z := by
      rcases hzOdd with ⟨k, hk⟩
      omega
    let n := z.toNat
    have hnCast : (n : Int) = z := by
      simpa only [n] using (Int.toNat_of_nonneg hzNonnegative)
    have hnPositive : 0 < n := by omega
    have hnOdd : Odd n := by
      rcases hzOdd with ⟨k, hk⟩
      have hkNonnegative : 0 ≤ k := by omega
      refine ⟨k.toNat, ?_⟩
      have hkCast : (k.toNat : Int) = k :=
        Int.toNat_of_nonneg hkNonnegative
      have hcast : (n : Int) =
          ((2 * k.toNat + 1 : Nat) : Int) := by
        push_cast
        omega
      exact_mod_cast hcast
    have hnLt : n < 2 * ramificationIndex K := by
      have hcast : (z : ℚ) < 2 * (ramificationIndex K : ℚ) := by
        simpa only [hd] using hlt
      rw [← hnCast] at hcast
      exact_mod_cast hcast
    obtain ⟨u, hu, hdefect⟩ :=
      exists_unit_quadraticDefect_eq_odd (K := K) n hnPositive hnOdd hnLt
    refine ⟨u, hu, ?_⟩
    unfold GoodBONG.defectOrder
    rw [hdefect]
    change (((n : Nat) : ℚ) : WithTop ℚ) = (d : WithTop ℚ)
    apply WithTop.coe_eq_coe.mpr
    rw [hd, ← hnCast]
    norm_num

end BONG

end Bong
