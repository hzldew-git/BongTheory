/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.QuadraticApproximationUnit

/-!
# Endpoint multiplier for Beli (2003), Lemma 7.3

The last vector of the ternary block may be multiplied by a valuation unit.
The multiplier below realizes the defect of `-(p₀p₁)` deeply enough that
its sum with the first vector has the required norm order.  The estimate is
strict for a negative first gap and weak at the zero-gap boundary.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

theorem exists_lemma73EndpointMultiplier
    (p₀ p₁ : Kˣ) (G : Int)
    (hG₀ : ordUnit K p₀ = G)
    (hG₁ : ordUnit K p₁ = -G)
    (hEven : Even G)
    (hlower : -(2 * (ramificationIndex K : Int)) ≤ G)
    (hupper : G ≤ 0)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K) p₀)
    (h₁ : SatisfiesLemma72UnitCriterion (K := K) p₁) :
    ∃ s : Kˣ,
      ordUnit K s = 0 ∧
      (((Dyadic.lemma73CentralDepth (K := K) G : Nat) : Int) : WithTop Int) ≤
        ord K (1 - (s : K) ^ 2 / ((-(p₀ * p₁) : Kˣ) : K)) ∧
      (G < 0 →
        (((Dyadic.lemma73CentralDepth (K := K) G : Nat) : Int) : WithTop Int) <
          ord K (1 - (s : K) ^ 2 / ((-(p₀ * p₁) : Kˣ) : K))) := by
  let k := Dyadic.lemma73CentralDepth (K := K) G
  have hqOrder : ordUnit K (-(p₀ * p₁)) = 0 := by
    rw [ordUnit_neg, ordUnit_mul, hG₀, hG₁]
    omega
  have hqUnit : IsValuationUnit K ((-(p₀ * p₁) : Kˣ) : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).2 hqOrder
  rcases Dyadic.lemma73_parameterProduct_defect_bounds
      (K := K) p₀ p₁ G hG₀ hG₁ hEven hlower hupper h₀ h₁ with
    ⟨hweak, hstrict⟩
  by_cases hGneg : G < 0
  · have hplus : ((k + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K (-(p₀ * p₁)) :=
      ENat.coe_add_one_le_iff.mpr (hstrict hGneg)
    rcases exists_valuationUnit_quadraticApproximation
        (K := K) (-(p₀ * p₁)) hqUnit (k + 1) (by omega) hplus with
      ⟨s, hs, herror⟩
    refine ⟨s, hs, ?_, ?_⟩
    · exact (show ((k : Int) : WithTop Int) ≤
          (((k + 1 : Nat) : Int) : WithTop Int) by exact_mod_cast (Nat.le_succ k)).trans
        herror
    · intro _
      exact (show ((k : Int) : WithTop Int) <
          (((k + 1 : Nat) : Int) : WithTop Int) by exact_mod_cast (Nat.lt_succ_self k)).trans_le
        herror
  · have hGzero : G = 0 := by omega
    have hkInt := Dyadic.lemma73CentralDepth_cast (K := K) G hlower
    have hkPos : 0 < k := by
      have hePos := ramificationIndex_pos K
      exact_mod_cast (show (0 : Int) < (k : Int) by
        rw [hkInt, hGzero]
        simp
        exact_mod_cast hePos)
    rcases exists_valuationUnit_quadraticApproximation
        (K := K) (-(p₀ * p₁)) hqUnit k hkPos hweak with
      ⟨s, hs, herror⟩
    exact ⟨s, hs, herror, fun h ↦ (hGneg h).elim⟩

end BONG

end Bong
