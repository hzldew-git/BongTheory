/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma73Scalar
import Bong.Bong.BinaryDiagonalEvenSpinorUpper

/-!
# The three-factor defect calculation in Beli (2003), Lemma 7.3

For adjacent parameters `p₀`, `p₁` of orders `G`, `-G`, the endpoint
ratio has negative parameter `-(p₀p₁)`.  Lemma 7.2 and the domination
principle bound its defect by combining `d(-p₀)`, `d(-p₁)`, and `d(-1)`.
The bound is strict when `G < 0`, exactly as used in the first branch of
Beli's ternary argument.
-/

namespace Bong

open Dyadic

universe u


variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

noncomputable def lemma73CentralDepth (G : Int) : Nat :=
  Int.toNat ((ramificationIndex K : Int) + G / 2)

theorem lemma73CentralDepth_cast
    (G : Int) (hlower : -(2 * (ramificationIndex K : Int)) ≤ G) :
    (lemma73CentralDepth (K := K) G : Int) =
      (ramificationIndex K : Int) + G / 2 := by
  unfold lemma73CentralDepth
  rw [Int.toNat_of_nonneg]
  omega

theorem lemma73_parameterProduct_defect_bounds
    (p₀ p₁ : Kˣ) (G : Int)
    (hG₀ : ordUnit K p₀ = G)
    (hG₁ : ordUnit K p₁ = -G)
    (hEven : Even G)
    (hlower : -(2 * (ramificationIndex K : Int)) ≤ G)
    (hupper : G ≤ 0)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K) p₀)
    (h₁ : SatisfiesLemma72UnitCriterion (K := K) p₁) :
    ((lemma73CentralDepth (K := K) G : Nat) : ℕ∞) ≤
        quadraticDefect K (-(p₀ * p₁)) ∧
      (G < 0 →
        ((lemma73CentralDepth (K := K) G : Nat) : ℕ∞) <
          quadraticDefect K (-(p₀ * p₁))) := by
  let k := lemma73CentralDepth (K := K) G
  have hkInt : (k : Int) = (ramificationIndex K : Int) + G / 2 :=
    lemma73CentralDepth_cast (K := K) G hlower
  have hcut₀ : 0 ≤ (ramificationIndex K : Int) - ordUnit K p₀ / 2 := by
    rw [hG₀]
    omega
  have hcut₁ : 0 ≤ (ramificationIndex K : Int) - ordUnit K p₁ / 2 := by
    rw [hG₁]
    omega
  have hd₀Cut := beliParameterDefect_cutoff_le_of_unitCriterion
    (K := K) p₀ h₀ hcut₀
  have hd₀ : (k : ℕ∞) ≤ beliParameterDefect K p₀ := by
    apply le_trans ?_ hd₀Cut
    have hkLeCutInt : (k : Int) ≤
        (ramificationIndex K : Int) - ordUnit K p₀ / 2 := by
      rw [hkInt, hG₀]
      omega
    have hkLeCutNat : k ≤
        ((ramificationIndex K : Int) - ordUnit K p₀ / 2).toNat := by
      have hcast : (k : Int) ≤
          (((ramificationIndex K : Int) - ordUnit K p₀ / 2).toNat : Nat) := by
        rw [Int.toNat_of_nonneg hcut₀]
        exact hkLeCutInt
      exact_mod_cast hcast
    exact_mod_cast hkLeCutNat
  have hnotEndpoint₁ :
      ¬IsNegativeDiscriminantQuarterParameter (K := K) p₁ := by
    intro hendpoint
    have hePos := ramificationIndex_pos K
    rcases hendpoint with ⟨hendpointOrder, _⟩
    rw [hG₁] at hendpointOrder
    omega
  have hd₁Strict :=
    beliParameterDefect_cutoff_lt_of_unitCriterion_of_not_endpoint
      (K := K) p₁ h₁ hnotEndpoint₁ hcut₁
  have hcut₁Eq :
      ((ramificationIndex K : Int) - ordUnit K p₁ / 2).toNat = k := by
    have hcast :
        ((((ramificationIndex K : Int) - ordUnit K p₁ / 2).toNat : Nat) : Int) =
          (k : Int) := by
      rw [Int.toNat_of_nonneg hcut₁, hkInt, hG₁]
      rcases hEven with ⟨r, hr⟩
      omega
    exact_mod_cast hcast
  have hd₁ : (k : ℕ∞) < beliParameterDefect K p₁ := by
    rwa [hcut₁Eq] at hd₁Strict
  have hkLeE : k ≤ ramificationIndex K := by
    exact_mod_cast (show (k : Int) ≤ (ramificationIndex K : Int) by
      rw [hkInt]
      rcases hEven with ⟨r, hr⟩
      omega)
  have hkLeE' : (k : ℕ∞) ≤ (ramificationIndex K : Nat) := by
    exact_mod_cast hkLeE
  have hdMinusOne : (k : ℕ∞) ≤ quadraticDefect K (-1 : Kˣ) :=
    hkLeE'.trans
      (BONG.ramificationIndex_le_quadraticDefect_neg_one (K := K))
  have hdom₀₁ := quadraticDefect_mul_ge_min K (-p₀) (-p₁)
  have hproduct₀₁ : (k : ℕ∞) ≤
      quadraticDefect K ((-p₀) * (-p₁)) :=
    (le_min (by simpa [beliParameterDefect] using hd₀)
      (by simpa [beliParameterDefect] using hd₁.le)).trans hdom₀₁
  have hdomFinal :=
    quadraticDefect_mul_ge_min K ((-p₀) * (-p₁)) (-1 : Kˣ)
  have hweak : (k : ℕ∞) ≤ quadraticDefect K (-(p₀ * p₁)) := by
    have h := (le_min hproduct₀₁ hdMinusOne).trans hdomFinal
    simpa [mul_assoc] using h
  refine ⟨hweak, ?_⟩
  intro hGneg
  have hkLtE : k < ramificationIndex K := by
    exact_mod_cast (show (k : Int) < (ramificationIndex K : Int) by
      rw [hkInt]
      rcases hEven with ⟨r, hr⟩
      omega)
  have hkLtE' : (k : ℕ∞) < (ramificationIndex K : Nat) := by
    exact_mod_cast hkLtE
  have hdMinusOneStrict :
      (k : ℕ∞) < quadraticDefect K (-1 : Kˣ) :=
    hkLtE'.trans_le
      (BONG.ramificationIndex_le_quadraticDefect_neg_one (K := K))
  have hd₀Strict : (k : ℕ∞) < beliParameterDefect K p₀ := by
    have hkLtCutNat : k <
        ((ramificationIndex K : Int) - ordUnit K p₀ / 2).toNat := by
      have hkLtCutInt : (k : Int) <
          (ramificationIndex K : Int) - ordUnit K p₀ / 2 := by
        rw [hkInt, hG₀]
        rcases hEven with ⟨r, hr⟩
        omega
      have hcast : (k : Int) <
          (((ramificationIndex K : Int) - ordUnit K p₀ / 2).toNat : Nat) := by
        rw [Int.toNat_of_nonneg hcut₀]
        exact hkLtCutInt
      exact_mod_cast hcast
    have hkLtCutENat : (k : ℕ∞) <
        (((ramificationIndex K : Int) - ordUnit K p₀ / 2).toNat : ℕ∞) := by
      exact_mod_cast hkLtCutNat
    exact hkLtCutENat.trans_le hd₀Cut
  have hproduct₀₁Strict :
      (k : ℕ∞) < quadraticDefect K ((-p₀) * (-p₁)) :=
    (lt_min (by simpa [beliParameterDefect] using hd₀Strict)
      (by simpa [beliParameterDefect] using hd₁)).trans_le hdom₀₁
  have hfinal :
      (k : ℕ∞) < quadraticDefect K (((-p₀) * (-p₁)) * (-1 : Kˣ)) :=
    (lt_min hproduct₀₁Strict hdMinusOneStrict).trans_le hdomFinal
  simpa [mul_assoc] using hfinal

end Dyadic

end Bong
