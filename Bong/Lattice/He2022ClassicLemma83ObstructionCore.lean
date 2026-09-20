/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicCorollary63

/-!
# Numerical core of the ramified even-rank obstruction

The local classification and Theorem 1.5 turn order scaling, a signed-prefix
defect bound, and unsigned adjacent defect bounds into a contradiction. The
defect bounds are explicit hypotheses here; a finite-completion application
must derive them from the actual coefficient map before claiming Lemma 8.3.
-/

namespace Bong

open Dyadic

universe u v u' v'

variable {F : Type u} [Field F] [CharZero F] [ValuativeRel F]
  [TopologicalSpace F] [DyadicContext F]
  {E : Type u'} [Field E] [CharZero E] [ValuativeRel E]
  [TopologicalSpace E] [DyadicContext E]
  {V : Type v} [AddCommGroup V] [Module F V]
  {W : Type v'} [AddCommGroup W] [Module E W]
  {q : QuadraticSpace F V} {L : Lattice F V}
  {r : QuadraticSpace E W} {M : Lattice E W}

namespace BONG.GoodBONG

/-- Before using any defect estimate, the upper even-universal criterion and
ramified order scaling already force the first `n+2` lower orders to zero. -/
theorem he2022ClassicLemma83_initialOrders_zero_of_scaled_evenUniversal
    [QuadraticDefectLaws E] [HilbertSymbolLaws E]
    [DyadicDiscriminantClassLaws E]
    {n e : Nat} (lower : GoodBONG q L (n + 3))
    (upper : GoodBONG r M (n + 3))
    (hn : 2 ≤ n) (hnEven : Even n) (he : 1 < e)
    (hScale : ∀ i : Fin (n + 3),
      upper.order i = lower.order i * (e : Int))
    (hClassic : Lattice.IsClassicIntegral r M)
    (hUniversal : Lattice.IsClassicNUniversal.{u', v', u'} r M n) :
    ∀ i : Fin (n + 3), i.1 < n + 2 → lower.order i = 0 := by
  have hConditions :=
    (upper.he2022ClassicTheorem11 hn hClassic).mp hUniversal
  have hEven : HeClassicEvenConditions upper n hConditions.rank_bound := by
    rcases hConditions.parity_branch with h | h
    · exact h
    · exact False.elim ((Nat.not_even_iff_odd.mpr h.parity) hnEven)
  have hN2 : upper.order ⟨n + 1, by omega⟩ = 0 := by
    rcases hEven.order_n2 with hZero | hOne
    · exact hZero
    · have hProduct : lower.order ⟨n + 1, by omega⟩ * (e : Int) = 1 := by
        rw [← hScale ⟨n + 1, by omega⟩]
        exact hOne
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hProduct with
        ⟨_, heOne⟩ | ⟨_, heNeg⟩ <;> omega
  intro i hi
  have hUpper : upper.order i = 0 := by
    by_cases hin : i.1 < n
    · simpa only [show (⟨i.1, by omega⟩ : Fin (n + 3)) = i by ext; rfl]
        using hConditions.initial_orders ⟨i.1, hin⟩
    · by_cases hinEq : i.1 = n
      · simpa only [show i = (⟨n, by omega⟩ : Fin (n + 3)) by
            ext; exact hinEq] using hEven.order_n1
      · have hinLast : i.1 = n + 1 := by omega
        simpa only [show i = (⟨n + 1, by omega⟩ : Fin (n + 3)) by
            ext; exact hinLast] using hN2
  have hProduct : lower.order i * (e : Int) = 0 := by
    rw [← hScale i]
    exact hUpper
  exact (mul_eq_zero.mp hProduct).resolve_right (by omega)

/-- Under ramified order scaling, the upper even-universal criterion and a
strict signed-prefix defect bound force every displayed BONG order to vanish
on both sides. The prefix bound is not inferred from order scaling alone. -/
theorem he2022ClassicLemma83_orders_zero_of_scaled_evenUniversal
    [QuadraticDefectLaws E] [HilbertSymbolLaws E]
    [DyadicDiscriminantClassLaws E]
    {n e : Nat} (lower : GoodBONG q L (n + 3))
    (upper : GoodBONG r M (n + 3))
    (hn : 2 ≤ n) (hnEven : Even n) (he : 1 < e)
    (hScale : ∀ i : Fin (n + 3),
      upper.order i = lower.order i * (e : Int))
    (hClassic : Lattice.IsClassicIntegral r M)
    (hUniversal : Lattice.IsClassicNUniversal.{u', v', u'} r M n)
    (hPrefix : (1 : WithTop ℚ) <
      upper.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2)) :
    (∀ i : Fin (n + 3), upper.order i = 0) ∧
      (∀ i : Fin (n + 3), lower.order i = 0) := by
  have hConditions :=
    (upper.he2022ClassicTheorem11 hn hClassic).mp hUniversal
  have hEven : HeClassicEvenConditions upper n hConditions.rank_bound := by
    rcases hConditions.parity_branch with h | h
    · exact h
    · exact False.elim ((Nat.not_even_iff_odd.mpr h.parity) hnEven)
  have hNoOne (i : Fin (n + 3)) (hOne : upper.order i = 1) : False := by
    have hProduct : lower.order i * (e : Int) = 1 := by
      rw [← hScale i]
      exact hOne
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hProduct with
      ⟨_, heOne⟩ | ⟨_, heNeg⟩ <;> omega
  have hN2 : upper.order ⟨n + 1, by omega⟩ = 0 := by
    rcases hEven.order_n2 with hZero | hOne
    · exact hZero
    · exact False.elim (hNoOne ⟨n + 1, by omega⟩ hOne)
  have hN3Option :
      HeClassicZeroOrOne (upper.order ⟨n + 2, by omega⟩) :=
    (hEven.zero_branch hN2).1.resolve_left (ne_of_gt hPrefix)
  have hN3 : upper.order ⟨n + 2, by omega⟩ = 0 := by
    rcases hN3Option with hZero | hOne
    · exact hZero
    · exact False.elim (hNoOne ⟨n + 2, by omega⟩ hOne)
  have hUpper : ∀ i : Fin (n + 3), upper.order i = 0 := by
    intro i
    by_cases hi : i.1 < n
    · simpa only [show (⟨i.1, by omega⟩ : Fin (n + 3)) = i by ext; rfl]
        using hConditions.initial_orders ⟨i.1, hi⟩
    · by_cases hin : i.1 = n
      · simpa only [show i = (⟨n, by omega⟩ : Fin (n + 3)) by
            ext; exact hin] using hEven.order_n1
      · by_cases hin2 : i.1 = n + 1
        · simpa only [show i = (⟨n + 1, by omega⟩ : Fin (n + 3)) by
              ext; exact hin2] using hN2
        · have hiBound := i.isLt
          have hiLast : i.1 = n + 2 := by omega
          simpa only [show i = (⟨n + 2, by omega⟩ : Fin (n + 3)) by
              ext; exact hiLast] using hN3
  refine ⟨hUpper, ?_⟩
  intro i
  have hProduct : lower.order i * (e : Int) = 0 := by
    rw [← hScale i]
    exact hUpper i
  exact (mul_eq_zero.mp hProduct).resolve_right (by omega)

/-- The last classification step of the local obstruction. The two defect
premises remain to be verified for mapped coefficients at finite completions;
this theorem does not silently assume the desired non-universality. -/
theorem he2022ClassicLemma83_contradiction_of_scaled_defects
    [QuadraticDefectLaws E] [HilbertSymbolLaws E]
    [DyadicDiscriminantClassLaws E]
    {n e : Nat} (lower : GoodBONG q L (n + 3))
    (upper : GoodBONG r M (n + 3))
    (hn : 2 ≤ n) (hnEven : Even n) (he : 1 < e)
    (hScale : ∀ i : Fin (n + 3),
      upper.order i = lower.order i * (e : Int))
    (hClassic : Lattice.IsClassicIntegral r M)
    (hUniversal : Lattice.IsClassicNUniversal.{u', v', u'} r M n)
    (hPrefix : (1 : WithTop ℚ) <
      upper.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2))
    (hUnsigned : (∀ i : Fin (n + 3), lower.order i = 0) →
      ∀ j : Fin (n + 2),
        (1 : WithTop ℚ) < upper.heClassicUnsignedAdjacentDefect j)
    (hAbsolute : 1 < ramificationIndex E) : False := by
  obtain ⟨_, hLower⟩ :=
    lower.he2022ClassicLemma83_orders_zero_of_scaled_evenUniversal
      upper hn hnEven he hScale hClassic hUniversal hPrefix
  have hOne := upper.he2022ClassicTheorem15 hn (by omega)
    hClassic hUniversal (hUnsigned hLower)
  omega

end BONG.GoodBONG

end Bong
