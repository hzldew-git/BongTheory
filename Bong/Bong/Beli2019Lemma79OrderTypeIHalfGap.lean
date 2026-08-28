/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeICentralParity

/-!
# Beli (2019), Lemma 7.9(i): excluding the type-I half-gap candidate

In the difficult even type-I class, a nonpositive half-gap candidate would
force the first source gap to be `1 - 2e`.  The normalized strict initial-gap
hypothesis and the evenness of every negative good-BONG gap make this
impossible.  Thus the active nonpositive candidate is primary or secondary.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The half-gap candidate is strictly positive whenever the direct target
comparison fails at a nonterminal difficult even type-I coordinate. -/
theorem lemma79_typeI_even_halfGap_pos_of_not_le
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkEven : Even k) (hleft : C.leftSwitch ≤ k)
    (hlast : k ≤ D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk) :
    0 < a.representationHalfGap c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } := by
  let i : RepresentationIndex (n + 2) (n + 2) := {
    val := k + 1
    pos := by omega
    lt_large := hkNext
    le_small := hkNext.le }
  rcases lemma79_typeI_even_failure_orders
      a b c D C hfirst hnorm k hk hkEven hleft hlast hnot with
    ⟨_, _, hcCurrent⟩
  by_contra hnotPositive
  have hhalf : a.representationHalfGap c i ≤ 0 :=
    le_of_not_gt hnotPositive
  unfold representationHalfGap at hhalf
  norm_cast at hhalf
  push_cast at hhalf
  simp only [Rat.divInt_eq_div] at hhalf
  have hdiffQ :
      ((a.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) ≤
        -(2 * (ramificationIndex K : ℚ)) := by
    linarith
  have hdiff : a.orderSequence.entryOrZero (k + 1) -
      c.orderSequence.entryOrZero k ≤
        -(2 * (ramificationIndex K : Int)) := by
    have hdiffInt : a.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
          -(2 * (ramificationIndex K : Int)) := by
      exact_mod_cast hdiffQ
    rw [a.orderSequence_entryOrZero_eq_order
        ⟨k + 1, hkNext⟩,
      c.orderSequence_entryOrZero_eq_order ⟨k, hk⟩]
    simpa only [i, Nat.add_sub_cancel] using hdiffInt
  have hsourceMonotone := a.orderSequence.entryOrZero_le_of_evenGap
    1 (k + 1) (by omega) hkNext (by
      simpa only [Nat.add_sub_cancel] using hkEven)
  have hinitialFormula : a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩ =
      a.orderSequence.entryOrZero 1 -
        a.orderSequence.entryOrZero 0 := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    rfl
  have hinitialUpper : a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩ ≤
      1 - 2 * (ramificationIndex K : Int) := by
    rw [hinitialFormula]
    omega
  have hinitialEq : a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩ =
      1 - 2 * (ramificationIndex K : Int) := by
    omega
  have hePos := ramificationIndex_pos (K := K)
  have hinitialNegative : a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩ < 0 := by
    rw [hinitialEq]
    omega
  have hinitialEven := a.orderGap_even_of_negative
    ⟨0, by have hbound := D.anchor_bound; omega⟩ hinitialNegative
  have hinitialOdd : Odd (a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩) := by
    rw [hinitialEq]
    exact ⟨-(ramificationIndex K : Int), by omega⟩
  exact (Int.not_even_iff_odd.mpr hinitialOdd) hinitialEven

end BONG.GoodBONG

end Bong
