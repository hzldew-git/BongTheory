/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62HalfGap

/-!
# Beli (2019), Proposition 6.2: reduction from condition 2.1(i)

If the second comparison alternative for an even entry of `W` fails,
property P1 turns that failure into a strict failure of the corresponding
pair alternative for the order sequences.  Condition 2.1(i) then forces the
pointwise order comparison and the strict cross inequality used in the
candidate analysis of `A_i`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Failure of the pair alternative at a noninitial even coordinate forces
the two order inequalities recorded at the start of Proposition 6.2. -/
theorem order_bounds_of_weightPair_lt
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val)
    (hpair :
      2 * (b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) +
          b.alphaValue ⟨i.val - 1, by
            have := i.pos
            have := i.lt_large
            omega⟩ -
          b.alphaValue ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ <
        (a.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) +
          (a.order ⟨i.val, i.lt_large⟩ : ℚ)) :
    a.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ ≤
        b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ ∧
      b.order ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ <
        a.order ⟨i.val, i.lt_large⟩ ∧
      b.order ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ +
          b.order ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ <
        a.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ + a.order ⟨i.val, i.lt_large⟩ := by
  let previous : Fin n := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let current : Fin n := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hnext : (⟨previous.val + 1, by
      simp only [previous]
      have := i.lt_large
      omega⟩ : Fin n) = current := by
    apply Fin.ext
    simp only [previous, current]
    omega
  have hp1 := (b.alpha_p1 previous (by
    simp only [previous]
    have := i.lt_large
    omega)).1
  unfold alphaLeftEndpoint at hp1
  rw [hnext] at hp1
  have htarget :
      (b.order previous.castSucc : ℚ) +
          (b.order current.castSucc : ℚ) ≤
        2 * (b.order current.castSucc : ℚ) + b.alphaValue current -
          b.alphaValue previous := by
    linarith
  have hpair' :
      2 * (b.order current.castSucc : ℚ) + b.alphaValue current -
          b.alphaValue previous <
        (a.order current.castSucc : ℚ) + (a.order current.succ : ℚ) := by
    simpa only [previous, current, Fin.castSucc_mk, Fin.succ_mk,
      Nat.sub_add_cancel i.pos] using hpair
  have hstrict :
      (b.order previous.castSucc : ℚ) +
          (b.order current.castSucc : ℚ) <
        (a.order current.castSucc : ℚ) + (a.order current.succ : ℚ) :=
    htarget.trans_lt hpair'
  let O := (a.representationOrderCondition_iff b le_rfl).mp horder
  have hcurrent : a.order current.castSucc ≤ b.order current.castSucc := by
    rcases O.compare current.val (by omega) with hdirect | ⟨_, hlarge, hsum⟩
    · exact hdirect
    · have hsumQ :
          (a.order current.castSucc : ℚ) + (a.order current.succ : ℚ) ≤
            (b.order previous.castSucc : ℚ) +
              (b.order current.castSucc : ℚ) := by
        exact_mod_cast (show
          a.order current.castSucc + a.order ⟨current.val + 1, hlarge⟩ ≤
            b.order ⟨current.val - 1, by omega⟩ +
              b.order current.castSucc from hsum)
      exact (not_lt_of_ge hsumQ hstrict).elim
  have hcurrentQ : (a.order current.castSucc : ℚ) ≤
      (b.order current.castSucc : ℚ) := by
    exact_mod_cast hcurrent
  have hcrossQ : (b.order previous.castSucc : ℚ) <
      (a.order current.succ : ℚ) := by
    linarith
  have hcross : b.order previous.castSucc < a.order current.succ := by
    exact_mod_cast hcrossQ
  have hstrictInt : b.order previous.castSucc + b.order current.castSucc <
      a.order current.castSucc + a.order current.succ := by
    exact_mod_cast hstrict
  simpa only [previous, current, Fin.castSucc_mk, Fin.succ_mk,
    Nat.sub_add_cancel i.pos] using
      And.intro hcurrent (And.intro hcross hstrictInt)

end BONG.GoodBONG

end Bong
