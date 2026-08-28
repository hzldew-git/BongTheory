/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneParity

/-!
# Beli (2019), Lemma 7.9(ii), case 8: extending prefix parity

On the strict gap-one tail every beta is an odd integer and equals the
difference between its right target order and the target order at the last
changed coordinate.  If that base order is `T + 1`, all following target
orders therefore lie in the class `T`.  This file turns that observation
into the prefix congruences consumed by the common parity engine.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V} {n : Nat}

/-- The odd explicit-beta formula puts every order following `first` in
the congruence class of `reference`. -/
theorem CaseEightStrictBetaTailConsequences.tail_order_modEq_reference
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (reference : Int)
    (hbase : b.order first.castSucc = reference + 1)
    (hformula : ∀ j : Fin (n + 1), first ≤ j → j ≤ last →
      b.alphaValue j =
        ((b.order j.succ - b.order first.castSucc : Int) : Rat))
    (k : Nat) (hfirst : first.val + 1 ≤ k)
    (hlast : k ≤ last.val + 1) :
    Int.ModEq 2 (b.orderSequence.entryOrZero k) reference := by
  have hkBound : k < n + 2 := by omega
  have hkPos : 0 < k := by omega
  let j : Fin (n + 1) := ⟨k - 1, by omega⟩
  have hjFirst : first ≤ j := by
    change first.val ≤ k - 1
    omega
  have hjLast : j ≤ last := by
    change k - 1 ≤ last.val
    omega
  rcases H.alpha_odd j hjFirst hjLast with ⟨z, hzOdd, hz⟩
  have hzEq : z = b.order j.succ - b.order first.castSucc := by
    exact_mod_cast hz.symm.trans (hformula j hjFirst hjLast)
  have hdiffOdd : Odd
      (b.order j.succ - b.order first.castSucc) := by
    simpa only [hzEq] using hzOdd
  let kFin : Fin (n + 2) := ⟨k, hkBound⟩
  have hkFin : kFin = j.succ := by
    apply Fin.ext
    simp only [kFin, j, Fin.val_succ]
    omega
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hkBound]
  change Int.ModEq 2 (b.order kFin) reference
  rw [hkFin]
  apply int_modEq_two_of_even_sub
  rcases hdiffOdd with ⟨d, hd⟩
  rw [hbase] at hd
  exact ⟨d + 1, by omega⟩

/-- Extend the initial prefix congruence across any initial segment of the
strict gap-one tail. -/
theorem CaseEightStrictBetaTailConsequences.targetPrefix_modEq_of_gapOne
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (reference : Int)
    (hbase : b.order first.castSucc = reference + 1)
    (hformula : ∀ j : Fin (n + 1), first ≤ j → j ≤ last →
      b.alphaValue j =
        ((b.order j.succ - b.order first.castSucc : Int) : Rat))
    (hprefix : Int.ModEq 2
      (b.orderSequence.prefixSum (first.val + 1))
      (((first.val + 1 : Nat) : Int) * reference + 1))
    (endIndex : Nat) (hstart : first.val + 1 ≤ endIndex)
    (hend : endIndex ≤ last.val + 2) :
    Int.ModEq 2 (b.orderSequence.prefixSum endIndex)
      ((endIndex : Int) * reference + 1) := by
  have hsum := b.orderSequence.prefixSum_modEq_add_mul_of_tail
    (((first.val + 1 : Nat) : Int) * reference + 1) reference
    hstart hprefix (by
      intro k hkStart hkEnd
      exact H.tail_order_modEq_reference reference hbase hformula k
        hkStart (by omega))
  have hcastSub : ((endIndex - (first.val + 1) : Nat) : Int) =
      (endIndex : Int) - (first.val + 1 : Nat) := by
    omega
  have hformulaReference :
      ((first.val + 1 : Nat) : Int) * reference + 1 +
          ((endIndex - (first.val + 1) : Nat) : Int) * reference =
        (endIndex : Int) * reference + 1 := by
    rw [hcastSub]
    push_cast
    ring
  rw [hformulaReference] at hsum
  exact hsum

end BONG.GoodBONG

end Bong
