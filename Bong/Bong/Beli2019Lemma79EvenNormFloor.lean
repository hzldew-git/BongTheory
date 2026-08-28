/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTargetDomination
import Bong.Bong.Beli2019Lemma79NormOrder

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the norm-floor branch

The strict norm-ideal inequality places the first target order at least one
above the first source order. Two-step monotonicity propagates this lower
bound to every even target entry. Consequently, the low-order witness from
the domination split is impossible whenever the next intermediate order is
the source norm floor.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Case 3 is immediate when the next intermediate order equals the lower
bound forced by the strict norm-ideal inequality. -/
theorem lemma79_even_targetDefect_of_sourceNext_eq_normFloor
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hsourceNext : b.order ⟨i.val, i.lt_large⟩ = a.order 0 + 1) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.alternatingPrefixDefect i.val := by
  rcases lemma79_even_targetDefect_or_exists_lowWitness
      b c i hiTwo hiEven with hdefect | ⟨j, hjEven, _, hjLow, _⟩
  · exact hdefect
  · have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
      c.toBONG hnorm
    have hcMonotoneEntry :=
      c.orderSequence.entryOrZero_le_of_evenGap
        0 j.val (Nat.zero_le _) (by omega) hjEven
    have hcMonotone : c.order 0 ≤ c.order j.castSucc := by
      calc
        c.order 0 = c.orderSequence.entryOrZero 0 := by
          rw [c.orderSequence.entryOrZero_of_lt (by omega)]
          rfl
        _ ≤ c.orderSequence.entryOrZero j.val := hcMonotoneEntry
        _ = c.order j.castSucc := by
          rw [c.orderSequence.entryOrZero_of_lt (by omega)]
          rfl
    have hsourceLe : b.order ⟨i.val, i.lt_large⟩ ≤
        c.order j.castSucc := by
      rw [hsourceNext]
      exact hnormOrder.trans hcMonotone
    exact (not_lt_of_ge hsourceLe hjLow).elim

end BONG.GoodBONG

end Bong
