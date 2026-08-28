/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710Extension
import Bong.Bong.Beli2019ExtremalDifference

/-!
# Beli (2019), Lemma 7.10: order propagation along the common prefix

In the right-end case of Lemma 7.10, the proof bounds the last two orders of
the unchanged prefix by `R_(t+1)`.  Goodness then bounds every earlier order:
each coordinate lies on one of the two monotone parity chains ending at those
last two coordinates.

This file proves that propagation independently of the later lattice
reconstruction.  Indices are zero based; `cut` is the length of the unchanged
prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/--
Every order strictly before `cut` is bounded by `T` once the final two
orders before `cut` are bounded by `T`.
-/
theorem order_le_of_lt_cut_of_last_two_le
    (b : GoodBONG q L n) (cut : Nat) (hcutTwo : 2 <= cut)
    (hcutRank : cut <= n) (T : Int)
    (hpenultimate :
      b.order ⟨cut - 2, by omega⟩ <= T)
    (hlast : b.order ⟨cut - 1, by omega⟩ <= T)
    (i : Fin n) (hi : i.val < cut) :
    b.order i <= T := by
  rcases Nat.even_or_odd ((cut - 1) - i.val) with heven | hodd
  · have hmono := b.orderSequence.entryOrZero_le_of_evenGap
      i.val (cut - 1) (by omega) (by omega) heven
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.isLt,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)] at hmono
    change b.order i <= b.order ⟨cut - 1, by omega⟩ at hmono
    exact hmono.trans hlast
  · rcases hodd with ⟨k, hk⟩
    have hiPenultimate : i.val <= cut - 2 := by omega
    have heven' : Even ((cut - 2) - i.val) := by
      exact ⟨k, by omega⟩
    have hmono := b.orderSequence.entryOrZero_le_of_evenGap
      i.val (cut - 2) hiPenultimate (by omega) heven'
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.isLt,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)] at hmono
    change b.order i <= b.order ⟨cut - 2, by omega⟩ at hmono
    exact hmono.trans hpenultimate

/--
The form used in the paper.  `s` is the first index of the replacement in
one-based notation, so the unchanged prefix has length `s - 1`.  The case
`s = 2` has only one prefix coordinate; for `s >= 3` the two parity endpoints
are supplied separately.
-/
theorem beli2019Lemma710_prefix_order_le
    (b : GoodBONG q L n) (s : Nat) (hs : 2 <= s)
    (hsRank : s - 1 <= n) (T : Int)
    (hprevious : 3 <= s ->
      b.order ⟨s - 3, by omega⟩ <= T)
    (hlast : b.order ⟨s - 2, by omega⟩ <= T)
    (i : Fin n) (hi : i.val < s - 1) :
    b.order i <= T := by
  by_cases hsTwo : s = 2
  · subst s
    let lastIndex : Fin n := ⟨2 - 2, by omega⟩
    have hindex : i = lastIndex := by
      apply Fin.ext
      simp [lastIndex]
      omega
    calc
      b.order i = b.order lastIndex := congrArg b.order hindex
      _ <= T := by simpa only [lastIndex] using hlast
  · have hsThree : 3 <= s := by omega
    apply b.order_le_of_lt_cut_of_last_two_le
      (s - 1) (by omega) hsRank T
    · simpa only [show s - 1 - 2 = s - 3 by omega] using
        hprevious hsThree
    · simpa only [show s - 1 - 1 = s - 2 by omega] using hlast
    · exact hi

end BONG.GoodBONG

end Bong
