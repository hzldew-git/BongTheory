/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72TypeI
import Bong.Bong.Beli2019Lemma79OrderTypeIITerminal

/-!
# Beli (2019), Lemma 7.9(i): full-rank type-I endpoint

At the final coordinate there is no adjacent-pair alternative.  The full
determinant-square parity, together with Lemma 7.2(i), rules out failure of
the direct comparison.  Both possibilities for the canonical right switch
are handled: a strict right tail contributes the paper's `-1` correction,
while a terminal right switch makes the full prefix length odd.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) at a type-I last difference which is the final rank
coordinate. -/
theorem beli2019Lemma79_i_typeI_fullRankTerminal
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hlastFull : D.profile.last + 1 = n + 2) :
    b.orderSequence.entry D.profile.last
        D.profile.lastDifference.bound ≤
      c.orderSequence.entry D.profile.last
        D.profile.lastDifference.bound := by
  have hk : D.profile.last < n + 2 := D.profile.lastDifference.bound
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    by_cases heq : D.anchor = D.profile.last
    · rw [← heq]
      exact ⟨0, by omega⟩
    · exact (D.profile.rightProfile
        (lt_of_le_of_ne D.profile.anchor_le_last heq)).1
  let R : Int := a.orderSequence.entryOrZero D.anchor
  have hbCurrent : b.orderSequence.entryOrZero D.profile.last = R + 2 := by
    calc
      b.orderSequence.entryOrZero D.profile.last =
          b.orderSequence.entryOrZero D.anchor :=
        C.target_from_anchor D.profile.last D.profile.anchor_le_last
          le_rfl hlastDistance
      _ = R + 2 := by simpa only [R] using D.anchor_gap
  by_contra hnot
  have hcCurrent : c.orderSequence.entryOrZero D.profile.last ≤ R + 1 := by
    rw [b.orderSequence.entryOrZero_of_lt hk] at hbCurrent
    rw [c.orderSequence.entryOrZero_of_lt hk]
    omega
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hreferenceFirst : R + 1 ≤ c.orderSequence.entryOrZero 0 := by
    calc
      R + 1 = a.orderSequence.entryOrZero 0 + 1 := by
        rw [hsourceZero]
      _ = a.order (0 : Fin (n + 2)) + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order (0 : Fin (n + 2)) := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hcParity :=
    c.prefixSum_modEq_mul_of_current_le_reference_le_first
      (R + 1) D.profile.last hk hreferenceFirst hcCurrent
  rcases a.beli2019Lemma72_i b D hfirst with ⟨P⟩
  have hfullParity := a.fullPrefixSum_modEq c
  have hacParity : Int.ModEq 2
      (a.orderSequence.prefixSum (D.profile.last + 1))
      (c.orderSequence.prefixSum (D.profile.last + 1)) := by
    simpa only [hlastFull] using hfullParity
  let X : Int := (((D.profile.last + 1 : Nat) : Int) * (R + 1))
  by_cases hrightLast : P.rightSwitch < D.profile.last
  · have haParity := P.source_after (D.profile.last + 1) (by omega) le_rfl
    have hcontradiction : Int.ModEq 2 (X - 1) X := by
      have ha : Int.ModEq 2
          (a.orderSequence.prefixSum (D.profile.last + 1)) (X - 1) := by
        simpa only [X] using haParity
      have hc : Int.ModEq 2
          (c.orderSequence.prefixSum (D.profile.last + 1)) X := by
        simpa only [X] using hcParity
      exact ha.symm.trans (hacParity.trans hc)
    rw [Int.modEq_iff_dvd] at hcontradiction
    rcases hcontradiction with ⟨d, hd⟩
    omega
  · have hrightEq : P.rightSwitch = D.profile.last :=
      Nat.le_antisymm P.right_le_last (Nat.le_of_not_gt hrightLast)
    have haParity := P.source_before (D.profile.last + 1) (by omega)
    let Y : Int := (((D.profile.last + 1 : Nat) : Int) * R)
    have hcontradiction : Int.ModEq 2 Y
        (Y + (D.profile.last + 1 : Nat)) := by
      have ha : Int.ModEq 2
          (a.orderSequence.prefixSum (D.profile.last + 1)) Y := by
        simpa only [Y] using haParity
      have hc : Int.ModEq 2
          (c.orderSequence.prefixSum (D.profile.last + 1))
            (Y + (D.profile.last + 1 : Nat)) := by
        have hformula : X = Y + (D.profile.last + 1 : Nat) := by
          simp only [X, Y]
          push_cast
          ring
        rw [← hformula]
        simpa only [X] using hcParity
      exact ha.symm.trans (hacParity.trans hc)
    rw [Int.modEq_iff_dvd] at hcontradiction
    rcases hcontradiction with ⟨d, hd⟩
    rcases P.right_even with ⟨e, he⟩
    rw [hrightEq] at he
    push_cast at hd
    omega

end BONG.GoodBONG

end Bong
