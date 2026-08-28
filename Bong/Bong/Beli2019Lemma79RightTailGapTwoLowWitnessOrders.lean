/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenDomination
import Bong.Bong.Beli2019Lemma66

/-!
# Beli (2019), Lemma 7.9(ii), case 8: low-witness orders

In the remaining domination branch the selected comparison order is below
the target order `S_u = T + 1`.  The norm-ideal inequality gives the lower
bound `T <= T_1`, while same-parity monotonicity gives `T_1 <= T_j`.
Integrality therefore forces `T_1 = T_j = T`.  Lemma 6.6(i) then supplies
the prefix parity used by the exceptional branches of the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The low domination witness has the base comparison order at both the
first coordinate and the selected odd paper index.  Its prefix sum is in
that same congruence class modulo two. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_lowWitness_orders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hlow : c.order j.castSucc <
      b.order (Fin.mk D.profile.last hlast).castSucc) :
    c.order (0 : Fin (n + 2)) =
        a.orderSequence.entryOrZero D.anchor + 1 ∧
      c.order j.castSucc =
        a.orderSequence.entryOrZero D.anchor + 1 ∧
      b.order (Fin.mk D.profile.last hlast).castSucc =
        a.orderSequence.entryOrZero D.anchor + 2 ∧
      Int.ModEq 2 (c.orderSequence.prefixSum (j.val + 1))
        (a.orderSequence.entryOrZero D.anchor + 1) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let reference : Int := a.orderSequence.entryOrZero D.anchor + 1
  let firstTarget : Fin (n + 1) := Fin.mk D.profile.last hlast
  have htarget : b.order firstTarget.castSucc = reference + 1 := by
    rw [<- b.orderSequence_entryOrZero_eq_order firstTarget.castSucc]
    change b.orderSequence.entryOrZero D.profile.last =
      (a.orderSequence.entryOrZero D.anchor + 1) + 1
    calc
      b.orderSequence.entryOrZero D.profile.last =
          a.orderSequence.entryOrZero D.anchor + 2 := I.target_last
      _ = (a.orderSequence.entryOrZero D.anchor + 1) + 1 := by omega
  have hsourceZeroEntry : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero D.anchor := by
    exact I.canonical.source_to_anchor 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hlowerZero : reference <= c.order (0 : Fin (n + 2)) := by
    have haZero : a.order (0 : Fin (n + 2)) =
        a.orderSequence.entryOrZero D.anchor := by
      rw [<- a.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2))]
      simpa using hsourceZeroEntry
    change a.order (0 : Fin (n + 2)) + 1 <=
      c.order (0 : Fin (n + 2)) at hnormOrder
    rw [haZero] at hnormOrder
    simpa only [reference] using hnormOrder
  have hzeroCurrentEntry := c.orderSequence.entryOrZero_le_of_evenGap
    0 j.val (Nat.zero_le _) (by omega) hjEven
  have hzeroCurrent : c.order (0 : Fin (n + 2)) <=
      c.order j.castSucc := by
    have hzeroEntry : c.orderSequence.entryOrZero 0 =
        c.order (0 : Fin (n + 2)) := by
      simpa using c.orderSequence_entryOrZero_eq_order
        (0 : Fin (n + 2))
    have hjEntry : c.orderSequence.entryOrZero j.val =
        c.order j.castSucc := by
      simpa using c.orderSequence_entryOrZero_eq_order j.castSucc
    rw [hzeroEntry, hjEntry] at hzeroCurrentEntry
    exact hzeroCurrentEntry
  have hcurrentUpper : c.order j.castSucc < reference + 1 := by
    simpa only [firstTarget, htarget] using hlow
  have hcurrent : c.order j.castSucc = reference := by omega
  have hzero : c.order (0 : Fin (n + 2)) = reference := by omega
  let zero : Fin (n + 2) := 0
  let current : Fin (n + 2) := j.castSucc
  have hjParity : Even (current.val - zero.val) := by
    simpa only [current, zero, Fin.val_castSucc, Fin.val_zero,
      Nat.sub_zero] using hjEven
  have hendpoint : c.order zero = c.order current := by
    simpa only [zero, current, hzero, hcurrent]
  have h66 := c.beli2019Lemma66_i zero current (by
      change zero.val <= current.val
      simp only [zero, current, Fin.val_zero, Fin.val_castSucc]
      omega) hjParity hendpoint
  have hprefix : Int.ModEq 2
      (c.orderSequence.prefixSum (j.val + 1)) reference := by
    have hsum := h66.closedSum_modEq
    simpa only [zero, current, Fin.val_zero, Fin.val_castSucc,
      BeliOrderSequence.closedSegmentSum, BeliOrderSequence.prefixSum,
      Nat.Ico_zero_eq_range, hzero] using hsum
  exact ⟨by simpa only [reference] using hzero,
    by simpa only [reference] using hcurrent,
    by
      simp only [firstTarget, reference] at htarget ⊢
      omega,
    by simpa only [reference] using hprefix⟩

end BONG.GoodBONG

end Bong
