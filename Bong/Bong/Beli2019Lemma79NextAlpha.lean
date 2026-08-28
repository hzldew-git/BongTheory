/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79DefectOdd

/-!
# Beli (2019), Lemma 7.9(ii): the next-alpha estimate

Property P1 turns equality of the source orders two coordinates apart and
the bound on the preceding alpha into the next-alpha estimate used in the
odd-coordinate branch of condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The P1 estimate `beta_(i+1) <= S_i - S_(i+1) + 1` from equality
`S_i = S_(i+2)` and `beta_i <= 1`, in zero-based Lean coordinates. -/
theorem nextAlphaValue_le_of_twoStep_eq
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 1)) (i : Fin n) (hi : 0 < i.1)
    (htwoStep : b.orderSequence.entryOrZero (i.1 + 1) =
      b.orderSequence.entryOrZero (i.1 - 1))
    (hprevious : b.alphaValue ⟨i.1 - 1, by omega⟩ ≤ 1) :
    b.alphaValue i ≤
      ((b.orderSequence.entryOrZero (i.1 - 1) -
        b.orderSequence.entryOrZero i.1 + 1 : Int) : ℚ) := by
  let previous : Fin n := ⟨i.1 - 1, by omega⟩
  have hpreviousInternal : previous.1 + 1 < n := by
    simp only [previous]
    omega
  have hp1 := (b.alpha_p1 previous hpreviousInternal).2
  have hnextAlphaIndex :
      (⟨previous.1 + 1, hpreviousInternal⟩ : Fin n) = i := by
    apply Fin.ext
    change i.1 - 1 + 1 = i.1
    omega
  rw [hnextAlphaIndex] at hp1
  unfold alphaRightEndpoint at hp1
  have hpreviousSucc : previous.succ =
      i.castSucc := by
    apply Fin.ext
    change i.1 - 1 + 1 = i.1
    omega
  rw [hpreviousSucc] at hp1
  have hnextEntry : b.orderSequence.entryOrZero (i.1 + 1) =
      b.order i.succ := by
    have h := b.orderSequence_entryOrZero_eq_order i.succ
    change b.orderSequence.entryOrZero (i.1 + 1) = b.order i.succ at h
    exact h
  have hpreviousEntry : b.orderSequence.entryOrZero (i.1 - 1) =
      b.order previous.castSucc := by
    have h := b.orderSequence_entryOrZero_eq_order previous.castSucc
    change b.orderSequence.entryOrZero (i.1 - 1) =
      b.order previous.castSucc at h
    exact h
  have hnextOrder : b.order i.succ = b.order previous.castSucc :=
    hnextEntry.symm.trans (htwoStep.trans hpreviousEntry)
  have hp1' : -(b.order i.succ : ℚ) + b.alphaValue i ≤
      -(b.order i.castSucc : ℚ) + b.alphaValue previous := by
    exact hp1
  rw [hnextOrder] at hp1'
  have hcurrentEntry : b.orderSequence.entryOrZero i.1 =
      b.order i.castSucc :=
    b.orderSequence_entryOrZero_eq_order i.castSucc
  rw [hpreviousEntry, hcurrentEntry]
  push_cast
  have hprevious' : b.alphaValue previous ≤ 1 := by
    simpa only [previous] using hprevious
  linarith

/-- In a normalized type-III profile, every even target alpha on the left
tail is at most one.  The central bound is Lemma 6.9(i), transferred by the
monotonicity of the left alpha endpoint along equal even target orders. -/
theorem beli2019Lemma69_i_typeIII_targetLeftTail
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hlast : D.outer.last = n + 1)
    (k : Nat) (hk : k ≤ D.outer.transition.lastZero) (heven : Even k) :
    b.alphaValue ⟨k, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ ≤ 1 := by
  let center : Fin (n + 1) := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let current : Fin (n + 1) := ⟨k, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have hcenterEven := D.outer.left_even_of_first_eq_zero hfirst
  have hcurrentOrder := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two k hk heven
  have hcenterOrder := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hcenterEven
  have horders : b.order current.castSucc = b.order center.castSucc := by
    rw [← b.orderSequence_entryOrZero_eq_order current.castSucc,
      ← b.orderSequence_entryOrZero_eq_order center.castSucc]
    change b.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero D.outer.transition.lastZero
    exact hcurrentOrder.trans hcenterOrder.symm
  have hmono := b.alphaLeftEndpoint_monotone
    (show current ≤ center by
      change k ≤ D.outer.transition.lastZero
      exact hk)
  unfold alphaLeftEndpoint at hmono
  rw [horders] at hmono
  have hcenterAlpha : b.alphaValue center ≤ 1 := by
    simpa only [center] using a.beli2019Lemma69_i_typeIII_target
      b D horder hdefect htotal hlast
  have hcurrentAlpha : b.alphaValue current ≤ 1 := by
    linarith
  simpa only [current] using hcurrentAlpha

end BONG.GoodBONG

end Bong
