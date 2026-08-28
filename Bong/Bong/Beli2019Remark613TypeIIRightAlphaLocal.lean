/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69SourceAlphaLocal
import Bong.Bong.Beli2019Lemma69TypeIIDual
import Bong.Bong.Beli2019Lemma69TypeIRightEndpoint
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha

/-!
# Beli (2019), Remark 6.13: local type-II right alphas

Reverse duality turns the right interval into a left outer interval.  The
local left-alpha theorem measures parity from the actual first unequal
order, so a common suffix of the original pair causes no normalization
problem.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The type-II source alpha at the left transition is one.  This local
seed only uses the transition and middle-order identities. -/
theorem lemma69_typeII_sourceBoundary_eq_one_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) :
    a.alphaValue ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      have hlong := D.long
      omega⟩ = 1 := by
  let left := D.outer.transition.lastZero
  have hleftBound : left < n + 1 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    dsimp only [left]
    omega
  let center : Fin (n + 1) := ⟨left, hleftBound⟩
  let T := b.orderSequence.entryOrZero left
  have hsourceCurrent : a.orderSequence.entryOrZero left = T - 1 := by
    have hboundary := D.outer.transition.leftBoundary
    have hboundary' : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using hboundary
    dsimp only [T]
    omega
  have hsourceNext : a.orderSequence.entryOrZero (left + 1) = T := by
    simpa only [T] using D.middle (left + 1) (by omega) (by
      have hlong := D.long
      omega)
  have hcurrentOrder : a.order center.castSucc = T - 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order center.castSucc]
    exact hsourceCurrent
  have hnextOrder : a.order center.succ = T := by
    rw [← a.orderSequence_entryOrZero_eq_order center.succ]
    change a.orderSequence.entryOrZero (left + 1) = T
    exact hsourceNext
  have hsumOdd : Odd (a.order center.castSucc + a.order center.succ) := by
    rw [hcurrentOrder, hnextOrder]
    exact ⟨T - 1, by omega⟩
  have hadjacent : a.adjacentDefect center = 0 :=
    a.adjacentDefect_eq_zero_of_order_sum_odd center hsumOdd
  have hgap : a.order center.succ - a.order center.castSucc = 1 := by
    rw [hcurrentOrder, hnextOrder]
    omega
  have hcandidate : a.leftDefectCandidate center center =
      (1 : WithTop ℚ) := by
    unfold leftDefectCandidate
    rw [hadjacent, hgap]
    norm_num
  have hupperTop := a.alpha_le_leftDefectCandidate
    (i := center) (j := center) le_rfl
  rw [← a.coe_alphaValue, hcandidate] at hupperTop
  have hupper : a.alphaValue center ≤ 1 := by
    exact_mod_cast hupperTop
  have hgapValue : a.orderGap center = 1 := by
    unfold orderGap
    rw [hcurrentOrder, hnextOrder]
    omega
  have hne : a.alphaValue center ≠ 0 := by
    intro hzero
    have hp2 := (a.alpha_p2 center).2.mp hzero
    rw [hgapValue] at hp2
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hlower := a.one_le_alphaValue_of_ne_zero center hne
  have heq : a.alphaValue center = 1 := le_antisymm hupper hlower
  simpa only [center, left] using heq

/-- On the alternating right interval of a type-II pair, every target
alpha at odd distance from the right transition is one, without requiring
the last unequal order to have full rank. -/
theorem beli2019Remark613_typeII_targetRightAlpha_eq_one_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (k : Nat) (hright : D.outer.transition.firstTwo ≤ k)
    (hbeforeLast : k < D.outer.last)
    (hodd : Odd (k - (D.outer.transition.firstTwo - 1))) :
    b.alphaValue ⟨k, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ = 1 := by
  rcases a.exists_reverseDual_typeII_local b D horder hdefect htotal with
    ⟨aDual, bDual, Ddual, _, _, _, hbAlpha, _, _, hdualFirst,
      hdualLeft, _⟩
  let target : Fin (n + 1) := ⟨k, by
    have hlastBound := D.outer.lastDifference.bound
    omega⟩
  let dualTarget : Fin (n + 1) := Fin.rev target
  let iDual := dualTarget.val + 2
  have hdualTargetVal : dualTarget.val = n - k := by
    simp only [dualTarget, target, Fin.rev]
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hcenter : bDual.alphaValue
      ⟨Ddual.outer.transition.lastZero, by
        have hbound := Ddual.outer.transition.firstTwo_le_rank
        have hlong := Ddual.long
        omega⟩ = 1 := by
    exact bDual.lemma69_typeII_sourceBoundary_eq_one_local
      aDual Ddual
  have hiFirst : Ddual.outer.first + 2 ≤ iDual := by
    simp only [iDual, hdualTargetVal]
    rw [hdualFirst]
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hiLeft : iDual ≤ Ddual.outer.transition.lastZero := by
    simp only [iDual, hdualTargetVal]
    rw [hdualLeft]
    have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hrightProfile := D.outer.rightProfile (by omega)
  have hiEven : Even (iDual - Ddual.outer.first) := by
    rcases hrightProfile.1 with ⟨e, he⟩
    rcases hodd with ⟨d, hd⟩
    refine ⟨e - d, ?_⟩
    simp only [iDual, hdualTargetVal]
    rw [hdualFirst]
    have hlastBound := D.outer.lastDifference.bound
    have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
    omega
  have hdualOne := bDual.lemma69_sourcePreviousAlpha_eq_one_local
    aDual Ddual.outer Ddual.no_gap_two hcenter iDual hiFirst hiLeft hiEven
  have hdualOneAt : bDual.alphaValue dualTarget = 1 := by
    convert hdualOne using 1
    apply congrArg bDual.alphaValue
    apply Fin.ext
    simp only [iDual]
    omega
  have hreverseTarget : Fin.rev dualTarget = target := by
    simp only [dualTarget, Fin.rev_rev]
  calc
    b.alphaValue ⟨k, by
        have hlastBound := D.outer.lastDifference.bound
        omega⟩ = b.alphaValue target := by rfl
    _ = b.alphaValue (Fin.rev dualTarget) := by rw [hreverseTarget]
    _ = bDual.alphaValue dualTarget := (hbAlpha dualTarget).symm
    _ = 1 := hdualOneAt

end BONG.GoodBONG

end Bong
