/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIIMiddleAlpha

/-!
# Beli (2019), Lemma 6.9(i): the type-II core alphas

The last alpha before the right type-II transition is also one.  Its
adjacent target orders are `T, T + 1`, so the adjacent defect is zero and
the corresponding left-defect candidate is exactly one.  Together with
the constant-middle result, this covers every alpha used in case 5 of
Lemma 7.9(ii).
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The target alpha immediately before the right type-II transition is
one. -/
theorem beli2019Lemma69_i_typeII_targetBoundary_eq_one
    [Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeII a b) :
    b.alphaValue ⟨D.outer.transition.firstTwo - 2, by
      have hbound := D.outer.transition.firstTwo_le_rank
      have hlong := D.long
      omega⟩ = 1 := by
  let k := D.outer.transition.firstTwo - 2
  have hkBound : k < n + 1 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    simp only [k]
    omega
  let current : Fin (n + 1) := ⟨k, hkBound⟩
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hsourceCurrent : a.orderSequence.entryOrZero k = T := by
    apply D.middle k
    · have hlong := D.long
      simp only [k]
      omega
    · have hlong := D.long
      simp only [k]
      omega
  have hcommonCurrent : a.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero k := by
    apply D.outer.transition.middle k
    · have hlong := D.long
      simp only [k]
      omega
    · have hlong := D.long
      simp only [k]
      omega
  have htargetCurrent : b.orderSequence.entryOrZero k = T :=
    hcommonCurrent.symm.trans hsourceCurrent
  have hnextIndex : k + 1 = D.outer.transition.firstTwo - 1 := by
    have hlong := D.long
    simp only [k]
    omega
  have htargetNext : b.orderSequence.entryOrZero (k + 1) = T + 1 := by
    rw [hnextIndex, D.right_target]
  have hcurrentOrder : b.order current.castSucc = T := by
    rw [← b.orderSequence_entryOrZero_eq_order current.castSucc]
    exact htargetCurrent
  have hnextOrder : b.order current.succ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order current.succ]
    change b.orderSequence.entryOrZero (k + 1) = T + 1
    exact htargetNext
  have hsumOdd : Odd (b.order current.castSucc + b.order current.succ) := by
    rw [hcurrentOrder, hnextOrder]
    exact ⟨T, by omega⟩
  have hadjacent : b.adjacentDefect current = 0 :=
    b.adjacentDefect_eq_zero_of_order_sum_odd current hsumOdd
  have hgap : b.order current.succ - b.order current.castSucc = 1 := by
    rw [hcurrentOrder, hnextOrder]
    omega
  have hcandidate : b.leftDefectCandidate current current =
      (1 : WithTop ℚ) := by
    unfold leftDefectCandidate
    rw [hadjacent, hgap]
    norm_num
  have hupperTop := b.alpha_le_leftDefectCandidate
    (i := current) (j := current) le_rfl
  rw [← b.coe_alphaValue, hcandidate] at hupperTop
  have hupper : b.alphaValue current ≤ 1 := by
    exact_mod_cast hupperTop
  have hgapValue : b.orderGap current = 1 := by
    unfold orderGap
    rw [hcurrentOrder, hnextOrder]
    omega
  have hne : b.alphaValue current ≠ 0 := by
    intro hzero
    have hp2 := (b.alpha_p2 current).2.mp hzero
    rw [hgapValue] at hp2
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hlower := b.one_le_alphaValue_of_ne_zero current hne
  have heq : b.alphaValue current = 1 := le_antisymm hupper hlower
  simpa only [current, k] using heq

/-- Every type-II target alpha from the left transition through the alpha
immediately before the right transition equals one. -/
theorem beli2019Lemma69_i_typeII_targetCore_eq_one
    [Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (k : Nat) (hleft : D.outer.transition.lastZero ≤ k)
    (hright : k + 2 ≤ D.outer.transition.firstTwo) :
    b.alphaValue ⟨k, by
      have hbound := D.outer.transition.firstTwo_le_rank
      omega⟩ = 1 := by
  rcases lt_or_eq_of_le hright with hstrict | heq
  · exact a.beli2019Lemma69_i_typeII_targetMiddle_eq_one
      b D hfirst k hleft hstrict
  · have hk : k = D.outer.transition.firstTwo - 2 := by omega
    subst k
    exact a.beli2019Lemma69_i_typeII_targetBoundary_eq_one b D

end BONG.GoodBONG

end Bong
