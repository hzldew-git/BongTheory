/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIILeftAlpha

/-!
# Beli (2019), Lemma 6.9(i): the type-II middle alphas

On the constant type-II target plateau, every alpha from the left
transition through the penultimate middle coordinate is one.  The upper
bound propagates from the left transition by right-endpoint antitonicity;
P2 excludes zero because both adjacent orders are equal.
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

/-- Every target alpha wholly contained in the constant type-II plateau
equals one. -/
theorem beli2019Lemma69_i_typeII_targetMiddle_eq_one
    [Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (k : Nat) (hleft : D.outer.transition.lastZero ≤ k)
    (hright : k + 2 < D.outer.transition.firstTwo) :
    b.alphaValue ⟨k, by
      have hbound := D.outer.transition.firstTwo_le_rank
      omega⟩ = 1 := by
  let left := D.outer.transition.lastZero
  let T := b.orderSequence.entryOrZero left
  have hleftBound : left < n + 1 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    simp only [left]
    omega
  have hkBound : k < n + 1 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    omega
  let leftFin : Fin (n + 1) := ⟨left, hleftBound⟩
  let current : Fin (n + 1) := ⟨k, hkBound⟩
  have htargetMiddle (j : Nat) (hleftJ : left < j)
      (hrightJ : j + 1 < D.outer.transition.firstTwo) :
      b.orderSequence.entryOrZero j = T := by
    have hcommon := D.outer.transition.middle j (by
      simpa only [left] using hleftJ) hrightJ
    have hsource := D.middle j (by
      simpa only [left] using hleftJ) hrightJ
    exact hcommon.symm.trans (by simpa only [T, left] using hsource)
  have hleftNext : b.order leftFin.succ = T := by
    rw [← b.orderSequence_entryOrZero_eq_order leftFin.succ]
    change b.orderSequence.entryOrZero (left + 1) = T
    apply htargetMiddle (left + 1)
    · omega
    · simpa only [left] using D.long
  have hcurrentOrder : b.order current.castSucc = T := by
    rw [← b.orderSequence_entryOrZero_eq_order current.castSucc]
    change b.orderSequence.entryOrZero k = T
    by_cases hkLeft : k = left
    · rw [hkLeft]
    · exact htargetMiddle k (lt_of_le_of_ne hleft (Ne.symm hkLeft))
        (by omega)
  have hcurrentNext : b.order current.succ = T := by
    rw [← b.orderSequence_entryOrZero_eq_order current.succ]
    change b.orderSequence.entryOrZero (k + 1) = T
    exact htargetMiddle (k + 1) (by omega) (by omega)
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hleftAlpha := a.beli2019Lemma69_i_typeII_targetLeftTail
    b D hfirst left le_rfl (by simpa only [left] using hleftEven)
  have hcurrentAlphaUpper : b.alphaValue current ≤ 1 := by
    have hmono := b.alphaRightEndpoint_antitone
      (show leftFin ≤ current by
        change left ≤ k
        exact hleft)
    unfold alphaRightEndpoint at hmono
    rw [hleftNext, hcurrentNext] at hmono
    have hleftAlpha' : b.alphaValue leftFin ≤ 1 := by
      simpa only [leftFin, left] using hleftAlpha
    linarith
  have hcurrentGap : b.orderGap current = 0 := by
    unfold orderGap
    rw [hcurrentOrder, hcurrentNext]
    omega
  have hcurrentNe : b.alphaValue current ≠ 0 := by
    intro hzero
    have hgap := (b.alpha_p2 current).2.mp hzero
    rw [hcurrentGap] at hgap
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hcurrentAlphaLower := b.one_le_alphaValue_of_ne_zero
    current hcurrentNe
  have hcurrentEq : b.alphaValue current = 1 :=
    le_antisymm hcurrentAlphaUpper hcurrentAlphaLower
  simpa only [current] using hcurrentEq

end BONG.GoodBONG

end Bong
