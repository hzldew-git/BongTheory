/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIMiddle
import Bong.Bong.Beli2019Lemma79RightProfileAlpha
import Bong.Bong.Beli2019Remark613TypeIIRightAlphaLocal
import Bong.Bong.Beli2019Remark613TypeIIIRightAlphaLocal

/-!
# Beli (2019), Lemma 7.9(iii): common right-tail exclusions

On a no-gap-two right profile the target alphas alternate between one and an
integer at most `2e - 1`.  This file derives the latter bound directly from
the two-step order equality and property P2, then packages the adjacent-alpha
exclusion used in cases 3 and 9.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- On the even-distance part of a no-gap-two right profile, an adjacent
odd-distance alpha equal to one forces the current alpha to be at most
`2e - 1`. -/
theorem lemma79Central_outerRight_evenAlpha_le_twoE_sub_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (k : Nat) (hright : O.transition.firstTwo - 1 ≤ k)
    (htwo : k + 2 ≤ O.last)
    (heven : Even (k - (O.transition.firstTwo - 1)))
    (hnextOne : b.alphaValue ⟨k + 1, by
      have hbound := O.lastDifference.bound
      omega⟩ = 1) :
    b.alphaValue ⟨k, by
      have hbound := O.lastDifference.bound
      omega⟩ ≤ 2 * (ramificationIndex K : ℚ) - 1 := by
  have hlastBound := O.lastDifference.bound
  have hkLarge : k < n + 2 := by omega
  have hkNextLarge : k + 1 < n + 2 := by omega
  have hkFarLarge : k + 2 < n + 2 := by omega
  let j : RepresentationIndex (n + 2) (n + 2) :=
    ⟨k + 1, by omega, hkNextLarge, hkNextLarge.le⟩
  have hjOdd : Odd (j.val - (O.transition.firstTwo - 1)) := by
    rcases heven with ⟨d, hd⟩
    exact ⟨d, by simp only [j]; omega⟩
  have hprofile := lemma79_rightProfile_target_twoStep_and_alpha
    a b O j (by simp only [j]; omega) (by simp only [j]; omega) hjOdd
  have htwoStep : b.order ⟨k, hkLarge⟩ =
      b.order ⟨k + 2, hkFarLarge⟩ := by
    simpa only [j, show k + 1 - 1 = k by omega] using hprofile.1
  let current : Fin (n + 1) := ⟨k, by omega⟩
  let next : Fin (n + 1) := ⟨k + 1, by omega⟩
  have hcurrentCast : current.castSucc = ⟨k, hkLarge⟩ := by
    apply Fin.ext
    rfl
  have hcurrentSucc : current.succ = ⟨k + 1, hkNextLarge⟩ := by
    apply Fin.ext
    rfl
  have hnextCast : next.castSucc = ⟨k + 1, hkNextLarge⟩ := by
    apply Fin.ext
    rfl
  have hnextSucc : next.succ = ⟨k + 2, hkFarLarge⟩ := by
    apply Fin.ext
    rfl
  have hgapOpposite : b.orderGap next = -b.orderGap current := by
    unfold orderGap
    rw [hcurrentCast, hcurrentSucc, hnextCast, hnextSucc, htwoStep]
    ring
  have hnextLower := b.orderGap_ge_neg_two_mul_e next
  have hgapLe : b.orderGap current ≤
      2 * (ramificationIndex K : Int) := by
    rw [hgapOpposite] at hnextLower
    omega
  have hgapNe : b.orderGap current ≠
      2 * (ramificationIndex K : Int) := by
    intro heq
    have hnextGap : b.orderGap next =
        -(2 * (ramificationIndex K : Int)) := by
      rw [hgapOpposite, heq]
    have hzero := (b.alpha_p2 next).2.mpr hnextGap
    have hnextOne' : b.alphaValue next = 1 := by
      simpa only [next] using hnextOne
    rw [hnextOne'] at hzero
    norm_num at hzero
  have hgapLt : b.orderGap current <
      2 * (ramificationIndex K : Int) := lt_of_le_of_ne hgapLe hgapNe
  have halphaLt : b.alphaValue current <
      2 * (ramificationIndex K : ℚ) :=
    (b.beli2009Corollary28_ii current).1.mpr hgapLt
  by_contra hnot
  have hstrict : 2 * (ramificationIndex K : ℚ) - 1 <
      b.alphaValue current := lt_of_not_ge hnot
  have hlarge := b.alphaValue_ge_twoE_of_gt_twoE_sub_one current hstrict
  exact (not_lt_of_ge hlarge) halphaLt

/-- An odd-distance point below an even-distance endpoint is at least one
step before that endpoint. -/
theorem lemma79Central_succ_le_of_odd_distance_of_even_endpoint
    (base i last : Nat) (hbase : base ≤ i) (hilast : i ≤ last)
    (hiOdd : Odd (i - base)) (hlastEven : Even (last - base)) :
    i + 1 ≤ last := by
  have hbaseLast : base ≤ last := hbase.trans hilast
  have hiRecover := Nat.sub_add_cancel hbase
  have hlastRecover := Nat.sub_add_cancel hbaseLast
  rcases hiOdd with ⟨d, hd⟩
  rcases hlastEven with ⟨e, he⟩
  omega

end BONG.GoodBONG

end Bong
