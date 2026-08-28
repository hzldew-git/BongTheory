/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralRegions
import Bong.Bong.Beli2019Lemma69TypeIICoreAlpha
import Bong.Bong.Beli2019Lemma76TypeICentral

/-!
# Beli (2019), Lemma 7.9(iii): profile exclusions in the middle region

The two alternatives produced by Lemma 2.18 are adjacent target-alpha
sums.  On the type-I middle interval their possible parity is forced by
the constant even-order plateau: the left sum cannot be strict at an even
boundary, and the right sum cannot be strict at an odd boundary.  On the
type-II middle interval both target alphas in the left sum are exactly one,
so that sum never exceeds `2e`.

These are the short exclusion arguments at the start of cases 2 and 6 of
the printed proof.  The remaining even type-I right alternative is the
parity contradiction completed separately in case 6.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- In the type-I middle interval, the first adjacent-alpha alternative is
impossible at an even boundary. -/
theorem lemma79Central_typeIMiddle_not_leftAlphaSum_of_even
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiEven : Even i.val) :
    ¬ 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ := by
  intro hsum
  have hstrict := b.order_twoStep_lt_of_alphaSum_gt_twoE i hsum
  have hiPreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hprevious := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst (i.val - 2) (by
      rcases hiEven with ⟨d, hd⟩
      rcases C.left_even with ⟨e, he⟩
      omega) (by omega) hiPreviousEven
  have hcurrent := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hleft.le hright hiEven
  have heq : b.order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hprevious.symm.trans hcurrent
  exact (ne_of_lt hstrict) heq

/-- In the type-I middle interval, the second adjacent-alpha alternative is
impossible at an odd boundary. -/
theorem lemma79Central_typeIMiddle_not_rightAlphaSum_of_odd
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiNext : i.val + 1 < n + 2)
    (hiOdd : Odd i.val) :
    ¬ 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val, by omega⟩ := by
  intro hsum
  let j : CentralRepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNext, by omega⟩
  have hsum' : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨j.val - 2, by
        have := j.lt_large
        omega⟩ +
        b.alphaValue ⟨j.val - 1, by
          have := j.lt_large
          omega⟩ := by
    simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega,
      show i.val + 1 - 1 = i.val by omega] using hsum
  have hstrict := b.order_twoStep_lt_of_alphaSum_gt_twoE j hsum'
  have hpreviousEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hnextEven : Even (i.val + 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hprevious := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst (i.val - 1) (by
      rcases C.left_even with ⟨d, hd⟩
      rcases hiOdd with ⟨e, he⟩
      omega) (by omega) hpreviousEven
  have hnext := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst (i.val + 1) (by omega) (by
      rcases C.right_even with ⟨d, hd⟩
      rcases hiOdd with ⟨e, he⟩
      omega) hnextEven
  have heq : b.order ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ =
      b.order ⟨i.val + 1, hiNext⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hprevious.symm.trans hnext
  have hstrict' : b.order ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ <
      b.order ⟨i.val + 1, hiNext⟩ := by
    simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega] using hstrict
  exact (ne_of_lt hstrict') heq

/-- In the type-II middle interval the two target alphas in the first
alternative are both one, so their sum is at most `2e`. -/
theorem lemma79Central_typeIIMiddle_not_leftAlphaSum
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : D.outer.transition.lastZero + 1 < i.val)
    (hright : i.val < D.outer.transition.firstTwo) :
    ¬ 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ := by
  intro hsum
  have hprevious := a.beli2019Lemma69_i_typeII_targetCore_eq_one
    b D hfirst (i.val - 2) (by omega) (by omega)
  have hcurrent := a.beli2019Lemma69_i_typeII_targetCore_eq_one
    b D hfirst (i.val - 1) (by omega) (by omega)
  rw [hprevious, hcurrent] at hsum
  have hePos := ramificationIndex_pos (K := K)
  norm_num at hsum
  exact (Nat.ne_of_gt hePos) hsum

end BONG.GoodBONG

end Bong
