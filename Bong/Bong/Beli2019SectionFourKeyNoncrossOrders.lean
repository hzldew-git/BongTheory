/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyCrossComplete

/-!
# Beli (2019), Lemma 4.2: order data in the noncrossed subcase

This file isolates the order calculations at lines 2251--2258.  They are
used repeatedly in the candidate analysis which follows.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- In the branch `S_i < T_(i-2)`, condition 2.1(i) gives
`S_(i-1)+S_i ≤ T_(i-2)+T_(i-1)`. -/
theorem middlePrevious_add_current_le_targetPreviousPair_of_noncross
    (b : GoodBONG r M (n + 1)) (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
        b.order ⟨j.val, j.lt_large⟩ ≤
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
  rcases hbc ⟨j.val - 1, by have := j.lt_large; omega⟩ with
    hcurrent | ⟨_, _, hpair⟩
  · have hcurrent' : b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
      simpa using hcurrent
    omega
  · simpa only [Fin.val_mk, Nat.sub_add_cancel (show 1 ≤ j.val by omega),
      Nat.sub_sub] using hpair

/-- The strict adjacent-pair inequality of the direct branch and the
noncrossed inequality imply `T_(i-1) < S_(i+1)`. -/
theorem targetPrevious_lt_middleNext_of_noncross
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
      b.order ⟨j.val + 1, hi.2⟩ := by
  have hpair := a.keyLemmaLeftDirect_middlePair_lt
    b c hab j hi.1 hi.2 hessential hdirect
  omega

/-- If the second essentiality inequality is present, the preceding
middle pair is strictly below the following source pair. -/
theorem middlePreviousPair_lt_sourceNextPair
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩)
    (hnext : j.val + 2 < n + 1) :
    b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
        b.order ⟨j.val, j.lt_large⟩ <
      a.order ⟨j.val + 1, hi.2⟩ +
        a.order ⟨j.val + 2, hnext⟩ := by
  have hmiddleTarget :=
    b.middlePrevious_add_current_le_targetPreviousPair_of_noncross
      c hbc j hi hnoncross
  have hessentialRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.2 hi.1 hnext
  simp only [orderSequence_at, nextEssentialIndex] at hessentialRaw
  exact hmiddleTarget.trans_lt hessentialRaw

/-- Weak form of `middlePreviousPair_lt_sourceNextPair`. -/
theorem middlePreviousPair_le_sourceNextPair
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩)
    (hnext : j.val + 2 < n + 1) :
    b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
        b.order ⟨j.val, j.lt_large⟩ ≤
      a.order ⟨j.val + 1, hi.2⟩ +
        a.order ⟨j.val + 2, hnext⟩ :=
  (a.middlePreviousPair_lt_sourceNextPair b c hbc j hi hessential
    hnoncross hnext).le

end BONG.GoodBONG

end Bong
