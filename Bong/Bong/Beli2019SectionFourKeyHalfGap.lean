/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyOrders
import Bong.Bong.Beli2019CappedDefectTriangle
import Bong.Bong.Beli2019Lemma214Bounds

/-!
# Beli (2019), Lemma 4.2: the half-gap candidate

This file proves the first candidate comparison in the direct branch of
Lemma 4.2(i).  It is the short contradiction at the start of the paper's
candidate analysis.
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

/-- The target invariant `C_(i-1)` cannot strictly exceed the half-gap
candidate of `A_(i-1)` in Lemma 4.2(i)'s interior direct branch. -/
theorem representationAlpha_le_leftDirect_sourceHalfGap
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val)
    (hsourceCurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩) :
    a.representationAlpha c j ≤ a.representationHalfGap b j := by
  have hjLarge := j.lt_large
  by_contra hnot
  have hstrict : a.representationHalfGap b j <
      a.representationAlpha c j := lt_of_not_ge hnot
  have htargetHalf : a.representationAlpha c j ≤
      a.representationHalfGap c j := a.representationAlpha_le_halfGap c j
  have hfirst : c.order ⟨j.val - 1, by omega⟩ <
      b.order ⟨j.val - 1, by omega⟩ := by
    have h := hstrict.trans_le htargetHalf
    unfold representationHalfGap at h
    norm_cast at h ⊢
    simp only [Rat.divInt_eq_div] at h ⊢
    push_cast at h ⊢
    have hcast :
        (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
          (b.order ⟨j.val - 1, by omega⟩ : ℚ) := by
      linarith
    exact_mod_cast hcast
  have hsecond :
      b.order ⟨j.val - 1, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ ≤
        c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ := by
    rcases hbc ⟨j.val - 1, by omega⟩ with hcurrent | ⟨_, _, hpair⟩
    · exact (not_lt_of_ge hcurrent hfirst).elim
    · simpa only [Fin.val_mk, Nat.sub_add_cancel (show 1 ≤ j.val by omega),
        Nat.sub_sub] using hpair
  let targetPair : Fin n := ⟨j.val - 2, by omega⟩
  have htargetCast : targetPair.castSucc =
      (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  have hsourceHalf : a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ : ℚ) -
          (c.order ⟨j.val - 2, by omega⟩ : ℚ) / 2 -
          (c.order ⟨j.val - 1, by omega⟩ : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    calc
      a.representationAlpha c j ≤ a.representationAlphaPrime c j :=
        a.representationAlpha_le_prime c j
      _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (c.halfGapValue targetPair : WithTop ℚ) :=
        a.representationAlphaPrime_le_primaryRightHalfGap c j hiTwo
      _ = _ := by
        norm_cast
        unfold halfGapValue orderGap
        rw [htargetCast, htargetSucc]
        simp only [Rat.divInt_eq_div]
        push_cast
        ring
  have hsum :
      c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val, j.lt_large⟩ + b.order ⟨j.val - 1, by omega⟩ := by
    have h := hstrict.trans_le hsourceHalf
    unfold representationHalfGap at h
    norm_cast at h ⊢
    simp only [Rat.divInt_eq_div] at h ⊢
    push_cast at h ⊢
    have hcast :
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
            (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
          (a.order ⟨j.val, j.lt_large⟩ : ℚ) +
            (b.order ⟨j.val - 1, by omega⟩ : ℚ) := by
      linarith
    exact_mod_cast hcast
  have htargetLt :
      c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ <
        b.order ⟨j.val - 1, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ := by
    omega
  exact (not_lt_of_ge hsecond) htargetLt

/-- The first-boundary case of the half-gap comparison in Lemma 4.2(i). -/
theorem representationAlpha_le_leftDirect_sourceHalfGap_of_eq_one
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1)) (hj : j.val = 1) :
    a.representationAlpha c j ≤ a.representationHalfGap b j := by
  by_contra hnot
  have hstrict : a.representationHalfGap b j <
      a.representationAlpha c j := lt_of_not_ge hnot
  have htargetHalf : a.representationAlpha c j ≤
      a.representationHalfGap c j := a.representationAlpha_le_halfGap c j
  have hfirst : c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
    have h := hstrict.trans_le htargetHalf
    unfold representationHalfGap at h
    norm_cast at h ⊢
    simp only [Rat.divInt_eq_div] at h ⊢
    push_cast at h ⊢
    have hcast :
        (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
          (b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) := by
      linarith
    exact_mod_cast hcast
  rcases hbc ⟨j.val - 1, by have := j.lt_large; omega⟩ with hcurrent |
      ⟨hiPos, _, _⟩
  · exact (not_lt_of_ge hcurrent hfirst).elim
  · change 0 < j.val - 1 at hiPos
    omega

/-- At the last boundary, condition 2.1(i) directly supplies the current
order comparison needed by the half-gap argument. -/
theorem representationAlpha_le_leftDirect_sourceHalfGap_of_last
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hlast : j.val + 1 = n + 1) :
    a.representationAlpha c j ≤ a.representationHalfGap b j := by
  have hsourceCurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩ := by
    rcases hab ⟨j.val, j.lt_large⟩ with hcurrent | ⟨_, hiNext, _⟩
    · exact hcurrent
    · change j.val + 1 < n + 1 at hiNext
      omega
  exact a.representationAlpha_le_leftDirect_sourceHalfGap
    b c hbc j hiTwo hsourceCurrent

/-- The half-gap part of the first direct conclusion of Lemma 4.2(i). -/
theorem representationAlpha_le_leftDirect_sourceHalfGap_of_conditions
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j ≤ a.representationHalfGap b j :=
  a.representationAlpha_le_leftDirect_sourceHalfGap b c hbc j hiTwo
    (a.keyLemmaLeftDirect_sourceCurrent_le_middleCurrent b c hab hbc j
      hiTwo hiNext hessential hdirect)

/-- The half-gap candidate in Lemma 4.2(i), including both endpoint
conventions of the paper. -/
theorem representationAlpha_le_leftDirect_sourceHalfGap_of_direct
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j ≤ a.representationHalfGap b j := by
  by_cases hfirst : j.val = 1
  · exact a.representationAlpha_le_leftDirect_sourceHalfGap_of_eq_one
      b c hbc j hfirst
  by_cases hlast : j.val + 1 = n + 1
  · have hiTwo : 1 < j.val := by
      have := j.pos
      omega
    exact a.representationAlpha_le_leftDirect_sourceHalfGap_of_last
      b c hab hbc j hiTwo hlast
  · have hiTwo : 1 < j.val := by
      have := j.pos
      omega
    have hiNext : j.val + 1 < n + 1 := by
      have := j.lt_large
      omega
    exact a.representationAlpha_le_leftDirect_sourceHalfGap_of_conditions
      b c hab hbc j hiTwo hiNext hessential hdirect

end BONG.GoodBONG

end Bong
