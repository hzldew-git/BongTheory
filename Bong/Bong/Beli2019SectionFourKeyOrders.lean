/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourDefectReduction

/-!
# Beli (2019), Lemma 4.2: order consequences in the left direct branch

The first paragraph of the proof of Lemma 4.2(i) derives three order
comparisons from essentiality, the direct-branch inequality, and the two
instances of condition 2.1(i).  They are isolated here because every later
candidate comparison uses the same three facts.
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

/-- In Lemma 4.2(i)'s interior direct branch,
`S_i + S_(i+1) > T_(i-2) + T_(i-1)`.

If `S_(i+1) >= R_(i+1)`, this follows from the direct trigger.  Otherwise
condition 2.1(i) for `M,N` selects its adjacent-pair alternative, and
essentiality supplies the strict comparison with the source pair. -/
theorem keyLemmaLeftDirect_middlePair_lt
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ <
      b.order ⟨j.val, j.lt_large⟩ + b.order ⟨j.val + 1, hiNext⟩ := by
  have htrigger :
      c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hiNext⟩ + b.order ⟨j.val, j.lt_large⟩ := by
    simpa only [nextEssentialIndex] using hdirect hiTwo hiNext
  by_cases hmiddle : a.order ⟨j.val + 1, hiNext⟩ ≤
      b.order ⟨j.val + 1, hiNext⟩
  · omega
  · have hmiddleLt : b.order ⟨j.val + 1, hiNext⟩ <
        a.order ⟨j.val + 1, hiNext⟩ := lt_of_not_ge hmiddle
    rcases hab ⟨j.val + 1, hiNext⟩ with hcurrent | ⟨_, hiLarge, hpair⟩
    · exact (not_lt_of_ge hcurrent hmiddleLt).elim
    · unfold IsNextEssential IsEssentialFor
        BeliOrderSequence.IsEssentialFor at hessential
      have hsourcePair := hessential.2 hiTwo hiLarge
      simp only [orderSequence_at, nextEssentialIndex] at hsourcePair
      have hpair' :
          a.order ⟨j.val + 1, hiNext⟩ +
              a.order ⟨j.val + 2, hiLarge⟩ ≤
            b.order ⟨j.val, j.lt_large⟩ +
              b.order ⟨j.val + 1, hiNext⟩ := by
        simpa only [Nat.add_sub_cancel] using hpair
      exact hsourcePair.trans_le hpair'

/-- In Lemma 4.2(i)'s interior direct branch, `R_(i+1) > S_(i-1)`.

Assuming the reverse inequality contradicts either alternative of condition
2.1(i) for `N,K`: the pointwise alternative contradicts essentiality, while
the adjacent-pair alternative contradicts the direct trigger. -/
theorem keyLemmaLeftDirect_middlePrevious_lt_sourceNext
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    b.order ⟨j.val - 1, by omega⟩ < a.order ⟨j.val + 1, hiNext⟩ := by
  have htrigger :
      c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hiNext⟩ + b.order ⟨j.val, j.lt_large⟩ := by
    simpa only [nextEssentialIndex] using hdirect hiTwo hiNext
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hessentialPos : 0 < (nextEssentialIndex j).val := by
    simp only [nextEssentialIndex]
    omega
  have hessentialNext : (nextEssentialIndex j).val + 1 < n + 1 := by
    simpa only [nextEssentialIndex] using hiNext
  have hcrossRaw := hessential.1 hessentialPos hessentialNext
  simp only [orderSequence_at, nextEssentialIndex] at hcrossRaw
  have hcross : c.order ⟨j.val - 1, by omega⟩ <
      a.order ⟨j.val + 1, hiNext⟩ := hcrossRaw
  by_cases hreverse : a.order ⟨j.val + 1, hiNext⟩ ≤
      b.order ⟨j.val - 1, by omega⟩
  · exfalso
    have htargetLt : c.order ⟨j.val - 1, by omega⟩ <
        b.order ⟨j.val - 1, by omega⟩ := hcross.trans_le hreverse
    rcases hbc ⟨j.val - 1, by omega⟩ with hcurrent | ⟨_, _, hpair⟩
    · exact (not_lt_of_ge hcurrent htargetLt).elim
    · have hpair' :
          b.order ⟨j.val - 1, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ ≤
            c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ := by
        simpa only [Fin.val_mk, Nat.sub_add_cancel (show 1 ≤ j.val by omega),
          Nat.sub_sub] using hpair
      have hsourceMiddle :
          a.order ⟨j.val + 1, hiNext⟩ + b.order ⟨j.val, j.lt_large⟩ ≤
            b.order ⟨j.val - 1, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ :=
        by simpa only [add_comm] using
          add_le_add_right hreverse (b.order ⟨j.val, j.lt_large⟩)
      exact (not_lt_of_ge (hsourceMiddle.trans hpair')) htrigger
  · exact lt_of_not_ge hreverse

/-- The preceding strict crossing forces `R_i <= S_i` by condition 2.1(i)
for the source-to-middle pair. -/
theorem keyLemmaLeftDirect_sourceCurrent_le_middleCurrent
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.order ⟨j.val, j.lt_large⟩ ≤ b.order ⟨j.val, j.lt_large⟩ := by
  have hcross := a.keyLemmaLeftDirect_middlePrevious_lt_sourceNext
    b c hbc j hiTwo hiNext hessential hdirect
  rcases hab ⟨j.val, j.lt_large⟩ with hcurrent | ⟨_, _, hpair⟩
  · exact hcurrent
  · have hpair' :
        a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hiNext⟩ ≤
          b.order ⟨j.val - 1, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ := by
      simpa using hpair
    omega

/-- At the first boundary of Lemma 4.2(i), essentiality and condition
2.1(i) for the middle-to-target pair imply `S₁ < R₃` whenever the third
source coefficient exists. -/
theorem keyLemmaLeftDirect_middleFirst_lt_sourceNext_of_eq_one
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hj : j.val = 1) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j) :
    b.order ⟨0, by omega⟩ < a.order ⟨j.val + 1, hiNext⟩ := by
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hpositive : 0 < (nextEssentialIndex j).val := by
    simp only [nextEssentialIndex, hj]
    omega
  have hnext : (nextEssentialIndex j).val + 1 < n + 1 := by
    simpa only [nextEssentialIndex] using hiNext
  have hcrossRaw := hessential.1 hpositive hnext
  have hcross : c.order ⟨0, by omega⟩ <
      a.order ⟨j.val + 1, hiNext⟩ := by
    simpa only [orderSequence_at, nextEssentialIndex, hj, Nat.reduceSubDiff] using hcrossRaw
  by_contra hnot
  have htargetLt : c.order ⟨0, by omega⟩ < b.order ⟨0, by omega⟩ :=
    hcross.trans_le (le_of_not_gt hnot)
  rcases hbc (0 : Fin (n + 1)) with hcurrent | ⟨hiPos, _, _⟩
  · exact (not_lt_of_ge hcurrent htargetLt).elim
  · simp at hiPos

/-- At `i = 2`, the preceding crossing forces `R₂ ≤ S₂`.  This is the
endpoint version of `keyLemmaLeftDirect_sourceCurrent_le_middleCurrent`;
the adjacent-pair alternative is now discharged using `S₁ < R₃`. -/
theorem keyLemmaLeftDirect_sourceCurrent_le_middleCurrent_of_eq_one
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hj : j.val = 1) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j) :
    a.order ⟨j.val, j.lt_large⟩ ≤ b.order ⟨j.val, j.lt_large⟩ := by
  have hcross := a.keyLemmaLeftDirect_middleFirst_lt_sourceNext_of_eq_one
    b c hbc j hj hiNext hessential
  rcases hab ⟨j.val, j.lt_large⟩ with hcurrent | ⟨_, _, hpair⟩
  · exact hcurrent
  · have hpair' :
        a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hiNext⟩ ≤
          b.order ⟨0, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ := by
      simpa only [hj, Nat.reduceSubDiff] using hpair
    omega

end BONG.GoodBONG

end Bong
