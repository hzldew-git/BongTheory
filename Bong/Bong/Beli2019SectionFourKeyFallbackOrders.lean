/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyOrders

/-!
# Beli (2019), Lemma 4.2: order consequences in the left fallback branch

The final paragraph of the proof of Lemma 4.2(i) starts from failure of the
strict direct-branch inequality.  Essentiality then gives the crossings
`S_i < T_(i-2)` and, away from the endpoint, `S_i < R_(i+2)`.  Condition
2.1(i) consequently gives `R_(i+1) <= S_(i+1)`.
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

/-- Failure of Lemma 4.2(i)'s direct trigger is precisely its weak reverse
inequality at an interior essential index. -/
theorem keyLemmaLeftFallback_sourceNext_add_middleCurrent_le_targetPreviousPair
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.order ⟨j.val + 1, hiNext⟩ + b.order ⟨j.val, j.lt_large⟩ ≤
      c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ := by
  apply le_of_not_gt
  intro hstrict
  apply hfailure
  intro _ _
  simpa only [nextEssentialIndex] using hstrict

/-- Essentiality at the next endpoint gives `T_(i-1) < R_(i+1)`. -/
theorem keyLemmaLeftFallback_targetPrevious_lt_sourceNext
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j) :
    c.order ⟨j.val - 1, by omega⟩ < a.order ⟨j.val + 1, hiNext⟩ := by
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hraw := hessential.1 j.pos hiNext
  simpa only [orderSequence_at, nextEssentialIndex] using hraw

/-- In the fallback branch, `S_i < T_(i-2)`. -/
theorem keyLemmaLeftFallback_middleCurrent_lt_targetPreviousPrevious
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    b.order ⟨j.val, j.lt_large⟩ < c.order ⟨j.val - 2, by omega⟩ := by
  have hweak :=
    a.keyLemmaLeftFallback_sourceNext_add_middleCurrent_le_targetPreviousPair
      b c j hiTwo hiNext hfailure
  have hcross :=
    a.keyLemmaLeftFallback_targetPrevious_lt_sourceNext c j hiNext hessential
  omega

/-- Condition 2.1(i) for the middle-to-target pair turns
`S_i < T_(i-2)` into the adjacent-pair comparison
`S_(i-1) + S_i <= T_(i-2) + T_(i-1)` used in the fallback proof. -/
theorem keyLemmaLeftFallback_middlePreviousPair_le_targetPreviousPair
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    b.order ⟨j.val - 1, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ ≤
      c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ := by
  have hcross :=
    a.keyLemmaLeftFallback_middleCurrent_lt_targetPreviousPrevious
      b c j hiTwo hiNext hessential hfailure
  rcases hbc ⟨j.val - 1, by omega⟩ with hprevious | ⟨_, _, hpair⟩
  · change b.order ⟨j.val - 1, by omega⟩ ≤
        c.order ⟨j.val - 1, by omega⟩ at hprevious
    omega
  · have hpair' :
        b.order ⟨j.val - 1, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ ≤
          c.order ⟨j.val - 2, by omega⟩ +
            c.order ⟨j.val - 1, by omega⟩ := by
      simpa only [Nat.sub_add_cancel (show 1 ≤ j.val by omega), Nat.sub_sub]
        using hpair
    exact hpair'

/-- Combining the preceding comparison with essentiality gives exactly the
positive secondary coefficient needed to apply Lemma 2.9 at `i + 1`. -/
theorem keyLemmaLeftFallback_middlePreviousPair_lt_sourceNextPair
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    b.order ⟨j.val - 1, by omega⟩ + b.order ⟨j.val, j.lt_large⟩ <
      a.order ⟨j.val + 1, hiNext⟩ +
        a.order ⟨j.val + 2, hiNextNext⟩ := by
  have hfirst :=
    a.keyLemmaLeftFallback_middlePreviousPair_le_targetPreviousPair
      b c hbc j hiTwo hiNext hessential hfailure
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hsecondRaw := hessential.2 hiTwo hiNextNext
  have hsecond :
      c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hiNext⟩ +
          a.order ⟨j.val + 2, hiNextNext⟩ := by
    simpa only [orderSequence_at, nextEssentialIndex] using hsecondRaw
  exact hfirst.trans_lt hsecond

/-- Away from the right endpoint, the fallback branch also gives
`S_i < R_(i+2)`. -/
theorem keyLemmaLeftFallback_middleCurrent_lt_sourceNextNext
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    b.order ⟨j.val, j.lt_large⟩ < a.order ⟨j.val + 2, hiNextNext⟩ := by
  have hweak :=
    a.keyLemmaLeftFallback_sourceNext_add_middleCurrent_le_targetPreviousPair
      b c j hiTwo hiNext hfailure
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hstrictRaw := hessential.2 hiTwo hiNextNext
  have hstrict :
      c.order ⟨j.val - 2, by omega⟩ + c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hiNext⟩ +
          a.order ⟨j.val + 2, hiNextNext⟩ := by
    simpa only [orderSequence_at, nextEssentialIndex] using hstrictRaw
  omega

/-- Condition 2.1(i) turns the preceding crossing into
`R_(i+1) <= S_(i+1)`, including the penultimate boundary. -/
theorem keyLemmaLeftFallback_sourceNext_le_middleNext
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hiNext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.order ⟨j.val + 1, hiNext⟩ ≤ b.order ⟨j.val + 1, hiNext⟩ := by
  by_cases hiNextNext : j.val + 2 < n + 1
  · have hcross := a.keyLemmaLeftFallback_middleCurrent_lt_sourceNextNext
      b c j hiTwo hiNext hiNextNext hessential hfailure
    have hbound := (a.representationOrderCondition_iff b le_rfl).mp hab
    have hcurrent := hbound.current_le_of_next_ge_previous
      (j.val + 1) (by omega) (by omega) hiNextNext (le_of_lt hcross)
    change a.order ⟨j.val + 1, hiNext⟩ ≤
      b.order ⟨j.val + 1, hiNext⟩ at hcurrent
    exact hcurrent
  · rcases hab ⟨j.val + 1, hiNext⟩ with hcurrent | ⟨_, hnext, _⟩
    · exact hcurrent
    · exact (hiNextNext hnext).elim

end BONG.GoodBONG

end Bong
