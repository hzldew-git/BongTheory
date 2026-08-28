/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyPrimary
import Bong.Bong.Beli2019Lemma27

/-!
# Beli (2019), Lemma 4.2: candidate normal forms

The interior proof of Lemma 4.2(i) uses Lemma 2.7(ii) to replace the
secondary candidate by the defect of the two current prefixes.  This file
derives the two crossing inequalities required for that replacement from
essentiality and the direct-branch hypotheses.
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

/-- At an interior next-essential boundary, Definition 5 for the target
pair has exactly the half-gap, primary-defect, and current-prefix secondary
defect candidates used in the proof of Lemma 4.2(i). -/
theorem representationAlpha_eq_min_halfGap_primary_current_of_nextEssential
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j) :
    a.representationAlpha c j =
      min (a.representationHalfGap c j)
        (min (a.representationPrimaryDefect c j)
          (a.representationSecondaryCurrentDefect c j hi)) := by
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hpositive : 0 < (nextEssentialIndex j).val := by
    simp only [nextEssentialIndex]
    omega
  have hnext : (nextEssentialIndex j).val + 1 < n + 1 := by
    simpa only [nextEssentialIndex] using hi.2
  have hcrossRaw := hessential.1 hpositive hnext
  have hcross : c.order ⟨j.val - 1, by omega⟩ ≤
      a.order ⟨j.val + 1, hi.2⟩ := by
    simpa only [orderSequence_at, nextEssentialIndex] using hcrossRaw.le
  rw [a.representationAlpha_eq_min_halfGap_prime c j,
    a.representationAlphaPrime_eq_min_primary_current c j hi hcross]

/-- In the direct branch, the source-to-middle alpha has the same three
candidate normal form.  The crossing `S_(i-1) < R_(i+1)` is the first
order consequence in the proof of Lemma 4.2(i). -/
theorem representationAlpha_eq_min_halfGap_primary_current_of_leftDirect
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha b j =
      min (a.representationHalfGap b j)
        (min (a.representationPrimaryDefect b j)
          (a.representationSecondaryCurrentDefect b j hi)) := by
  have hcross := a.keyLemmaLeftDirect_middlePrevious_lt_sourceNext
    b c hbc j hi.1 hi.2 hessential hdirect
  rw [a.representationAlpha_eq_min_halfGap_prime b j,
    a.representationAlphaPrime_eq_min_primary_current b j hi hcross.le]

end BONG.GoodBONG

end Bong
