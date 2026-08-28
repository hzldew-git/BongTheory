/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyNormalForm

/-!
# Beli (2019), Lemma 4.2: extracting a putative failing candidate

After the half-gap comparison, a failure of either direct conclusion can
only be caused by a primary or secondary defect candidate.  These lemmas
make that reduction explicit, including the endpoint convention.
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

/-- If `C` is below the half-gap candidate but strictly above `A`, then
one of the two defect candidates defining `A'` is strictly below `C`.
The existential secondary branch carries the proof that it exists. -/
theorem representationDefectCandidate_lt_of_alpha_lt_of_le_halfGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1)) (C : WithTop ℚ)
    (halpha : a.representationAlpha b j < C)
    (hhalf : C ≤ a.representationHalfGap b j) :
    a.representationPrimaryDefect b j < C ∨
      ∃ hi : 1 < j.val ∧ j.val + 1 < n + 1,
        a.representationSecondaryDefect b j hi < C := by
  rw [a.representationAlpha_eq_min_halfGap_prime b j] at halpha
  rcases min_lt_iff.mp halpha with hhalfStrict | hprime
  · exact False.elim ((not_lt_of_ge hhalf) hhalfStrict)
  · by_cases hi : 1 < j.val ∧ j.val + 1 < n + 1
    · rw [a.representationAlphaPrime_eq_min_primary_secondary b j hi]
        at hprime
      rcases min_lt_iff.mp hprime with hprimary | hsecondary
      · exact Or.inl hprimary
      · exact Or.inr ⟨hi, hsecondary⟩
    · rw [a.representationAlphaPrime_eq_primary_of_not_interior b j hi]
        at hprime
      exact Or.inl hprime

/-- The target alpha is bounded by the middle-to-target half-gap whenever
the current source order is at most the current middle order. -/
theorem representationAlpha_le_middleHalfGap_of_sourceCurrent_le
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩) :
    a.representationAlpha c j ≤ b.representationHalfGap c j := by
  calc
    a.representationAlpha c j ≤ a.representationHalfGap c j :=
      a.representationAlpha_le_halfGap c j
    _ ≤ b.representationHalfGap c j := by
      unfold representationHalfGap
      norm_cast
      simp only [Rat.divInt_eq_div]
      push_cast
      have hcast : (a.order ⟨j.val, j.lt_large⟩ : ℚ) ≤
          (b.order ⟨j.val, j.lt_large⟩ : ℚ) := by
        exact_mod_cast hcurrent
      linarith

/-- In the interior direct branch, failure of `C_(i-1) ≤ A_(i-1)`
forces exactly one of the primary or current-prefix secondary candidates
from the paper to be strictly smaller than `C_(i-1)`. -/
theorem leftDirect_sourceFailure_candidates
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hfailure : ¬a.representationAlpha c j ≤
      a.representationAlpha b j) :
    a.representationPrimaryDefect b j < a.representationAlpha c j ∨
      a.representationSecondaryCurrentDefect b j hi <
        a.representationAlpha c j := by
  have hnormal :=
    by
      letI : Beli2006AlphaLaws.{u, w} K := middleLaws
      exact
        a.representationAlpha_eq_min_halfGap_primary_current_of_leftDirect
          b c hbc j hi hessential hdirect
  have hstrict : a.representationAlpha b j <
      a.representationAlpha c j := lt_of_not_ge hfailure
  rw [hnormal] at hstrict
  rcases min_lt_iff.mp hstrict with hhalf | hdefect
  · have hhalfLe :=
      by
        letI : Beli2006AlphaLaws.{u, z} K := targetLaws
        exact
          a.representationAlpha_le_leftDirect_sourceHalfGap_of_conditions
            b c hab hbc j hi.1 hi.2 hessential hdirect
    exact False.elim ((not_lt_of_ge hhalfLe) hhalf)
  · exact min_lt_iff.mp hdefect

/-- Failure of `C_(i-1) ≤ B_(i-1)` is likewise reduced to a primary
or an existing secondary candidate of the middle-to-target alpha. -/
theorem leftDirect_middleFailure_candidates
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    b.representationPrimaryDefect c j < a.representationAlpha c j ∨
      ∃ hi : 1 < j.val ∧ j.val + 1 < n + 1,
        b.representationSecondaryDefect c j hi <
          a.representationAlpha c j := by
  apply b.representationDefectCandidate_lt_of_alpha_lt_of_le_halfGap c j
  · exact lt_of_not_ge hfailure
  · exact a.representationAlpha_le_middleHalfGap_of_sourceCurrent_le
      b c j hcurrent

end BONG.GoodBONG

end Bong
