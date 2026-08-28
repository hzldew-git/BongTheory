/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyMiddlePrime

/-!
# Beli (2019), Lemma 4.2: candidates at the preceding boundary

In the branch `T_(i-2) <= S_i`, condition 2.1(ii) bounds the shifted
`B_(i-2)` by the failing primary candidate `A_(i-1)`.  The shifted half-gap
candidate is at least `C_(i-1)`, so it cannot attain `B_(i-2)`.  Only the
primary and, away from the endpoint, current secondary candidates remain.
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

/-- Lines 2188--2195: after shifting, the half-gap candidate cannot attain
`B_(i-2)`.  At the first preceding boundary only the primary candidate
remains; otherwise the current secondary candidate is the sole alternative. -/
theorem previousMiddleAlpha_eq_primary_or_current_of_cross_failure
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j) :
    let previous := previousRepresentationIndex j hiTwo
    b.representationAlpha c previous =
        b.representationPrimaryDefect c previous ∨
      ∃ hj : 2 < j.val,
        b.representationAlpha c previous =
          b.representationSecondaryCurrentDefect c previous (by
            dsimp only [previous, previousRepresentationIndex]
            have := j.lt_large
            omega) := by
  dsimp only
  let previous := previousRepresentationIndex j hiTwo
  let shift : WithTop ℚ :=
    (((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ)
  have hprevious :=
    b.middlePrevious_le_targetPrevious_of_targetTwoPrevious_le_middleCurrent
      c hbcOrder j hiTwo hcross
  have hhalf := a.targetAlpha_le_shift_previousMiddleHalfGap_of_cross
    b c j hiTwo hprevious
  have hlower := a.shift_previousMiddleAlpha_le_sourcePrimary
    b c hbcOrder hbcDefect j hiTwo hcross hprimary
  have hstrict : shift + b.representationAlpha c previous <
      a.representationAlpha c j := by
    exact hlower.trans_lt hprimary
  have hhalf' : a.representationAlpha c j ≤
      shift + b.representationHalfGap c previous := by
    simpa only [shift, previous] using hhalf
  by_cases hj : j.val = 2
  · have hnormal := b.previousMiddleAlpha_eq_min_halfGap_primary_of_eq_two
      c j hj
    have hnormal' : b.representationAlpha c previous =
        min (b.representationHalfGap c previous)
          (b.representationPrimaryDefect c previous) := by
      simpa only [previous] using hnormal
    rcases min_choice (b.representationHalfGap c previous)
        (b.representationPrimaryDefect c previous) with hgap | hdefect
    · have heq : b.representationAlpha c previous =
          b.representationHalfGap c previous := by
        exact hnormal'.trans hgap
      have hshiftEq := congrArg (fun x => shift + x) heq
      exact False.elim ((not_lt_of_ge hhalf') (hshiftEq ▸ hstrict))
    · exact Or.inl (hnormal'.trans hdefect)
  · have hj' : 2 < j.val := by omega
    have hnormal :=
      b.previousMiddleAlpha_eq_min_halfGap_primary_current_of_cross
        c j hj' hcross
    let hk : 1 < previous.val ∧ previous.val + 1 < n + 1 := by
      dsimp only [previous, previousRepresentationIndex]
      have := j.lt_large
      omega
    have hnormal' : b.representationAlpha c previous =
        min (b.representationHalfGap c previous)
          (min (b.representationPrimaryDefect c previous)
            (b.representationSecondaryCurrentDefect c previous hk)) := by
      simpa only [previous, hk] using hnormal
    rcases min_choice (b.representationHalfGap c previous)
        (min (b.representationPrimaryDefect c previous)
          (b.representationSecondaryCurrentDefect c previous hk)) with
      hgap | hdefect
    · have heq : b.representationAlpha c previous =
          b.representationHalfGap c previous := hnormal'.trans hgap
      have hshiftEq := congrArg (fun x => shift + x) heq
      exact False.elim ((not_lt_of_ge hhalf') (hshiftEq ▸ hstrict))
    · rcases min_choice (b.representationPrimaryDefect c previous)
          (b.representationSecondaryCurrentDefect c previous hk) with
        hprimary' | hcurrent
      · exact Or.inl (hnormal'.trans (hdefect.trans hprimary'))
      · exact Or.inr ⟨hj', by
          simpa only [hk] using hnormal'.trans (hdefect.trans hcurrent)⟩

end BONG.GoodBONG

end Bong
