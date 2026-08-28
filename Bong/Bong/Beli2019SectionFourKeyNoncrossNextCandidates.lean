/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyNoncrossOrders

/-!
# Beli (2019), Lemma 4.2: next-source candidates in the noncrossed subcase

Lines 2253--2256 apply Lemma 2.9 at the boundary following `i`.  The
noncrossed order calculation makes its secondary shift positive, and the
left crossing removes the source-alpha candidate.  Thus only the half-gap,
primary, and target-alpha candidates remain.  At the endpoint the last
candidate is absent.
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

/-- The exhaustive candidate split for `A_i` displayed at lines
2253--2256.  The existential alternative records that the following
boundary is interior, so its target-alpha candidate is defined. -/
theorem nextSourceAlpha_noncross_candidates
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    let next := nextRepresentationIndex j hi.2
    a.representationAlpha b next = a.representationHalfGap b next ∨
      a.representationAlpha b next =
        a.representationPrimaryDefect b next ∨
      ∃ hinterior : 1 < next.val ∧ next.val + 1 < n + 1,
        a.representationAlpha b next =
          a.representationSecondaryTargetAlpha b next hinterior
            next.lt_large := by
  let next := nextRepresentationIndex j hi.2
  have hcross : b.order ⟨next.val - 2, by
      have := next.le_small
      omega⟩ ≤ a.order ⟨next.val, next.lt_large⟩ := by
    have hlt := a.keyLemmaLeftDirect_middlePrevious_lt_sourceNext
      b c hbcOrder j hi.1 hi.2 hessential hdirect
    dsimp only [next, nextRepresentationIndex]
    exact hlt.le
  by_cases hinterior : 1 < next.val ∧ next.val + 1 < n + 1
  · have hpair := a.middlePreviousPair_lt_sourceNextPair
      b c hbcOrder j hi hessential hnoncross (by
        dsimp only [next, nextRepresentationIndex] at hinterior
        omega)
    have hshift : 0 <
        a.order ⟨next.val, next.lt_large⟩ +
            a.order ⟨next.val + 1, hinterior.2⟩ -
          b.order ⟨next.val - 2, by have := next.le_small; omega⟩ -
          b.order ⟨next.val - 1, by have := next.le_small; omega⟩ := by
      dsimp only [next, nextRepresentationIndex] at hpair ⊢
      simp only [show j.val + 1 - 2 = j.val - 1 by omega,
        show j.val + 1 + 1 = j.val + 2 by omega,
        Nat.add_sub_cancel] at hpair ⊢
      omega
    have hcomparison : a.representationAlpha b next ≤
        a.truncatedPrefixDefect b 1 next.val next.val := by
      simpa only [← a.coe_representationAlphaValue b next] using
        habDefect next
    have hreduced := a.representationAlpha_eq_reduced_of_positiveShift
      (sourceLaws := sourceLaws) (targetLaws := middleLaws)
      b next hinterior next.lt_large hshift hcomparison
    have hnormal : a.representationAlpha b next =
        min (a.representationHalfGap b next)
          (min (a.representationPrimaryDefect b next)
            (a.representationSecondaryTargetAlpha b next hinterior
              next.lt_large)) := by
      calc
        a.representationAlpha b next =
            a.representationAlphaReduced b next hinterior next.lt_large :=
          hreduced
        _ = _ :=
          a.representationAlphaReduced_eq_min_halfGap_primary_target_of_cross
            b next hinterior next.lt_large hcross
    rcases min_choice (a.representationHalfGap b next)
        (min (a.representationPrimaryDefect b next)
          (a.representationSecondaryTargetAlpha b next hinterior
            next.lt_large)) with hhalf | hrest
    · exact Or.inl (hnormal.trans hhalf)
    · rcases min_choice (a.representationPrimaryDefect b next)
          (a.representationSecondaryTargetAlpha b next hinterior
            next.lt_large) with hprimary | htarget
      · exact Or.inr (Or.inl (hnormal.trans (hrest.trans hprimary)))
      · exact Or.inr (Or.inr ⟨hinterior,
          hnormal.trans (hrest.trans htarget)⟩)
  · have hnormal : a.representationAlpha b next =
        min (a.representationHalfGap b next)
          (a.representationPrimaryDefect b next) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b next,
        a.representationAlphaPrime_eq_primary_of_not_interior
          b next hinterior]
    rcases min_choice (a.representationHalfGap b next)
        (a.representationPrimaryDefect b next) with hhalf | hprimary
    · exact Or.inl (hnormal.trans hhalf)
    · exact Or.inr (Or.inl (hnormal.trans hprimary))

end BONG.GoodBONG

end Bong
