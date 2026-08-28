/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyFallbackOrders
import Bong.Bong.Beli2019Lemma29ReducedEquality

/-!
# Beli (2019), Lemma 4.2: normal form in the left fallback branch

The fallback paragraph applies Lemma 2.9 at the following boundary.  Its
positive secondary coefficient follows from the order chain isolated in
`Beli2019SectionFourKeyFallbackOrders`.  The crossing `S_i < R_(i+2)`
deletes the target-alpha candidate.  At the right endpoint that candidate
and the source-alpha candidate are both absent from the unreduced formula.
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

/-- The exhaustive candidates for `A_(i+1)` in the fallback paragraph of
Lemma 4.2(i).  The existential branch records the interior proof needed to
form the source-alpha candidate. -/
theorem nextSourceAlpha_fallback_candidates
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    let next := nextRepresentationIndex j hi.2
    a.representationAlpha b next = a.representationHalfGap b next ∨
      a.representationAlpha b next =
        a.representationPrimaryDefect b next ∨
      ∃ hinterior : 1 < next.val ∧ next.val + 1 < n + 1,
        a.representationAlpha b next =
          a.representationSecondarySourceAlpha b next hinterior := by
  let next := nextRepresentationIndex j hi.2
  by_cases hinterior : 1 < next.val ∧ next.val + 1 < n + 1
  · have hiNextNext : j.val + 2 < n + 1 := by
      dsimp only [next, nextRepresentationIndex] at hinterior
      omega
    have hpair :=
      a.keyLemmaLeftFallback_middlePreviousPair_lt_sourceNextPair
        b c hbcOrder j hi.1 hi.2 hiNextNext hessential hfailure
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
    have hcross : b.order ⟨next.val - 1, by
        have := next.le_small
        omega⟩ ≤ a.order ⟨next.val + 1, hinterior.2⟩ := by
      have hlt := a.keyLemmaLeftFallback_middleCurrent_lt_sourceNextNext
        b c j hi.1 hi.2 hiNextNext hessential hfailure
      dsimp only [next, nextRepresentationIndex]
      exact hlt.le
    have hnormal : a.representationAlpha b next =
        min (a.representationHalfGap b next)
          (min (a.representationPrimaryDefect b next)
            (a.representationSecondarySourceAlpha b next hinterior)) := by
      calc
        a.representationAlpha b next =
            a.representationAlphaReduced b next hinterior next.lt_large :=
          hreduced
        _ = _ :=
          a.representationAlphaReduced_eq_min_halfGap_primary_source_of_cross
            b next hinterior next.lt_large hcross
    rcases min_choice (a.representationHalfGap b next)
        (min (a.representationPrimaryDefect b next)
          (a.representationSecondarySourceAlpha b next hinterior)) with
      hhalf | hrest
    · exact Or.inl (hnormal.trans hhalf)
    · rcases min_choice (a.representationPrimaryDefect b next)
          (a.representationSecondarySourceAlpha b next hinterior) with
        hprimary | hsource
      · exact Or.inr (Or.inl (hnormal.trans (hrest.trans hprimary)))
      · exact Or.inr (Or.inr ⟨hinterior,
          hnormal.trans (hrest.trans hsource)⟩)
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
