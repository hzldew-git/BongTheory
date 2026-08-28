/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma65
import Bong.Bong.Beli2019Lemma67Middle

/-!
# Beli (2019), Lemma 6.7: applying Lemma 6.5 in the middle interval

Every intermediate prefix gap in the no-gap-two branch is one.  This file
turns that equality into the congruence required by Lemma 6.5, translates its
two good-BONG conclusions back to zero-extended order sequences, and feeds
the result into the middle-plateau induction.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Lemma 6.5 at every strict interior prefix of the transition interval. -/
theorem lemma65_cross_of_prefixGapTransition
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (T : BeliOrderLE.PrefixGapTransitionConsequences
      a.orderSequence b.orderSequence)
    (p : Nat) (hleft : T.lastZero + 1 < p)
    (hright : p + 1 < T.firstTwo) :
    a.orderSequence.entryOrZero p ≤
        b.orderSequence.entryOrZero (p - 1) ∨
      a.orderSequence.entryOrZero p +
          a.orderSequence.entryOrZero (p + 1) ≤
        b.orderSequence.entryOrZero (p - 2) +
          b.orderSequence.entryOrZero (p - 1) := by
  have hpBound : p < n + 1 := by
    have := T.firstTwo_le_rank
    omega
  have hpNextBound : p + 1 < n + 1 := by
    have := T.firstTwo_le_rank
    omega
  let i : RepresentationIndex (n + 1) (n + 1) := {
    val := p
    pos := by omega
    lt_large := hpBound
    le_small := hpBound.le }
  have hgap := T.gap_between p (by omega) (by omega)
  have hparity : Int.ModEq 2
      (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val + 1) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨1, ?_⟩
    simp only [i]
    unfold BeliOrderSequence.prefixGap at hgap
    omega
  rcases a.beli2019Lemma65
      (alphaV := alphaV) (alphaW := alphaW)
      b hdefect i hparity with hdirect | ⟨hi, hpair⟩
  · apply Or.inl
    rw [BeliOrderSequence.entryOrZero_of_lt
        a.orderSequence hpBound,
      BeliOrderSequence.entryOrZero_of_lt
        b.orderSequence (show p - 1 < n + 1 by omega)]
    simpa only [BeliOrderSequence.entry, orderSequence, i] using hdirect
  · apply Or.inr
    rw [BeliOrderSequence.entryOrZero_of_lt
        a.orderSequence hpBound,
      BeliOrderSequence.entryOrZero_of_lt
        a.orderSequence hpNextBound,
      BeliOrderSequence.entryOrZero_of_lt
        b.orderSequence (show p - 2 < n + 1 by omega),
      BeliOrderSequence.entryOrZero_of_lt
        b.orderSequence (show p - 1 < n + 1 by omega)]
    simpa only [BeliOrderSequence.entry, orderSequence, i] using hpair

/-- The middle plateau for actual good BONGs, conditional only on the seed
entry treated separately in the paper. -/
theorem middle_order_eq_leftTarget_of_seed
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (T : BeliOrderLE.PrefixGapTransitionConsequences
      a.orderSequence b.orderSequence)
    (hseed : a.orderSequence.entryOrZero (T.lastZero + 1) =
      b.orderSequence.entryOrZero T.lastZero) :
    ∀ k, T.lastZero < k → k + 1 < T.firstTwo →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero T.lastZero := by
  apply BeliOrderLE.middle_eq_leftTarget_of_seed_of_cross T hseed
  intro p hleft hright
  exact a.lemma65_cross_of_prefixGapTransition
    (alphaV := alphaV) (alphaW := alphaW)
    b hdefect T p hleft hright

end BONG.GoodBONG

end Bong
