/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Right

/-!
# Beli (2019), Lemma 6.7: type-I/type-II/type-III classification

This file assembles the preceding layers into the three alternatives stated
after Lemma 6.7.  Type I is the pointwise-gap-two branch.  In the remaining
branch, adjacent transition indices give type III, while a longer transition
gives type II together with its constant middle interval and `S - R = 2`.
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

/-- The pointwise-gap-two, or type-I, branch of Lemma 6.7. -/
structure Lemma67TypeI
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) where
  anchor : Nat
  anchor_bound : anchor < n + 1
  target_le_source_add_two (k : Nat) (hk : k < n + 1) :
    b.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero k + 2
  anchor_gap : b.orderSequence.entryOrZero anchor =
    a.orderSequence.entryOrZero anchor + 2
  profile : BeliOrderLE.GapTwoAnchorConsequences
    a.orderSequence b.orderSequence anchor

/-- The long no-gap-two, or type-II, branch of Lemma 6.7. -/
structure Lemma67TypeII
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) where
  outer : BeliOrderLE.NoGapTwoOuterConsequences
    a.orderSequence b.orderSequence
  no_gap_two (k : Nat) (hk : k < n + 1) :
    b.orderSequence.entryOrZero k <
      a.orderSequence.entryOrZero k + 2
  long : outer.transition.lastZero + 2 < outer.transition.firstTwo
  middle (k : Nat) (hlast : outer.transition.lastZero < k)
      (hfirst : k + 1 < outer.transition.firstTwo) :
    a.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero outer.transition.lastZero
  right_source :
    a.orderSequence.entryOrZero (outer.transition.firstTwo - 1) =
      b.orderSequence.entryOrZero outer.transition.lastZero
  right_target :
    b.orderSequence.entryOrZero (outer.transition.firstTwo - 1) =
      b.orderSequence.entryOrZero outer.transition.lastZero + 1

/-- The adjacent-transition, or type-III, branch of Lemma 6.7. -/
structure Lemma67TypeIII
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) where
  outer : BeliOrderLE.NoGapTwoOuterConsequences
    a.orderSequence b.orderSequence
  no_gap_two (k : Nat) (hk : k < n + 1) :
    b.orderSequence.entryOrZero k <
      a.orderSequence.entryOrZero k + 2
  adjacent : outer.transition.firstTwo =
    outer.transition.lastZero + 2

/-- The three mutually exhaustive shapes in Beli (2019), Lemma 6.7. -/
inductive Lemma67Classification
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) : Prop
  | typeI (data : Lemma67TypeI a b)
  | typeII (data : Lemma67TypeII a b)
  | typeIII (data : Lemma67TypeIII a b)

/-- Beli (2019), Lemma 6.7, assembled from the concrete type-I, type-II,
and type-III branches. -/
theorem beli2019Lemma67
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1)) :
    Lemma67Classification a b := by
  classical
  have hle := (a.representationOrderCondition_iff b le_rfl).mp horder
  by_cases hanchor : ∃ k, k < n + 1 ∧
      b.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero k + 2
  · rcases hanchor with ⟨anchor, hanchorBound, hanchorGap⟩
    rcases hle.gapTwoAnchorConsequences htotal anchor
        hanchorBound hanchorGap with ⟨profile⟩
    exact .typeI {
      anchor := anchor
      anchor_bound := hanchorBound
      target_le_source_add_two :=
        hle.entryOrZero_le_add_two_of_totalGap htotal
      anchor_gap := hanchorGap
      profile := profile }
  · have hnoTwoNe : ∀ k, k < n + 1 →
        b.orderSequence.entryOrZero k ≠
          a.orderSequence.entryOrZero k + 2 := by
      intro k hk heq
      exact hanchor ⟨k, hk, heq⟩
    have hnoTwo : ∀ k, k < n + 1 →
        b.orderSequence.entryOrZero k <
          a.orderSequence.entryOrZero k + 2 := by
      intro k hk
      have hupper := hle.entryOrZero_le_add_two_of_totalGap
        htotal k hk
      have hne : b.orderSequence.entryOrZero k ≠
          a.orderSequence.entryOrZero k + 2 := by
        intro heq
        exact hanchor ⟨k, hk, heq⟩
      exact lt_of_le_of_ne hupper hne
    rcases hle.noGapTwoOuterConsequences htotal hnoTwoNe with ⟨outer⟩
    by_cases hadjacent : outer.transition.firstTwo =
        outer.transition.lastZero + 2
    · exact .typeIII {
        outer := outer
        no_gap_two := hnoTwo
        adjacent := hadjacent }
    · have hlong : outer.transition.lastZero + 2 <
          outer.transition.firstTwo := by
        have := outer.transition.separated
        omega
      have hmiddle := a.middle_order_eq_leftTarget
        (alphaV := alphaV) (alphaW := alphaW)
        b hdefect outer hnoTwo hlong
      have hright := a.rightBoundarySource_eq_leftTarget
        (alphaV := alphaV) (alphaW := alphaW)
        b hdefect outer hnoTwo hlong
      have hrightTarget := outer.transition.rightBoundary
      rw [hright] at hrightTarget
      exact .typeII {
        outer := outer
        no_gap_two := hnoTwo
        long := hlong
        middle := hmiddle
        right_source := hright
        right_target := hrightTarget }

end BONG.GoodBONG

end Bong
