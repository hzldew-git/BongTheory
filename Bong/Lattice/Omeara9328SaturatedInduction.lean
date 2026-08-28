/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328Classification
import Bong.Lattice.Omeara9328TailConditions

/-!
# The saturated induction in O'Meara 93:28

This file separates the formal recursion in the sufficiency proof from its
computational heart.  Once the first corresponding modular components can be
aligned, saturatedness identifies the fundamental invariants of the exact
tails, the three conditions pass to those tails, and ordinary Witt
cancellation supplies their ambient isometry.  The recursion then glues the
head and tail lattice isometries.

The `replaceHead` argument below is a theorem-shaped argument, not a type
class or an axiom.  It records precisely the remaining cases 4--8 in the
printed proof: one changes the target Jordan splitting, without changing the
target lattice, until its first component is aligned with the fixed source.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Output of the computational head-normalization step in 93:28.  The new
target is another saturated Jordan decomposition of the *same* target
lattice.  This distinction is essential: the original target head need not
already be isometric to the source head. -/
structure Omeara9328HeadAlignedReplacement
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m : Nat}
    (J : JordanDecomposition q L (m + 2))
    (_H : JordanDecomposition r M (m + 2))
    (A : FundamentalNormGeneratorChoice J) where
  target : JordanDecomposition r M (m + 2)
  saturated : target.IsSaturated
  fundamentalType : SameFundamentalType J target
  conditions : J.Omeara9328ConditionsWith target A
  head : Isometry (J.component 0).space (target.component 0).space
    (J.component 0).lattice (target.component 0).lattice

/-- The formal saturated recursion in the sufficiency half of 93:28.

The only mathematical input not supplied by earlier semantic lemmas is the
uniform target-splitting replacement theorem.  It is quantified over all
suffix ambient types so that the recursive call is genuinely on the exact
tail lattices. -/
noncomputable def omeara9328SaturatedIsometry
    (replaceHead :
      ∀ {V' : Type v} [AddCommGroup V'] [Module K V']
        {W' : Type w} [AddCommGroup W'] [Module K W']
        {q' : QuadraticSpace K V'} {r' : QuadraticSpace K W'}
        {L' : Lattice K V'} {M' : Lattice K W'} {m : Nat}
        (J' : JordanDecomposition q' L' (m + 2))
        (H' : JordanDecomposition r' M' (m + 2))
        (ambient' : q'.IsIsometric r')
        (hJ' : J'.IsSaturated) (hH' : H'.IsSaturated)
        (F' : SameFundamentalType J' H')
        (A' : FundamentalNormGeneratorChoice J')
        (conditions' : J'.Omeara9328ConditionsWith H' A'),
        Omeara9328HeadAlignedReplacement J' H' A')
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (ambient : q.IsIsometric r)
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A) :
    Isometry q r L M := by
  cases n with
  | zero =>
      exact omeara9328_singleComponent J H ambient F
  | succ m =>
      let R := replaceHead J H ambient hJ hH F A conditions
      let ambientIsometry : QuadraticSpace.Isometry q r :=
        Classical.choice ambient
      let tailAmbient :
          (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space.IsIsometric
            (R.target.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space :=
        ⟨J.tailSpaceIsometry R.target ambientIsometry
          R.head.toQuadraticSpaceIsometry⟩
      let tailFundamental : SameFundamentalType J.tail R.target.tail :=
        R.fundamentalType.tail hJ R.saturated
      let tailConditions :
          J.tail.Omeara9328ConditionsWith R.target.tail (A.tail hJ) :=
        omeara9328ConditionsWith_tail hJ R.head A R.conditions
      let tailIsometry := omeara9328SaturatedIsometry replaceHead
        J.tail R.target.tail tailAmbient (hJ.tail) (R.saturated.tail) tailFundamental
          (A.tail hJ) tailConditions
      exact J.headTailIsometry R.target R.head tailIsometry
termination_by n

/-- Canonical-generator specialization of the saturated recursion. -/
noncomputable def omeara9328SaturatedIsometryOfConditions
    (replaceHead :
      ∀ {V' : Type v} [AddCommGroup V'] [Module K V']
        {W' : Type w} [AddCommGroup W'] [Module K W']
        {q' : QuadraticSpace K V'} {r' : QuadraticSpace K W'}
        {L' : Lattice K V'} {M' : Lattice K W'} {m : Nat}
        (J' : JordanDecomposition q' L' (m + 2))
        (H' : JordanDecomposition r' M' (m + 2))
        (ambient' : q'.IsIsometric r')
        (hJ' : J'.IsSaturated) (hH' : H'.IsSaturated)
        (F' : SameFundamentalType J' H')
        (A' : FundamentalNormGeneratorChoice J')
        (conditions' : J'.Omeara9328ConditionsWith H' A'),
        Omeara9328HeadAlignedReplacement J' H' A')
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (ambient : q.IsIsometric r)
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H)
    (conditions : J.Omeara9328Conditions H) :
    Isometry q r L M :=
  omeara9328SaturatedIsometry replaceHead J H ambient hJ hH F
    (canonicalFundamentalNormGeneratorChoice J)
    ((omeara9328ConditionsWith_canonical_iff J H).2 conditions)

/-- Rank-aware form of the saturated recursion.  O'Meara's preliminary
hyperbolic adjunctions produce components of rank at least five.  Carrying
that fact through the recursion avoids demanding a head-normalization
theorem for arbitrary low-rank decompositions that never arise in the
normalized proof. -/
noncomputable def omeara9328SaturatedIsometryOfComponentRankAtLeastFive
    (replaceHead :
      ∀ {V' : Type v} [AddCommGroup V'] [Module K V']
        {W' : Type w} [AddCommGroup W'] [Module K W']
        {q' : QuadraticSpace K V'} {r' : QuadraticSpace K W'}
        {L' : Lattice K V'} {M' : Lattice K W'} {m : Nat}
        (J' : JordanDecomposition q' L' (m + 2))
        (H' : JordanDecomposition r' M' (m + 2))
        (ambient' : q'.IsIsometric r')
        (hJ' : J'.IsSaturated) (hH' : H'.IsSaturated)
        (F' : SameFundamentalType J' H')
        (A' : FundamentalNormGeneratorChoice J')
        (conditions' : J'.Omeara9328ConditionsWith H' A')
        (hrank' : ∀ i, 5 ≤ J'.componentRank i),
        Omeara9328HeadAlignedReplacement J' H' A')
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (ambient : q.IsIsometric r)
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A)
    (hrank : ∀ i, 5 ≤ J.componentRank i) :
    Isometry q r L M := by
  cases n with
  | zero =>
      exact omeara9328_singleComponent J H ambient F
  | succ m =>
      let R := replaceHead J H ambient hJ hH F A conditions hrank
      let ambientIsometry : QuadraticSpace.Isometry q r :=
        Classical.choice ambient
      let tailAmbient :
          (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space.IsIsometric
            (R.target.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space :=
        ⟨J.tailSpaceIsometry R.target ambientIsometry
          R.head.toQuadraticSpaceIsometry⟩
      let tailFundamental : SameFundamentalType J.tail R.target.tail :=
        R.fundamentalType.tail hJ R.saturated
      let tailConditions :
          J.tail.Omeara9328ConditionsWith R.target.tail (A.tail hJ) :=
        omeara9328ConditionsWith_tail hJ R.head A R.conditions
      have tailRank : ∀ i, 5 ≤ J.tail.componentRank i := by
        intro i
        rw [J.tail_componentRank]
        exact hrank i.succ
      let tailIsometry :=
        omeara9328SaturatedIsometryOfComponentRankAtLeastFive replaceHead
          J.tail R.target.tail tailAmbient (hJ.tail) (R.saturated.tail)
            tailFundamental (A.tail hJ) tailConditions tailRank
      exact J.headTailIsometry R.target R.head tailIsometry
termination_by n

end Lattice.JordanDecomposition

end Bong
