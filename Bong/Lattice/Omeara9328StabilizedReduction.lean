/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328SaturatedInduction
import Bong.Lattice.Omeara9328StabilizationConditions

/-!
# The rank-stabilized reduction in O'Meara 93:28

Starting from saturated Jordan splittings, adjoin two hyperbolic planes at
every component scale.  The enlarged splittings remain saturated, retain the
three conditions and the complete fundamental type, and have component rank
at least five.  A head-normalization theorem on that range therefore proves
the enlarged lattices isometric.  Iterated 93:14 cancellation then recovers
an isometry of the original lattices.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The preliminary stabilization and final hyperbolic cancellation in the
sufficiency proof of O'Meara 93:28.  It reduces the proof to the computational
head-alignment step for saturated decompositions whose components all have
rank at least five. -/
noncomputable def omeara9328IsometryOfStabilizedHeadReplacement
    (replaceHead :
      ∀ {V' : Type (max u v)} [AddCommGroup V'] [Module K V']
        {W' : Type (max u w)} [AddCommGroup W'] [Module K W']
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
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (ambient : q.IsIsometric r)
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A) :
    Isometry q r L M := by
  let JS := J.saturationStableJordan
  let HS := H.saturationStableJordan
  let FS : SameFundamentalType JS HS := F.saturationStable
  let AS : FundamentalNormGeneratorChoice JS := A.saturationStable
  have hJS : JS.IsSaturated :=
    J.saturationStableJordan_isSaturated_of_isSaturated hJ
  have hHS : HS.IsSaturated :=
    H.saturationStableJordan_isSaturated_of_isSaturated hH
  have hconditions : JS.Omeara9328ConditionsWith HS AS :=
    omeara9328ConditionsWith_saturationStable F A conditions
  have hambient :
      (BONG.blockOrthogonalForm (n + 1) J.saturationStableCarrier
        J.saturationStableForm).IsIsometric
        (BONG.blockOrthogonalForm (n + 1) H.saturationStableCarrier
          H.saturationStableForm) :=
    F.saturationStableAmbientIsometry ambient
  have hrank : ∀ i, 5 ≤ JS.componentRank i := by
    intro i
    rw [J.saturationStableJordan_componentRank]
    have hpos := J.component_finrank_pos i
    change 0 < J.componentRank i at hpos
    omega
  let stableIsometry :=
    omeara9328SaturatedIsometryOfComponentRankAtLeastFive replaceHead
      JS HS hambient hJS hHS FS AS hconditions hrank
  exact isometryOfSaturationStableJordanIsometry J H F stableIsometry

end Lattice.JordanDecomposition

end Bong
