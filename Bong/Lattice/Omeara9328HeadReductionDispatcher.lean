/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightHeadReduction

/-!
# Exhaustive head-reduction dispatcher for O'Meara 93:28
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type u} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Steps 4--7 handle the ordinary branch; the complementary numerical
case is exactly Step 8.  Both branches expose the same decreasing aligned
interface and an integral descent to the original pair. -/
noncomputable def Omeara9328RankFourReductionSystem.firstHeadAlignedReduction
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (S : Omeara9328RankFourReductionSystem J H)
    (ambient : q.IsIsometric r)
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A) :
    Omeara9328HeadAlignedReduction J H :=
  match S.firstBoundaryOutcome A conditions with
  | Sum.inl R => S.alignedHeadReduction ambient A R
  | Sum.inr E => S.stepEightHeadReduction ambient A conditions E

end Lattice.JordanDecomposition

end Bong
