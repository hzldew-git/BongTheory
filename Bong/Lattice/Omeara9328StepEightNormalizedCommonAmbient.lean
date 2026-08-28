/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightNormalizedCommon

/-!
# Ambient isometry for the Step-8 common adjunction

This is kept behind its own compilation boundary because the inferred type of
the ambient orthogonal sum is substantially larger than the arithmetic data of
the common Jordan pair.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition
namespace Omeara9328RankFourReductionSystem.StepEightCase

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type u} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}
  (S : Omeara9328RankFourReductionSystem J H)

/-- Ambient isometry of the common-adjunction pair. -/
theorem commonAmbient
    (ambient : q.IsIsometric r) (E : S.StepEightCase) :
    (E.commonSource S).space.IsIsometric (E.commonTarget S).space :=
  (E.saturatedToStable S).commonAdjunctionAmbientIsometry
    (E.saturatedToTarget S) (E.saturatedSource_isSaturated S)
      (E.stableAmbient S ambient)

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
