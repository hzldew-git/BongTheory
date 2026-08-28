/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightNormalizedCommonConditions

/-! # Saturation and rank properties of the Step-8 common adjunction -/

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

/-- The source common adjunction is saturated. -/
theorem commonSource_isSaturated (E : S.StepEightCase) :
    (E.commonSource S).IsSaturated :=
  (E.saturatedSource S).commonAdjunctionJordan_isSaturated (E.stableSource S)
    (E.saturatedToStable S) (E.saturatedSource_isSaturated S)

/-- The target common adjunction is saturated. -/
theorem commonTarget_isSaturated (E : S.StepEightCase) :
    (E.commonTarget S).IsSaturated :=
  (E.saturatedSource S).commonAdjunctionJordan_isSaturated (E.stableTarget S)
    (E.saturatedToTarget S) (E.saturatedSource_isSaturated S)

/-- Every common-adjunction source component has rank at least two. -/
theorem commonSource_componentRank_atLeastTwo (E : S.StepEightCase) :
    ∀ i, 2 ≤ (E.commonSource S).componentRank i := by
  intro i
  change 2 ≤ ((E.saturatedSource S).commonAdjunctionJordan
    (E.stableSource S) (E.saturatedToStable S)
      (E.saturatedSource_isSaturated S)).componentRank i
  rw [commonAdjunctionJordan_componentRank]
  have hi := E.stableComponentRank_atLeastThree S i
  omega

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
