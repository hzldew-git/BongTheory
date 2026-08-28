/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightNormalizedRaw

/-!
# The 93:21 saturated splitting in O'Meara 93:28, Step 8
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

/-- Saturated splitting of the stabilized Step-8 source supplied by 93:21. -/
noncomputable def saturatedSource (E : S.StepEightCase) :=
  (E.stableSource S).saturatedJordanOfComponentRanksAtLeastThreeNonempty
    (E.stableComponentRank_atLeastThree S)

/-- The chosen 93:21 splitting is saturated. -/
theorem saturatedSource_isSaturated (E : S.StepEightCase) :
    (E.saturatedSource S).IsSaturated :=
  (E.stableSource S).saturatedJordanOfComponentRanksAtLeastThreeNonempty_isSaturated
    (E.stableComponentRank_atLeastThree S)

/-- Fundamental type from the saturated splitting to the displayed stable
source splitting. -/
noncomputable def saturatedToStable (E : S.StepEightCase) :
    SameFundamentalType (E.saturatedSource S) (E.stableSource S) :=
  (SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThreeNonempty
    (E.stableSource S) (E.stableComponentRank_atLeastThree S)).symm

/-- Fundamental type from the saturated source splitting to the stable
target. -/
noncomputable def saturatedToTarget (E : S.StepEightCase) :
    SameFundamentalType (E.saturatedSource S) (E.stableTarget S) :=
  (E.saturatedToStable S).trans (E.stableFundamentalType S)

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
