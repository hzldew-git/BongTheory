/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightNormalizedRaw

/-!
# The 93:21 saturation certificate in O'Meara 93:28, Step 8
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
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

/-- A saturated Jordan splitting of the stabilized Step-8 source, with the
same complete fundamental type. -/
structure Omeara9328StepEightSaturationData
    (S : Omeara9328RankFourReductionSystem J H)
    (E : S.StepEightCase) where
  jordan : JordanDecomposition
    (BONG.blockOrthogonalForm (n + 2)
      (E.rawSource S).saturationStableCarrier
      (E.rawSource S).saturationStableForm)
    (BONG.blockProductLattice (n + 2)
      (E.rawSource S).saturationStableCarrier
      (E.rawSource S).saturationStableLattice)
    (n + 3)
  saturated : jordan.IsSaturated
  toStable : SameFundamentalType jordan (E.stableSource S)

namespace Omeara9328RankFourReductionSystem.StepEightCase

/-- O'Meara 93:21 supplies the required saturated splitting because every
stabilized Step-8 component has rank at least three. -/
noncomputable def saturationData
    (S : Omeara9328RankFourReductionSystem J H)
    (E : S.StepEightCase) : Omeara9328StepEightSaturationData S E where
  jordan := (E.stableSource S).saturatedJordanOfComponentRanksAtLeastThreeNonempty
    (E.stableComponentRank_atLeastThree S)
  saturated :=
    (E.stableSource S).saturatedJordanOfComponentRanksAtLeastThreeNonempty_isSaturated
      (E.stableComponentRank_atLeastThree S)
  toStable :=
    (SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThreeNonempty
      (E.stableSource S) (E.stableComponentRank_atLeastThree S)).symm

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
