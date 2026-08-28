/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightCommonPair

/-! # Fundamental type of the abstract Step-8 common pair -/

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

/-- The two packaged common adjunctions have the same complete fundamental
type. -/
noncomputable def commonPairFundamentalType (E : S.StepEightCase) :
    SameFundamentalType (E.commonPair S).sourceJordan
      (E.commonPair S).targetJordan := by
  unfold commonPair
  exact (E.saturatedToStable S).commonAdjunction (E.saturatedToTarget S)
    (E.stableFundamentalType S) (E.saturatedSource_isSaturated S)

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
