/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightCommonBundle

/-! # The two common-adjunction Jordan splittings in O'Meara 93:28, Step 8 -/

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

/-- Common adjunction on the stable source. -/
noncomputable abbrev commonSource (E : S.StepEightCase) :=
  (E.commonBundle S).sourceJordan

/-- Common adjunction on the stable target. -/
noncomputable abbrev commonTarget (E : S.StepEightCase) :=
  (E.commonBundle S).targetJordan

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
