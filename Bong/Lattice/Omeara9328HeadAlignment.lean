/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328SaturatedInduction

/-!
# The already-aligned branch of O'Meara 93:28

When the first corresponding component spaces are already isometric,
saturatedness and equality of fundamental type promote that field isometry
to an integral component isometry by O'Meara 93:16.  Thus no change of the
target Jordan splitting is required.
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
  {L : Lattice K V} {M : Lattice K W} {m : Nat}

/-- Package an already isometric pair of head spaces as the replacement
required by the saturated induction. -/
noncomputable def headAlignedReplacementOfHeadSpaceIsometry
    (J : JordanDecomposition q L (m + 2))
    (H : JordanDecomposition r M (m + 2))
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A)
    (headSpace : (J.component 0).space.IsIsometric
      (H.component 0).space) :
    Omeara9328HeadAlignedReplacement J H A where
  target := H
  saturated := hH
  fundamentalType := F
  conditions := conditions
  head := hJ.componentIsometry hH F 0 headSpace

end Lattice.JordanDecomposition

end Bong
