/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaCommonAdjunctionCancellation
import Bong.Lattice.Omeara9328StepEightScaleSpread

/-!
# Ambient isometries for the adjunctions in O'Meara 93:28

The Step-8 insertion and the common saturated adjunction both preserve
ambient isometry.  These are space-level statements; integral cancellation
is performed separately after the enlarged lattices have been classified.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w x

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {X : Type x} [AddCommGroup X] [Module K X]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K X}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K X}
  {n : Nat}

/-- Inserting the Step-8 hyperbolic plane on both sides preserves ambient
isometry. -/
theorem SameFundamentalType.stepEightAmbientIsometry
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H)
    (ambient : q.IsIsometric r) :
    (BONG.blockOrthogonalForm (n + 2)
      J.stepEightCarrier J.stepEightForm).IsIsometric
      (BONG.blockOrthogonalForm (n + 2)
        H.stepEightCarrier H.stepEightForm) := by
  have hstep : ordUnit K J.stepEightScale =
      ordUnit K H.stepEightScale := by
    rw [stepEightScale_order, stepEightScale_order,
      F.scaleGenerator_order_eq_sameIndex 0]
  let inserted := scaledHyperbolicChangeScaleIsometry
    J.stepEightScale H.stepEightScale hstep
  let base : QuadraticSpace.Isometry q r := Classical.choice ambient
  exact ⟨J.stepEightProductPresentation.toQuadraticSpaceIsometry.trans <|
    (inserted.toQuadraticSpaceIsometry.orthogonalSum base).trans <|
      H.stepEightProductPresentation.symm.toQuadraticSpaceIsometry⟩

/-- Adjoining one common saturated splitting to two ambient-isometric
spaces preserves ambient isometry. -/
theorem SameFundamentalType.commonAdjunctionAmbientIsometry
    {P : JordanDecomposition q L (n + 2)}
    {J : JordanDecomposition r M (n + 2)}
    {H : JordanDecomposition s N (n + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (hP : P.IsSaturated)
    (ambient : r.IsIsometric s) :
    (BONG.blockOrthogonalForm (n + 1)
      (P.commonAdjunctionCarrier J) (P.commonAdjunctionForm J)).IsIsometric
      (BONG.blockOrthogonalForm (n + 1)
        (P.commonAdjunctionCarrier H) (P.commonAdjunctionForm H)) := by
  let middle : QuadraticSpace.Isometry
      (q.orthogonalSum r) (q.orthogonalSum s) :=
    (QuadraticSpace.Isometry.refl q).orthogonalSum (Classical.choice ambient)
  exact ⟨(P.commonAdjunctionProductIsometry J).toQuadraticSpaceIsometry.trans <|
    middle.trans <|
      (P.commonAdjunctionProductIsometry H).symm.toQuadraticSpaceIsometry⟩

end Lattice.JordanDecomposition

end Bong
