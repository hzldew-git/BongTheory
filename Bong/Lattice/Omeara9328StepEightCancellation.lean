/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightProductPresentation
import Bong.Lattice.ScaledHyperbolicChangeScale

/-!
# Cancelling the insertion in O'Meara 93:28, Step 8

The enlarged Step-8 block products are the original lattices with one scaled
hyperbolic plane adjoined.  Equal first scale orders identify those two
planes integrally.  O'Meara's hyperbolic cancellation theorem 93:14 then
cancels them directly.  No norm-group containment is needed here: that extra
hypothesis belongs only to the general modular cancellation corollary 93:14a.
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

/-- Step-8 hyperbolic insertion is cancellable by the concrete general form
of O'Meara 93:14a. -/
noncomputable def cancelStepEightInsertion
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (hfirst : ordUnit K (J.scaleGenerator 0) =
      ordUnit K (H.scaleGenerator 0))
    (enlarged : Isometry
      (BONG.blockOrthogonalForm (n + 2) J.stepEightCarrier J.stepEightForm)
      (BONG.blockOrthogonalForm (n + 2) H.stepEightCarrier H.stepEightForm)
      (BONG.blockProductLattice (n + 2)
        J.stepEightCarrier J.stepEightLattice)
      (BONG.blockProductLattice (n + 2)
        H.stepEightCarrier H.stepEightLattice)) :
    Isometry q r L M := by
  have hstep : ordUnit K J.stepEightScale =
      ordUnit K H.stepEightScale := by
    rw [stepEightScale_order, stepEightScale_order, hfirst]
  let total : Isometry
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane H.stepEightScale).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M) :=
    J.stepEightProductPresentation.symm.trans <|
      enlarged.trans H.stepEightProductPresentation
  exact omeara9314_scaled_of_isometric_summand J.stepEightScale
    (Isometry.refl (QuadraticSpace.hyperbolicPlane J.stepEightScale)
      (hyperbolicPlaneLattice (K := K)))
    (scaledHyperbolicChangeScaleIsometry
      H.stepEightScale J.stepEightScale hstep.symm)
    total

end Lattice.JordanDecomposition

end Bong
