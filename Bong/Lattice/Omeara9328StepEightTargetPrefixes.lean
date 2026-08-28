/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightPrefixes

/-!
# Target prefix presentations for O'Meara 93:28, Step 8

The target Step-8 Jordan decomposition uses the source scale generators in
order to align the two fundamental types.  Its underlying orthogonal
decomposition is nevertheless definitionally the raw target Step-8 block
decomposition.  We therefore reuse the target prefix presentations and then
change the scale of the inserted hyperbolic plane by the common scale order.
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
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

/-- Aligning the target scale generators changes no component, space, or
lattice in the underlying Step-8 orthogonal decomposition. -/
theorem SameFundamentalType.targetStepEightJordan_toOrthogonalDecomposition
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0)) :
    (F.targetStepEightJordan hgap).toOrthogonalDecomposition =
      (H.stepEightJordan hgapH).toOrthogonalDecomposition := by
  rfl

/-- The first target Step-8 prefix is just the old target first prefix. -/
noncomputable def SameFundamentalType.targetStepEightFirstPrefixPresentation
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0)) :
    Isometry
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1).space
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1).lattice
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice := by
  change Isometry
    ((H.stepEightJordan hgapH).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice 1).space
    (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
    ((H.stepEightJordan hgapH).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice 1).lattice
    (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice
  exact H.stepEightFirstPrefixPresentation hgapH

/-- The first two target Step-8 components, before scale alignment, are the
target inserted hyperbolic plane followed by the old target head. -/
noncomputable def SameFundamentalType.targetStepEightFirstTwoPrefixPresentationRaw
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0)) :
    Isometry
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 2).space
      ((QuadraticSpace.hyperbolicPlane H.stepEightScale).orthogonalSum
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space)
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 2).lattice
      (product (hyperbolicPlaneLattice (K := K))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice) := by
  change Isometry
    ((H.stepEightJordan hgapH).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice 2).space
    ((QuadraticSpace.hyperbolicPlane H.stepEightScale).orthogonalSum
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space)
    ((H.stepEightJordan hgapH).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice 2).lattice
    (product (hyperbolicPlaneLattice (K := K))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice)
  exact H.stepEightFirstTwoPrefixPresentation hgapH

/-- Every later target Step-8 prefix, before scale alignment, is the target
inserted hyperbolic plane followed by the corresponding old target prefix. -/
noncomputable def SameFundamentalType.targetStepEightLaterPrefixPresentationRaw
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0))
    (m : Nat) (hk : m + 1 ≤ n + 1) :
    Isometry
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 3)).space
      ((QuadraticSpace.hyperbolicPlane H.stepEightScale).orthogonalSum
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 2)).space)
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 3)).lattice
      (product (hyperbolicPlaneLattice (K := K))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 2)).lattice) := by
  change Isometry
    ((H.stepEightJordan hgapH).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (m + 3)).space
    ((QuadraticSpace.hyperbolicPlane H.stepEightScale).orthogonalSum
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 2)).space)
    ((H.stepEightJordan hgapH).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (m + 3)).lattice
    (product (hyperbolicPlaneLattice (K := K))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 2)).lattice)
  exact H.stepEightLaterPrefixPresentation hgapH m hk

/-- Corresponding inserted hyperbolic planes have the same integral
isometry class because their scale generators have equal valuation. -/
noncomputable def SameFundamentalType.stepEightInsertedScaleIsometry
    (F : SameFundamentalType J H) :
    Isometry (QuadraticSpace.hyperbolicPlane H.stepEightScale)
      (QuadraticSpace.hyperbolicPlane J.stepEightScale)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  apply scaledHyperbolicChangeScaleIsometry
  rw [H.stepEightScale_order, J.stepEightScale_order,
    F.scaleGenerator_order_eq_sameIndex 0]

/-- The first two target Step-8 components presented with the same inserted
plane as on the source side. -/
noncomputable def SameFundamentalType.targetStepEightFirstTwoPrefixPresentation
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0)) :
    Isometry
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 2).space
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space)
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 2).lattice
      (product (hyperbolicPlaneLattice (K := K))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice) :=
  (F.targetStepEightFirstTwoPrefixPresentationRaw hgap hgapH).trans
    (F.stepEightInsertedScaleIsometry.orthogonalProductBasic
      (Isometry.refl _ _))

/-- Every later target Step-8 prefix presented with the same inserted plane
as on the source side. -/
noncomputable def SameFundamentalType.targetStepEightLaterPrefixPresentation
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0))
    (m : Nat) (hk : m + 1 ≤ n + 1) :
    Isometry
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 3)).space
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 2)).space)
      ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 3)).lattice
      (product (hyperbolicPlaneLattice (K := K))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 2)).lattice) :=
  (F.targetStepEightLaterPrefixPresentationRaw hgap hgapH m hk).trans
    (F.stepEightInsertedScaleIsometry.orthogonalProductBasic
      (Isometry.refl _ _))

end Lattice.JordanDecomposition

end Bong
