/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightTargetPrefixes
import Bong.Lattice.HyperbolicLatticeInvariants
import Bong.Dyadic.UnitsCongruentModuloAlgebra

/-!
# Prefix determinants in O'Meara 93:28, Step 8

The first new prefix is the old first prefix.  Every prefix containing the
inserted plane acquires the same refined square-class factor `-s₈²` on
both sides.  These are the determinant identities used to transfer
condition 93:28(i).
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

/-- The common refined determinant factor of the inserted scaled
hyperbolic plane. -/
noncomputable def stepEightDeterminantFactor
    (J : JordanDecomposition q L (n + 2)) : UnitSquareClass K :=
  unitSquareClass K ((-1 : Kˣ) * J.stepEightScale ^ 2)

/-- The first new source prefix has the old determinant class. -/
theorem determinantClass_stepEight_firstPrefix
    (J : JordanDecomposition q L (n + 2))
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    determinantClass
        ((J.stepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        ((J.stepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      determinantClass
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice :=
  determinantClass_eq_of_isometry
    (J.stepEightFirstPrefixPresentation hgap)

/-- The source prefix ending at the inserted plane acquires exactly the
inserted hyperbolic determinant factor. -/
theorem determinantClass_stepEight_firstTwoPrefix
    (J : JordanDecomposition q L (n + 2))
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    determinantClass
        ((J.stepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 2).space
        ((J.stepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 2).lattice =
      J.stepEightDeterminantFactor *
        determinantClass
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice := by
  have hdet := determinantClass_eq_of_isometry
    (J.stepEightFirstTwoPrefixPresentation hgap)
  rw [determinantClass_orthogonalProduct,
    determinantClass_hyperbolicPlaneLattice] at hdet
  simpa only [stepEightDeterminantFactor] using hdet

/-- Every later source prefix acquires the same inserted hyperbolic
determinant factor. -/
theorem determinantClass_stepEight_laterPrefix
    (J : JordanDecomposition q L (n + 2))
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (i : Fin n) :
    determinantClass
        ((J.stepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 3)).space
        ((J.stepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 3)).lattice =
      J.stepEightDeterminantFactor *
        determinantClass
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice
            (i.val + 2)).space
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice
            (i.val + 2)).lattice := by
  have hk : i.val + 1 ≤ n + 1 := by omega
  have hdet := determinantClass_eq_of_isometry
    (J.stepEightLaterPrefixPresentation hgap i.val hk)
  rw [determinantClass_orthogonalProduct,
    determinantClass_hyperbolicPlaneLattice] at hdet
  simpa only [stepEightDeterminantFactor] using hdet

/-- The first new target prefix has the old target determinant class. -/
theorem SameFundamentalType.determinantClass_targetStepEight_firstPrefix
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0)) :
    determinantClass
        ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      determinantClass
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice :=
  determinantClass_eq_of_isometry
    (F.targetStepEightFirstPrefixPresentation hgap hgapH)

/-- The first two target components acquire the same source-aligned
hyperbolic determinant factor. -/
theorem SameFundamentalType.determinantClass_targetStepEight_firstTwoPrefix
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0)) :
    determinantClass
        ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 2).space
        ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 2).lattice =
      J.stepEightDeterminantFactor *
        determinantClass
          (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
          (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice := by
  have hdet := determinantClass_eq_of_isometry
    (F.targetStepEightFirstTwoPrefixPresentation hgap hgapH)
  rw [determinantClass_orthogonalProduct,
    determinantClass_hyperbolicPlaneLattice] at hdet
  simpa only [stepEightDeterminantFactor] using hdet

/-- Every later target prefix acquires the common source-aligned
hyperbolic determinant factor. -/
theorem SameFundamentalType.determinantClass_targetStepEight_laterPrefix
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hgapH : 1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0))
    (i : Fin n) :
    determinantClass
        ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 3)).space
        ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (i.val + 3)).lattice =
      J.stepEightDeterminantFactor *
        determinantClass
          (H.toOrthogonalDecomposition.prefixQuadraticSublattice
            (i.val + 2)).space
          (H.toOrthogonalDecomposition.prefixQuadraticSublattice
            (i.val + 2)).lattice := by
  have hk : i.val + 1 ≤ n + 1 := by omega
  have hdet := determinantClass_eq_of_isometry
    (F.targetStepEightLaterPrefixPresentation hgap hgapH i.val hk)
  rw [determinantClass_orthogonalProduct,
    determinantClass_hyperbolicPlaneLattice] at hdet
  simpa only [stepEightDeterminantFactor] using hdet

end Lattice.JordanDecomposition

end Bong
