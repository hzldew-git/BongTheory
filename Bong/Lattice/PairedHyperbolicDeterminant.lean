/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaPairedHyperbolicCancellation
import Bong.Lattice.ScaledHyperbolicChangeScale
import Bong.Lattice.HyperbolicLatticeInvariants
import Bong.Lattice.OrthogonalDecompositionDeterminant

/-!
# Determinants of paired hyperbolic towers

The determinant class of a paired tower is the determinant class of its
base multiplied by the two hyperbolic determinant factors at every level.
The factor depends only on the valuation of each selected scale generator.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Product of the two hyperbolic determinant classes at every level of a
paired tower. -/
noncomputable def pairedHyperbolicDeterminantFactor :
    (t : Nat) → (Fin t → Kˣ) → Kˣ
  | 0, _ => 1
  | t + 1, scale =>
      determinantUnit (QuadraticSpace.hyperbolicPlane (scale 0))
          (hyperbolicPlaneLattice (K := K)) *
        determinantUnit (QuadraticSpace.hyperbolicPlane (scale 0))
          (hyperbolicPlaneLattice (K := K)) *
        pairedHyperbolicDeterminantFactor t (Fin.tail scale)

/-- The paired-tower determinant formula. -/
theorem determinantClass_pairedHyperbolicExtension
    {W : Type v} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) (L : Lattice K W) :
    ∀ (t : Nat) (scale : Fin t → Kˣ),
      determinantClass (pairedHyperbolicExtensionForm q t scale)
          (pairedHyperbolicExtensionLattice L t) =
        unitSquareClass K (pairedHyperbolicDeterminantFactor t scale) *
          determinantClass q L
  | 0, scale => by
      calc
        determinantClass (pairedHyperbolicExtensionForm q 0 scale)
            (pairedHyperbolicExtensionLattice L 0) =
            determinantClass q L :=
          determinantClass_eq_of_isometry
            (pairedHyperbolicExtensionBaseIsometry q L scale)
        _ = unitSquareClass K (pairedHyperbolicDeterminantFactor 0 scale) *
            determinantClass q L := by
          rw [show pairedHyperbolicDeterminantFactor 0 scale = 1 by rfl]
          rw [unitSquareClass_one]
          exact (@one_mul (UnitSquareClass K) _ (determinantClass q L)).symm
  | t + 1, scale => by
      let H := QuadraticSpace.hyperbolicPlane (scale 0)
      let HL := hyperbolicPlaneLattice (K := K)
      let T := pairedHyperbolicExtensionForm q t (Fin.tail scale)
      let TL := pairedHyperbolicExtensionLattice L t
      change determinantClass (H.orthogonalSum (H.orthogonalSum T))
          (product HL (product HL TL)) =
        unitSquareClass K (determinantUnit H HL * determinantUnit H HL *
          pairedHyperbolicDeterminantFactor t (Fin.tail scale)) *
            determinantClass q L
      rw [determinantClass_orthogonalProduct H (H.orthogonalSum T)
          HL (product HL TL),
        determinantClass_orthogonalProduct H T HL TL,
        determinantClass_pairedHyperbolicExtension q L t (Fin.tail scale)]
      unfold determinantClass
      simp only [unitSquareClass_mul]
      ac_rfl

/-- Equal valuations of all scale generators give equal paired hyperbolic
determinant factors. -/
theorem pairedHyperbolicDeterminantFactor_eq_of_orders
    (t : Nat) (sourceScale targetScale : Fin t → Kˣ)
    (hord : ∀ i,
      ordUnit K (sourceScale i) = ordUnit K (targetScale i)) :
    unitSquareClass K (pairedHyperbolicDeterminantFactor t sourceScale) =
      unitSquareClass K (pairedHyperbolicDeterminantFactor t targetScale) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hhead := determinantClass_eq_of_isometry
        (scaledHyperbolicChangeScaleIsometry
          (sourceScale 0) (targetScale 0) (hord 0))
      unfold pairedHyperbolicDeterminantFactor
      simp only [unitSquareClass_mul]
      change unitSquareClass K
          (determinantUnit
            (QuadraticSpace.hyperbolicPlane (sourceScale 0))
            (hyperbolicPlaneLattice (K := K))) *
          unitSquareClass K
            (determinantUnit
              (QuadraticSpace.hyperbolicPlane (sourceScale 0))
              (hyperbolicPlaneLattice (K := K))) * _ = _
      change determinantClass
          (QuadraticSpace.hyperbolicPlane (sourceScale 0))
            (hyperbolicPlaneLattice (K := K)) *
          determinantClass
            (QuadraticSpace.hyperbolicPlane (sourceScale 0))
              (hyperbolicPlaneLattice (K := K)) * _ = _
      rw [hhead, ih (Fin.tail sourceScale) (Fin.tail targetScale)
        (fun i => hord i.succ)]
      unfold determinantClass
      rfl

end Lattice

end Bong
