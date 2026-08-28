/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryHyperbolicEndpoint
import Bong.Lattice.HyperbolicLatticeInvariants

/-!
# The refined binary invariant of a scaled hyperbolic lattice

This is the converse direction to the endpoint construction: every binary
BONG on a lattice integrally isometric to a scaled hyperbolic plane has
refined parameter class `-1/4`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- A binary lattice isometric to `H_a` has Beli's exceptional refined
parameter class `-1/4`. -/
theorem binaryUnitSquareClass_eq_negativeQuarter_of_isometry_hyperbolicPlane
    (c : BONG V q L 2) (a : Kˣ)
    (e : Lattice.Isometry q (QuadraticSpace.hyperbolicPlane a) L
      (Lattice.hyperbolicPlaneLattice (K := K))) :
    c.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K) := by
  have hdet := Lattice.determinantClass_eq_of_isometry e
  rw [Lattice.determinantClass_hyperbolicPlaneLattice] at hdet
  let twoA : Kˣ := Units.mk0 (2 * (a : K))
    (mul_ne_zero (by norm_num) (Units.ne_zero a))
  have hnormMap := Lattice.normIdeal_map_isometry
    e.toQuadraticSpaceIsometry L
  change Lattice.normIdeal (QuadraticSpace.hyperbolicPlane a)
      (Lattice.map e.toLinearEquiv L) = Lattice.normIdeal q L at hnormMap
  rw [e.map_eq, Lattice.normIdeal_hyperbolicPlaneLattice] at hnormMap
  have hprincipal :
      Lattice.principalIdeal (K := K) (c.valueUnit 0 : K) =
        Lattice.principalIdeal (K := K) (twoA : K) := by
    calc
      Lattice.principalIdeal (K := K) (c.valueUnit 0 : K) =
          Lattice.normIdeal q L := c.normIdeal_eq_principal_value_zero.symm
      _ = Lattice.principalIdeal (K := K) (2 * (a : K)) := hnormMap.symm
      _ = Lattice.principalIdeal (K := K) (twoA : K) := by
        simpa only [twoA, Units.val_mk0]
  rcases Lattice.exists_valuationUnit_mul_eq_of_principalIdeal_eq
      (c.valueUnit 0) twoA hprincipal with ⟨u, hu, huEq⟩
  have hd : (-1 : Kˣ) * a ^ 2 = negativeQuarterUnit K * twoA ^ 2 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg,
      Units.val_one, twoA, Units.val_mk0]
    dsimp only [negativeQuarterUnit]
    change (-1 : K) * (a : K) ^ 2 = -(4 : K)⁻¹ * (2 * (a : K)) ^ 2
    field_simp
    ring
  rw [← c.binaryDeterminantInvariant_eq_parameter]
  unfold binaryDeterminantInvariant
  rw [hdet]
  change unitSquareClass K
      (((-1 : Kˣ) * a ^ 2) * (c.valueUnit 0)⁻¹ ^ 2) =
    unitSquareClass K (negativeQuarterUnit K)
  have hfactor :
      ((-1 : Kˣ) * a ^ 2) * (c.valueUnit 0)⁻¹ ^ 2 =
        negativeQuarterUnit K * u ^ 2 := by
    rw [hd, ← huEq]
    simp only [mul_pow]
    group
  rw [hfactor]
  exact unitSquareClass_mul_unit_square K (negativeQuarterUnit K) u hu

end BONG

end Bong
