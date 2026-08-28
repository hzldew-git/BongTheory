/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.SpinorNorm
import Bong.QuadraticSpace.SpinorNormMultiplicative

/-!
# The integral spinor norm as a group homomorphism
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Multiplicativity of the integral spinor norm. -/
theorem integralSpinorNorm_mul
    (f g : IntegralOrthogonalGroup q L) :
    integralSpinorNorm (f * g) =
      integralSpinorNorm f * integralSpinorNorm g := by
  letI : Module.Finite K V := L.moduleFinite
  change QuadraticSpace.spinorNorm
      (g.toQuadraticSpaceIsometry.trans f.toQuadraticSpaceIsometry) =
    QuadraticSpace.spinorNorm f.toQuadraticSpaceIsometry *
      QuadraticSpace.spinorNorm g.toQuadraticSpaceIsometry
  simpa only [mul_comm] using
    QuadraticSpace.spinorNorm_trans
      g.toQuadraticSpaceIsometry f.toQuadraticSpaceIsometry

/-- The integral spinor norm, bundled as a group homomorphism. -/
noncomputable def integralSpinorNormHom :
    IntegralOrthogonalGroup q L →* SquareClass K where
  toFun := integralSpinorNorm
  map_one' := by
    letI : Module.Finite K V := L.moduleFinite
    exact QuadraticSpace.spinorNorm_refl
  map_mul' := integralSpinorNorm_mul

@[simp]
theorem integralSpinorNormHom_apply
    (f : IntegralOrthogonalGroup q L) :
    integralSpinorNormHom f = integralSpinorNorm f :=
  rfl

/-- Multiplicativity on Beli's proper integral rotation group. -/
theorem IntegralRotation.spinorNorm_mul
    (f g : IntegralRotation q L) :
    (f * g).spinorNorm = f.spinorNorm * g.spinorNorm :=
  integralSpinorNorm_mul f.toIntegralOrthogonalGroup
    g.toIntegralOrthogonalGroup

/-- The spinor norm on proper integral rotations, bundled as a group
homomorphism. -/
noncomputable def integralRotationSpinorNormHom :
    IntegralRotation q L →* SquareClass K where
  toFun := IntegralRotation.spinorNorm
  map_one' := by
    change integralSpinorNorm (1 : IntegralOrthogonalGroup q L) = 1
    exact integralSpinorNormHom.map_one
  map_mul' := IntegralRotation.spinorNorm_mul

@[simp]
theorem integralRotationSpinorNormHom_apply (f : IntegralRotation q L) :
    integralRotationSpinorNormHom f = f.spinorNorm :=
  rfl

/-- The subgroup form of Beli's integral spinor-norm image. -/
noncomputable def spinorNormImageSubgroup : Subgroup (SquareClass K) :=
  MonoidHom.range (integralRotationSpinorNormHom (q := q) (L := L))

@[simp]
theorem mem_spinorNormImageSubgroup_iff (a : SquareClass K) :
    a ∈ spinorNormImageSubgroup (q := q) (L := L) ↔
      ∃ f : IntegralRotation q L, f.spinorNorm = a :=
  Iff.rfl

/-- The subgroup carrier agrees with the original set-valued image. -/
theorem coe_spinorNormImageSubgroup :
    (spinorNormImageSubgroup (q := q) (L := L) :
      Set (SquareClass K)) = spinorNormImage (q := q) (L := L) :=
  rfl

end Lattice

end Bong
