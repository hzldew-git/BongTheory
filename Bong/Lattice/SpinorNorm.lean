/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Reflection
import Bong.QuadraticSpace.SpinorNorm
import Bong.QuadraticSpace.SpinorNormReflection
import Bong.QuadraticSpace.SpinorNormExtension

/-!
# Integral spinor-norm images

The integral spinor-norm set `θ(O(L))` is the image of the ambient Wall spinor
norm on the integral orthogonal group.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The spinor norm of an integral lattice automorphism. -/
noncomputable def integralSpinorNorm (f : IntegralOrthogonalGroup q L) :
    SquareClass K := by
  letI : Module.Finite K V := L.moduleFinite
  exact QuadraticSpace.spinorNorm f.toQuadraticSpaceIsometry

/-- The spinor-norm image of the full integral orthogonal group.  Beli's
`θ(L)` uses only proper rotations and is defined separately below. -/
noncomputable def orthogonalSpinorNormImage : Set (SquareClass K) :=
  Set.range (integralSpinorNorm (q := q) (L := L))

theorem mem_orthogonalSpinorNormImage_iff (a : SquareClass K) :
    a ∈ orthogonalSpinorNormImage (q := q) (L := L) ↔
      ∃ f : IntegralOrthogonalGroup q L, integralSpinorNorm f = a :=
  Iff.rfl

namespace IntegralRotation

/-- The spinor norm of an integral proper rotation. -/
noncomputable def spinorNorm (f : IntegralRotation q L) : SquareClass K :=
  integralSpinorNorm f.toIntegralOrthogonalGroup

end IntegralRotation

/-- Beli's integral spinor-norm image `θ(L) = θ(O⁺(L))`. -/
noncomputable def spinorNormImage : Set (SquareClass K) :=
  Set.range (IntegralRotation.spinorNorm (q := q) (L := L))

theorem mem_spinorNormImage_iff (a : SquareClass K) :
    a ∈ spinorNormImage (q := q) (L := L) ↔
      ∃ f : IntegralRotation q L, f.spinorNorm = a :=
  Iff.rfl

/-- The spinor-norm image `θ(O⁻(L))` of the determinant-`-1` integral
orthogonal transformations. -/
noncomputable def improperSpinorNormImage : Set (SquareClass K) :=
  {a | ∃ f : IntegralOrthogonalGroup q L,
    LinearEquiv.det f.toLinearEquiv = (-1 : Kˣ) ∧
      integralSpinorNorm f = a}

theorem mem_improperSpinorNormImage_iff (a : SquareClass K) :
    a ∈ improperSpinorNormImage (q := q) (L := L) ↔
      ∃ f : IntegralOrthogonalGroup q L,
        LinearEquiv.det f.toLinearEquiv = (-1 : Kˣ) ∧
          integralSpinorNorm f = a :=
  Iff.rfl

/-- An integral reflection has spinor norm represented by `Q(x)`. -/
@[simp]
theorem integralSpinorNorm_integralReflection {x : V}
    (anisotropic : q.IsAnisotropic x)
    (integral : IsIntegralReflection (q := q) (L := L) anisotropic) :
    integralSpinorNorm (integralReflection anisotropic integral) =
      reflectionSpinorClass anisotropic := by
  letI : Module.Finite K V := L.moduleFinite
  change QuadraticSpace.spinorNorm (q.reflectionIsometry x anisotropic) =
    squareClass K (Units.mk0 (q.quadratic x) anisotropic)
  exact QuadraticSpace.spinorNorm_reflection anisotropic

/-- Every integral reflection class lies in the spinor image of the full
orthogonal group.  A single reflection is not a proper rotation. -/
theorem reflectionSpinorClass_mem_orthogonalSpinorNormImage {x : V}
    (anisotropic : q.IsAnisotropic x)
    (integral : IsIntegralReflection (q := q) (L := L) anisotropic) :
    reflectionSpinorClass anisotropic ∈
      orthogonalSpinorNormImage (q := q) (L := L) := by
  exact ⟨integralReflection anisotropic integral,
    integralSpinorNorm_integralReflection anisotropic integral⟩

/-- Extending a projected automorphism preserves its spinor norm. -/
theorem integralSpinorNorm_extendProjectedAutomorphism {x : V}
    {anisotropic : q.IsAnisotropic x}
    (generator : IsNormGenerator q L x)
    (f : IntegralOrthogonalGroup (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)) :
    integralSpinorNorm (f.extendProjectedAutomorphism generator) =
      integralSpinorNorm f := by
  letI : Module.Finite K V := L.moduleFinite
  change QuadraticSpace.spinorNorm
      (QuadraticSpace.orthogonalExtensionIsometry
        f.toQuadraticSpaceIsometry) =
    QuadraticSpace.spinorNorm f.toQuadraticSpaceIsometry
  exact QuadraticSpace.spinorNorm_orthogonalExtension
    f.toQuadraticSpaceIsometry

/-- Extending a projected integral rotation preserves its spinor norm. -/
theorem IntegralRotation.spinorNorm_extendProjectedAutomorphism {x : V}
    {anisotropic : q.IsAnisotropic x}
    (generator : IsNormGenerator q L x)
    (f : IntegralRotation (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)) :
    (f.extendProjectedAutomorphism generator).spinorNorm = f.spinorNorm :=
  integralSpinorNorm_extendProjectedAutomorphism generator
    f.toIntegralOrthogonalGroup

/--
Beli (2003), Section 2.5: the spinor-norm image of the projected lattice is
contained in that of the original lattice.
-/
theorem spinorNormImage_projectedLattice_subset {x : V}
    {anisotropic : q.IsAnisotropic x}
    (generator : IsNormGenerator q L x) :
    spinorNormImage
        (q := q.orthogonalSpace x anisotropic)
        (L := projectedLattice q L x anisotropic) ⊆
      spinorNormImage (q := q) (L := L) := by
  intro a ha
  rcases ha with ⟨f, rfl⟩
  exact ⟨f.extendProjectedAutomorphism generator,
    f.spinorNorm_extendProjectedAutomorphism generator⟩

/-- Determinant-`-1` spinor classes also extend from the projected lattice. -/
theorem improperSpinorNormImage_projectedLattice_subset {x : V}
    {anisotropic : q.IsAnisotropic x}
    (generator : IsNormGenerator q L x) :
    improperSpinorNormImage
        (q := q.orthogonalSpace x anisotropic)
        (L := projectedLattice q L x anisotropic) ⊆
      improperSpinorNormImage (q := q) (L := L) := by
  rintro a ⟨f, hdet, rfl⟩
  let extended := f.extendProjectedAutomorphism generator
  refine ⟨extended, ?_,
    integralSpinorNorm_extendProjectedAutomorphism generator f⟩
  letI : Module.Finite K V := L.moduleFinite
  change LinearEquiv.det
      (QuadraticSpace.orthogonalExtensionLinearEquiv
        f.toQuadraticSpaceIsometry) = (-1 : Kˣ)
  rw [QuadraticSpace.det_orthogonalExtensionLinearEquiv]
  exact hdet

end Lattice

end Bong
