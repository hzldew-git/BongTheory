/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BinaryRotationReflection
import Bong.Lattice.ReflectionScaling

/-!
# Binary spinor norms through primitive reflection vectors

In a binary lattice every proper rotation is a product of two integral
reflections.  Since a reflection vector may be rescaled along its line
without changing either the reflection or its spinor class, the variable
reflection vector may always be chosen primitive.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The binary proper spinor image, expressed using one fixed integral
reflection and one primitive integral reflection. -/
theorem spinorNormImage_eq_fixed_mul_primitiveReflectionClasses
    [FiniteDimensional K V] (hfin : Module.finrank K V = 2)
    {x : V} (hx : q.IsAnisotropic x)
    (hxIntegral : IsIntegralReflection (L := L) hx) :
    spinorNormImage (q := q) (L := L) =
      {a | ∃ (y : V) (hy : q.IsAnisotropic y),
        y ∈ L ∧ y ∉ rescale (uniformizerUnit K) L ∧
        ∃ hyIntegral : IsIntegralReflection (L := L) hy,
          reflectionSpinorClass hx * reflectionSpinorClass hy = a} := by
  rw [spinorNormImage_eq_fixed_mul_integralReflectionClasses
    hfin hx hxIntegral]
  ext a
  constructor
  · rintro ⟨y, hy, hyIntegral, hclass⟩
    have hyNe : y ≠ 0 := by
      intro hyZero
      apply hy
      rw [hyZero]
      simp [QuadraticSpace.quadratic]
    obtain ⟨t, htyMem, htyPrimitive⟩ :=
      exists_unit_smul_mem_not_mem_uniformizer_rescale L hyNe
    let hty : q.IsAnisotropic ((t : K) • y) := hy.unit_smul t
    have htyIntegral : IsIntegralReflection (L := L) hty := by
      exact (isIntegralReflection_unit_smul_iff t hy).2 hyIntegral
    refine ⟨(t : K) • y, hty, htyMem, htyPrimitive,
      htyIntegral, ?_⟩
    rw [reflectionSpinorClass_unit_smul]
    exact hclass
  · rintro ⟨y, hy, _hyMem, _hyPrimitive, hyIntegral, hclass⟩
    exact ⟨y, hy, hyIntegral, hclass⟩

end Lattice

end Bong
