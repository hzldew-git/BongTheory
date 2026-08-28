/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Determinant
import Bong.Lattice.NormGenerator
import Bong.QuadraticSpace.Rescale

/-!
# Rescaling the quadratic form of a lattice

Multiplying a quadratic form by a nonzero field element leaves its
anisotropic vectors unchanged, multiplies every norm value by that element,
and shifts the lattice volume order by `rank * ord(a)`.  These elementary
facts are kept separate from rescaling the lattice itself.
-/

namespace Bong

open Dyadic
open Module

universe u v

namespace QuadraticSpace

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {x : V}

/-- An anisotropic vector stays anisotropic after rescaling the quadratic
form by a nonzero scalar. -/
theorem IsAnisotropic.rescaleUnit (hx : q.IsAnisotropic x) (a : Kˣ) :
    (q.rescaleUnit a).IsAnisotropic x := by
  rw [QuadraticSpace.IsAnisotropic, rescaleUnit_quadratic]
  exact mul_ne_zero (Units.ne_zero a) hx

end QuadraticSpace

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V}

/-- A norm generator stays a norm generator when the quadratic form is
rescaled.  The generated principal ideal is rescaled by the same factor. -/
theorem IsNormGenerator.rescaleQuadraticUnit
    (generator : IsNormGenerator q L x) (a : Kˣ) :
    IsNormGenerator (q.rescaleUnit a) L x := by
  constructor
  · exact generator.mem
  · apply le_antisymm
    · apply normIdeal_le_of_quadratic_mem
      intro y hy
      have hqy := quadratic_mem_normIdeal_of_mem q L hy
      rw [generator.normIdeal_eq, principalIdeal,
        Submodule.mem_span_singleton] at hqy
      rcases hqy with ⟨c, hc⟩
      rw [principalIdeal, Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      change (c : K) * ((a : K) * q.quadratic x) =
        (a : K) * q.quadratic y
      have hc' : (c : K) * q.quadratic x = q.quadratic y := by
        simpa [Algebra.smul_def] using hc
      rw [← hc']
      ring
    · rw [principalIdeal, Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact quadratic_mem_normIdeal_of_mem (q.rescaleUnit a) L generator.mem

/-- Rescaling a quadratic form by a nonzero scalar does not change which
vectors are norm generators. -/
theorem isNormGenerator_rescaleQuadraticUnit_iff (a : Kˣ) :
    IsNormGenerator (q.rescaleUnit a) L x ↔ IsNormGenerator q L x := by
  constructor
  · intro generator
    have h := generator.rescaleQuadraticUnit a⁻¹
    simpa [QuadraticSpace.rescaleUnit] using h
  · intro generator
    exact generator.rescaleQuadraticUnit a

/-- The integral Gram matrix is multiplied entrywise by the form-rescaling
factor. -/
theorem integralGramMatrix_rescaleUnit (q : QuadraticSpace K V)
    (a : Kˣ) (L : Lattice K V) :
    integralGramMatrix (q.rescaleUnit a) L =
      (a : K) • integralGramMatrix q L := by
  ext i j
  simp [integralGramMatrix_apply, Matrix.smul_apply, smul_eq_mul]

/-- Rescaling a rank-`n` quadratic form multiplies its lattice determinant
by `a^n`. -/
theorem determinant_rescaleUnit (q : QuadraticSpace K V)
    (a : Kˣ) (L : Lattice K V) :
    determinant (q.rescaleUnit a) L =
      (a : K) ^ finrank K V * determinant q L := by
  rw [determinant, determinant, integralGramMatrix_rescaleUnit,
    Matrix.det_smul, Fintype.card_fin]

/-- Unit-valued form of `determinant_rescaleUnit`. -/
theorem determinantUnit_rescaleUnit (q : QuadraticSpace K V)
    (a : Kˣ) (L : Lattice K V) :
    determinantUnit (q.rescaleUnit a) L =
      a ^ finrank K V * determinantUnit q L := by
  apply Units.ext
  change determinant (q.rescaleUnit a) L =
    (a : K) ^ finrank K V * determinant q L
  exact determinant_rescaleUnit q a L

/-- Rescaling a form multiplies its refined determinant class by the
corresponding rank power of the rescaling unit. -/
theorem determinantClass_rescaleUnit (q : QuadraticSpace K V)
    (a : Kˣ) (L : Lattice K V) :
    determinantClass (q.rescaleUnit a) L =
      unitSquareClass K (a ^ finrank K V) * determinantClass q L := by
  rw [determinantClass, determinantClass,
    determinantUnit_rescaleUnit, unitSquareClass_mul]

/-- Form rescaling shifts the volume order by
`rank * ord(a)`. -/
theorem volumeOrder_rescaleUnit (q : QuadraticSpace K V)
    (a : Kˣ) (L : Lattice K V) :
    volumeOrder (q.rescaleUnit a) L =
      volumeOrder q L + (finrank K V : Int) * ordUnit K a := by
  apply WithTop.coe_injective
  rw [coe_volumeOrder, determinant_rescaleUnit, ord_mul, ord_pow,
    ← coe_ordUnit, ← coe_volumeOrder]
  norm_cast
  simp
  ring

end Lattice

end Bong
