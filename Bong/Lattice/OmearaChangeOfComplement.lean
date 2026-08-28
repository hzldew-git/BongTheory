/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Dual
import Bong.Lattice.Isometry
import Bong.Lattice.Product
import Bong.Lattice.BasisUnits
import Bong.QuadraticSpace.HyperbolicPlane
import Bong.QuadraticSpace.Isometry
import Bong.QuadraticSpace.OrthogonalSum
import Bong.QuadraticSpace.Rescale
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# O'Meara 93:12: the elementary change of complement

This file formalizes the coordinate calculation at the beginning of
O'Meara's dyadic cancellation argument.  If `z` belongs both to a lattice
`M` and to its integral dual, the basis change

`(a, b, u) ↦ (a, b - B(u,z), u + a z)`

identifies `A(Q(z),0) ⊥ M` with `A(0,0) ⊥ M`.  The two hypotheses on
`z` are exactly what makes the change of basis integral in both directions.
This is the coordinate core of O'Meara 93:12 used in the proof of the
hyperbolic cancellation theorem 93:14.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u

variable {K : Type u} [Field K]

/-- The Gram matrix of O'Meara's unimodular binary lattice `A(a,0)`. -/
def omearaPlaneMatrix (a : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a, 1; 1, 0]

@[simp]
theorem omearaPlaneMatrix_zero_zero (a : K) :
    omearaPlaneMatrix a 0 0 = a :=
  rfl

@[simp]
theorem omearaPlaneMatrix_zero_one (a : K) :
    omearaPlaneMatrix a 0 1 = 1 :=
  rfl

@[simp]
theorem omearaPlaneMatrix_one_zero (a : K) :
    omearaPlaneMatrix a 1 0 = 1 :=
  rfl

@[simp]
theorem omearaPlaneMatrix_one_one (a : K) :
    omearaPlaneMatrix a 1 1 = 0 :=
  rfl

theorem omearaPlaneMatrix_isSymm (a : K) :
    (omearaPlaneMatrix a).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem omearaPlaneMatrix_det (a : K) :
    (omearaPlaneMatrix a).det = -1 := by
  simp [omearaPlaneMatrix, Matrix.det_fin_two_of]

/-- The nondegenerate binary quadratic space with Gram matrix
`[[a,1],[1,0]]`. -/
noncomputable def omearaPlane (a : K) :
    QuadraticSpace K (Fin 2 → K) where
  bilin := Matrix.toBilin' (omearaPlaneMatrix a)
  isSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2
    (omearaPlaneMatrix_isSymm a)
  nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (omearaPlaneMatrix a) (by simp)

/-- Coordinate formula for O'Meara's plane `A(a,0)`. -/
theorem omearaPlane_bilin_apply (a : K) (x y : Fin 2 → K) :
    (omearaPlane a).bilin x y =
      a * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 := by
  rw [omearaPlane, Matrix.toBilin'_apply]
  simp only [Fin.sum_univ_two, omearaPlaneMatrix_zero_zero,
    omearaPlaneMatrix_zero_one, omearaPlaneMatrix_one_zero,
    omearaPlaneMatrix_one_one]
  ring

end QuadraticSpace

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type v} [AddCommGroup W] [Module K W]

/-- Membership in the standard rank-two lattice, recorded here without
importing the later maximality development. -/
theorem mem_omearaPlaneLattice_iff (x : Fin 2 → K) :
    x ∈ hyperbolicPlaneLattice (K := K) ↔
      x 0 ∈ IntegerRing K ∧ x 1 ∈ IntegerRing K := by
  rw [hyperbolicPlaneLattice,
    mem_basisLattice_iff_repr_mem_integerRing]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i <;> simpa

/-- The elementary basis change in O'Meara 93:12. -/
noncomputable def omearaChangeOfComplementLinearEquiv
    (r : QuadraticSpace K W) (z : W) :
    ((Fin 2 → K) × W) ≃ₗ[K] ((Fin 2 → K) × W) where
  toFun x :=
    (![x.1 0, x.1 1 - r.bilin x.2 z], x.2 + x.1 0 • z)
  invFun x :=
    (![x.1 0,
        x.1 1 + r.bilin (x.2 - x.1 0 • z) z],
      x.2 - x.1 0 • z)
  left_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · simp
  right_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · simp
  map_add' x y := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [LinearMap.BilinForm.add_left] <;> ring
    · simp [add_smul]
      abel
  map_smul' c x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [LinearMap.BilinForm.smul_left] <;> ring
    · simp [mul_smul, smul_add]

@[simp]
theorem omearaChangeOfComplementLinearEquiv_apply_first_zero
    (r : QuadraticSpace K W) (z : W) (x : (Fin 2 → K) × W) :
    (omearaChangeOfComplementLinearEquiv r z x).1 0 = x.1 0 :=
  rfl

@[simp]
theorem omearaChangeOfComplementLinearEquiv_apply_first_one
    (r : QuadraticSpace K W) (z : W) (x : (Fin 2 → K) × W) :
    (omearaChangeOfComplementLinearEquiv r z x).1 1 =
      x.1 1 - r.bilin x.2 z :=
  rfl

@[simp]
theorem omearaChangeOfComplementLinearEquiv_apply_second
    (r : QuadraticSpace K W) (z : W) (x : (Fin 2 → K) × W) :
    (omearaChangeOfComplementLinearEquiv r z x).2 =
      x.2 + x.1 0 • z :=
  rfl

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- The elementary change of complement is a product of two transvections,
and hence has determinant one. -/
theorem det_omearaChangeOfComplementLinearEquiv
    (r : QuadraticSpace K W) (z : W) :
    LinearEquiv.det (omearaChangeOfComplementLinearEquiv r z) = 1 := by
  let X := (Fin 2 → K) × W
  let pairing : Module.Dual K X :=
    { toFun := fun x ↦ r.bilin x.2 z
      map_add' := by
        intro x y
        exact r.bilin.add_left x.2 y.2 z
      map_smul' := by
        intro c x
        exact r.bilin.smul_left c x.2 z }
  let secondNegative : X := (![0, -1], 0)
  have hpairing : pairing secondNegative = 0 := by
    exact r.bilin.zero_left z
  let firstCoordinate : Module.Dual K X :=
    { toFun := fun x ↦ x.1 0
      map_add' := by
        intro x y
        change x.1 0 + y.1 0 = x.1 0 + y.1 0
        rfl
      map_smul' := by
        intro c x
        change c * x.1 0 = c * x.1 0
        rfl }
  let complementVector : X := (0, z)
  have hfirst : firstCoordinate complementVector = 0 := by
    rfl
  let removePairing := LinearEquiv.transvection hpairing
  let addComplement := LinearEquiv.transvection hfirst
  have hfactor : omearaChangeOfComplementLinearEquiv r z =
      removePairing.trans addComplement := by
    apply LinearEquiv.ext
    intro x
    apply Prod.ext
    · funext i
      change (![x.1 0, x.1 1 - r.bilin x.2 z] : Fin 2 → K) i =
        (addComplement (removePairing x)).1 i
      rw [LinearEquiv.transvection.apply hpairing x,
        LinearEquiv.transvection.apply hfirst]
      fin_cases i <;>
        simp [X, pairing, secondNegative, firstCoordinate, complementVector,
          Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
      all_goals simp only [sub_eq_add_neg]
    · change x.2 + x.1 0 • z =
        (addComplement (removePairing x)).2
      rw [LinearEquiv.transvection.apply hpairing x,
        LinearEquiv.transvection.apply hfirst]
      simp [X, pairing, secondNegative, firstCoordinate, complementVector]
  rw [hfactor, LinearEquiv.det_trans,
    LinearEquiv.transvection.det_eq_one,
    LinearEquiv.transvection.det_eq_one, one_mul]

/-- The change of complement preserves the total quadratic form. -/
noncomputable def omearaChangeOfComplementSpaceIsometry
    (r : QuadraticSpace K W) (z : W) :
    QuadraticSpace.Isometry
      ((QuadraticSpace.omearaPlane (r.quadratic z)).orthogonalSum r)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r) where
  toLinearEquiv := omearaChangeOfComplementLinearEquiv r z
  map_bilin x y := by
    rw [QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.omearaPlane_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply]
    simp only [omearaChangeOfComplementLinearEquiv_apply_first_zero,
      omearaChangeOfComplementLinearEquiv_apply_first_one,
      omearaChangeOfComplementLinearEquiv_apply_second, Units.val_one,
      one_mul, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, smul_eq_mul]
    rw [r.isSymm.eq z y.2]
    rw [show r.quadratic z = r.bilin z z by rfl]
    ring

/-- O'Meara 93:12 in an exact integral coordinate model.  A vector lying
in both `M` and `M⁺` may be moved into the first vector of a unimodular
hyperbolic plane without changing the integral isometry class. -/
noncomputable def omeara9312
    (r : QuadraticSpace K W) (M : Lattice K W) (z : W)
    (hzM : z ∈ M) (hzDual : z ∈ dualLattice r M) :
    Isometry
      ((QuadraticSpace.omearaPlane (r.quadratic z)).orthogonalSum r)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M)
      (product (hyperbolicPlaneLattice (K := K)) M) where
  toLinearEquiv := omearaChangeOfComplementLinearEquiv r z
  map_bilin := (omearaChangeOfComplementSpaceIsometry r z).map_bilin
  map_mem x := by
    rw [mem_product_iff, mem_product_iff]
    constructor
    · rintro ⟨hxPlane, hxM⟩
      rw [mem_omearaPlaneLattice_iff] at hxPlane ⊢
      have hpair : r.bilin x.2 z ∈ IntegerRing K := by
        rw [r.isSymm.eq]
        exact (mem_dualLattice_iff r M z).mp hzDual x.2 hxM
      refine ⟨⟨hxPlane.1,
        (IntegerRing K).toSubring.sub_mem hxPlane.2 hpair⟩, ?_⟩
      exact M.add_mem hxM (M.smul_mem
        ⟨x.1 0, hxPlane.1⟩ hzM)
    · rintro ⟨hxPlane, hxM⟩
      rw [mem_omearaPlaneLattice_iff] at hxPlane ⊢
      have hxM' : x.2 + x.1 0 • z ∈ M := by
        simpa only [omearaChangeOfComplementLinearEquiv_apply_second]
          using hxM
      have hxOriginalM : x.2 ∈ M := by
        have hscaled : x.1 0 • z ∈ M :=
          M.smul_mem ⟨x.1 0, hxPlane.1⟩ hzM
        simpa only [add_sub_cancel_right] using M.sub_mem hxM' hscaled
      have hxPlaneOne : x.1 1 - r.bilin x.2 z ∈ IntegerRing K := by
        simpa only [omearaChangeOfComplementLinearEquiv_apply_first_one]
          using hxPlane.2
      have hpair : r.bilin x.2 z ∈ IntegerRing K := by
        rw [r.isSymm.eq]
        exact (mem_dualLattice_iff r M z).mp hzDual x.2 hxOriginalM
      refine ⟨⟨hxPlane.1, ?_⟩, hxOriginalM⟩
      have hadd := (IntegerRing K).toSubring.add_mem hxPlaneOne hpair
      change x.1 1 ∈ (IntegerRing K).toSubring
      simpa only [sub_add_cancel] using hadd

/-- O'Meara 93:12 with the initial binary coefficient retained.  Moving
`z ∈ M ∩ M⁺` into the first vector changes `A(α + Q(z), 0)` into
`A(α, 0)` and leaves the complement integrally isometric.  The earlier
`omeara9312` is the special case `α = 0`. -/
noncomputable def omeara9312_general
    (r : QuadraticSpace K W) (M : Lattice K W) (α : K) (z : W)
    (hzM : z ∈ M) (hzDual : z ∈ dualLattice r M) :
    Isometry
      ((QuadraticSpace.omearaPlane (α + r.quadratic z)).orthogonalSum r)
      ((QuadraticSpace.omearaPlane α).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M)
      (product (hyperbolicPlaneLattice (K := K)) M) where
  toLinearEquiv := omearaChangeOfComplementLinearEquiv r z
  map_bilin x y := by
    rw [QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.omearaPlane_bilin_apply,
      QuadraticSpace.omearaPlane_bilin_apply]
    simp only [omearaChangeOfComplementLinearEquiv_apply_first_zero,
      omearaChangeOfComplementLinearEquiv_apply_first_one,
      omearaChangeOfComplementLinearEquiv_apply_second,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      smul_eq_mul]
    rw [r.isSymm.eq z y.2]
    rw [show r.quadratic z = r.bilin z z by rfl]
    ring
  map_mem := (omeara9312 r M z hzM hzDual).map_mem

/-- O'Meara 93:13 for a represented correction in the complement.  In the
scaled plane `s A(α,0)`, a vector of value `Q(z)` changes the displayed
coefficient by `s⁻¹ Q(z)`. -/
noncomputable def omeara9313_represented
    (r : QuadraticSpace K W) (M : Lattice K W) (s : Kˣ) (α : K)
    (z : W) (hzM : z ∈ M)
    (hzDual : z ∈ dualLattice (r.rescaleUnit s⁻¹) M) :
    Isometry
      (((QuadraticSpace.omearaPlane
          (α + (s⁻¹ : Kˣ) * r.quadratic z)).rescaleUnit s).orthogonalSum r)
      (((QuadraticSpace.omearaPlane α).rescaleUnit s).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M)
      (product (hyperbolicPlaneLattice (K := K)) M) where
  toLinearEquiv :=
    omearaChangeOfComplementLinearEquiv (r.rescaleUnit s⁻¹) z
  map_bilin x y := by
    rw [QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.omearaPlane_bilin_apply,
      QuadraticSpace.omearaPlane_bilin_apply]
    simp only [omearaChangeOfComplementLinearEquiv_apply_first_zero,
      omearaChangeOfComplementLinearEquiv_apply_first_one,
      omearaChangeOfComplementLinearEquiv_apply_second,
      QuadraticSpace.rescaleUnit_bilin_apply,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      smul_eq_mul, Units.val_inv_eq_inv_val]
    rw [r.isSymm.eq z y.2]
    rw [show r.quadratic z = r.bilin z z by rfl]
    field_simp [Units.ne_zero s]
    ring
  map_mem :=
    (omeara9312 (r.rescaleUnit s⁻¹) M z hzM hzDual).map_mem

end Lattice

end Bong
