/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaChangeOfComplement
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Integral Eichler transformations on a hyperbolic adjunction

This file records the explicit integral transformation used in the final
step of O'Meara 93:14.  If `z` belongs to a lattice and its integral dual,
and `Q(z) = 2s` with `s` integral, then

`(a,b,u) ↦ (a - sb - B(u,z), b, u + bz)`

is an automorphism of `A(0,0) ⊥ M`.  It fixes the first isotropic vector
and sends the second one to `(-s,1,z)`.  The construction is factored
through O'Meara 93:12, so its integrality is derived rather than assumed.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-! ## Binary coordinate isometries -/

/-- The change of coordinates from `A(0,0)` to `A(a,0)` when `a = 2s`.
It sends the two standard hyperbolic vectors to `(0,1)` and `(1,-s)`.
-/
noncomputable def hyperbolicToOmearaPlaneLinearEquiv (s : K) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![x 1, x 0 - s * x 1]
  invFun x := ![x 1 + s * x 0, x 0]
  left_inv x := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv x := by
    funext i
    fin_cases i <;> simp <;> ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem hyperbolicToOmearaPlaneLinearEquiv_zero
    (s : K) (x : Fin 2 → K) :
    hyperbolicToOmearaPlaneLinearEquiv s x 0 = x 1 :=
  rfl

@[simp]
theorem hyperbolicToOmearaPlaneLinearEquiv_one
    (s : K) (x : Fin 2 → K) :
    hyperbolicToOmearaPlaneLinearEquiv s x 1 = x 0 - s * x 1 :=
  rfl

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- The binary coordinate change has determinant `-1`. -/
theorem det_hyperbolicToOmearaPlaneLinearEquiv (s : K) :
    LinearEquiv.det (hyperbolicToOmearaPlaneLinearEquiv s) = (-1 : Kˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  let A := LinearMap.toMatrix'
    (hyperbolicToOmearaPlaneLinearEquiv s).toLinearMap
  have hA : A = !![(0 : K), 1; 1, -s] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, hyperbolicToOmearaPlaneLinearEquiv]
  change A.det = -1
  rw [hA]
  simp [Matrix.det_fin_two_of]

/-- The binary coordinate change preserves the indicated quadratic spaces. -/
noncomputable def hyperbolicToOmearaPlaneSpaceIsometry
    (a s : K) (ha : a = 2 * s) :
    QuadraticSpace.Isometry
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (QuadraticSpace.omearaPlane a) where
  toLinearEquiv := hyperbolicToOmearaPlaneLinearEquiv s
  map_bilin x y := by
    rw [QuadraticSpace.omearaPlane_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply]
    simp only [hyperbolicToOmearaPlaneLinearEquiv_zero,
      hyperbolicToOmearaPlaneLinearEquiv_one, Units.val_one, one_mul]
    rw [ha]
    ring

/-- If `s` is integral, the binary coordinate change preserves the standard
rank-two lattice. -/
noncomputable def hyperbolicToOmearaPlaneLatticeIsometry
    (a s : K) (ha : a = 2 * s) (hs : s ∈ IntegerRing K) :
    Isometry
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (QuadraticSpace.omearaPlane a)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := hyperbolicToOmearaPlaneLinearEquiv s
  map_bilin := (hyperbolicToOmearaPlaneSpaceIsometry a s ha).map_bilin
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    constructor
    · rintro ⟨hzero, hone⟩
      exact ⟨hone, (IntegerRing K).toSubring.sub_mem hzero
        ((IntegerRing K).toSubring.mul_mem hs hone)⟩
    · rintro ⟨hzero, hone⟩
      refine ⟨?_, hzero⟩
      have hadd := (IntegerRing K).toSubring.add_mem hone
        ((IntegerRing K).toSubring.mul_mem hs hzero)
      change x 0 - s * x 1 + s * x 1 ∈ (IntegerRing K).toSubring at hadd
      change x 0 ∈ (IntegerRing K).toSubring
      simpa only [sub_add_cancel] using hadd

/-- Swap the two standard isotropic vectors of the hyperbolic plane. -/
noncomputable def omearaHyperbolicSwapLinearEquiv :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![x 1, x 0]
  invFun x := ![x 1, x 0]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' c x := by
    funext i
    fin_cases i <;> simp

@[simp]
theorem omearaHyperbolicSwapLinearEquiv_zero (x : Fin 2 → K) :
    omearaHyperbolicSwapLinearEquiv x 0 = x 1 :=
  rfl

@[simp]
theorem omearaHyperbolicSwapLinearEquiv_one (x : Fin 2 → K) :
    omearaHyperbolicSwapLinearEquiv x 1 = x 0 :=
  rfl

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- Swapping the two hyperbolic coordinates has determinant `-1`. -/
theorem det_omearaHyperbolicSwapLinearEquiv :
    LinearEquiv.det
      (omearaHyperbolicSwapLinearEquiv (K := K)) = (-1 : Kˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  change Matrix.det !![(0 : K), 1; 1, 0] = -1
  simp [Matrix.det_fin_two_of]

/-- Swapping the two coordinates is an integral isometry of `A(0,0)`. -/
noncomputable def omearaHyperbolicSwapLatticeIsometry :
    Isometry
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := omearaHyperbolicSwapLinearEquiv
  map_bilin x y := by
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply]
    simp only [omearaHyperbolicSwapLinearEquiv_zero,
      omearaHyperbolicSwapLinearEquiv_one, Units.val_one, one_mul]
    ring
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    exact and_comm

/-- Swap the hyperbolic coordinates and leave an orthogonal factor fixed. -/
noncomputable def omearaHyperbolicProductSwap
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) L) :=
  Isometry.orthogonalProductBasic
    (omearaHyperbolicSwapLatticeIsometry (K := K))
    (Isometry.refl q L)

@[simp]
theorem omearaHyperbolicProductSwap_apply
    (q : QuadraticSpace K V) (L : Lattice K V)
    (x : (Fin 2 → K) × V) :
    (omearaHyperbolicProductSwap q L).toLinearEquiv x =
      (![x.1 1, x.1 0], x.2) :=
  rfl

/-! ## The integral Eichler transformation -/

/-- The Eichler transformation on a hyperbolic adjunction, constructed from
the binary shear, O'Meara 93:12, and the hyperbolic swap. -/
noncomputable def hyperbolicEichlerLatticeIsometry
    (q : QuadraticSpace K V) (L : Lattice K V) (z : V)
    (hzL : z ∈ L) (hzDual : z ∈ dualLattice q L)
    (s : K) (hquadratic : q.quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) :
    Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) L) := by
  let shear := Isometry.orthogonalProductBasic
    (hyperbolicToOmearaPlaneLatticeIsometry
      (q.quadratic z) s hquadratic hs)
    (Isometry.refl q L)
  let change := omeara9312 q L z hzL hzDual
  let swap := Isometry.orthogonalProductBasic
    (omearaHyperbolicSwapLatticeIsometry (K := K))
    (Isometry.refl q L)
  exact (shear.trans change).trans swap

/-- The integral Eichler transformation is proper.  Its two determinant
`-1` binary coordinate changes surround the determinant-one O'Meara 93:12
change of complement. -/
theorem det_hyperbolicEichlerLatticeIsometry
    (q : QuadraticSpace K V) (L : Lattice K V) (z : V)
    (hzL : z ∈ L) (hzDual : z ∈ dualLattice q L)
    (s : K) (hquadratic : q.quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) :
    LinearEquiv.det
      (hyperbolicEichlerLatticeIsometry
        q L z hzL hzDual s hquadratic hs).toLinearEquiv = 1 := by
  letI : Module.Finite K V := L.moduleFinite
  let shear :=
    (hyperbolicToOmearaPlaneLatticeIsometry
      (q.quadratic z) s hquadratic hs).orthogonalProductBasic
        (Isometry.refl q L)
  let change := omeara9312 q L z hzL hzDual
  let swap := Isometry.orthogonalProductBasic
    (omearaHyperbolicSwapLatticeIsometry (K := K))
    (Isometry.refl q L)
  have hshear : LinearEquiv.det shear.toLinearEquiv = (-1 : Kˣ) := by
    rw [Isometry.det_orthogonalProductBasic]
    change LinearEquiv.det (hyperbolicToOmearaPlaneLinearEquiv s) *
      LinearEquiv.det (LinearEquiv.refl K V) = (-1 : Kˣ)
    rw [det_hyperbolicToOmearaPlaneLinearEquiv,
      LinearEquiv.det_refl, mul_one]
  have hchange : LinearEquiv.det change.toLinearEquiv = 1 :=
    det_omearaChangeOfComplementLinearEquiv q z
  have hswap : LinearEquiv.det swap.toLinearEquiv = (-1 : Kˣ) := by
    rw [Isometry.det_orthogonalProductBasic]
    change LinearEquiv.det (omearaHyperbolicSwapLinearEquiv (K := K)) *
      LinearEquiv.det (LinearEquiv.refl K V) = (-1 : Kˣ)
    rw [det_omearaHyperbolicSwapLinearEquiv,
      LinearEquiv.det_refl, mul_one]
  change LinearEquiv.det
      ((shear.toLinearEquiv.trans change.toLinearEquiv).trans
        swap.toLinearEquiv) = 1
  rw [LinearEquiv.det_trans, LinearEquiv.det_trans,
    hshear, hchange, hswap]
  norm_num

/-- The Eichler transformation after an arbitrary common form scaling.
The complement is tested for integrality in the rescaled form `a⁻¹ q`;
multiplying the resulting identity by `a` gives an automorphism of
`H_a ⊥ q` with the same coordinate formula. -/
noncomputable def hyperbolicEichlerLatticeIsometry_scaled
    (a : Kˣ) (q : QuadraticSpace K V) (L : Lattice K V) (z : V)
    (hzL : z ∈ L) (hzDual : z ∈ dualLattice (q.rescaleUnit a⁻¹) L)
    (s : K) (hquadratic : (q.rescaleUnit a⁻¹).quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) :
    Isometry
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum q)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) L) := by
  let T := hyperbolicEichlerLatticeIsometry
    (q.rescaleUnit a⁻¹) L z hzL hzDual s hquadratic hs
  exact {
    toLinearEquiv := T.toLinearEquiv
    map_bilin := by
      intro x y
      have h := T.map_bilin x y
      simp only [QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply,
        QuadraticSpace.rescaleUnit_bilin_apply,
        Units.val_one, one_mul] at h ⊢
      have ha : (a : K) ≠ 0 := Units.ne_zero a
      have haInv : ((a⁻¹ : Kˣ) : K) = (a : K)⁻¹ := by
        simpa only [Units.val_inv_eq_inv_val]
      rw [haInv] at h
      calc
        (a : K) *
              ((T.toLinearEquiv x).1 0 * (T.toLinearEquiv y).1 1 +
                (T.toLinearEquiv x).1 1 * (T.toLinearEquiv y).1 0) +
            q.bilin (T.toLinearEquiv x).2 (T.toLinearEquiv y).2 =
            (a : K) *
              (((T.toLinearEquiv x).1 0 * (T.toLinearEquiv y).1 1 +
                  (T.toLinearEquiv x).1 1 * (T.toLinearEquiv y).1 0) +
                (a : K)⁻¹ *
                  q.bilin (T.toLinearEquiv x).2 (T.toLinearEquiv y).2) := by
              field_simp [ha]
        _ = (a : K) *
              ((x.1 0 * y.1 1 + x.1 1 * y.1 0) +
                (a : K)⁻¹ * q.bilin x.2 y.2) := by rw [h]
        _ = (a : K) * (x.1 0 * y.1 1 + x.1 1 * y.1 0) +
              q.bilin x.2 y.2 := by
              field_simp [ha]
    map_mem := T.map_mem
  }

/-- Common rescaling does not alter the underlying determinant-one Eichler
transformation. -/
theorem det_hyperbolicEichlerLatticeIsometry_scaled
    (a : Kˣ) (q : QuadraticSpace K V) (L : Lattice K V) (z : V)
    (hzL : z ∈ L) (hzDual : z ∈ dualLattice (q.rescaleUnit a⁻¹) L)
    (s : K) (hquadratic : (q.rescaleUnit a⁻¹).quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) :
    LinearEquiv.det
      (hyperbolicEichlerLatticeIsometry_scaled
        a q L z hzL hzDual s hquadratic hs).toLinearEquiv = 1 := by
  exact det_hyperbolicEichlerLatticeIsometry
    (q.rescaleUnit a⁻¹) L z hzL hzDual s hquadratic hs

@[simp]
theorem hyperbolicEichlerLatticeIsometry_scaled_apply_first_zero
    (a : Kˣ) (z : V) (hzL : z ∈ L)
    (hzDual : z ∈ dualLattice (q.rescaleUnit a⁻¹) L)
    (s : K) (hquadratic : (q.rescaleUnit a⁻¹).quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) (x : (Fin 2 → K) × V) :
    (hyperbolicEichlerLatticeIsometry_scaled
      a q L z hzL hzDual s hquadratic hs |>.toLinearEquiv x).1 0 =
        x.1 0 - s * x.1 1 - (q.rescaleUnit a⁻¹).bilin x.2 z :=
  rfl

@[simp]
theorem hyperbolicEichlerLatticeIsometry_scaled_apply_first_one
    (a : Kˣ) (z : V) (hzL : z ∈ L)
    (hzDual : z ∈ dualLattice (q.rescaleUnit a⁻¹) L)
    (s : K) (hquadratic : (q.rescaleUnit a⁻¹).quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) (x : (Fin 2 → K) × V) :
    (hyperbolicEichlerLatticeIsometry_scaled
      a q L z hzL hzDual s hquadratic hs |>.toLinearEquiv x).1 1 = x.1 1 :=
  rfl

@[simp]
theorem hyperbolicEichlerLatticeIsometry_scaled_apply_second
    (a : Kˣ) (z : V) (hzL : z ∈ L)
    (hzDual : z ∈ dualLattice (q.rescaleUnit a⁻¹) L)
    (s : K) (hquadratic : (q.rescaleUnit a⁻¹).quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) (x : (Fin 2 → K) × V) :
    (hyperbolicEichlerLatticeIsometry_scaled
      a q L z hzL hzDual s hquadratic hs |>.toLinearEquiv x).2 =
        x.2 + x.1 1 • z :=
  rfl

@[simp]
theorem hyperbolicEichlerLatticeIsometry_apply_first_zero
    (z : V) (hzL : z ∈ L) (hzDual : z ∈ dualLattice q L)
    (s : K) (hquadratic : q.quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) (x : (Fin 2 → K) × V) :
    (hyperbolicEichlerLatticeIsometry q L z hzL hzDual s hquadratic hs
      |>.toLinearEquiv x).1 0 =
        x.1 0 - s * x.1 1 - q.bilin x.2 z :=
  rfl

@[simp]
theorem hyperbolicEichlerLatticeIsometry_apply_first_one
    (z : V) (hzL : z ∈ L) (hzDual : z ∈ dualLattice q L)
    (s : K) (hquadratic : q.quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) (x : (Fin 2 → K) × V) :
    (hyperbolicEichlerLatticeIsometry q L z hzL hzDual s hquadratic hs
      |>.toLinearEquiv x).1 1 = x.1 1 :=
  rfl

@[simp]
theorem hyperbolicEichlerLatticeIsometry_apply_second
    (z : V) (hzL : z ∈ L) (hzDual : z ∈ dualLattice q L)
    (s : K) (hquadratic : q.quadratic z = 2 * s)
    (hs : s ∈ IntegerRing K) (x : (Fin 2 → K) × V) :
    (hyperbolicEichlerLatticeIsometry q L z hzL hzDual s hquadratic hs
      |>.toLinearEquiv x).2 = x.2 + x.1 1 • z :=
  rfl

end Lattice

end Bong
