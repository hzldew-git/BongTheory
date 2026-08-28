/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicCancellation
import Bong.Lattice.OmearaHyperbolicSpinor
import Bong.Lattice.SpinorNormIsometry
import Bong.Lattice.SpinorNormMultiplicative
import Bong.Lattice.SpinorNormOrthogonalProduct
import Bong.QuadraticSpace.IsometryDeterminant

/-!
# Transport of a scaled hyperbolic summand by Eichler transformations

Beli (2003), Lemma 7.1(ii), uses the standard fact that two displayed
scaled hyperbolic summands in the same lattice are carried to one another
by a product of Eichler transformations.  The geometric core is the same
four-cross-pairing reduction as O'Meara 93:14.  This file retains the
ambient transformations, together with determinant-one and spinor-norm-one
certificates; the cancellation theorem itself only retained the induced
isometry of the complements.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private noncomputable abbrev ScaledHyperbolicSum
    (q : QuadraticSpace K V) (a : Kˣ) :=
  (QuadraticSpace.hyperbolicPlane a).orthogonalSum q

private noncomputable abbrev ScaledHyperbolicProduct
    (L : Lattice K V) :=
  product (hyperbolicPlaneLattice (K := K)) L

/-- The first standard isotropic vector belongs to the coordinate lattice. -/
private theorem first_mem_hyperbolicPlaneLattice :
    omearaHyperbolicFirst (K := K) ∈
      hyperbolicPlaneLattice (K := K) := by
  rw [mem_omearaPlaneLattice_iff]
  simp [omearaHyperbolicFirst]

/-- The second standard isotropic vector belongs to the coordinate lattice. -/
private theorem second_mem_hyperbolicPlaneLattice :
    omearaHyperbolicSecond (K := K) ∈
      hyperbolicPlaneLattice (K := K) := by
  rw [mem_omearaPlaneLattice_iff]
  simp [omearaHyperbolicSecond]

/-- The complement coordinate of the image of the first hyperbolic vector
lies in the dual lattice for the rescaled complement form. -/
private theorem firstImage_second_mem_scaledDual
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)) :
    (f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0)).2 ∈
      dualLattice (q.rescaleUnit a⁻¹) L := by
  rw [mem_dualLattice_iff]
  intro y hy
  let pre := f.toLinearEquiv.symm ((0 : Fin 2 → K), y)
  have htarget : ((0 : Fin 2 → K), y) ∈
      ScaledHyperbolicProduct (K := K) L := by
    rw [mem_product_iff]
    exact ⟨by simp, hy⟩
  have hpre : pre ∈ ScaledHyperbolicProduct (K := K) L := by
    exact (f.symm.map_mem _).mp htarget
  have hprePlane : pre.1 ∈ hyperbolicPlaneLattice (K := K) :=
    (mem_product_iff.mp hpre).1
  have hpreOne : pre.1 1 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff pre.1).mp hprePlane |>.2
  have hbilin := f.map_bilin
    (omearaHyperbolicFirst (K := K), (0 : V)) pre
  have hfpre : f.toLinearEquiv pre = ((0 : Fin 2 → K), y) := by
    exact f.toLinearEquiv.apply_symm_apply _
  rw [hfpre] at hbilin
  change ((a⁻¹ : Kˣ) : K) *
      q.bilin
        (f.toLinearEquiv
          (omearaHyperbolicFirst (K := K), (0 : V))).2 y ∈
    IntegerRing K
  have heq : q.bilin
      (f.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).2 y =
      (a : K) * pre.1 1 := by
    simpa [ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
    omearaHyperbolicFirst] using hbilin
  rw [heq]
  simpa [Units.ne_zero a] using hpreOne

/-- The analogous dual-lattice statement for the second hyperbolic vector. -/
private theorem secondImage_second_mem_scaledDual
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)) :
    (f.toLinearEquiv (omearaHyperbolicSecond (K := K), 0)).2 ∈
      dualLattice (q.rescaleUnit a⁻¹) L := by
  rw [mem_dualLattice_iff]
  intro y hy
  let pre := f.toLinearEquiv.symm ((0 : Fin 2 → K), y)
  have htarget : ((0 : Fin 2 → K), y) ∈
      ScaledHyperbolicProduct (K := K) L := by
    rw [mem_product_iff]
    exact ⟨by simp, hy⟩
  have hpre : pre ∈ ScaledHyperbolicProduct (K := K) L := by
    exact (f.symm.map_mem _).mp htarget
  have hprePlane : pre.1 ∈ hyperbolicPlaneLattice (K := K) :=
    (mem_product_iff.mp hpre).1
  have hpreZero : pre.1 0 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff pre.1).mp hprePlane |>.1
  have hbilin := f.map_bilin
    (omearaHyperbolicSecond (K := K), (0 : V)) pre
  have hfpre : f.toLinearEquiv pre = ((0 : Fin 2 → K), y) := by
    exact f.toLinearEquiv.apply_symm_apply _
  rw [hfpre] at hbilin
  change ((a⁻¹ : Kˣ) : K) *
      q.bilin
        (f.toLinearEquiv
          (omearaHyperbolicSecond (K := K), (0 : V))).2 y ∈
    IntegerRing K
  have heq : q.bilin
      (f.toLinearEquiv
        (omearaHyperbolicSecond (K := K), (0 : V))).2 y =
      (a : K) * pre.1 0 := by
    simpa [ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
    omearaHyperbolicSecond] using hbilin
  rw [heq]
  simpa [Units.ne_zero a] using hpreZero

/-- A single Eichler transformation that sends an isotropic image whose
second hyperbolic coordinate is a unit to a multiple of the standard second
isotropic vector. -/
structure UnitSecondEichlerReduction (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)) where
  rotation : IntegralRotation (ScaledHyperbolicSum (q := q) a)
    (ScaledHyperbolicProduct (K := K) L)
  spinorNorm_eq_one : rotation.spinorNorm = 1
  fixes_first : rotation.apply
      (omearaHyperbolicFirst (K := K), (0 : V)) =
    (omearaHyperbolicFirst (K := K), 0)
  image_first_eq : rotation.apply
      (f.toLinearEquiv (omearaHyperbolicFirst (K := K), (0 : V))) =
    ((f.toLinearEquiv
      (omearaHyperbolicFirst (K := K), (0 : V))).1 1 •
        omearaHyperbolicSecond (K := K), 0)

/-- Explicit construction of the unit-cross-pairing reduction. -/
noncomputable def unitSecondEichlerReduction
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L))
    (hunit : IsValuationUnit K
      ((f.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 1)) :
    UnitSecondEichlerReduction a f := by
  let X := f.toLinearEquiv
    (omearaHyperbolicFirst (K := K), (0 : V))
  let c : K := X.1 1
  have hc : IsValuationUnit K c := by simpa [c, X] using hunit
  have hc0 : c ≠ 0 := ne_zero_of_isValuationUnit hc
  let cu : Kˣ := Units.mk0 c hc0
  let cinv : K := ((cu⁻¹ : Kˣ) : K)
  have hcinvUnit : IsValuationUnit K cinv := by
    simpa [cinv, IsValuationUnit, AddValuation.map_inv, cu] using hc
  have hcinvMem : cinv ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 hcinvUnit.ge
  have hXmem : X ∈ ScaledHyperbolicProduct (K := K) L := by
    have hsource : (omearaHyperbolicFirst (K := K), (0 : V)) ∈
        ScaledHyperbolicProduct (K := K) L := by
      rw [mem_product_iff]
      exact ⟨first_mem_hyperbolicPlaneLattice, L.zero_mem⟩
    exact (f.map_mem _).mp hsource
  have hXzero : X.1 0 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff X.1).mp
      (mem_product_iff.mp hXmem).1 |>.1
  have hXsecond : X.2 ∈ L := (mem_product_iff.mp hXmem).2
  have hXdual : X.2 ∈ dualLattice (q.rescaleUnit a⁻¹) L := by
    simpa [X] using firstImage_second_mem_scaledDual (q := q) (L := L) a f
  let z : V := -cinv • X.2
  have hzL : z ∈ L := by
    let d : IntegerRing K :=
      ⟨-cinv, (IntegerRing K).neg_mem cinv hcinvMem⟩
    have := L.smul_mem d hXsecond
    change (-cinv) • X.2 ∈ L
    exact this
  have hzDual : z ∈ dualLattice (q.rescaleUnit a⁻¹) L := by
    let d : IntegerRing K :=
      ⟨-cinv, (IntegerRing K).neg_mem cinv hcinvMem⟩
    have := (dualLattice (q.rescaleUnit a⁻¹) L).smul_mem d hXdual
    change (-cinv) • X.2 ∈ dualLattice (q.rescaleUnit a⁻¹) L
    exact this
  let s : K := -X.1 0 * cinv
  have hsMem : s ∈ IntegerRing K := by
    change s ∈ (IntegerRing K).toSubring
    exact (IntegerRing K).toSubring.mul_mem
      ((IntegerRing K).toSubring.neg_mem hXzero) hcinvMem
  have hXisotropic :
      (ScaledHyperbolicSum (q := q) a).quadratic X = 0 := by
    have h := f.map_quadratic
      (omearaHyperbolicFirst (K := K), (0 : V))
    simpa [X, ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply,
      omearaHyperbolicFirst] using h
  have hcinvEq : cinv = c⁻¹ := by simp [cinv, cu]
  have ha0 : (a : K) ≠ 0 := Units.ne_zero a
  have hrelation : q.quadratic X.2 =
      -2 * (a : K) * X.1 0 * c := by
    have hXisotropic' := hXisotropic
    simp only [ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply] at hXisotropic'
    change 2 * (a : K) * (X.1 0 * c) + q.quadratic X.2 = 0 at hXisotropic'
    linear_combination hXisotropic'
  have hrescaledX : (q.rescaleUnit a⁻¹).quadratic X.2 =
      -2 * X.1 0 * c := by
    rw [QuadraticSpace.rescaleUnit_quadratic, hrelation]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [ha0]
  have hquadratic : (q.rescaleUnit a⁻¹).quadratic z = 2 * s := by
    rw [show (q.rescaleUnit a⁻¹).quadratic z =
        cinv ^ 2 * (q.rescaleUnit a⁻¹).quadratic X.2 by
      simp only [z, QuadraticSpace.quadratic_neg,
        (q.rescaleUnit a⁻¹).quadratic_smul]
      ring]
    rw [hrescaledX, hcinvEq]
    simp only [s]
    rw [hcinvEq]
    field_simp [hc0]
  let T := hyperbolicEichlerLatticeIsometry_scaled
    a q L z hzL hzDual s hquadratic hsMem
  have hdet : LinearEquiv.det T.toLinearEquiv = 1 :=
    det_hyperbolicEichlerLatticeIsometry_scaled
      a q L z hzL hzDual s hquadratic hsMem
  let rotation : IntegralRotation (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) := ⟨T, hdet⟩
  refine {
    rotation := rotation
    spinorNorm_eq_one := ?_
    fixes_first := ?_
    image_first_eq := ?_ }
  · exact integralSpinorNorm_hyperbolicEichlerLatticeIsometry_scaled
      (q := q) (L := L) a z hzL hzDual s hquadratic hsMem
  · apply Prod.ext
    · funext i
      fin_cases i
      · have h := hyperbolicEichlerLatticeIsometry_scaled_apply_first_zero
          (q := q) (L := L) a z hzL hzDual s hquadratic hsMem
          (omearaHyperbolicFirst (K := K), (0 : V))
        simpa [rotation, IntegralRotation.apply,
          T, omearaHyperbolicFirst] using h
      · have h := hyperbolicEichlerLatticeIsometry_scaled_apply_first_one
          (q := q) (L := L) a z hzL hzDual s hquadratic hsMem
          (omearaHyperbolicFirst (K := K), (0 : V))
        simpa [rotation, IntegralRotation.apply,
          T, omearaHyperbolicFirst] using h
    · have h := hyperbolicEichlerLatticeIsometry_scaled_apply_second
        (q := q) (L := L) a z hzL hzDual s hquadratic hsMem
        (omearaHyperbolicFirst (K := K), (0 : V))
      simpa [rotation, IntegralRotation.apply,
        T, omearaHyperbolicFirst] using h
  · change T.toLinearEquiv X = (c • omearaHyperbolicSecond (K := K), 0)
    apply Prod.ext
    · funext i
      fin_cases i
      · have hcoord := hyperbolicEichlerLatticeIsometry_scaled_apply_first_zero
          (q := q) (L := L) a z hzL hzDual s hquadratic hsMem X
        change (T.toLinearEquiv X).1 0 =
          (c • omearaHyperbolicSecond (K := K)) 0
        rw [show (T.toLinearEquiv X).1 0 =
            X.1 0 - s * X.1 1 -
              (q.rescaleUnit a⁻¹).bilin X.2 z by
          simpa only [T] using hcoord]
        simp only [omearaHyperbolicSecond, Matrix.cons_val_zero,
          Pi.smul_apply, smul_eq_mul, mul_zero]
        have hbilinSelf : (q.rescaleUnit a⁻¹).bilin X.2 X.2 =
            (q.rescaleUnit a⁻¹).quadratic X.2 := rfl
        rw [show (q.rescaleUnit a⁻¹).bilin X.2 z =
            -cinv * (q.rescaleUnit a⁻¹).quadratic X.2 by
          simp only [z, map_neg, map_smul, hbilinSelf]
          ring]
        rw [hrescaledX]
        simp only [s, hcinvEq, omearaHyperbolicSecond,
          Matrix.cons_val_zero, smul_eq_mul, mul_zero]
        field_simp [hc0]
        ring
      · have hcoord := hyperbolicEichlerLatticeIsometry_scaled_apply_first_one
          (q := q) (L := L) a z hzL hzDual s hquadratic hsMem X
        change (T.toLinearEquiv X).1 1 =
          (c • omearaHyperbolicSecond (K := K)) 1
        rw [show (T.toLinearEquiv X).1 1 = X.1 1 by
          simpa only [T] using hcoord]
        simp [c, omearaHyperbolicSecond]
    · have hcoord := hyperbolicEichlerLatticeIsometry_scaled_apply_second
        (q := q) (L := L) a z hzL hzDual s hquadratic hsMem X
      rw [hcoord]
      change X.2 + c • ((-cinv) • X.2) = 0
      rw [smul_smul, hcinvEq]
      have hcoeff : c * -c⁻¹ = (-1 : K) := by
        field_simp [hc0]
      rw [hcoeff]
      simp

/-! ## Stabilizing the displayed hyperbolic plane in the unit-cross case -/

/-- Swapping the two coordinates is an integral isometry for every common
scale of the hyperbolic form. -/
noncomputable def scaledHyperbolicProductSwap (a : Kˣ) :
    IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) where
  toLinearEquiv :=
    (omearaHyperbolicSwapLinearEquiv (K := K)).prodCongr
      (LinearEquiv.refl K V)
  map_bilin x y := by
    simp only [LinearEquiv.prodCongr_apply,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
      omearaHyperbolicSwapLinearEquiv_zero,
      omearaHyperbolicSwapLinearEquiv_one,
      LinearEquiv.refl_apply]
    ring
  map_mem x := by
    rw [mem_product_iff, mem_product_iff]
    simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    exact and_congr and_comm Iff.rfl

@[simp]
theorem scaledHyperbolicProductSwap_apply (a : Kˣ)
    (x : (Fin 2 → K) × V) :
    (scaledHyperbolicProductSwap (q := q) (L := L) a).toLinearEquiv x =
      (![x.1 1, x.1 0], x.2) :=
  rfl

@[simp]
theorem scaledHyperbolicProductSwap_sq (a : Kˣ) :
    scaledHyperbolicProductSwap (q := q) (L := L) a *
        scaledHyperbolicProductSwap (q := q) (L := L) a = 1 := by
  apply Isometry.ext
  intro x
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

/-- An ambient spinor-one rotation after which the image of the displayed
hyperbolic plane is again the displayed hyperbolic plane. -/
structure HyperbolicSummandTransport (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)) where
  rotation : IntegralRotation (ScaledHyperbolicSum (q := q) a)
    (ScaledHyperbolicProduct (K := K) L)
  spinorNorm_eq_one : rotation.spinorNorm = 1
  first_complement_eq_zero :
    (rotation.apply
      (f.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V)))).2 = 0
  second_complement_eq_zero :
    (rotation.apply
      (f.toLinearEquiv
        (omearaHyperbolicSecond (K := K), (0 : V)))).2 = 0

/-- Two Eichler reductions stabilize the moving hyperbolic summand whenever
the first moving isotropic vector has a unit second coordinate. -/
noncomputable def hyperbolicSummandTransport_of_firstSecondUnit
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L))
    (hunit : IsValuationUnit K
      ((f.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 1)) :
    HyperbolicSummandTransport a f := by
  let D₁ := unitSecondEichlerReduction (q := q) (L := L) a f hunit
  let T₁ := D₁.rotation
  let g : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) :=
    T₁.toIntegralOrthogonalGroup * f
  let E : Fin 2 → K := omearaHyperbolicFirst (K := K)
  let F : Fin 2 → K := omearaHyperbolicSecond (K := K)
  let c : K := (f.toLinearEquiv (E, (0 : V))).1 1
  have hc : IsValuationUnit K c := by simpa [c, E] using hunit
  have hc0 : c ≠ 0 := ne_zero_of_isValuationUnit hc
  have hgE : g.toLinearEquiv (E, (0 : V)) = (c • F, 0) := by
    change T₁.apply (f.toLinearEquiv (E, (0 : V))) = (c • F, 0)
    simpa [T₁, D₁, c, E, F] using D₁.image_first_eq
  have hpair := g.map_bilin (E, (0 : V)) (F, (0 : V))
  have hpair' : c * (g.toLinearEquiv (F, (0 : V))).1 0 = 1 := by
    rw [hgE] at hpair
    simp only [ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply] at hpair
    simp [E, F, omearaHyperbolicFirst,
      omearaHyperbolicSecond] at hpair
    have ha0 : (a : K) ≠ 0 := Units.ne_zero a
    apply mul_left_cancel₀ ha0
    simpa [F, omearaHyperbolicSecond, mul_assoc] using hpair
  have hgFzero : (g.toLinearEquiv (F, (0 : V))).1 0 = c⁻¹ := by
    apply mul_left_cancel₀ hc0
    rw [hpair']
    field_simp [hc0]
  have hgFzeroUnit : IsValuationUnit K
      ((g.toLinearEquiv (F, (0 : V))).1 0) := by
    rw [hgFzero, IsValuationUnit, AddValuation.map_inv, hc]
    exact neg_zero
  let W := scaledHyperbolicProductSwap (q := q) (L := L) a
  let g' : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) := W * g * W
  have hg'Unit : IsValuationUnit K
      ((g'.toLinearEquiv (E, (0 : V))).1 1) := by
    simpa [g', W, E, F, omearaHyperbolicFirst,
      omearaHyperbolicSecond] using hgFzeroUnit
  let D₂ := unitSecondEichlerReduction (q := q) (L := L) a g' hg'Unit
  let T₂ := D₂.rotation
  let C₂ := T₂.conjugateAutomorphism W
  let R : IntegralRotation (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) := C₂ * T₁
  have hC₂spinor : C₂.spinorNorm = 1 := by
    exact (T₂.spinorNorm_conjugateAutomorphism W).trans D₂.spinorNorm_eq_one
  have hRspinor : R.spinorNorm = 1 := by
    rw [show R.spinorNorm = C₂.spinorNorm * T₁.spinorNorm by
      exact IntegralRotation.spinorNorm_mul C₂ T₁]
    rw [hC₂spinor, D₁.spinorNorm_eq_one, one_mul]
  refine {
    rotation := R
    spinorNorm_eq_one := hRspinor
    first_complement_eq_zero := ?_
    second_complement_eq_zero := ?_ }
  · have hT₁E : T₁.apply (f.toLinearEquiv (E, (0 : V))) =
        (c • F, 0) := hgE
    change (C₂.apply
      (T₁.apply (f.toLinearEquiv (E, (0 : V))))).2 = 0
    rw [hT₁E]
    change
      (W.toLinearEquiv
        (T₂.apply (W.toLinearEquiv (c • F, (0 : V))))).2 = 0
    have hWcF : W.toLinearEquiv (c • F, (0 : V)) =
        (c • E, 0) := by
      apply Prod.ext
      · funext i
        fin_cases i <;> simp [W, E, F, omearaHyperbolicFirst,
          omearaHyperbolicSecond]
      · rfl
    rw [hWcF]
    have hT₂cE : T₂.apply (c • E, (0 : V)) = (c • E, 0) := by
      rw [show (c • E, (0 : V)) = c • (E, (0 : V)) by simp]
      change T₂.toIntegralOrthogonalGroup.toLinearEquiv
          (c • (E, (0 : V))) = _
      rw [map_smul]
      have hfix : T₂.toIntegralOrthogonalGroup.toLinearEquiv
          (E, (0 : V)) = (E, 0) := by
        change T₂.apply (E, (0 : V)) = (E, 0)
        simpa [T₂, D₂, E] using D₂.fixes_first
      rw [hfix]
    rw [hT₂cE]
    rfl
  · have hg'Image : g'.toLinearEquiv (E, (0 : V)) =
        W.toLinearEquiv (g.toLinearEquiv (F, (0 : V))) := by
      simp [g', W, E, F, omearaHyperbolicFirst,
        omearaHyperbolicSecond]
    have hD₂ := D₂.image_first_eq
    have hT₂WgF : T₂.apply
        (W.toLinearEquiv (g.toLinearEquiv (F, (0 : V)))) =
        (((g'.toLinearEquiv (E, (0 : V))).1 1) • F, 0) := by
      rw [← hg'Image]
      simpa [T₂, D₂, E, F] using hD₂
    change (C₂.apply
      (T₁.apply (f.toLinearEquiv (F, (0 : V))))).2 = 0
    change (W.toLinearEquiv
      (T₂.apply (W.toLinearEquiv
        (g.toLinearEquiv (F, (0 : V)))))).2 = 0
    rw [hT₂WgF]
    rfl

/-- Target-coordinate-swapped form of the unit-cross reduction. -/
noncomputable def hyperbolicSummandTransport_of_firstZeroUnit
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L))
    (hunit : IsValuationUnit K
      ((f.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 0)) :
    HyperbolicSummandTransport a f := by
  let W := scaledHyperbolicProductSwap (q := q) (L := L) a
  let f' : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) := W * f
  have hunit' : IsValuationUnit K
      ((f'.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 1) := by
    simpa [f', W, omearaHyperbolicFirst] using hunit
  let D := hyperbolicSummandTransport_of_firstSecondUnit
    (q := q) (L := L) a f' hunit'
  let R := D.rotation.conjugateAutomorphism W
  refine {
    rotation := R
    spinorNorm_eq_one :=
      (D.rotation.spinorNorm_conjugateAutomorphism W).trans
        D.spinorNorm_eq_one
    first_complement_eq_zero := ?_
    second_complement_eq_zero := ?_ }
  · change
      (W.toLinearEquiv
        (D.rotation.apply
          (W.toLinearEquiv
            (f.toLinearEquiv
              (omearaHyperbolicFirst (K := K), (0 : V)))))).2 = 0
    change
      (D.rotation.apply
        (W.toLinearEquiv
          (f.toLinearEquiv
            (omearaHyperbolicFirst (K := K), (0 : V))))).2 = 0
    simpa [f', W] using D.first_complement_eq_zero
  · change
      (W.toLinearEquiv
        (D.rotation.apply
          (W.toLinearEquiv
            (f.toLinearEquiv
              (omearaHyperbolicSecond (K := K), (0 : V)))))).2 = 0
    change
      (D.rotation.apply
        (W.toLinearEquiv
          (f.toLinearEquiv
            (omearaHyperbolicSecond (K := K), (0 : V))))).2 = 0
    simpa [f', W] using D.second_complement_eq_zero

/-- Source-basis-swapped form: a unit second coordinate on the second
moving isotropic vector. -/
noncomputable def hyperbolicSummandTransport_of_secondSecondUnit
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L))
    (hunit : IsValuationUnit K
      ((f.toLinearEquiv
        (omearaHyperbolicSecond (K := K), (0 : V))).1 1)) :
    HyperbolicSummandTransport a f := by
  let W := scaledHyperbolicProductSwap (q := q) (L := L) a
  let f' : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) := f * W
  have hunit' : IsValuationUnit K
      ((f'.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 1) := by
    simpa [f', W, omearaHyperbolicFirst,
      omearaHyperbolicSecond] using hunit
  let D := hyperbolicSummandTransport_of_firstSecondUnit
    (q := q) (L := L) a f' hunit'
  refine {
    rotation := D.rotation
    spinorNorm_eq_one := D.spinorNorm_eq_one
    first_complement_eq_zero := ?_
    second_complement_eq_zero := ?_ }
  · simpa [f', W, omearaHyperbolicFirst,
      omearaHyperbolicSecond] using D.second_complement_eq_zero
  · simpa [f', W, omearaHyperbolicFirst,
      omearaHyperbolicSecond] using D.first_complement_eq_zero

/-- Source- and target-swapped form: a unit first coordinate on the second
moving isotropic vector. -/
noncomputable def hyperbolicSummandTransport_of_secondZeroUnit
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L))
    (hunit : IsValuationUnit K
      ((f.toLinearEquiv
        (omearaHyperbolicSecond (K := K), (0 : V))).1 0)) :
    HyperbolicSummandTransport a f := by
  let W := scaledHyperbolicProductSwap (q := q) (L := L) a
  let f' : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) := f * W
  have hunit' : IsValuationUnit K
      ((f'.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 0) := by
    simpa [f', W, omearaHyperbolicFirst,
      omearaHyperbolicSecond] using hunit
  let D := hyperbolicSummandTransport_of_firstZeroUnit
    (q := q) (L := L) a f' hunit'
  refine {
    rotation := D.rotation
    spinorNorm_eq_one := D.spinorNorm_eq_one
    first_complement_eq_zero := ?_
    second_complement_eq_zero := ?_ }
  · simpa [f', W, omearaHyperbolicFirst,
      omearaHyperbolicSecond] using D.second_complement_eq_zero
  · simpa [f', W, omearaHyperbolicFirst,
      omearaHyperbolicSecond] using D.first_complement_eq_zero

/-! ## The all-small cross-pairing branch -/

/-- The Eichler transformation used in the last branch of O'Meara 93:14,
retained together with the unit cross-pairing it creates. -/
structure SmallCrossEichlerReduction (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)) where
  rotation : IntegralRotation (ScaledHyperbolicSum (q := q) a)
    (ScaledHyperbolicProduct (K := K) L)
  spinorNorm_eq_one : rotation.spinorNorm = 1
  transformed_second_second_unit : IsValuationUnit K
    ((f.toLinearEquiv
      (rotation.apply
        (omearaHyperbolicSecond (K := K), (0 : V)))).1 1)

/-- When all four cross-pairings are nonunits, O'Meara's explicit
all-small construction creates a unit cross-pairing with one Eichler
transformation. -/
noncomputable def smallCrossEichlerReduction
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L))
    (hX0 : IsInMaximalIdeal K
      ((f.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 0))
    (hX1 : IsInMaximalIdeal K
      ((f.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 1))
    (hY0 : IsInMaximalIdeal K
      ((f.toLinearEquiv
        (omearaHyperbolicSecond (K := K), (0 : V))).1 0))
    (hY1 : IsInMaximalIdeal K
      ((f.toLinearEquiv
        (omearaHyperbolicSecond (K := K), (0 : V))).1 1)) :
    SmallCrossEichlerReduction a f := by
  let E : Fin 2 → K := omearaHyperbolicFirst (K := K)
  let F : Fin 2 → K := omearaHyperbolicSecond (K := K)
  let P : (Fin 2 → K) × V := f.toLinearEquiv.symm (F, 0)
  let α : K := P.1 0
  let β : K := P.1 1
  let z : V := P.2
  have hfP : f.toLinearEquiv P = (F, (0 : V)) := by
    simpa [P] using f.toLinearEquiv.apply_symm_apply (F, (0 : V))
  have htargetSecond : (F, (0 : V)) ∈
      ScaledHyperbolicProduct (K := K) L := by
    rw [mem_product_iff]
    exact ⟨by simpa [F] using second_mem_hyperbolicPlaneLattice,
      L.zero_mem⟩
  have hPmem : P ∈ ScaledHyperbolicProduct (K := K) L :=
    (f.symm.map_mem (F, (0 : V))).mp htargetSecond
  have hzL : z ∈ L := (mem_product_iff.mp hPmem).2
  have hαEq : α =
      (f.toLinearEquiv (F, (0 : V))).1 0 := by
    have h := f.map_bilin (F, (0 : V)) P
    rw [hfP] at h
    have ha0 : (a : K) ≠ 0 := Units.ne_zero a
    apply mul_left_cancel₀ ha0
    simpa [α, F, ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
      omearaHyperbolicSecond] using h.symm
  have hβEq : β =
      (f.toLinearEquiv (E, (0 : V))).1 0 := by
    have h := f.map_bilin (E, (0 : V)) P
    rw [hfP] at h
    have ha0 : (a : K) ≠ 0 := Units.ne_zero a
    apply mul_left_cancel₀ ha0
    simpa [β, E, F, ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
      omearaHyperbolicFirst, omearaHyperbolicSecond] using h.symm
  have hαMax : IsInMaximalIdeal K α := by rw [hαEq]; exact hY0
  have hβMax : IsInMaximalIdeal K β := by rw [hβEq]; exact hX0
  have hαMem : α ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (le_of_lt hαMax)
  have hβMem : β ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (le_of_lt hβMax)
  have hqz : (q.rescaleUnit a⁻¹).quadratic z = -2 * α * β := by
    have h := f.map_quadratic P
    rw [hfP] at h
    have hraw : 2 * (a : K) * (α * β) + q.quadratic z = 0 := by
      simpa [F, α, β, z, ScaledHyperbolicSum,
        QuadraticSpace.orthogonalSum_quadratic_apply,
        QuadraticSpace.hyperbolicPlane_quadratic_apply,
        omearaHyperbolicSecond] using h.symm
    rw [QuadraticSpace.rescaleUnit_quadratic]
    simp only [Units.val_inv_eq_inv_val]
    have ha0 : (a : K) ≠ 0 := Units.ne_zero a
    field_simp [ha0]
    linear_combination hraw
  have hzDual : z ∈ dualLattice (q.rescaleUnit a⁻¹) L := by
    rw [mem_dualLattice_iff]
    intro v hv
    let fv := f.toLinearEquiv ((0 : Fin 2 → K), v)
    have hsource : ((0 : Fin 2 → K), v) ∈
        ScaledHyperbolicProduct (K := K) L := by
      rw [mem_product_iff]
      exact ⟨by simp, hv⟩
    have hfvMem : fv ∈ ScaledHyperbolicProduct (K := K) L :=
      (f.map_mem _).mp hsource
    have hcoord : fv.1 0 ∈ IntegerRing K :=
      (mem_omearaPlaneLattice_iff fv.1).mp
        (mem_product_iff.mp hfvMem).1 |>.1
    have hbilin := f.map_bilin P ((0 : Fin 2 → K), v)
    rw [hfP] at hbilin
    have heq : q.bilin z v = (a : K) * fv.1 0 := by
      simpa [fv, F, z, ScaledHyperbolicSum,
        QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply,
        omearaHyperbolicSecond] using hbilin.symm
    change ((a⁻¹ : Kˣ) : K) * q.bilin z v ∈ IntegerRing K
    rw [heq]
    simpa [Units.ne_zero a] using hcoord
  let u : K := 1 + β
  have hu : IsValuationUnit K u := by
    simpa [u] using isValuationUnit_one_add_of_isInMaximalIdeal hβMax
  have hu0 : u ≠ 0 := ne_zero_of_isValuationUnit hu
  let uu : Kˣ := Units.mk0 u hu0
  let uinv : K := ((uu⁻¹ : Kˣ) : K)
  have huinv_eq : uinv = u⁻¹ := by simp [uinv, uu]
  have huinv : IsValuationUnit K uinv := by
    simpa [uinv, IsValuationUnit, AddValuation.map_inv, hu]
  have huinvMem : uinv ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 huinv.ge
  let z' : V := uinv • z
  have hz'L : z' ∈ L := L.smul_mem ⟨uinv, huinvMem⟩ hzL
  have hz'Dual : z' ∈ dualLattice (q.rescaleUnit a⁻¹) L :=
    (dualLattice (q.rescaleUnit a⁻¹) L).smul_mem
      ⟨uinv, huinvMem⟩ hzDual
  let s : K := -(α * β * uinv ^ 2)
  have hsMem : s ∈ IntegerRing K := by
    change s ∈ (IntegerRing K).toSubring
    exact (IntegerRing K).toSubring.neg_mem
      ((IntegerRing K).toSubring.mul_mem
        ((IntegerRing K).toSubring.mul_mem hαMem hβMem)
        ((IntegerRing K).toSubring.pow_mem huinvMem 2))
  have hquadratic : (q.rescaleUnit a⁻¹).quadratic z' = 2 * s := by
    rw [show (q.rescaleUnit a⁻¹).quadratic z' =
        uinv ^ 2 * (q.rescaleUnit a⁻¹).quadratic z by
      exact (q.rescaleUnit a⁻¹).quadratic_smul uinv z]
    rw [hqz]
    simp only [s]
    ring
  let T := hyperbolicEichlerLatticeIsometry_scaled
    a q L z' hz'L hz'Dual s hquadratic hsMem
  have hdet : LinearEquiv.det T.toLinearEquiv = 1 :=
    det_hyperbolicEichlerLatticeIsometry_scaled
      a q L z' hz'L hz'Dual s hquadratic hsMem
  let rotation : IntegralRotation (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) := ⟨T, hdet⟩
  let X1 : K := (f.toLinearEquiv (E, (0 : V))).1 1
  let Y1 : K := (f.toLinearEquiv (F, (0 : V))).1 1
  have hPdecomp : P =
      α • (E, (0 : V)) + β • (F, (0 : V)) +
        ((0 : Fin 2 → K), z) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [α, β, E, F, P,
        omearaHyperbolicFirst, omearaHyperbolicSecond]
    · simp [z, P]
  have hfzOne :
      (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1 =
        1 - α * X1 - β * Y1 := by
    have hmap := congrArg f.toLinearEquiv hPdecomp
    rw [hfP, map_add, map_add, map_smul, map_smul] at hmap
    have hcoord := congrArg
      (fun x : (Fin 2 → K) × V => x.1 1) hmap
    change 1 = α * X1 + β * Y1 +
      (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1 at hcoord
    calc
      (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1 =
          (α * X1 + β * Y1 +
            (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1) -
              α * X1 - β * Y1 := by ring
      _ = 1 - α * X1 - β * Y1 := by rw [← hcoord]
  have hTSecond : T.toLinearEquiv (F, (0 : V)) =
      (![-s, 1], z') := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [T, F, omearaHyperbolicSecond]
    · simp [T, F, omearaHyperbolicSecond]
  have hcrossFormula :
      (f.toLinearEquiv (T.toLinearEquiv (F, (0 : V)))).1 1 =
        uinv * (1 + Y1 - α * uinv * X1) := by
    rw [hTSecond]
    have hvector : (![-s, 1], z') =
        (-s) • (E, (0 : V)) + (F, (0 : V)) +
          ((0 : Fin 2 → K), z') := by
      apply Prod.ext
      · funext i
        fin_cases i <;> simp [E, F, omearaHyperbolicFirst,
          omearaHyperbolicSecond]
      · simp
    rw [hvector, map_add, map_add, map_smul]
    have hz'Image : f.toLinearEquiv ((0 : Fin 2 → K), z') =
        uinv • f.toLinearEquiv ((0 : Fin 2 → K), z) := by
      rw [show ((0 : Fin 2 → K), z') =
          uinv • ((0 : Fin 2 → K), z) by simp [z']]
      exact map_smul f.toLinearEquiv uinv _
    rw [hz'Image]
    change -s * X1 + Y1 + uinv *
      (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1 = _
    rw [hfzOne]
    simp only [s, huinv_eq, u]
    have hu0' : 1 + β ≠ 0 := by simpa [u] using hu0
    field_simp [hu0']
    ring
  have hX1Int : Dyadic.IsIntegral K X1 := by
    change 0 ≤ ord K X1
    have hX1' := hX1
    change 0 < ord K
      ((f.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V))).1 1) at hX1'
    exact le_of_lt (by simpa [X1, E] using hX1')
  have huinvInt : Dyadic.IsIntegral K uinv := huinv.ge
  have hαUinvMax : IsInMaximalIdeal K (α * uinv) :=
    isInMaximalIdeal_mul_isIntegral K hαMax huinvInt
  have hαUinvX1Max : IsInMaximalIdeal K (α * uinv * X1) :=
    isInMaximalIdeal_mul_isIntegral K hαUinvMax hX1Int
  have hm : IsInMaximalIdeal K (Y1 - α * uinv * X1) := by
    apply isInMaximalIdeal_sub hY1
    exact hαUinvX1Max
  have hd : IsValuationUnit K (1 + Y1 - α * uinv * X1) := by
    have := isValuationUnit_one_add_of_isInMaximalIdeal hm
    simpa only [add_sub_assoc] using this
  refine {
    rotation := rotation
    spinorNorm_eq_one := ?_
    transformed_second_second_unit := ?_ }
  · exact integralSpinorNorm_hyperbolicEichlerLatticeIsometry_scaled
      (q := q) (L := L) a z' hz'L hz'Dual s hquadratic hsMem
  · change IsValuationUnit K
      ((f.toLinearEquiv (T.toLinearEquiv (F, (0 : V)))).1 1)
    rw [hcrossFormula]
    exact isValuationUnit_mul huinv hd

/-! ## Exhaustive transport theorem -/

/-- Every integral image of a displayed scaled hyperbolic summand can be
returned to the displayed summand by an ambient integral rotation of spinor
norm one.  This is the precise transport statement used in Beli (2003),
Lemma 7.1(ii). -/
noncomputable def hyperbolicSummandTransport
    (a : Kˣ)
    (f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)) :
    HyperbolicSummandTransport a f := by
  let E : Fin 2 → K := omearaHyperbolicFirst (K := K)
  let F : Fin 2 → K := omearaHyperbolicSecond (K := K)
  have hEsource : (E, (0 : V)) ∈ ScaledHyperbolicProduct (K := K) L := by
    rw [mem_product_iff]
    exact ⟨by simpa [E] using first_mem_hyperbolicPlaneLattice,
      L.zero_mem⟩
  have hFsource : (F, (0 : V)) ∈ ScaledHyperbolicProduct (K := K) L := by
    rw [mem_product_iff]
    exact ⟨by simpa [F] using second_mem_hyperbolicPlaneLattice,
      L.zero_mem⟩
  have hXmem : f.toLinearEquiv (E, (0 : V)) ∈
      ScaledHyperbolicProduct (K := K) L :=
    (f.map_mem _).mp hEsource
  have hYmem : f.toLinearEquiv (F, (0 : V)) ∈
      ScaledHyperbolicProduct (K := K) L :=
    (f.map_mem _).mp hFsource
  have hXplane := (mem_product_iff.mp hXmem).1
  have hYplane := (mem_product_iff.mp hYmem).1
  have hX0mem : (f.toLinearEquiv (E, (0 : V))).1 0 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hXplane |>.1
  have hX1mem : (f.toLinearEquiv (E, (0 : V))).1 1 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hXplane |>.2
  have hY0mem : (f.toLinearEquiv (F, (0 : V))).1 0 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hYplane |>.1
  have hY1mem : (f.toLinearEquiv (F, (0 : V))).1 1 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hYplane |>.2
  by_cases hX1 : IsValuationUnit K
      ((f.toLinearEquiv (E, (0 : V))).1 1)
  · exact hyperbolicSummandTransport_of_firstSecondUnit
      (q := q) (L := L) a f hX1
  by_cases hX0 : IsValuationUnit K
      ((f.toLinearEquiv (E, (0 : V))).1 0)
  · exact hyperbolicSummandTransport_of_firstZeroUnit
      (q := q) (L := L) a f hX0
  by_cases hY1 : IsValuationUnit K
      ((f.toLinearEquiv (F, (0 : V))).1 1)
  · exact hyperbolicSummandTransport_of_secondSecondUnit
      (q := q) (L := L) a f hY1
  by_cases hY0 : IsValuationUnit K
      ((f.toLinearEquiv (F, (0 : V))).1 0)
  · exact hyperbolicSummandTransport_of_secondZeroUnit
      (q := q) (L := L) a f hY0
  have hX0max : IsInMaximalIdeal K
      ((f.toLinearEquiv (E, (0 : V))).1 0) :=
    isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit hX0mem hX0
  have hX1max : IsInMaximalIdeal K
      ((f.toLinearEquiv (E, (0 : V))).1 1) :=
    isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit hX1mem hX1
  have hY0max : IsInMaximalIdeal K
      ((f.toLinearEquiv (F, (0 : V))).1 0) :=
    isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit hY0mem hY0
  have hY1max : IsInMaximalIdeal K
      ((f.toLinearEquiv (F, (0 : V))).1 1) :=
    isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit hY1mem hY1
  let D₀ := smallCrossEichlerReduction (q := q) (L := L) a f
    hX0max hX1max hY0max hY1max
  let T₀ := D₀.rotation
  let C₀ := T₀.conjugateAutomorphism f
  let f' : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) :=
    C₀.toIntegralOrthogonalGroup * f
  have hf'F : f'.toLinearEquiv (F, (0 : V)) =
      f.toLinearEquiv (T₀.apply (F, (0 : V))) := by
    change f.toLinearEquiv
        (T₀.toIntegralOrthogonalGroup.toLinearEquiv
          (f.toLinearEquiv.symm
            (f.toLinearEquiv (F, (0 : V))))) = _
    rw [f.toLinearEquiv.symm_apply_apply]
    rfl
  have hf'Unit : IsValuationUnit K
      ((f'.toLinearEquiv (F, (0 : V))).1 1) := by
    rw [hf'F]
    exact D₀.transformed_second_second_unit
  let D₁ := hyperbolicSummandTransport_of_secondSecondUnit
    (q := q) (L := L) a f' hf'Unit
  let R : IntegralRotation (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) := D₁.rotation * C₀
  have hC₀spinor : C₀.spinorNorm = 1 :=
    (T₀.spinorNorm_conjugateAutomorphism f).trans D₀.spinorNorm_eq_one
  refine {
    rotation := R
    spinorNorm_eq_one := ?_
    first_complement_eq_zero := ?_
    second_complement_eq_zero := ?_ }
  · rw [show R.spinorNorm = D₁.rotation.spinorNorm * C₀.spinorNorm by
      exact IntegralRotation.spinorNorm_mul D₁.rotation C₀]
    rw [D₁.spinorNorm_eq_one, hC₀spinor, one_mul]
  · change (D₁.rotation.apply
      (C₀.apply (f.toLinearEquiv (E, (0 : V))))).2 = 0
    simpa [f', E, IntegralRotation.apply] using
      D₁.first_complement_eq_zero
  · change (D₁.rotation.apply
      (C₀.apply (f.toLinearEquiv (F, (0 : V))))).2 = 0
    simpa [f', F, IntegralRotation.apply] using
      D₁.second_complement_eq_zero

/-! ## Block factorization after transport -/

namespace HyperbolicSummandTransport

/-- The transported ambient automorphism. -/
noncomputable def stabilized {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L) :=
  D.rotation.toIntegralOrthogonalGroup * f

/-- The stabilized map carries every vector of the left hyperbolic factor
back into that factor. -/
theorem stabilized_apply_left_second {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) (x : Fin 2 → K) :
    (D.stabilized.toLinearEquiv (x, (0 : V))).2 = 0 := by
  let E : Fin 2 → K := omearaHyperbolicFirst (K := K)
  let F : Fin 2 → K := omearaHyperbolicSecond (K := K)
  have hx : (x, (0 : V)) =
      x 0 • (E, (0 : V)) + x 1 • (F, (0 : V)) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [E, F, omearaHyperbolicFirst,
        omearaHyperbolicSecond]
    · simp
  rw [hx, map_add, map_smul, map_smul]
  change x 0 •
      (D.rotation.apply
        (f.toLinearEquiv
          (omearaHyperbolicFirst (K := K), (0 : V)))).2 +
      x 1 •
      (D.rotation.apply
        (f.toLinearEquiv
          (omearaHyperbolicSecond (K := K), (0 : V)))).2 = 0
  rw [D.first_complement_eq_zero, D.second_complement_eq_zero]
  simp

/-- The field-linear map induced on the hyperbolic factor. -/
noncomputable def leftLinearMap {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun x := (D.stabilized.toLinearEquiv (x, (0 : V))).1
  map_add' x y := by
    have h := D.stabilized.toLinearEquiv.map_add (x, (0 : V)) (y, 0)
    simpa using congrArg Prod.fst h
  map_smul' c x := by
    have h := D.stabilized.toLinearEquiv.map_smul c (x, (0 : V))
    simpa using congrArg Prod.fst h

/-- The left block is injective because the ambient stabilized map is. -/
theorem leftLinearMap_injective {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    Function.Injective D.leftLinearMap := by
  intro x y hxy
  have hp : D.stabilized.toLinearEquiv (x, (0 : V)) =
      D.stabilized.toLinearEquiv (y, (0 : V)) := by
    apply Prod.ext
    · exact hxy
    · rw [D.stabilized_apply_left_second,
        D.stabilized_apply_left_second]
  exact congrArg Prod.fst (D.stabilized.toLinearEquiv.injective hp)

/-- The induced field-linear automorphism of the hyperbolic factor. -/
noncomputable def leftLinearEquiv {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  LinearEquiv.ofInjectiveEndo D.leftLinearMap D.leftLinearMap_injective

@[simp]
theorem leftLinearEquiv_apply {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) (x : Fin 2 → K) :
    D.leftLinearEquiv x =
      (D.stabilized.toLinearEquiv (x, (0 : V))).1 := by
  rfl

/-- Orthogonality forces the stabilized map to carry every vector of the
right factor back into the right factor. -/
theorem stabilized_apply_right_first {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) (x : V) :
    (D.stabilized.toLinearEquiv ((0 : Fin 2 → K), x)).1 = 0 := by
  apply (QuadraticSpace.hyperbolicPlane a).nondegenerate.1
  intro y
  obtain ⟨z, hz⟩ := D.leftLinearEquiv.surjective y
  have hbilin := D.stabilized.map_bilin
    (z, (0 : V)) ((0 : Fin 2 → K), x)
  simp only [ScaledHyperbolicSum,
    QuadraticSpace.orthogonalSum_bilin_apply] at hbilin
  rw [D.stabilized_apply_left_second] at hbilin
  simp at hbilin
  have hz' :
      (D.stabilized.toLinearEquiv (z, (0 : V))).1 = y := by
    rw [← D.leftLinearEquiv_apply]
    exact hz
  rw [hz'] at hbilin
  rw [(QuadraticSpace.hyperbolicPlane a).isSymm.eq]
  exact hbilin

/-- The field-linear map induced on the orthogonal-complement factor. -/
noncomputable def rightLinearMap {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) : V →ₗ[K] V where
  toFun x := (D.stabilized.toLinearEquiv ((0 : Fin 2 → K), x)).2
  map_add' x y := by
    have h := D.stabilized.toLinearEquiv.map_add
      ((0 : Fin 2 → K), x) (0, y)
    simpa using congrArg Prod.snd h
  map_smul' c x := by
    have h := D.stabilized.toLinearEquiv.map_smul c
      ((0 : Fin 2 → K), x)
    simpa using congrArg Prod.snd h

/-- The right block is injective because the ambient stabilized map is. -/
theorem rightLinearMap_injective {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    Function.Injective D.rightLinearMap := by
  intro x y hxy
  have hp : D.stabilized.toLinearEquiv ((0 : Fin 2 → K), x) =
      D.stabilized.toLinearEquiv ((0 : Fin 2 → K), y) := by
    apply Prod.ext
    · rw [D.stabilized_apply_right_first,
        D.stabilized_apply_right_first]
    · exact hxy
  exact congrArg Prod.snd (D.stabilized.toLinearEquiv.injective hp)

/-- The induced field-linear automorphism of the complement factor. -/
noncomputable def rightLinearEquiv {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) : V ≃ₗ[K] V :=
  letI : Module.Finite K V := L.moduleFinite
  LinearEquiv.ofInjectiveEndo D.rightLinearMap D.rightLinearMap_injective

@[simp]
theorem rightLinearEquiv_apply {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) (x : V) :
    D.rightLinearEquiv x =
      (D.stabilized.toLinearEquiv ((0 : Fin 2 → K), x)).2 := by
  letI : Module.Finite K V := L.moduleFinite
  change (LinearEquiv.ofInjectiveEndo D.rightLinearMap
      D.rightLinearMap_injective) x = _
  exact congrFun
    (LinearEquiv.coe_ofInjectiveEndo D.rightLinearMap
      D.rightLinearMap_injective) x

/-- The restriction of the stabilized automorphism to the hyperbolic
summand, bundled as an integral lattice automorphism. -/
noncomputable def leftIsometry {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    IntegralOrthogonalGroup (QuadraticSpace.hyperbolicPlane a)
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := D.leftLinearEquiv
  map_bilin x y := by
    have h := D.stabilized.map_bilin (x, (0 : V)) (y, (0 : V))
    simpa [ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_bilin_apply,
      D.leftLinearEquiv_apply,
      D.stabilized_apply_left_second] using h
  map_mem x := by
    have h := D.stabilized.map_mem (x, (0 : V))
    rw [mem_product_iff, mem_product_iff] at h
    simpa [D.leftLinearEquiv_apply,
      D.stabilized_apply_left_second] using h

/-- The restriction of the stabilized automorphism to the orthogonal
complement, bundled as an integral lattice automorphism. -/
noncomputable def rightIsometry {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) : IntegralOrthogonalGroup q L where
  toLinearEquiv := D.rightLinearEquiv
  map_bilin x y := by
    have h := D.stabilized.map_bilin
      ((0 : Fin 2 → K), x) ((0 : Fin 2 → K), y)
    simpa [ScaledHyperbolicSum,
      QuadraticSpace.orthogonalSum_bilin_apply,
      D.rightLinearEquiv_apply,
      D.stabilized_apply_right_first] using h
  map_mem x := by
    have h := D.stabilized.map_mem ((0 : Fin 2 → K), x)
    rw [mem_product_iff, mem_product_iff] at h
    simpa [D.rightLinearEquiv_apply,
      D.stabilized_apply_right_first] using h

/-- After transport, the ambient automorphism is exactly the orthogonal
product of its two restrictions. -/
theorem stabilized_eq_orthogonalProduct {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    D.stabilized = D.leftIsometry.orthogonalProductBasic D.rightIsometry := by
  apply Isometry.ext
  intro x
  rw [Isometry.orthogonalProductBasic_apply]
  change D.stabilized.toLinearEquiv x =
    (D.leftLinearEquiv x.1, D.rightLinearEquiv x.2)
  calc
    D.stabilized.toLinearEquiv x =
        D.stabilized.toLinearEquiv (x.1, (0 : V)) +
          D.stabilized.toLinearEquiv ((0 : Fin 2 → K), x.2) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    _ = (D.leftLinearEquiv x.1, D.rightLinearEquiv x.2) := by
      apply Prod.ext
      · simp only [Prod.fst_add, D.stabilized_apply_right_first,
          add_zero, D.leftLinearEquiv_apply]
      · simp only [Prod.snd_add, D.stabilized_apply_left_second,
          zero_add, D.rightLinearEquiv_apply]

/-- The spinor-one transport does not alter the determinant of the original
ambient automorphism. -/
theorem stabilized_det_eq {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    LinearEquiv.det D.stabilized.toLinearEquiv =
      LinearEquiv.det f.toLinearEquiv := by
  letI : Module.Finite K V := L.moduleFinite
  change LinearEquiv.det
      (f.toLinearEquiv.trans
        D.rotation.toIntegralOrthogonalGroup.toLinearEquiv) = _
  rw [LinearEquiv.det_trans, D.rotation.det_eq_one, one_mul]

/-- The spinor-one transport does not alter the spinor norm of the original
ambient automorphism. -/
theorem stabilized_spinorNorm_eq {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    integralSpinorNorm D.stabilized = integralSpinorNorm f := by
  change integralSpinorNorm
      (D.rotation.toIntegralOrthogonalGroup * f) = _
  rw [integralSpinorNorm_mul]
  change D.rotation.spinorNorm * integralSpinorNorm f =
    integralSpinorNorm f
  rw [D.spinorNorm_eq_one, one_mul]

/-- Determinant factorization of the stabilized automorphism. -/
theorem det_left_mul_right {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    LinearEquiv.det D.stabilized.toLinearEquiv =
      LinearEquiv.det D.leftIsometry.toLinearEquiv *
        LinearEquiv.det D.rightIsometry.toLinearEquiv := by
  rw [D.stabilized_eq_orthogonalProduct,
    Isometry.det_orthogonalProductBasic]

/-- Spinor-norm factorization of the stabilized automorphism. -/
theorem spinorNorm_left_mul_right {a : Kˣ}
    {f : IntegralOrthogonalGroup (ScaledHyperbolicSum (q := q) a)
      (ScaledHyperbolicProduct (K := K) L)}
    (D : HyperbolicSummandTransport a f) :
    integralSpinorNorm D.stabilized =
      integralSpinorNorm D.leftIsometry *
        integralSpinorNorm D.rightIsometry := by
  rw [D.stabilized_eq_orthogonalProduct,
    integralSpinorNorm_orthogonalProductBasic]

end HyperbolicSummandTransport

end Lattice

end Bong
