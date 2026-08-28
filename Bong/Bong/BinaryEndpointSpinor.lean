/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryHyperbolicEndpoint
import Bong.Bong.BinaryPrimitiveCoordinates
import Bong.Bong.BeliLemma71
import Bong.Lattice.HyperbolicDiagonalSpinor

/-!
# Spinor norms at the hyperbolic binary endpoint

This file proves the exceptional clause in Beli (2003), Definition 4:
the proper spinor-norm image of the endpoint `a = -1/4` is the subgroup of
unit square classes.  The calculation is made on the fixed scaled
hyperbolic plane and then transported to an arbitrary binary BONG.
-/

namespace Bong

open Dyadic

universe u v

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The vector `(1,1)` defines an integral reflection of every scaled
hyperbolic plane on the standard lattice. -/
theorem hyperbolicOneOne_isIntegralReflection (s : Kˣ) :
    IsIntegralReflection
      (q := QuadraticSpace.hyperbolicPlane s)
      (L := hyperbolicPlaneLattice (K := K))
      (x := (![1, 1] : Fin 2 → K))
      (by
        rw [QuadraticSpace.IsAnisotropic,
          QuadraticSpace.hyperbolicPlane_quadratic_apply]
        norm_num [Units.ne_zero]) := by
  let x : Fin 2 → K := ![1, 1]
  have hx : (QuadraticSpace.hyperbolicPlane s).IsAnisotropic x := by
    rw [QuadraticSpace.IsAnisotropic,
      QuadraticSpace.hyperbolicPlane_quadratic_apply]
    norm_num [x, Units.ne_zero]
  change IsIntegralReflection
    (q := QuadraticSpace.hyperbolicPlane s)
    (L := hyperbolicPlaneLattice (K := K)) hx
  apply isIntegralReflection_of_coefficient_mem_integerRing hx
  · rw [mem_omearaPlaneLattice_iff]
    simp [x]
  · intro y hy
    have hyCoords := (mem_omearaPlaneLattice_iff y).1 hy
    have hcoefficient :
        2 * (QuadraticSpace.hyperbolicPlane s).bilin x y /
            (QuadraticSpace.hyperbolicPlane s).quadratic x =
          y 0 + y 1 := by
      rw [QuadraticSpace.hyperbolicPlane_bilin_apply,
        QuadraticSpace.hyperbolicPlane_quadratic_apply]
      simp [x]
      field_simp [Units.ne_zero s]
      ring
    rw [hcoefficient]
    exact (IntegerRing K).add_mem _ _ hyCoords.1 hyCoords.2

/-- A primitive integral-reflection vector in the standard hyperbolic
lattice has two valuation-unit coordinates. -/
theorem hyperbolic_primitive_integralReflection_coordinates_units
    (s : Kˣ) {y : Fin 2 → K}
    (hy : (QuadraticSpace.hyperbolicPlane s).IsAnisotropic y)
    (hyMem : y ∈ hyperbolicPlaneLattice (K := K))
    (hyPrimitive : y ∉ rescale (uniformizerUnit K)
      (hyperbolicPlaneLattice (K := K)))
    (hyIntegral : IsIntegralReflection
      (q := QuadraticSpace.hyperbolicPlane s)
      (L := hyperbolicPlaneLattice (K := K)) hy) :
    IsValuationUnit K (y 0) ∧ IsValuationUnit K (y 1) := by
  let e0 : Fin 2 → K := ![1, 0]
  let e1 : Fin 2 → K := ![0, 1]
  have hy0 : y 0 ≠ 0 := by
    intro hzero
    apply hy
    rw [QuadraticSpace.hyperbolicPlane_quadratic_apply, hzero]
    simp
  have hy1 : y 1 ≠ 0 := by
    intro hone
    apply hy
    rw [QuadraticSpace.hyperbolicPlane_quadratic_apply, hone]
    simp
  have he0Mem : e0 ∈ hyperbolicPlaneLattice (K := K) := by
    rw [mem_omearaPlaneLattice_iff]
    simp [e0]
  have he1Mem : e1 ∈ hyperbolicPlaneLattice (K := K) := by
    rw [mem_omearaPlaneLattice_iff]
    simp [e1]
  have href0 := hyIntegral e0 he0Mem
  have href1 := hyIntegral e1 he1Mem
  have href0Coords := (mem_omearaPlaneLattice_iff _).1 href0
  have href1Coords := (mem_omearaPlaneLattice_iff _).1 href1
  have hratio10neg : -(y 1 / y 0) ∈ IntegerRing K := by
    have h := href0Coords.2
    have hreflection :
        ((QuadraticSpace.hyperbolicPlane s).reflectionLinearEquiv
          y hy e0) 1 = -(y 1 / y 0) := by
      rw [QuadraticSpace.reflectionLinearEquiv_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply,
        QuadraticSpace.hyperbolicPlane_quadratic_apply]
      simp [e0]
      field_simp [hy0, hy1, Units.ne_zero s]
    rwa [hreflection] at h
  have hratio01neg : -(y 0 / y 1) ∈ IntegerRing K := by
    have h := href1Coords.1
    have hreflection :
        ((QuadraticSpace.hyperbolicPlane s).reflectionLinearEquiv
          y hy e1) 0 = -(y 0 / y 1) := by
      rw [QuadraticSpace.reflectionLinearEquiv_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply,
        QuadraticSpace.hyperbolicPlane_quadratic_apply]
      simp [e1]
      field_simp [hy0, hy1, Units.ne_zero s]
    rwa [hreflection] at h
  have hratio10 : y 1 / y 0 ∈ IntegerRing K := by
    have h := (IntegerRing K).neg_mem (-(y 1 / y 0)) hratio10neg
    simpa using h
  have hratio01 : y 0 / y 1 ∈ IntegerRing K := by
    have h := (IntegerRing K).neg_mem (-(y 0 / y 1)) hratio01neg
    simpa using h
  let y0 : Kˣ := Units.mk0 (y 0) hy0
  let y1 : Kˣ := Units.mk0 (y 1) hy1
  let r10 : Kˣ := y1 * y0⁻¹
  let r01 : Kˣ := y0 * y1⁻¹
  have hr10Mem : (r10 : K) ∈ IntegerRing K := by
    simpa [r10, y0, y1, div_eq_mul_inv] using hratio10
  have hr01Mem : (r01 : K) ∈ IntegerRing K := by
    simpa [r01, y0, y1, div_eq_mul_inv] using hratio01
  have hr10Nonneg : 0 ≤ ordUnit K r10 :=
    ordUnit_nonneg_of_mem_integerRing r10 hr10Mem
  have hr01Nonneg : 0 ≤ ordUnit K r01 :=
    ordUnit_nonneg_of_mem_integerRing r01 hr01Mem
  have horders : ordUnit K y0 = ordUnit K y1 := by
    simp only [r10, ordUnit_mul, ordUnit_inv] at hr10Nonneg
    simp only [r01, ordUnit_mul, ordUnit_inv] at hr01Nonneg
    omega
  have hyMem' : y ∈ BONG.binaryModelLattice (K := K) := by
    simpa [BONG.binaryModelLattice, BONG.binaryModelBasis,
      hyperbolicPlaneLattice] using hyMem
  have hyPrimitive' : y ∉ rescale (uniformizerUnit K)
      (BONG.binaryModelLattice (K := K)) := by
    simpa [BONG.binaryModelLattice, BONG.binaryModelBasis,
      hyperbolicPlaneLattice] using hyPrimitive
  have hcoordinateUnit :=
    (BONG.primitive_binaryModelLattice_iff_coordinate_unit y hyMem').1
      hyPrimitive'
  rcases hcoordinateUnit with hzeroUnit | honeUnit
  · have hzeroOrder : ordUnit K y0 = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K y0).1
        (by simpa [y0] using hzeroUnit)
    have honeOrder : ordUnit K y1 = 0 := by omega
    exact ⟨by
      simpa [y0] using
        (isValuationUnit_iff_ordUnit_eq_zero K y0).2 hzeroOrder,
      by
        simpa [y1] using
          (isValuationUnit_iff_ordUnit_eq_zero K y1).2 honeOrder⟩
  · have honeOrder : ordUnit K y1 = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K y1).1
        (by simpa [y1] using honeUnit)
    have hzeroOrder : ordUnit K y0 = 0 := by omega
    exact ⟨by
      simpa [y0] using
        (isValuationUnit_iff_ordUnit_eq_zero K y0).2 hzeroOrder,
      by
        simpa [y1] using
          (isValuationUnit_iff_ordUnit_eq_zero K y1).2 honeOrder⟩

/-- Hsia's hyperbolic calculation: the proper spinor image of a scaled
hyperbolic plane is exactly the subgroup of unit square classes. -/
theorem spinorNormImage_hyperbolicPlane_eq_valuationUnitSquareClassSubgroup
    (s : Kˣ) :
    spinorNormImage
        (q := QuadraticSpace.hyperbolicPlane s)
        (L := hyperbolicPlaneLattice (K := K)) =
      valuationUnitSquareClassSubgroup K := by
  let q := QuadraticSpace.hyperbolicPlane s
  let L := hyperbolicPlaneLattice (K := K)
  let x : Fin 2 → K := ![1, 1]
  have hx : q.IsAnisotropic x := by
    rw [QuadraticSpace.IsAnisotropic,
      QuadraticSpace.hyperbolicPlane_quadratic_apply]
    norm_num [q, x, Units.ne_zero]
  have hxIntegral : IsIntegralReflection (q := q) (L := L) hx := by
    simpa [q, L, x] using hyperbolicOneOne_isIntegralReflection s
  ext A
  constructor
  · intro hA
    rw [spinorNormImage_eq_fixed_mul_primitiveReflectionClasses
      (q := q) (L := L) (by simp) hx hxIntegral] at hA
    rcases hA with
      ⟨y, hy, hyMem, hyPrimitive, hyIntegral, hclass⟩
    have hyUnits :
        IsValuationUnit K (y 0) ∧ IsValuationUnit K (y 1) :=
      hyperbolic_primitive_integralReflection_coordinates_units
        s (y := y) hy (by simpa [L] using hyMem)
          (by simpa [L] using hyPrimitive)
          (by simpa [q, L] using hyIntegral)
    have hy0 : y 0 ≠ 0 := by
      intro hzero
      apply hy
      rw [QuadraticSpace.hyperbolicPlane_quadratic_apply, hzero]
      simp
    have hy1 : y 1 ≠ 0 := by
      intro hone
      apply hy
      rw [QuadraticSpace.hyperbolicPlane_quadratic_apply, hone]
      simp
    let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
    let y0 : Kˣ := Units.mk0 (y 0) hy0
    let y1 : Kˣ := Units.mk0 (y 1) hy1
    let qx : Kˣ := Units.mk0 (q.quadratic x) hx
    let qy : Kˣ := Units.mk0 (q.quadratic y) hy
    have hqx : qx = two * s := by
      apply Units.ext
      simp [qx, q, x, two,
        QuadraticSpace.hyperbolicPlane_quadratic_apply]
    have hqy : qy = two * s * y0 * y1 := by
      apply Units.ext
      simp [qy, q, two, y0, y1,
        QuadraticSpace.hyperbolicPlane_quadratic_apply]
      ring
    have htwoOrder :
        ordUnit K two = (ramificationIndex K : Int) := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, ramificationIndex_spec]
      rfl
    have hy0Order : ordUnit K y0 = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K y0).1
        (by simpa [y0] using hyUnits.1)
    have hy1Order : ordUnit K y1 = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K y1).1
        (by simpa [y1] using hyUnits.2)
    have heven : Even (ordUnit K (qx * qy)) := by
      refine ⟨ordUnit K two + ordUnit K s, ?_⟩
      rw [ordUnit_mul, hqx, hqy]
      simp only [ordUnit_mul, hy0Order, hy1Order, add_zero]
    have hmem : squareClass K (qx * qy) ∈
        valuationUnitSquareClassSubgroup K :=
      (squareClass_mem_valuationUnitSquareClassSubgroup_iff_even
        (K := K) (qx * qy)).2 heven
    have hproduct :
        reflectionSpinorClass (q := q) hx *
            reflectionSpinorClass (q := q) hy ∈
          valuationUnitSquareClassSubgroup K := by
      simpa [reflectionSpinorClass, qx, qy] using hmem
    rw [hclass] at hproduct
    exact hproduct
  · intro hA
    rcases hA with ⟨t, ht, hclass⟩
    let g : IntegralRotation q L :=
      { toIntegralOrthogonalGroup :=
          scaledHyperbolicDiagonalLatticeIsometry s t ht
        det_eq_one := det_hyperbolicDiagonalLinearEquiv t }
    refine ⟨g, ?_⟩
    change integralSpinorNorm
      (scaledHyperbolicDiagonalLatticeIsometry s t ht) = A
    rw [integralSpinorNorm_scaledHyperbolicDiagonalLatticeIsometry]
    exact hclass

end Lattice

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The exceptional `-1/4` branch of Beli (2003), Lemma 3.7, without a
binary local-law hypothesis. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_of_negativeQuarter
    (b : BONG V q L 2)
    (hclass : b.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K)) :
    Lattice.spinorNormImage (q := q) (L := L) =
      beliSpinorGroupRepresentative K b.binaryParameter := by
  have hparameterClass : unitSquareClass K b.binaryParameter =
      unitSquareClass K (negativeQuarterUnit K) := hclass
  have hformula := beliSpinorGroupRepresentative_of_negativeQuarter
    K b.binaryParameter b.binaryParameter_isBinaryParameterAdmissible
      hparameterClass
  rcases b.isIsometric_hyperbolicPlane_of_binaryUnitSquareClass_eq_negativeQuarter
      hclass with ⟨e⟩
  calc
    Lattice.spinorNormImage (q := q) (L := L) =
        Lattice.spinorNormImage
          (q := QuadraticSpace.hyperbolicPlane
            (uniformizerPowerUnit K
              (b.order 0 - ramificationIndex K)))
          (L := Lattice.hyperbolicPlaneLattice (K := K)) :=
      Lattice.spinorNormImage_eq_of_isometry e
    _ = valuationUnitSquareClassSubgroup K :=
      Lattice.spinorNormImage_hyperbolicPlane_eq_valuationUnitSquareClassSubgroup
        (uniformizerPowerUnit K
          (b.order 0 - ramificationIndex K))
    _ = beliSpinorGroupRepresentative K b.binaryParameter := by
      exact congrArg
        (fun H : Subgroup (SquareClass K) => (H : Set (SquareClass K)))
        hformula.symm

end BONG

end Bong
