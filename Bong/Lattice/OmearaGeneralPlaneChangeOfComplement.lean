/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.MinimalScaleComponent
import Bong.Lattice.ModularIsometry
import Bong.Lattice.ModularOrthogonalProduct
import Bong.Lattice.OmearaGeneralPlane
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.OrthogonalDecompositionVolume
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Changing the complement of a general O'Meara plane

This is the splitting step used in O'Meara 93:18(ii).  Inside
`A(alpha,beta) ⊥ M`, replace the first displayed vector by its sum with a
vector `z ∈ M`.  The resulting binary plane has Gram matrix
`A(alpha + Q(z), beta)`.  When its determinant is a valuation unit, the new
plane is an integral unimodular sublattice and O'Meara 82:15a supplies a new
orthogonal complement.

Unlike 93:12, the new complement is not asserted to be isometric to the old
one when `beta` is nonzero.  This distinction is essential in the proof of
93:18(ii), where the complement is denoted `K'`.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type v} [AddCommGroup W] [Module K W]

/-- The standard integral general plane is unimodular when its two
coefficients are integral and its determinant is a valuation unit. -/
theorem omearaGeneralPlane_isModular_one
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hdetUnit : IsValuationUnit K (alpha * beta - 1)) :
    IsModular
      (QuadraticSpace.omearaGeneralPlane alpha beta hnondegenerate)
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) := by
  let q := QuadraticSpace.omearaGeneralPlane alpha beta hnondegenerate
  let b : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  have hscale : scaleIdeal q (hyperbolicPlaneLattice (K := K)) ≤
      principalIdeal (K := K) (1 : K) := by
    change scaleIdeal q (basisLattice b) ≤
      principalIdeal (K := K) (1 : K)
    apply scaleIdeal_basisLattice_le_of_basis q b
      (principalIdeal (K := K) (1 : K))
    intro i j
    fin_cases i <;> fin_cases j
    all_goals simp [q, b,
      QuadraticSpace.omearaGeneralPlane_bilin_apply]
    · simpa using mul_mem_principalIdeal_of_mem_integerRing
        (K := K) (1 : K) alpha halpha
    · exact generator_mem_principalIdeal (K := K) (1 : K)
    · exact generator_mem_principalIdeal (K := K) (1 : K)
    · simpa using mul_mem_principalIdeal_of_mem_integerRing
        (K := K) (1 : K) beta hbeta
  have hgramDet :
      (LinearMap.BilinForm.toMatrix b q.bilin).det = alpha * beta - 1 := by
    change
      (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin 2))
        (Matrix.toBilin'
          (QuadraticSpace.omearaGeneralPlaneMatrix alpha beta))).det = _
    rw [LinearMap.BilinForm.toMatrix_basisFun,
      LinearMap.BilinForm.toMatrix'_toBilin',
      QuadraticSpace.omearaGeneralPlaneMatrix_det]
  have hvolume : volumeOrder q (hyperbolicPlaneLattice (K := K)) =
      (finrank K (Fin 2 → K) : Int) * ordUnit K (1 : Kˣ) := by
    have hfin : finrank K (Fin 2 → K) = 2 := by simp
    rw [hfin]
    change volumeOrder q (basisLattice b) =
      2 * ordUnit K (1 : Kˣ)
    apply WithTop.coe_injective
    rw [coe_volumeOrder_basisLattice_eq_ord_det_toMatrix,
      hgramDet, hdetUnit]
    simp [ordUnit]
  exact isModular_of_scaleIdeal_le_of_volumeOrder_eq q
    (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) hscale hvolume

/-- Add a complement vector to the first standard vector of a binary
plane.  The first coordinate makes injectivity immediate. -/
def omearaGeneralPlaneAdjoinLinearMap (z : W) :
    (Fin 2 → K) →ₗ[K] ((Fin 2 → K) × W) where
  toFun x := (x, x 0 • z)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · simp [add_smul]
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · simp [mul_smul]

@[simp]
theorem omearaGeneralPlaneAdjoinLinearMap_apply
    (z : W) (x : Fin 2 → K) :
    omearaGeneralPlaneAdjoinLinearMap z x = (x, x 0 • z) :=
  rfl

theorem omearaGeneralPlaneAdjoinLinearMap_injective (z : W) :
    Function.Injective (omearaGeneralPlaneAdjoinLinearMap (K := K) z) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

/-- The source plane is linearly equivalent to the range of the adjoin
map. -/
noncomputable def omearaGeneralPlaneAdjoinRangeEquiv (z : W) :
    (Fin 2 → K) ≃ₗ[K]
      LinearMap.range (omearaGeneralPlaneAdjoinLinearMap (K := K) z) :=
  LinearEquiv.ofBijective
    (omearaGeneralPlaneAdjoinLinearMap (K := K) z).rangeRestrict
    ⟨by
      intro x y hxy
      apply omearaGeneralPlaneAdjoinLinearMap_injective (K := K) z
      exact congrArg Subtype.val hxy,
      LinearMap.surjective_rangeRestrict _⟩

@[simp]
theorem coe_omearaGeneralPlaneAdjoinRangeEquiv_apply
    (z : W) (x : Fin 2 → K) :
    ((omearaGeneralPlaneAdjoinRangeEquiv (K := K) z x :
        LinearMap.range (omearaGeneralPlaneAdjoinLinearMap (K := K) z)) :
      (Fin 2 → K) × W) = (x, x 0 • z) :=
  rfl

/-- The range form is the general plane with first coefficient shifted by
`Q(z)`. -/
theorem omearaGeneralPlaneAdjoinRange_nondegenerate
    (r : QuadraticSpace K W) (alpha beta : K)
    (hold : alpha * beta ≠ 1) (z : W)
    (hnew : (alpha + r.quadratic z) * beta ≠ 1) :
    (LinearMap.BilinForm.restrict
      ((QuadraticSpace.omearaGeneralPlane alpha beta hold).orthogonalSum r).bilin
      (LinearMap.range
        (omearaGeneralPlaneAdjoinLinearMap (K := K) z))).Nondegenerate := by
  let source := QuadraticSpace.omearaGeneralPlane
    (alpha + r.quadratic z) beta hnew
  let e := omearaGeneralPlaneAdjoinRangeEquiv (K := K) z
  have hform :
      LinearMap.BilinForm.restrict
          ((QuadraticSpace.omearaGeneralPlane alpha beta hold).orthogonalSum r).bilin
          (LinearMap.range
            (omearaGeneralPlaneAdjoinLinearMap (K := K) z)) =
        LinearMap.BilinForm.congr e source.bilin := by
    ext x y
    change
      ((QuadraticSpace.omearaGeneralPlane alpha beta hold).orthogonalSum r).bilin
          (x : (Fin 2 → K) × W) (y : (Fin 2 → K) × W) =
        source.bilin (e.symm x) (e.symm y)
    have hx := congrArg Subtype.val (e.apply_symm_apply x)
    have hy := congrArg Subtype.val (e.apply_symm_apply y)
    rw [show (x : (Fin 2 → K) × W) =
        ((e.symm x), (e.symm x) 0 • z) by exact hx.symm,
      show (y : (Fin 2 → K) × W) =
        ((e.symm y), (e.symm y) 0 • z) by exact hy.symm]
    rw [QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.omearaGeneralPlane_bilin_apply,
      QuadraticSpace.omearaGeneralPlane_bilin_apply,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    simp only [Prod.fst, Prod.snd, smul_eq_mul]
    rw [show r.quadratic z = r.bilin z z by rfl]
    ring
  rw [hform]
  exact source.nondegenerate.congr e

/-- The shifted binary plane as a quadratic sublattice of the old
orthogonal product. -/
noncomputable def omearaGeneralPlaneAdjoinComponent
    (r : QuadraticSpace K W) (alpha beta : K)
    (hold : alpha * beta ≠ 1) (z : W)
    (hnew : (alpha + r.quadratic z) * beta ≠ 1) :
    QuadraticSublattice
      ((QuadraticSpace.omearaGeneralPlane alpha beta hold).orthogonalSum r) where
  carrier := LinearMap.range (omearaGeneralPlaneAdjoinLinearMap (K := K) z)
  nondegenerate :=
    omearaGeneralPlaneAdjoinRange_nondegenerate r alpha beta hold z hnew
  lattice := map (omearaGeneralPlaneAdjoinRangeEquiv (K := K) z)
    (hyperbolicPlaneLattice (K := K))

/-- The shifted standard plane is isometric to its image component. -/
noncomputable def omearaGeneralPlaneAdjoinImageIsometry
    (r : QuadraticSpace K W) (alpha beta : K)
    (hold : alpha * beta ≠ 1) (z : W)
    (hnew : (alpha + r.quadratic z) * beta ≠ 1) :
    Isometry
      (QuadraticSpace.omearaGeneralPlane
        (alpha + r.quadratic z) beta hnew)
      (omearaGeneralPlaneAdjoinComponent r alpha beta hold z hnew).space
      (hyperbolicPlaneLattice (K := K))
      (omearaGeneralPlaneAdjoinComponent r alpha beta hold z hnew).lattice where
  toLinearEquiv := omearaGeneralPlaneAdjoinRangeEquiv (K := K) z
  map_bilin x y := by
    change
      ((QuadraticSpace.omearaGeneralPlane alpha beta hold).orthogonalSum r).bilin
          ((x, x 0 • z)) ((y, y 0 • z)) =
        (QuadraticSpace.omearaGeneralPlane
          (alpha + r.quadratic z) beta hnew).bilin x y
    rw [QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.omearaGeneralPlane_bilin_apply,
      QuadraticSpace.omearaGeneralPlane_bilin_apply,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    simp only [Prod.fst, Prod.snd, smul_eq_mul]
    rw [show r.quadratic z = r.bilin z z by rfl]
    ring
  map_mem x := by
    exact (map_mem_map_iff (omearaGeneralPlaneAdjoinRangeEquiv (K := K) z)
      (hyperbolicPlaneLattice (K := K)) x).symm

/-- The shifted image lattice is contained in the original product
lattice whenever the adjoined vector is integral. -/
theorem omearaGeneralPlaneAdjoinComponent_ambientSubmodule_le
    (r : QuadraticSpace K W) (M : Lattice K W)
    (alpha beta : K) (hold : alpha * beta ≠ 1) (z : W)
    (hnew : (alpha + r.quadratic z) * beta ≠ 1)
    (hz : z ∈ M) :
    (omearaGeneralPlaneAdjoinComponent r alpha beta hold z hnew).ambientSubmodule ≤
      (product (hyperbolicPlaneLattice (K := K)) M).toSubmodule := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : (omearaGeneralPlaneAdjoinRangeEquiv z).symm y ∈
      hyperbolicPlaneLattice (K := K) := by
    exact (mem_map_iff (omearaGeneralPlaneAdjoinRangeEquiv (K := K) z)
      (hyperbolicPlaneLattice (K := K)) y).mp hy
  let x := (omearaGeneralPlaneAdjoinRangeEquiv (K := K) z).symm y
  have hcoe := congrArg Subtype.val
    ((omearaGeneralPlaneAdjoinRangeEquiv (K := K) z).apply_symm_apply y)
  change (y : (Fin 2 → K) × W) ∈
    product (hyperbolicPlaneLattice (K := K)) M
  rw [show (y : (Fin 2 → K) × W) = (x, x 0 • z) by exact hcoe.symm]
  rw [mem_product_iff]
  refine ⟨hy', ?_⟩
  have hx0 : x 0 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff x).mp hy' |>.1
  exact M.smul_mem ⟨x 0, hx0⟩ hz

/-- Output of the general-plane change of complement. -/
structure OmearaGeneralPlaneChangeOfComplementData
    (r : QuadraticSpace K W) (M : Lattice K W)
    (alpha beta : K) (hold : alpha * beta ≠ 1) (z : W)
    (hnew : (alpha + r.quadratic z) * beta ≠ 1) where
  decomposition : OrthogonalDecomposition
    ((QuadraticSpace.omearaGeneralPlane alpha beta hold).orthogonalSum r)
    (product (hyperbolicPlaneLattice (K := K)) M) 2
  first : Isometry
    (decomposition.component 0).space
    (QuadraticSpace.omearaGeneralPlane
      (alpha + r.quadratic z) beta hnew)
    (decomposition.component 0).lattice
    (hyperbolicPlaneLattice (K := K))

namespace OmearaGeneralPlaneChangeOfComplementData

/-- Display the changed plane and the newly constructed complement. -/
noncomputable def displayedIsometry
    {r : QuadraticSpace K W} {M : Lattice K W}
    {alpha beta : K} {hold : alpha * beta ≠ 1} {z : W}
    {hnew : (alpha + r.quadratic z) * beta ≠ 1}
    (D : OmearaGeneralPlaneChangeOfComplementData
      r M alpha beta hold z hnew) :
    Isometry
      ((QuadraticSpace.omearaGeneralPlane alpha beta hold).orthogonalSum r)
      ((QuadraticSpace.omearaGeneralPlane
          (alpha + r.quadratic z) beta hnew).orthogonalSum
        (D.decomposition.component 1).space)
      (product (hyperbolicPlaneLattice (K := K)) M)
      (product (hyperbolicPlaneLattice (K := K))
        (D.decomposition.component 1).lattice) :=
  D.decomposition.pairProductLatticeIsometry.symm |>.trans
    (D.first.orthogonalProductBasic
      (Isometry.refl (D.decomposition.component 1).space
        (D.decomposition.component 1).lattice))

end OmearaGeneralPlaneChangeOfComplementData

/-- O'Meara 82:15a applied to the plane generated by `e₀ + z, e₁`.
The result is the general-plane complement change used in 93:18(ii). -/
noncomputable def omearaGeneralPlaneChangeOfComplement
    (r : QuadraticSpace K W) (M : Lattice K W)
    (alpha beta : K) (hold : alpha * beta ≠ 1) (z : W)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hz : z ∈ M)
    (hnewIntegral : alpha + r.quadratic z ∈ IntegerRing K)
    (hnewDetUnit : IsValuationUnit K
      ((alpha + r.quadratic z) * beta - 1))
    (hambient : IsModular
      ((QuadraticSpace.omearaGeneralPlane alpha beta hold).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M) (1 : Kˣ)) :
    OmearaGeneralPlaneChangeOfComplementData r M alpha beta hold z
      (sub_ne_zero.mp (by
        intro hzero
        rw [hzero] at hnewDetUnit
        simp [IsValuationUnit] at hnewDetUnit)) := by
  let hnew : (alpha + r.quadratic z) * beta ≠ 1 :=
    sub_ne_zero.mp (by
      intro hzero
      rw [hzero] at hnewDetUnit
      simp [IsValuationUnit] at hnewDetUnit)
  let C := omearaGeneralPlaneAdjoinComponent r alpha beta hold z hnew
  have hCL : C.ambientSubmodule ≤
      (product (hyperbolicPlaneLattice (K := K)) M).toSubmodule :=
    omearaGeneralPlaneAdjoinComponent_ambientSubmodule_le
      r M alpha beta hold z hnew hz
  let imageIso := omearaGeneralPlaneAdjoinImageIsometry
    r alpha beta hold z hnew
  have hsourceModular : IsModular
      (QuadraticSpace.omearaGeneralPlane
        (alpha + r.quadratic z) beta hnew)
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    omearaGeneralPlane_isModular_one
      (alpha + r.quadratic z) beta hnew hnewIntegral hbeta hnewDetUnit
  have hCModular : IsModular C.space C.lattice (1 : Kˣ) :=
    hsourceModular.mapLatticeIsometry imageIso
  let D := omearaModularSplittingOfScaleIdealLe C hCL hCModular
    hambient.scaleIdeal_le_principal
  have hfirst : Isometry
      (D.component 0).space
      (QuadraticSpace.omearaGeneralPlane
        (alpha + r.quadratic z) beta hnew)
      (D.component 0).lattice
      (hyperbolicPlaneLattice (K := K)) := by
    change Isometry C.space
      (QuadraticSpace.omearaGeneralPlane
        (alpha + r.quadratic z) beta hnew)
      C.lattice (hyperbolicPlaneLattice (K := K))
    exact imageIso.symm
  exact ⟨D, hfirst⟩

end Lattice

end Bong
