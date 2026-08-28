/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaGeneralPlane
import Bong.Lattice.MinimalScaleComponent
import Bong.Lattice.ModularCriterion
import Bong.Lattice.OrthogonalDecompositionVolume

/-!
# The binary exchange used in O'Meara 93:19

Inside `A(alpha,beta) ⊥ s A(gamma,0)`, replace the first vector of the
first plane by its sum with the first vector of the second plane.  Its value
changes from `alpha` to `alpha + s * gamma`.  The two displayed vectors still
span a unimodular plane, and the formulas below give an integral basis of its
orthogonal complement.  This is the explicit four-dimensional change of
basis in the middle line of O'Meara's proof of 93:19.
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u

variable {K : Type u} [Field K]

/-- Gram matrix of the binary complement left by the 93:19 exchange. -/
def omearaExchangeComplementMatrix
    (alpha beta gamma s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![-s * gamma, s * (alpha * beta - 1);
      s * (alpha * beta - 1), beta * s ^ 2 * (alpha * beta - 1)]

theorem omearaExchangeComplementMatrix_isSymm
    (alpha beta gamma s : K) :
    (omearaExchangeComplementMatrix alpha beta gamma s).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem omearaExchangeComplementMatrix_det
    (alpha beta gamma s : K) :
    (omearaExchangeComplementMatrix alpha beta gamma s).det =
      -(s ^ 2 * (alpha * beta - 1) *
        ((alpha + s * gamma) * beta - 1)) := by
  simp [omearaExchangeComplementMatrix, Matrix.det_fin_two_of]
  ring

/-- The regular binary complement in the 93:19 exchange. -/
noncomputable def omearaExchangeComplement
    (alpha beta gamma s : K)
    (hs : s ≠ 0)
    (hold : alpha * beta ≠ 1)
    (hnew : (alpha + s * gamma) * beta ≠ 1) :
    QuadraticSpace K (Fin 2 → K) where
  bilin := Matrix.toBilin' (omearaExchangeComplementMatrix alpha beta gamma s)
  isSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2
    (omearaExchangeComplementMatrix_isSymm alpha beta gamma s)
  nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (omearaExchangeComplementMatrix alpha beta gamma s) (by
        rw [omearaExchangeComplementMatrix_det]
        exact neg_ne_zero.mpr (mul_ne_zero
          (mul_ne_zero (pow_ne_zero 2 hs) (sub_ne_zero.mpr hold))
          (sub_ne_zero.mpr hnew)))

/-- Coordinate formula for the exchanged complement. -/
theorem omearaExchangeComplement_bilin_apply
    (alpha beta gamma s : K)
    (hs : s ≠ 0)
    (hold : alpha * beta ≠ 1)
    (hnew : (alpha + s * gamma) * beta ≠ 1)
    (x y : Fin 2 → K) :
    (omearaExchangeComplement alpha beta gamma s hs hold hnew).bilin x y =
      (-s * gamma) * x 0 * y 0 +
        (s * (alpha * beta - 1)) * x 0 * y 1 +
        (s * (alpha * beta - 1)) * x 1 * y 0 +
        (beta * s ^ 2 * (alpha * beta - 1)) * x 1 * y 1 := by
  rw [omearaExchangeComplement, Matrix.toBilin'_apply]
  simp only [Fin.sum_univ_two]
  simp [omearaExchangeComplementMatrix]
  ring

/-- The determinant of the integral exchange matrix. -/
def omearaExchangeDeterminant
    (alpha beta gamma s : K) : K :=
  (alpha + s * gamma) * beta - 1

/-- The four-dimensional exchange, written from the new orthogonal
coordinates to the old ones. -/
noncomputable def omearaExchangeLinearEquiv
    (alpha beta gamma s : K)
    (hdet : omearaExchangeDeterminant alpha beta gamma s ≠ 0) :
    ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 2 → K) × (Fin 2 → K)) where
  toFun := fun x ↦
    (![
      x.1 0 - beta * s * x.2 1,
      x.1 1 + s * x.2 1],
     ![
      x.1 0 + x.2 0,
      -gamma * x.2 0 - (1 - alpha * beta) * x.2 1])
  invFun := fun y ↦
    let d := omearaExchangeDeterminant alpha beta gamma s
    (![
      d⁻¹ * ((alpha * beta - 1) * y.1 0 +
        beta * gamma * s * y.2 0 + beta * s * y.2 1),
      d⁻¹ * (gamma * s * y.1 0 + d * y.1 1 -
        gamma * s * y.2 0 - s * y.2 1)],
     ![
      d⁻¹ * ((1 - alpha * beta) * y.1 0 +
        (alpha * beta - 1) * y.2 0 - beta * s * y.2 1),
      d⁻¹ * (-gamma * y.1 0 + gamma * y.2 0 + y.2 1)])
  left_inv := by
    intro x
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp <;>
        field_simp [hdet] <;>
        simp [omearaExchangeDeterminant] <;>
        ring
    · funext i
      fin_cases i <;>
        simp <;>
        field_simp [hdet] <;>
        simp [omearaExchangeDeterminant] <;>
        ring
  right_inv := by
    intro y
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp <;>
        field_simp [hdet] <;>
        simp [omearaExchangeDeterminant] <;>
        ring
    · funext i
      fin_cases i <;>
        simp <;>
        field_simp [hdet] <;>
        simp [omearaExchangeDeterminant] <;>
        ring
  map_add' := by
    intro x y
    ext i <;> fin_cases i <;> simp <;> ring
  map_smul' := by
    intro c x
    ext i <;> fin_cases i <;> simp <;> ring

/-- The exchange is an isometry of the two explicitly displayed
orthogonal sums. -/
noncomputable def omearaBinaryExchangeSpaceIsometry
    (alpha beta gamma : K) (s : Kˣ)
    (hold : alpha * beta ≠ 1)
    (hnew : (alpha + (s : K) * gamma) * beta ≠ 1) :
    Isometry
      ((omearaGeneralPlane
          (alpha + (s : K) * gamma) beta hnew).orthogonalSum
        (omearaExchangeComplement alpha beta gamma (s : K)
          (Units.ne_zero s) hold hnew))
      ((omearaGeneralPlane alpha beta hold).orthogonalSum
        ((omearaPlane gamma).rescaleUnit s)) where
  toLinearEquiv := omearaExchangeLinearEquiv alpha beta gamma (s : K)
    (by simpa [omearaExchangeDeterminant] using sub_ne_zero.mpr hnew)
  map_bilin x y := by
    rw [orthogonalSum_bilin_apply, orthogonalSum_bilin_apply,
      omearaGeneralPlane_bilin_apply, omearaGeneralPlane_bilin_apply,
      omearaExchangeComplement_bilin_apply,
      rescaleUnit_bilin_apply, omearaPlane_bilin_apply]
    simp [omearaExchangeLinearEquiv]
    ring

end QuadraticSpace

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A local valuation unit is nonzero; kept local to the exchange layer so
this file does not depend on the later hyperbolic-cancellation development. -/
theorem omearaExchange_ne_zero_of_isValuationUnit {c : K}
    (hc : IsValuationUnit K c) : c ≠ 0 := by
  intro hzero
  subst c
  simp [IsValuationUnit] at hc

/-- A maximal-ideal perturbation cannot change the unit determinant of the
displayed unimodular plane.  This is the determinant check used immediately
before the four-dimensional exchange in 93:19. -/
theorem omearaExchangeDeterminant_isValuationUnit
    (alpha beta gamma : K) (s : Kˣ)
    (hbeta : beta ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K)
    (hsMaximal : IsInMaximalIdeal K (s : K))
    (holdUnit : IsValuationUnit K (alpha * beta - 1)) :
    IsValuationUnit K
      (QuadraticSpace.omearaExchangeDeterminant
        alpha beta gamma (s : K)) := by
  have hgammaBeta : Dyadic.IsIntegral K (gamma * beta) :=
    isIntegral_mul K
      ((mem_integerRing_iff K).1 hgamma)
      ((mem_integerRing_iff K).1 hbeta)
  have hcorrection : IsInMaximalIdeal K ((s : K) * (gamma * beta)) :=
    isInMaximalIdeal_mul_isIntegral K hsMaximal hgammaBeta
  have hstrict : ord K (alpha * beta - 1) <
      ord K ((s : K) * (gamma * beta)) := by
    rw [holdUnit]
    exact hcorrection
  unfold QuadraticSpace.omearaExchangeDeterminant
  rw [show (alpha + (s : K) * gamma) * beta - 1 =
      (alpha * beta - 1) + (s : K) * (gamma * beta) by ring]
  change ord K
      ((alpha * beta - 1) + (s : K) * (gamma * beta)) = 0
  exact ((ord K).map_add_eq_of_lt_left hstrict).trans holdUnit

/-- Integrality of the four standard coordinates of two binary planes. -/
def OmearaBinaryCoordinatesIntegral
    (x : (Fin 2 → K) × (Fin 2 → K)) : Prop :=
  x.1 0 ∈ IntegerRing K ∧ x.1 1 ∈ IntegerRing K ∧
    x.2 0 ∈ IntegerRing K ∧ x.2 1 ∈ IntegerRing K

theorem mem_twoHyperbolicPlaneLattice_iff
    (x : (Fin 2 → K) × (Fin 2 → K)) :
    x ∈ product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)) ↔
      OmearaBinaryCoordinatesIntegral x := by
  rw [mem_product_iff, mem_omearaPlaneLattice_iff,
    mem_omearaPlaneLattice_iff]
  constructor
  · rintro ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
    exact ⟨h00, h01, h10, h11⟩
  · rintro ⟨h00, h01, h10, h11⟩
    exact ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩

/-- Integral coefficients make the forward exchange matrix integral. -/
theorem omearaExchangeLinearEquiv_integral
    (alpha beta gamma s : K)
    (hdet : QuadraticSpace.omearaExchangeDeterminant
      alpha beta gamma s ≠ 0)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K)
    (hs : s ∈ IntegerRing K)
    {x : (Fin 2 → K) × (Fin 2 → K)}
    (hx : OmearaBinaryCoordinatesIntegral x) :
    OmearaBinaryCoordinatesIntegral
      (QuadraticSpace.omearaExchangeLinearEquiv
        alpha beta gamma s hdet x) := by
  let R := (IntegerRing K).toSubring
  have hbetaS : beta * s ∈ R := R.mul_mem hbeta hs
  have honeMinus : 1 - alpha * beta ∈ R :=
    R.sub_mem R.one_mem (R.mul_mem halpha hbeta)
  rcases hx with ⟨hx00, hx01, hx10, hx11⟩
  change
    x.1 0 - beta * s * x.2 1 ∈ IntegerRing K ∧
      x.1 1 + s * x.2 1 ∈ IntegerRing K ∧
      x.1 0 + x.2 0 ∈ IntegerRing K ∧
      -gamma * x.2 0 - (1 - alpha * beta) * x.2 1 ∈ IntegerRing K
  exact ⟨
    R.sub_mem hx00 (R.mul_mem hbetaS hx11),
    R.add_mem hx01 (R.mul_mem hs hx11),
    R.add_mem hx00 hx10,
    R.sub_mem (R.mul_mem (R.neg_mem hgamma) hx10)
      (R.mul_mem honeMinus hx11)⟩

/-- A valuation-unit determinant makes the inverse exchange matrix
integral as well. -/
theorem omearaExchangeLinearEquiv_symm_integral
    (alpha beta gamma s : K)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K)
    (hs : s ∈ IntegerRing K)
    (hdetUnit : IsValuationUnit K
      (QuadraticSpace.omearaExchangeDeterminant alpha beta gamma s))
    {y : (Fin 2 → K) × (Fin 2 → K)}
    (hy : OmearaBinaryCoordinatesIntegral y) :
    OmearaBinaryCoordinatesIntegral
      ((QuadraticSpace.omearaExchangeLinearEquiv alpha beta gamma s
        (omearaExchange_ne_zero_of_isValuationUnit hdetUnit)).symm y) := by
  let R := (IntegerRing K).toSubring
  let d := QuadraticSpace.omearaExchangeDeterminant alpha beta gamma s
  have hdMem : d ∈ IntegerRing K := by
    dsimp only [d, QuadraticSpace.omearaExchangeDeterminant]
    exact R.sub_mem
      (R.mul_mem (R.add_mem halpha (R.mul_mem hs hgamma)) hbeta)
      R.one_mem
  have hdInvUnit : IsValuationUnit K d⁻¹ := by
    simpa [d, IsValuationUnit, AddValuation.map_inv, hdetUnit]
  have hdInvMem : d⁻¹ ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 hdInvUnit.ge
  rcases hy with ⟨hy00, hy01, hy10, hy11⟩
  have hn00 :
      (alpha * beta - 1) * y.1 0 + beta * gamma * s * y.2 0 +
          beta * s * y.2 1 ∈ R := by
    exact R.add_mem
      (R.add_mem
        (R.mul_mem (R.sub_mem (R.mul_mem halpha hbeta) R.one_mem) hy00)
        (R.mul_mem (R.mul_mem (R.mul_mem hbeta hgamma) hs) hy10))
      (R.mul_mem (R.mul_mem hbeta hs) hy11)
  have hn01 :
      gamma * s * y.1 0 + d * y.1 1 - gamma * s * y.2 0 -
          s * y.2 1 ∈ R := by
    exact R.sub_mem
      (R.sub_mem
        (R.add_mem
          (R.mul_mem (R.mul_mem hgamma hs) hy00)
          (R.mul_mem hdMem hy01))
        (R.mul_mem (R.mul_mem hgamma hs) hy10))
      (R.mul_mem hs hy11)
  have hn10 :
      (1 - alpha * beta) * y.1 0 + (alpha * beta - 1) * y.2 0 -
          beta * s * y.2 1 ∈ R := by
    exact R.sub_mem
      (R.add_mem
        (R.mul_mem (R.sub_mem R.one_mem (R.mul_mem halpha hbeta)) hy00)
        (R.mul_mem (R.sub_mem (R.mul_mem halpha hbeta) R.one_mem) hy10))
      (R.mul_mem (R.mul_mem hbeta hs) hy11)
  have hn11 : -gamma * y.1 0 + gamma * y.2 0 + y.2 1 ∈ R := by
    exact R.add_mem
      (R.add_mem (R.mul_mem (R.neg_mem hgamma) hy00)
        (R.mul_mem hgamma hy10)) hy11
  change
    d⁻¹ * ((alpha * beta - 1) * y.1 0 +
        beta * gamma * s * y.2 0 + beta * s * y.2 1) ∈ IntegerRing K ∧
      d⁻¹ * (gamma * s * y.1 0 + d * y.1 1 -
        gamma * s * y.2 0 - s * y.2 1) ∈ IntegerRing K ∧
      d⁻¹ * ((1 - alpha * beta) * y.1 0 +
        (alpha * beta - 1) * y.2 0 - beta * s * y.2 1) ∈ IntegerRing K ∧
      d⁻¹ * (-gamma * y.1 0 + gamma * y.2 0 + y.2 1) ∈ IntegerRing K
  exact ⟨R.mul_mem hdInvMem hn00, R.mul_mem hdInvMem hn01,
    R.mul_mem hdInvMem hn10, R.mul_mem hdInvMem hn11⟩

/-- Integral form of the middle four-dimensional isometry in O'Meara
93:19. -/
noncomputable def omearaBinaryExchangeLatticeIsometry
    (alpha beta gamma : K) (s : Kˣ)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K)
    (hs : (s : K) ∈ IntegerRing K)
    (holdUnit : IsValuationUnit K (alpha * beta - 1))
    (hnewUnit : IsValuationUnit K
      ((alpha + (s : K) * gamma) * beta - 1)) :
    Isometry
      ((QuadraticSpace.omearaGeneralPlane
          (alpha + (s : K) * gamma) beta
            (sub_ne_zero.mp
              (omearaExchange_ne_zero_of_isValuationUnit hnewUnit))).orthogonalSum
        (QuadraticSpace.omearaExchangeComplement alpha beta gamma (s : K)
          (Units.ne_zero s)
          (sub_ne_zero.mp (omearaExchange_ne_zero_of_isValuationUnit holdUnit))
          (sub_ne_zero.mp (omearaExchange_ne_zero_of_isValuationUnit hnewUnit))))
      ((QuadraticSpace.omearaGeneralPlane alpha beta
          (sub_ne_zero.mp (omearaExchange_ne_zero_of_isValuationUnit holdUnit))).orthogonalSum
        ((QuadraticSpace.omearaPlane gamma).rescaleUnit s))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicPlaneLattice (K := K))) where
  toLinearEquiv :=
    (QuadraticSpace.omearaBinaryExchangeSpaceIsometry alpha beta gamma s
      (sub_ne_zero.mp (omearaExchange_ne_zero_of_isValuationUnit holdUnit))
      (sub_ne_zero.mp (omearaExchange_ne_zero_of_isValuationUnit hnewUnit))).toLinearEquiv
  map_bilin :=
    (QuadraticSpace.omearaBinaryExchangeSpaceIsometry alpha beta gamma s
      (sub_ne_zero.mp (omearaExchange_ne_zero_of_isValuationUnit holdUnit))
      (sub_ne_zero.mp (omearaExchange_ne_zero_of_isValuationUnit hnewUnit))).map_bilin
  map_mem x := by
    rw [mem_twoHyperbolicPlaneLattice_iff,
      mem_twoHyperbolicPlaneLattice_iff]
    let E := QuadraticSpace.omearaExchangeLinearEquiv
      alpha beta gamma (s : K)
      (omearaExchange_ne_zero_of_isValuationUnit hnewUnit)
    constructor
    · intro hx
      exact omearaExchangeLinearEquiv_integral
        alpha beta gamma (s : K)
          (omearaExchange_ne_zero_of_isValuationUnit hnewUnit)
          halpha hbeta hgamma hs hx
    · intro hEx
      change OmearaBinaryCoordinatesIntegral (E x) at hEx
      have hInv := omearaExchangeLinearEquiv_symm_integral
        alpha beta gamma (s : K) halpha hbeta hgamma hs hnewUnit hEx
      change OmearaBinaryCoordinatesIntegral (E.symm (E x)) at hInv
      simpa only [LinearEquiv.symm_apply_apply] using hInv

set_option maxHeartbeats 600000 in
-- The proof expands a binary Gram determinant through ideal normalization.
/-- The binary complement created by the exchange is modular at the old
lower scale.  Its normalized determinant is the product of the old and new
unimodular-plane determinants. -/
theorem omearaExchangeComplement_isModular
    (alpha beta gamma : K) (s : Kˣ)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K)
    (hs : (s : K) ∈ IntegerRing K)
    (holdUnit : IsValuationUnit K (alpha * beta - 1))
    (hnewUnit : IsValuationUnit K
      ((alpha + (s : K) * gamma) * beta - 1)) :
    IsModular
      (QuadraticSpace.omearaExchangeComplement alpha beta gamma (s : K)
        (Units.ne_zero s)
        (sub_ne_zero.mp
          (omearaExchange_ne_zero_of_isValuationUnit holdUnit))
        (sub_ne_zero.mp
          (omearaExchange_ne_zero_of_isValuationUnit hnewUnit)))
      (hyperbolicPlaneLattice (K := K)) s := by
  let q := QuadraticSpace.omearaExchangeComplement
    alpha beta gamma (s : K) (Units.ne_zero s)
      (sub_ne_zero.mp
        (omearaExchange_ne_zero_of_isValuationUnit holdUnit))
      (sub_ne_zero.mp
        (omearaExchange_ne_zero_of_isValuationUnit hnewUnit))
  let b : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  have hscale : scaleIdeal q (hyperbolicPlaneLattice (K := K)) ≤
      principalIdeal (K := K) (s : K) := by
    change scaleIdeal q (basisLattice b) ≤
      principalIdeal (K := K) (s : K)
    apply scaleIdeal_basisLattice_le_of_basis q b
      (principalIdeal (K := K) (s : K))
    intro i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [q, b, QuadraticSpace.omearaExchangeComplement_bilin_apply]
    · change (s : K) * gamma ∈ principalIdeal (K := K) (s : K)
      exact mul_mem_principalIdeal_of_mem_integerRing
        (s : K) gamma hgamma
    · change (s : K) * (alpha * beta - 1) ∈
        principalIdeal (K := K) (s : K)
      exact mul_mem_principalIdeal_of_mem_integerRing
        (s : K) (alpha * beta - 1)
          ((IntegerRing K).toSubring.sub_mem
            ((IntegerRing K).toSubring.mul_mem halpha hbeta)
            (IntegerRing K).toSubring.one_mem)
    · change (s : K) * (alpha * beta - 1) ∈
        principalIdeal (K := K) (s : K)
      exact mul_mem_principalIdeal_of_mem_integerRing
        (s : K) (alpha * beta - 1)
          ((IntegerRing K).toSubring.sub_mem
            ((IntegerRing K).toSubring.mul_mem halpha hbeta)
            (IntegerRing K).toSubring.one_mem)
    · change beta * (s : K) ^ 2 * (alpha * beta - 1) ∈
        principalIdeal (K := K) (s : K)
      rw [show beta * (s : K) ^ 2 * (alpha * beta - 1) =
          (s : K) * (beta * (s : K) * (alpha * beta - 1)) by ring]
      exact mul_mem_principalIdeal_of_mem_integerRing
        (s : K) (beta * (s : K) * (alpha * beta - 1))
          ((IntegerRing K).toSubring.mul_mem
            ((IntegerRing K).toSubring.mul_mem hbeta hs)
            ((IntegerRing K).toSubring.sub_mem
              ((IntegerRing K).toSubring.mul_mem halpha hbeta)
              (IntegerRing K).toSubring.one_mem))
  have hgramDet : (LinearMap.BilinForm.toMatrix b q.bilin).det =
      -((s : K) ^ 2 * (alpha * beta - 1) *
        ((alpha + (s : K) * gamma) * beta - 1)) := by
    rw [show LinearMap.BilinForm.toMatrix b q.bilin =
        QuadraticSpace.omearaExchangeComplementMatrix
          alpha beta gamma (s : K) by
      change
        LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin 2))
            (Matrix.toBilin'
              (QuadraticSpace.omearaExchangeComplementMatrix
                alpha beta gamma (s : K))) =
          QuadraticSpace.omearaExchangeComplementMatrix
            alpha beta gamma (s : K)
      rw [LinearMap.BilinForm.toMatrix_basisFun,
        LinearMap.BilinForm.toMatrix'_toBilin']]
    exact QuadraticSpace.omearaExchangeComplementMatrix_det
      alpha beta gamma (s : K)
  have hvolume : volumeOrder q (hyperbolicPlaneLattice (K := K)) =
      (finrank K (Fin 2 → K) : Int) * ordUnit K s := by
    have hfin : finrank K (Fin 2 → K) = 2 := by simp
    rw [hfin]
    change volumeOrder q (basisLattice b) = 2 * ordUnit K s
    apply WithTop.coe_injective
    rw [coe_volumeOrder_basisLattice_eq_ord_det_toMatrix,
      hgramDet, ord_neg, ord_mul, ord_mul, ord_pow,
      holdUnit, hnewUnit]
    have hsOrder := coe_ordUnit K s
    change ((ordUnit K s : Int) : WithTop Int) = ord K (s : K) at hsOrder
    rw [← hsOrder]
    rw [two_mul]
    simp only [two_nsmul, add_zero, WithTop.coe_add]
  exact isModular_of_scaleIdeal_le_of_volumeOrder_eq q
    (hyperbolicPlaneLattice (K := K)) s hscale hvolume

end Lattice

end Bong
