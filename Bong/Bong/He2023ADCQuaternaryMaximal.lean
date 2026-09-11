/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCSectionFour
import Bong.Bong.He2023ADCPublishedProfiles
import Bong.Bong.BeliUniversalAnisotropicQuaternary

/-!
# He (2025), Proposition 4.16: dyadic quaternary maximal lattices

The hyperbolic lattice is the paper's `H = (1/2) A(0,0)`.
The results in this file concern dyadic fields. The published proposition
also includes non-dyadic fields, which are not covered by this file.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A maximal dyadic lattice represents the half-hyperbolic plane exactly
when its ambient quadratic space is isotropic. No rank restriction is needed. -/
theorem IsOMaximal.represents_halfHyperbolic_iff (hL : IsOMaximal q L) :
    Represents q ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (dyadicHalfUnit (K := K))) L (hyperbolicPlaneLattice (K := K)) ↔
      ¬ q.IsAnisotropicSpace := by
  constructor
  · rintro ⟨f⟩ han
    let x : Fin 2 → K := ![1, 0]
    have hx : x ≠ 0 := by
      intro h
      have hzero := congrFun h (0 : Fin 2)
      norm_num [x] at hzero
    have hiso : q.quadratic (f.toLinearMap x) = 0 := by
      rw [f.map_quadratic, QuadraticSpace.rescaleUnit_quadratic]
      simp [QuadraticSpace.quadratic, QuadraticSpace.omearaPlane_bilin_apply, x]
    exact hx (f.injective (by simpa using han _ hiso))
  · intro hnot
    rw [QuadraticSpace.IsAnisotropicSpace] at hnot
    push Not at hnot
    obtain ⟨z, hzIso, hzNe⟩ := hnot
    let D := oMaximalRescaledTwoDecomposition hL hzNe hzIso
    let tail := (D.component 1).space.rescaleUnit (dyadicHalfUnit (K := K))
    let head := QuadraticSpace.hyperbolicPlane (dyadicHalfUnit (K := K))
    let inclusion : Representation head (head.orthogonalSum tail)
        (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) (D.component 1).lattice) :=
      { toLinearMap := LinearMap.inl K (Fin 2 → K) (D.component 1).carrier
        injective := fun _ _ h ↦ congrArg Prod.fst h
        map_bilin := by
          intro x y
          simp [QuadraticSpace.orthogonalSum_bilin_apply]
        map_mem := fun hx ↦ ⟨hx, (D.component 1).lattice.zero_mem⟩ }
    let split := oMaximalHyperbolicSplitIsometry hL hzNe hzIso
    let identify := scaledZeroOmearaPlaneLatticeIsometry (dyadicHalfUnit (K := K))
    exact ⟨split.toRepresentation.trans (inclusion.trans identify.toRepresentation)⟩

end Lattice

/-- The four-dimensional square row `W_2^4(1)` is exactly the fixed
anisotropic coefficient family; the casts only reconcile rank expressions. -/
theorem heADCW2QuaternaryOne_eq_anisotropic :
    heADCW2Even (K := K) 1 1 (Or.inl (by omega)) =
      beliAnisotropicQuaternaryUnits (K := K) := by
  have h := heHuEvenSecond_succ_of_square (K := K) 0 1 (Or.inl (by omega))
    (show IsSquare (1 : Kˣ) from ⟨1, by simp⟩)
  exact h.trans (by funext i; fin_cases i <;> rfl)

/-- The paper's binary lattice `A = (1/2) A(2,2rho)`, in the standard
integral coordinate lattice. Its Gram formula is verified below. -/
noncomputable def heADCAForm : QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.binaryModel
    (negativeQuarterUnit K * (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (BONG.standardEndpointShear (K := K))

/-- Exact Gram normalization of `A`; in particular the off-diagonal
entry is `1/2`, not `1`. -/
theorem heADCAForm_bilin_apply (x y : Fin 2 → K) :
    (heADCAForm (K := K)).bilin x y =
      x 0 * y 0 + (2 : K)⁻¹ * (x 0 * y 1 + x 1 * y 0) +
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).rho * x 1 * y 1 := by
  rw [heADCAForm, QuadraticSpace.binaryModel, Matrix.toBilin'_apply]
  simp only [Fin.sum_univ_two, QuadraticSpace.binaryModelMatrix_zero_zero,
    QuadraticSpace.binaryModelMatrix_zero_one, QuadraticSpace.binaryModelMatrix_one_zero,
    QuadraticSpace.binaryModelMatrix_one_one, Units.val_mul]
  rw [(Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminant_eq_one_sub_four_mul_rho]
  dsimp [BONG.standardEndpointShear, negativeQuarterUnit]
  norm_num [show (4 : K) = 2 * 2 by norm_num]
  field_simp
  ring

/-- The published endpoint BONG is integrally isometric to `A` with its
form scaled by `pi^R`. The lattice vectors themselves are not rescaled. -/
theorem heADCDiscriminantEndpoint_isIsometric_scaledA (R : Int) :
    Lattice.IsIsometric
      (BONG.binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) R 0)
        (heHuDiscriminantEndpointValues (K := K) R 1)
        (heHuDiscriminantEndpoint_admissible (K := K) R))
      ((heADCAForm (K := K)).rescaleUnit (uniformizerPowerUnit K R))
      (BONG.binaryDiagonalModelLattice (K := K))
      (BONG.binaryModelLattice (K := K)) := by
  have h := heHuDiscriminantEndpoint_isIsometric_standard (K := K) R
  change Lattice.IsIsometric _
    ((heADCAForm (K := K)).rescaleUnit
      ((heHuDiscriminantEndpointGoodBONG (K := K) R).valueUnit 0)) _ _ at h
  simpa only [heHuDiscriminantEndpointGoodBONG_valueUnit,
    heHuDiscriminantEndpointValues_zero] using h

/-- The exceptional maximal lattice is the actual orthogonal product
`A perp A^(pi)`, not only an ambient diagonal space. -/
theorem heADCN2QuaternaryOne_isIsometric_A_product_scaledA :
    Lattice.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Even (K := K) 1 1 (Or.inl (by omega))))
      ((heADCAForm (K := K)).orthogonalSum
        ((heADCAForm (K := K)).rescaleUnit (uniformizerPowerUnit K 1)))
      (heADCN2Even (K := K) 1 1 (Or.inl (by omega))).lattice
      (Lattice.product (BONG.binaryModelLattice (K := K))
        (BONG.binaryModelLattice (K := K))) := by
  let b := heHuLemma311EvenSecondOneTail (K := K)
  have hM := heHu2022Proposition37EvenSecondOne (K := K) 0
  have htail := Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    b.valueUnit (heHuLemma311EvenSecondOneStandardValues (K := K))
    (heHuLemma311EvenSecondOneFactors (K := K))
    (heHuLemma311EvenSecondOneTail_eq_anisotropic_mul_square (K := K))
  rw [heHuLemma311EvenSecondOneStandardValues_eq_anisotropic,
    ← heADCW2QuaternaryOne_eq_anisotropic] at htail
  have hambient := b.ambientIsometric_of_diagonalRepresents _ rfl htail
  obtain ⟨f⟩ := Lattice.oMaximal_isIsometric_of_isometric hM
    (heHuOMaximalLattice_isOMaximal _) hambient
  obtain ⟨g₀⟩ := heADCDiscriminantEndpoint_isIsometric_scaledA (K := K) 0
  obtain ⟨g₁⟩ := heADCDiscriminantEndpoint_isIsometric_scaledA (K := K) 1
  have hzero : uniformizerPowerUnit K 0 = 1 := by simp [uniformizerPowerUnit]
  rw [hzero] at g₀
  let g := g₀.trans (Lattice.Isometry.rescaleUnitOne
    (heADCAForm (K := K)) (BONG.binaryModelLattice (K := K)))
  exact ⟨f.symm.trans (g.orthogonalProductBasic g₁)⟩

namespace Lattice

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Among quaternary maximal dyadic lattices, anisotropy characterizes
the exceptional lattice `N_2^4(1)` up to integral isometry. -/
theorem IsOMaximal.isAnisotropic_iff_heADCN2QuaternaryOne
    (hL : IsOMaximal q L) (hrank : finrank K V = 4) :
    q.IsAnisotropicSpace ↔
      IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Even (K := K) 1 1 (Or.inl (by omega)))) L
        (heADCN2Even (K := K) 1 1 (Or.inl (by omega))).lattice := by
  letI : Module.Finite K V := L.moduleFinite
  constructor
  · intro han
    apply oMaximal_isIsometric_of_isometric hL (heHuOMaximalLattice_isOMaximal _)
    rw [heADCW2QuaternaryOne_eq_anisotropic]
    exact anisotropicQuaternary_isIsometric_beliModel q hrank han
  · rintro ⟨f⟩
    have hspace := f.toQuadraticSpaceIsometry
    rw [heADCW2QuaternaryOne_eq_anisotropic] at hspace
    exact hspace.isAnisotropicSpace_iff.mpr
      (beliAnisotropicQuaternaryForm_isAnisotropic (K := K))

/-- The representability and exceptional-class clause of Proposition 4.16
over dyadic fields, with no good-BONG or prescribed-profile premise. -/
theorem heADC2025Proposition416Dyadic_represents_iff
    (hL : IsOMaximal q L) (hrank : finrank K V = 4) :
    Represents q ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (dyadicHalfUnit (K := K))) L (hyperbolicPlaneLattice (K := K)) ↔
      ¬ IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Even (K := K) 1 1 (Or.inl (by omega)))) L
        (heADCN2Even (K := K) 1 1 (Or.inl (by omega))).lattice := by
  rw [hL.represents_halfHyperbolic_iff, hL.isAnisotropic_iff_heADCN2QuaternaryOne hrank]

/-- Both clauses of Proposition 4.16 over dyadic fields: the exact
representation exception and its explicit integral orthogonal-product model. -/
theorem heADC2025Proposition416Dyadic
    (hL : IsOMaximal q L) (hrank : finrank K V = 4) :
    (Represents q ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (dyadicHalfUnit (K := K))) L (hyperbolicPlaneLattice (K := K)) ↔
      ¬ IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Even (K := K) 1 1 (Or.inl (by omega)))) L
        (heADCN2Even (K := K) 1 1 (Or.inl (by omega))).lattice) ∧
      (¬ Represents q ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
          (dyadicHalfUnit (K := K))) L (hyperbolicPlaneLattice (K := K)) →
        IsIsometric q ((heADCAForm (K := K)).orthogonalSum
          ((heADCAForm (K := K)).rescaleUnit (uniformizerPowerUnit K 1))) L
          (product (BONG.binaryModelLattice (K := K)) (BONG.binaryModelLattice (K := K)))) := by
  refine ⟨heADC2025Proposition416Dyadic_represents_iff hL hrank, ?_⟩
  intro hnot
  have han : q.IsAnisotropicSpace := by
    by_contra hiso
    exact hnot (hL.represents_halfHyperbolic_iff.mpr hiso)
  obtain ⟨f⟩ := (hL.isAnisotropic_iff_heADCN2QuaternaryOne hrank).mp han
  obtain ⟨g⟩ := heADCN2QuaternaryOne_isIsometric_A_product_scaledA (K := K)
  exact ⟨f.trans g⟩

end Lattice

end Bong
