/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NecessityAdaptedBasis

/-!
# O'Meara 93:28 necessity: orthogonalizing the projected adapted basis

In Step 1 of the necessity proof, the adapted source basis is transported
through the residual isometry and projected to the target head.  Its Gram
matrix is congruent to the source Gram matrix modulo the relative second
Jordan scale.  The first projected binary block is therefore unimodular.
Solving its two-by-two Gram system orthogonalizes the last two projected
vectors, and the exact ideal congruence shows that all correction
coefficients still belong to the relative second-scale ideal.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- An integral scalar preserves membership in a coefficient ideal. -/
theorem mul_mem_coefficientIdeal_of_isIntegral_left
    {a x : K} {I : CoefficientIdeal (K := K)}
    (ha : Dyadic.IsIntegral K a) (hx : x ∈ I) : a * x ∈ I := by
  let aO : IntegerRing K := ⟨a, (mem_integerRing_iff K).2 ha⟩
  have h := I.smul_mem aO hx
  change a * x ∈ I at h
  exact h

/-- Cramer's-rule identity for the first row of a symmetric binary Gram
system. -/
theorem binaryGramSolve_left {A B C p q : K}
    (hdet : A * C - B ^ 2 ≠ 0) :
    p + ((-C * p + B * q) / (A * C - B ^ 2)) * A +
      ((B * p - A * q) / (A * C - B ^ 2)) * B = 0 := by
  have hdet' : C * A - B ^ 2 ≠ 0 := by
    simpa only [mul_comm] using hdet
  field_simp [hdet, hdet']
  ring

/-- Cramer's-rule identity for the second row of a symmetric binary Gram
system. -/
theorem binaryGramSolve_right {A B C p q : K}
    (hdet : A * C - B ^ 2 ≠ 0) :
    q + ((-C * p + B * q) / (A * C - B ^ 2)) * B +
      ((B * p - A * q) / (A * C - B ^ 2)) * C = 0 := by
  have hdet' : C * A - B ^ 2 ≠ 0 := by
    simpa only [mul_comm] using hdet
  field_simp [hdet, hdet']
  ring

/-- Ideal-valued Cramer's rule for the first numerator. -/
theorem binaryCramerZero_mem_coefficientIdeal
    {I : CoefficientIdeal (K := K)} {B C p q D : K}
    (hC : Dyadic.IsIntegral K C) (hB : Dyadic.IsIntegral K B)
    (hp : p ∈ I) (hq : q ∈ I)
    (hDinv : Dyadic.IsIntegral K D⁻¹) :
    (-C * p + B * q) / D ∈ I := by
  have hCp : C * p ∈ I :=
    mul_mem_coefficientIdeal_of_isIntegral_left hC hp
  have hBq : B * q ∈ I :=
    mul_mem_coefficientIdeal_of_isIntegral_left hB hq
  have hnum : -C * p + B * q ∈ I := by
    convert I.add_mem (I.neg_mem hCp) hBq using 1 <;> ring
  have hquot : D⁻¹ * (-C * p + B * q) ∈ I :=
    mul_mem_coefficientIdeal_of_isIntegral_left hDinv hnum
  rw [div_eq_mul_inv]
  simpa only [mul_comm] using hquot

/-- Ideal-valued Cramer's rule for the second numerator. -/
theorem binaryCramerOne_mem_coefficientIdeal
    {I : CoefficientIdeal (K := K)} {A B p q D : K}
    (hB : Dyadic.IsIntegral K B) (hA : Dyadic.IsIntegral K A)
    (hp : p ∈ I) (hq : q ∈ I)
    (hDinv : Dyadic.IsIntegral K D⁻¹) :
    (B * p - A * q) / D ∈ I := by
  have hBp : B * p ∈ I :=
    mul_mem_coefficientIdeal_of_isIntegral_left hB hp
  have hAq : A * q ∈ I :=
    mul_mem_coefficientIdeal_of_isIntegral_left hA hq
  have hnum : B * p - A * q ∈ I := I.sub_mem hBp hAq
  have hquot : D⁻¹ * (B * p - A * q) ∈ I :=
    mul_mem_coefficientIdeal_of_isIntegral_left hDinv hnum
  rw [div_eq_mul_inv]
  simpa only [mul_comm] using hquot

/-- Adding arbitrary combinations of the first two vectors of a four-vector
basis to its last two vectors preserves linear independence. -/
theorem linearIndependent_finFour_tailShear
    {X : Type*} [AddCommGroup X] [Module K X]
    (b : Basis (Fin 4) K X) (a b₀ c d : K) :
    LinearIndependent K
      ![b 0, b 1, b 2 + a • b 0 + b₀ • b 1,
        b 3 + c • b 0 + d • b 1] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := congrArg b.repr hg
  have h₀ := congrArg (fun v ↦ v (0 : Fin 4)) hr
  have h₁ := congrArg (fun v ↦ v (1 : Fin 4)) hr
  have h₂ := congrArg (fun v ↦ v (2 : Fin 4)) hr
  have h₃ := congrArg (fun v ↦ v (3 : Fin 4)) hr
  simp [Fin.sum_univ_four] at h₀ h₁ h₂ h₃
  fin_cases i
  · simpa [h₂, h₃] using h₀
  · simpa [h₂, h₃] using h₁
  · exact h₂
  · exact h₃

end Lattice

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The projected adapted basis of the normalized target head. -/
noncomputable def projectedAdaptedBasis
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Basis (Fin 4) K (S.targetJordan.component 0).carrier :=
  S.projectedHeadBasis S.sourceHeadAdaptedBasis
    S.sourceHeadAdaptedBasisLattice_eq f

@[simp]
theorem projectedAdaptedBasis_apply
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin 4) :
    S.projectedAdaptedBasis f i =
      S.projectedHeadFamily S.sourceHeadAdaptedBasis f i := by
  exact S.projectedHeadBasis_apply S.sourceHeadAdaptedBasis
    S.sourceHeadAdaptedBasisLattice_eq f i

/-- The first two-by-two Gram block of the projected adapted basis. -/
noncomputable def projectedAdaptedFirstGramMatrix
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Matrix (Fin 2) (Fin 2) K :=
  fun i j ↦ S.targetFirstNormalized.bilin
    (S.projectedAdaptedBasis f (Fin.castAdd 2 i))
    (S.projectedAdaptedBasis f (Fin.castAdd 2 j))

/-- The corresponding first source Gram block. -/
noncomputable def sourceAdaptedFirstGramMatrix :
    Matrix (Fin 2) (Fin 2) K :=
  fun i j ↦ S.sourceFirstNormalized.bilin
    (S.sourceHeadAdaptedBasis (Fin.castAdd 2 i))
    (S.sourceHeadAdaptedBasis (Fin.castAdd 2 j))

theorem sourceAdaptedFirstGramMatrix_eq :
    S.sourceAdaptedFirstGramMatrix =
      !![(S.firstNormGenerator : K), 1; 1, 0] := by
  ext i j
  rw [sourceAdaptedFirstGramMatrix,
    S.sourceHeadAdaptedBasis_bilin]
  fin_cases i <;> fin_cases j <;> rfl

theorem sourceAdaptedFirstGramMatrix_det :
    S.sourceAdaptedFirstGramMatrix.det = (-1 : K) := by
  rw [S.sourceAdaptedFirstGramMatrix_eq]
  simp [Matrix.det_fin_two]

theorem projectedAdaptedFirstGramMatrix_isIntegral
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 2) :
    Dyadic.IsIntegral K (S.projectedAdaptedFirstGramMatrix f i j) := by
  simpa only [projectedAdaptedFirstGramMatrix,
    projectedAdaptedBasis_apply,
    projectedHeadNormalizedGramMatrix, projectedHeadFamily] using
      S.projectedHeadNormalizedGramMatrix_isIntegral
        S.sourceHeadAdaptedBasis S.sourceHeadAdaptedBasisLattice_eq f
        (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem sourceAdaptedFirstGramMatrix_isIntegral (i j : Fin 2) :
    Dyadic.IsIntegral K (S.sourceAdaptedFirstGramMatrix i j) := by
  simpa only [sourceAdaptedFirstGramMatrix,
    sourceHeadNormalizedGramMatrix,
    LinearMap.BilinForm.toMatrix_apply] using
      S.sourceHeadNormalizedGramMatrix_isIntegral
        S.sourceHeadAdaptedBasis S.sourceHeadAdaptedBasisLattice_eq
        (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem projectedAdaptedFirstGramMatrix_sub_source_isInMaximalIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 2) :
    IsInMaximalIdeal K
      (S.projectedAdaptedFirstGramMatrix f i j -
        S.sourceAdaptedFirstGramMatrix i j) := by
  simpa only [projectedAdaptedFirstGramMatrix,
    sourceAdaptedFirstGramMatrix, projectedAdaptedBasis_apply,
    projectedHeadNormalizedGramMatrix, sourceHeadNormalizedGramMatrix,
    projectedHeadFamily, LinearMap.BilinForm.toMatrix_apply] using
      S.projectedHeadNormalizedGramMatrix_sub_source_isInMaximalIdeal
        S.sourceHeadAdaptedBasis S.sourceHeadAdaptedBasisLattice_eq f
        (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem projectedAdaptedFirstGramDet_sub_negOne_isInMaximalIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    IsInMaximalIdeal K
      ((S.projectedAdaptedFirstGramMatrix f).det - (-1 : K)) := by
  rw [← S.sourceAdaptedFirstGramMatrix_det]
  exact isInMaximalIdeal_det_sub_det
    (S.projectedAdaptedFirstGramMatrix f)
    S.sourceAdaptedFirstGramMatrix
    (S.projectedAdaptedFirstGramMatrix_isIntegral f)
    S.sourceAdaptedFirstGramMatrix_isIntegral
    (S.projectedAdaptedFirstGramMatrix_sub_source_isInMaximalIdeal f)

/-- The first projected binary Gram determinant is a valuation unit. -/
theorem projectedAdaptedFirstGramDet_isValuationUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    IsValuationUnit K (S.projectedAdaptedFirstGramMatrix f).det := by
  apply isValuationUnit_of_sub_isInMaximalIdeal
    (b := (-1 : K))
  · simp [IsValuationUnit]
  · exact S.projectedAdaptedFirstGramDet_sub_negOne_isInMaximalIdeal f

/-- First coefficient in the solution of the binary Gram system. -/
noncomputable def projectedOrthogonalCoefficientZero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (z : (S.targetJordan.component 0).carrier) : K :=
  let y := S.projectedAdaptedBasis f
  let B := S.targetFirstNormalized.bilin (y 0) (y 1)
  let C := S.targetFirstNormalized.bilin (y 1) (y 1)
  let p := S.targetFirstNormalized.bilin (y 0) z
  let q := S.targetFirstNormalized.bilin (y 1) z
  (-C * p + B * q) /
    (S.projectedAdaptedFirstGramMatrix f).det

/-- Second coefficient in the solution of the binary Gram system. -/
noncomputable def projectedOrthogonalCoefficientOne
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (z : (S.targetJordan.component 0).carrier) : K :=
  let y := S.projectedAdaptedBasis f
  let A := S.targetFirstNormalized.bilin (y 0) (y 0)
  let B := S.targetFirstNormalized.bilin (y 0) (y 1)
  let p := S.targetFirstNormalized.bilin (y 0) z
  let q := S.targetFirstNormalized.bilin (y 1) z
  (B * p - A * q) /
    (S.projectedAdaptedFirstGramMatrix f).det

/-- Orthogonal projection away from the first projected binary block. -/
noncomputable def orthogonalizeAgainstProjectedFirstPlane
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (z : (S.targetJordan.component 0).carrier) :
    (S.targetJordan.component 0).carrier :=
  z + S.projectedOrthogonalCoefficientZero f z •
      S.projectedAdaptedBasis f 0 +
    S.projectedOrthogonalCoefficientOne f z •
      S.projectedAdaptedBasis f 1

set_option maxHeartbeats 800000 in
theorem projectedAdaptedFirstGramDet_formula
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.projectedAdaptedFirstGramMatrix f).det =
      S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0)
          (S.projectedAdaptedBasis f 0) *
        S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1)
          (S.projectedAdaptedBasis f 1) -
      S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0)
          (S.projectedAdaptedBasis f 1) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [projectedAdaptedFirstGramMatrix]
  change
    S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0)
          (S.projectedAdaptedBasis f 0) *
        S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1)
          (S.projectedAdaptedBasis f 1) -
      S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0)
          (S.projectedAdaptedBasis f 1) *
        S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1)
          (S.projectedAdaptedBasis f 0) = _
  rw [S.targetFirstNormalized.isSymm.eq
    (S.projectedAdaptedBasis f 1) (S.projectedAdaptedBasis f 0)]
  ring

theorem orthogonalizeAgainstProjectedFirstPlane_left
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (z : (S.targetJordan.component 0).carrier) :
    S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0)
      (S.orthogonalizeAgainstProjectedFirstPlane f z) = 0 := by
  have hdetNe : (S.projectedAdaptedFirstGramMatrix f).det ≠ 0 :=
    Lattice.ne_zero_of_isValuationUnit
      (S.projectedAdaptedFirstGramDet_isValuationUnit f)
  rw [S.projectedAdaptedFirstGramDet_formula] at hdetNe
  simp only [orthogonalizeAgainstProjectedFirstPlane,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]
  unfold projectedOrthogonalCoefficientZero
    projectedOrthogonalCoefficientOne
  rw [S.projectedAdaptedFirstGramDet_formula]
  exact Lattice.binaryGramSolve_left hdetNe

set_option maxHeartbeats 800000 in
theorem orthogonalizeAgainstProjectedFirstPlane_right
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (z : (S.targetJordan.component 0).carrier) :
    S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1)
      (S.orthogonalizeAgainstProjectedFirstPlane f z) = 0 := by
  have hdetNe : (S.projectedAdaptedFirstGramMatrix f).det ≠ 0 :=
    Lattice.ne_zero_of_isValuationUnit
      (S.projectedAdaptedFirstGramDet_isValuationUnit f)
  rw [S.projectedAdaptedFirstGramDet_formula] at hdetNe
  simp only [orthogonalizeAgainstProjectedFirstPlane,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]
  unfold projectedOrthogonalCoefficientZero
    projectedOrthogonalCoefficientOne
  rw [S.projectedAdaptedFirstGramDet_formula]
  rw [S.targetFirstNormalized.isSymm.eq
    (S.projectedAdaptedBasis f 1)
    (S.projectedAdaptedBasis f 0)]
  exact Lattice.binaryGramSolve_right hdetNe

set_option maxHeartbeats 800000 in
/-- Every pairing between the first and second projected adapted pairs lies
in the exact relative second-scale ideal. -/
theorem projectedAdaptedFirstTailPairing_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i k : Fin 2) :
    S.targetFirstNormalized.bilin
        (S.projectedAdaptedBasis f (Fin.castAdd 2 i))
        (S.projectedAdaptedBasis f (Fin.natAdd 2 k)) ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  have h :=
    S.projectedHeadNormalizedGramMatrix_sub_source_mem_relativeSecondScaleIdeal
      S.sourceHeadAdaptedBasis S.sourceHeadAdaptedBasisLattice_eq f
      (Fin.castAdd 2 i) (Fin.natAdd 2 k)
  have h' :
      S.targetFirstNormalized.bilin
          (S.projectedAdaptedBasis f (Fin.castAdd 2 i))
          (S.projectedAdaptedBasis f (Fin.natAdd 2 k)) -
        S.sourceFirstNormalized.bilin
          (S.sourceHeadAdaptedBasis (Fin.castAdd 2 i))
          (S.sourceHeadAdaptedBasis (Fin.natAdd 2 k)) ∈
        principalIdeal (K := K) (S.relativeSecondScale : K) := by
    simpa only [projectedHeadNormalizedGramMatrix,
      sourceHeadNormalizedGramMatrix,
      LinearMap.BilinForm.toMatrix_apply,
      projectedAdaptedBasis_apply, projectedHeadFamily] using h
  rw [S.sourceHeadAdaptedBasis_bilin] at h'
  fin_cases i <;> fin_cases k <;> simpa using h'

/-- The relative second-scale ideal is integral (indeed, it is contained
in the maximal ideal). -/
theorem relativeSecondScaleIdeal_le_unitIdeal :
    principalIdeal (K := K) (S.relativeSecondScale : K) ≤
      unitIdeal (K := K) := by
  unfold unitIdeal
  apply (principalIdeal_le_iff_ord_ge
    (Units.ne_zero S.relativeSecondScale) one_ne_zero).2
  rw [ord_one]
  exact le_of_lt S.relativeSecondScale_isInMaximalIdeal

theorem mem_integerRing_of_mem_relativeSecondScaleIdeal
    {x : K}
    (hx : x ∈ principalIdeal (K := K) (S.relativeSecondScale : K)) :
    x ∈ IntegerRing K := by
  rw [← mem_unitIdeal_iff]
  exact S.relativeSecondScaleIdeal_le_unitIdeal hx

private theorem projectedAdaptedGramEntry_isIntegral
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 4) :
    Dyadic.IsIntegral K
      (S.targetFirstNormalized.bilin
        (S.projectedAdaptedBasis f i)
        (S.projectedAdaptedBasis f j)) := by
  simpa only [projectedAdaptedBasis_apply,
    projectedHeadNormalizedGramMatrix, projectedHeadFamily] using
      S.projectedHeadNormalizedGramMatrix_isIntegral
        S.sourceHeadAdaptedBasis S.sourceHeadAdaptedBasisLattice_eq f i j

private theorem projectedAdaptedFirstGramDet_inv_isIntegral
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Dyadic.IsIntegral K (S.projectedAdaptedFirstGramMatrix f).det⁻¹ := by
  have hunit := S.projectedAdaptedFirstGramDet_isValuationUnit f
  have hinv : IsValuationUnit K
      (S.projectedAdaptedFirstGramMatrix f).det⁻¹ := by
    simpa [IsValuationUnit, AddValuation.map_inv, hunit]
  exact hinv.ge

/-- Cramer's first correction coefficient stays in the prescribed ideal. -/
theorem projectedOrthogonalCoefficientZero_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (z : (S.targetJordan.component 0).carrier)
    (hp : S.targetFirstNormalized.bilin
        (S.projectedAdaptedBasis f 0) z ∈
      principalIdeal (K := K) (S.relativeSecondScale : K))
    (hq : S.targetFirstNormalized.bilin
        (S.projectedAdaptedBasis f 1) z ∈
      principalIdeal (K := K) (S.relativeSecondScale : K)) :
    S.projectedOrthogonalCoefficientZero f z ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  unfold projectedOrthogonalCoefficientZero
  exact Lattice.binaryCramerZero_mem_coefficientIdeal
    (I := principalIdeal (K := K) (S.relativeSecondScale : K))
    (C := S.targetFirstNormalized.bilin
      (S.projectedAdaptedBasis f 1) (S.projectedAdaptedBasis f 1))
    (B := S.targetFirstNormalized.bilin
      (S.projectedAdaptedBasis f 0) (S.projectedAdaptedBasis f 1))
    (p := S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0) z)
    (q := S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1) z)
    (D := (S.projectedAdaptedFirstGramMatrix f).det)
    (S.projectedAdaptedGramEntry_isIntegral f 1 1)
    (S.projectedAdaptedGramEntry_isIntegral f 0 1)
    hp hq (S.projectedAdaptedFirstGramDet_inv_isIntegral f)

/-- Cramer's second correction coefficient stays in the prescribed ideal. -/
theorem projectedOrthogonalCoefficientOne_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (z : (S.targetJordan.component 0).carrier)
    (hp : S.targetFirstNormalized.bilin
        (S.projectedAdaptedBasis f 0) z ∈
      principalIdeal (K := K) (S.relativeSecondScale : K))
    (hq : S.targetFirstNormalized.bilin
        (S.projectedAdaptedBasis f 1) z ∈
      principalIdeal (K := K) (S.relativeSecondScale : K)) :
    S.projectedOrthogonalCoefficientOne f z ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  unfold projectedOrthogonalCoefficientOne
  exact Lattice.binaryCramerOne_mem_coefficientIdeal
    (I := principalIdeal (K := K) (S.relativeSecondScale : K))
    (B := S.targetFirstNormalized.bilin
      (S.projectedAdaptedBasis f 0) (S.projectedAdaptedBasis f 1))
    (A := S.targetFirstNormalized.bilin
      (S.projectedAdaptedBasis f 0) (S.projectedAdaptedBasis f 0))
    (p := S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0) z)
    (q := S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1) z)
    (D := (S.projectedAdaptedFirstGramMatrix f).det)
    (S.projectedAdaptedGramEntry_isIntegral f 0 1)
    (S.projectedAdaptedGramEntry_isIntegral f 0 0)
    hp hq (S.projectedAdaptedFirstGramDet_inv_isIntegral f)

theorem projectedOrthogonalCoefficientZero_tail_mem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (k : Fin 2) :
    S.projectedOrthogonalCoefficientZero f
        (S.projectedAdaptedBasis f (Fin.natAdd 2 k)) ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  apply S.projectedOrthogonalCoefficientZero_mem_relativeSecondScaleIdeal
  · simpa using
      S.projectedAdaptedFirstTailPairing_mem_relativeSecondScaleIdeal f 0 k
  · simpa using
      S.projectedAdaptedFirstTailPairing_mem_relativeSecondScaleIdeal f 1 k

theorem projectedOrthogonalCoefficientOne_tail_mem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (k : Fin 2) :
    S.projectedOrthogonalCoefficientOne f
        (S.projectedAdaptedBasis f (Fin.natAdd 2 k)) ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  apply S.projectedOrthogonalCoefficientOne_mem_relativeSecondScaleIdeal
  · simpa using
      S.projectedAdaptedFirstTailPairing_mem_relativeSecondScaleIdeal f 0 k
  · simpa using
      S.projectedAdaptedFirstTailPairing_mem_relativeSecondScaleIdeal f 1 k

/-- The projected adapted family after orthogonalizing its last two vectors
against the first binary block. -/
noncomputable def orthogonalizedProjectedAdaptedFamily
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Fin 4 → (S.targetJordan.component 0).carrier :=
  ![S.projectedAdaptedBasis f 0,
    S.projectedAdaptedBasis f 1,
    S.orthogonalizeAgainstProjectedFirstPlane f
      (S.projectedAdaptedBasis f 2),
    S.orthogonalizeAgainstProjectedFirstPlane f
      (S.projectedAdaptedBasis f 3)]

@[simp]
theorem orthogonalizedProjectedAdaptedFamily_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.orthogonalizedProjectedAdaptedFamily f 0 =
      S.projectedAdaptedBasis f 0 := by
  simp [orthogonalizedProjectedAdaptedFamily]

@[simp]
theorem orthogonalizedProjectedAdaptedFamily_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.orthogonalizedProjectedAdaptedFamily f 1 =
      S.projectedAdaptedBasis f 1 := by
  simp [orthogonalizedProjectedAdaptedFamily]

@[simp]
theorem orthogonalizedProjectedAdaptedFamily_two
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.orthogonalizedProjectedAdaptedFamily f 2 =
      S.orthogonalizeAgainstProjectedFirstPlane f
        (S.projectedAdaptedBasis f 2) := by
  simp [orthogonalizedProjectedAdaptedFamily]

@[simp]
theorem orthogonalizedProjectedAdaptedFamily_three
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.orthogonalizedProjectedAdaptedFamily f 3 =
      S.orthogonalizeAgainstProjectedFirstPlane f
        (S.projectedAdaptedBasis f 3) := by
  simp [orthogonalizedProjectedAdaptedFamily]

/-- Orthogonalizing the last two projected vectors preserves linear
independence. -/
theorem orthogonalizedProjectedAdaptedFamily_linearIndependent
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    LinearIndependent K (S.orthogonalizedProjectedAdaptedFamily f) := by
  simpa only [orthogonalizedProjectedAdaptedFamily,
    orthogonalizeAgainstProjectedFirstPlane] using
      Lattice.linearIndependent_finFour_tailShear
        (S.projectedAdaptedBasis f)
        (S.projectedOrthogonalCoefficientZero f
          (S.projectedAdaptedBasis f 2))
        (S.projectedOrthogonalCoefficientOne f
          (S.projectedAdaptedBasis f 2))
        (S.projectedOrthogonalCoefficientZero f
          (S.projectedAdaptedBasis f 3))
        (S.projectedOrthogonalCoefficientOne f
          (S.projectedAdaptedBasis f 3))

/-- The orthogonalized projected family as an ambient basis. -/
noncomputable def orthogonalizedProjectedAdaptedBasis
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Basis (Fin 4) K (S.targetJordan.component 0).carrier := by
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  exact basisOfLinearIndependentOfCardEqFinrank'
    (S.orthogonalizedProjectedAdaptedFamily f)
    (S.orthogonalizedProjectedAdaptedFamily_linearIndependent f)
    (by simpa using S.targetFirstNormalized_finrank.symm)

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_apply
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin 4) :
    S.orthogonalizedProjectedAdaptedBasis f i =
      S.orthogonalizedProjectedAdaptedFamily f i := by
  simp [orthogonalizedProjectedAdaptedBasis]

private theorem projectedOrthogonalCoefficientZero_tail_integral
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (k : Fin 2) :
    S.projectedOrthogonalCoefficientZero f
        (S.projectedAdaptedBasis f (Fin.natAdd 2 k)) ∈ IntegerRing K :=
  S.mem_integerRing_of_mem_relativeSecondScaleIdeal
    (S.projectedOrthogonalCoefficientZero_tail_mem f k)

private theorem projectedOrthogonalCoefficientOne_tail_integral
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (k : Fin 2) :
    S.projectedOrthogonalCoefficientOne f
        (S.projectedAdaptedBasis f (Fin.natAdd 2 k)) ∈ IntegerRing K :=
  S.mem_integerRing_of_mem_relativeSecondScaleIdeal
    (S.projectedOrthogonalCoefficientOne_tail_mem f k)

/-- The unmodified projected adapted basis is an integral basis of the
target head. -/
theorem projectedAdaptedBasisLattice_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    basisLattice (S.projectedAdaptedBasis f) =
      (S.targetJordan.component 0).lattice :=
  S.projectedHeadBasisLattice_eq S.sourceHeadAdaptedBasis
    S.sourceHeadAdaptedBasisLattice_eq f

theorem projectedAdaptedBasis_mem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin 4) :
    S.projectedAdaptedBasis f i ∈
      (S.targetJordan.component 0).lattice :=
  S.projectedHeadBasis_mem S.sourceHeadAdaptedBasis
    S.sourceHeadAdaptedBasisLattice_eq f i

/-- An integral Cramer correction of an integral vector stays in the
target lattice. -/
theorem orthogonalizeAgainstProjectedFirstPlane_mem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (z : (S.targetJordan.component 0).carrier)
    (hz : z ∈ (S.targetJordan.component 0).lattice)
    (hc₀ : S.projectedOrthogonalCoefficientZero f z ∈ IntegerRing K)
    (hc₁ : S.projectedOrthogonalCoefficientOne f z ∈ IntegerRing K) :
    S.orthogonalizeAgainstProjectedFirstPlane f z ∈
      (S.targetJordan.component 0).lattice := by
  let c₀O : IntegerRing K :=
    ⟨S.projectedOrthogonalCoefficientZero f z, hc₀⟩
  let c₁O : IntegerRing K :=
    ⟨S.projectedOrthogonalCoefficientOne f z, hc₁⟩
  have hzero := S.projectedAdaptedBasis_mem f 0
  have hone := S.projectedAdaptedBasis_mem f 1
  have hc₀smul : S.projectedOrthogonalCoefficientZero f z •
      S.projectedAdaptedBasis f 0 ∈
        (S.targetJordan.component 0).lattice := by
    change (c₀O : K) • S.projectedAdaptedBasis f 0 ∈
      (S.targetJordan.component 0).lattice
    exact (S.targetJordan.component 0).lattice.smul_mem c₀O hzero
  have hc₁smul : S.projectedOrthogonalCoefficientOne f z •
      S.projectedAdaptedBasis f 1 ∈
        (S.targetJordan.component 0).lattice := by
    change (c₁O : K) • S.projectedAdaptedBasis f 1 ∈
      (S.targetJordan.component 0).lattice
    exact (S.targetJordan.component 0).lattice.smul_mem c₁O hone
  exact (S.targetJordan.component 0).lattice.add_mem
    ((S.targetJordan.component 0).lattice.add_mem hz hc₀smul) hc₁smul

theorem orthogonalizedProjectedAdaptedFamily_mem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin 4) :
    S.orthogonalizedProjectedAdaptedFamily f i ∈
      (S.targetJordan.component 0).lattice := by
  fin_cases i
  · change S.projectedAdaptedBasis f 0 ∈
      (S.targetJordan.component 0).lattice
    exact S.projectedAdaptedBasis_mem f 0
  · change S.projectedAdaptedBasis f 1 ∈
      (S.targetJordan.component 0).lattice
    exact S.projectedAdaptedBasis_mem f 1
  · change S.orthogonalizeAgainstProjectedFirstPlane f
        (S.projectedAdaptedBasis f 2) ∈
      (S.targetJordan.component 0).lattice
    apply S.orthogonalizeAgainstProjectedFirstPlane_mem f
    · exact S.projectedAdaptedBasis_mem f 2
    · have h :=
          S.projectedOrthogonalCoefficientZero_tail_integral f (0 : Fin 2)
      have hk : Fin.natAdd 2 (0 : Fin 2) = (2 : Fin 4) := by ext; rfl
      rw [hk] at h
      exact h
    · have h :=
          S.projectedOrthogonalCoefficientOne_tail_integral f (0 : Fin 2)
      have hk : Fin.natAdd 2 (0 : Fin 2) = (2 : Fin 4) := by ext; rfl
      rw [hk] at h
      exact h
  · change S.orthogonalizeAgainstProjectedFirstPlane f
        (S.projectedAdaptedBasis f 3) ∈
      (S.targetJordan.component 0).lattice
    apply S.orthogonalizeAgainstProjectedFirstPlane_mem f
    · exact S.projectedAdaptedBasis_mem f 3
    · have h :=
          S.projectedOrthogonalCoefficientZero_tail_integral f (1 : Fin 2)
      have hk : Fin.natAdd 2 (1 : Fin 2) = (3 : Fin 4) := by ext; rfl
      rw [hk] at h
      exact h
    · have h :=
          S.projectedOrthogonalCoefficientOne_tail_integral f (1 : Fin 2)
      have hk : Fin.natAdd 2 (1 : Fin 2) = (3 : Fin 4) := by ext; rfl
      rw [hk] at h
      exact h

/-- The orthogonalized basis lattice is contained in the target head. -/
theorem orthogonalizedProjectedAdaptedBasisLattice_le
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    basisLattice (S.orthogonalizedProjectedAdaptedBasis f) ≤
      (S.targetJordan.component 0).lattice := by
  change Submodule.span (IntegerRing K)
      (Set.range (S.orthogonalizedProjectedAdaptedBasis f)) ≤
    (S.targetJordan.component 0).lattice.toSubmodule
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [S.orthogonalizedProjectedAdaptedBasis_apply]
  exact S.orthogonalizedProjectedAdaptedFamily_mem f i

private theorem projectedAdaptedTail_mem_orthogonalizedBasisLattice
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (k : Fin 2) :
    S.projectedAdaptedBasis f (Fin.natAdd 2 k) ∈
      basisLattice (S.orthogonalizedProjectedAdaptedBasis f) := by
  let P := basisLattice (S.orthogonalizedProjectedAdaptedBasis f)
  have hzero : S.projectedAdaptedBasis f 0 ∈ P := by
    change S.projectedAdaptedBasis f 0 ∈
      Submodule.span (IntegerRing K)
        (Set.range (S.orthogonalizedProjectedAdaptedBasis f))
    apply Submodule.subset_span
    refine ⟨0, ?_⟩
    rw [S.orthogonalizedProjectedAdaptedBasis_apply,
      S.orthogonalizedProjectedAdaptedFamily_zero]
  have hone : S.projectedAdaptedBasis f 1 ∈ P := by
    change S.projectedAdaptedBasis f 1 ∈
      Submodule.span (IntegerRing K)
        (Set.range (S.orthogonalizedProjectedAdaptedBasis f))
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    rw [S.orthogonalizedProjectedAdaptedBasis_apply,
      S.orthogonalizedProjectedAdaptedFamily_one]
  fin_cases k
  · have hk : Fin.natAdd 2 (0 : Fin 2) = (2 : Fin 4) := by ext; rfl
    change S.projectedAdaptedBasis f 2 ∈
      basisLattice (S.orthogonalizedProjectedAdaptedBasis f)
    let c₀ := S.projectedOrthogonalCoefficientZero f
      (S.projectedAdaptedBasis f 2)
    let c₁ := S.projectedOrthogonalCoefficientOne f
      (S.projectedAdaptedBasis f 2)
    let c₀O : IntegerRing K := ⟨c₀, by
      have h := S.projectedOrthogonalCoefficientZero_tail_integral
        f (0 : Fin 2)
      rw [hk] at h
      simpa only [c₀] using h⟩
    let c₁O : IntegerRing K := ⟨c₁, by
      have h := S.projectedOrthogonalCoefficientOne_tail_integral
        f (0 : Fin 2)
      rw [hk] at h
      simpa only [c₁] using h⟩
    have htwo : S.orthogonalizedProjectedAdaptedBasis f 2 ∈ P := by
      change S.orthogonalizedProjectedAdaptedBasis f 2 ∈
        Submodule.span (IntegerRing K)
          (Set.range (S.orthogonalizedProjectedAdaptedBasis f))
      exact Submodule.subset_span ⟨2, rfl⟩
    have hc₀ : c₀ • S.projectedAdaptedBasis f 0 ∈ P := by
      change (c₀O : K) • S.projectedAdaptedBasis f 0 ∈ P
      exact P.smul_mem c₀O hzero
    have hc₁ : c₁ • S.projectedAdaptedBasis f 1 ∈ P := by
      change (c₁O : K) • S.projectedAdaptedBasis f 1 ∈ P
      exact P.smul_mem c₁O hone
    have hsub := P.sub_mem (P.sub_mem htwo hc₀) hc₁
    have heq : S.projectedAdaptedBasis f 2 =
        S.orthogonalizedProjectedAdaptedBasis f 2 -
          c₀ • S.projectedAdaptedBasis f 0 -
          c₁ • S.projectedAdaptedBasis f 1 := by
      rw [S.orthogonalizedProjectedAdaptedBasis_apply,
        S.orthogonalizedProjectedAdaptedFamily_two,
        orthogonalizeAgainstProjectedFirstPlane]
      module
    rw [heq]
    exact hsub
  · have hk : Fin.natAdd 2 (1 : Fin 2) = (3 : Fin 4) := by ext; rfl
    change S.projectedAdaptedBasis f 3 ∈
      basisLattice (S.orthogonalizedProjectedAdaptedBasis f)
    let c₀ := S.projectedOrthogonalCoefficientZero f
      (S.projectedAdaptedBasis f 3)
    let c₁ := S.projectedOrthogonalCoefficientOne f
      (S.projectedAdaptedBasis f 3)
    let c₀O : IntegerRing K := ⟨c₀, by
      have h := S.projectedOrthogonalCoefficientZero_tail_integral
        f (1 : Fin 2)
      rw [hk] at h
      simpa only [c₀] using h⟩
    let c₁O : IntegerRing K := ⟨c₁, by
      have h := S.projectedOrthogonalCoefficientOne_tail_integral
        f (1 : Fin 2)
      rw [hk] at h
      simpa only [c₁] using h⟩
    have hthree : S.orthogonalizedProjectedAdaptedBasis f 3 ∈ P := by
      change S.orthogonalizedProjectedAdaptedBasis f 3 ∈
        Submodule.span (IntegerRing K)
          (Set.range (S.orthogonalizedProjectedAdaptedBasis f))
      exact Submodule.subset_span ⟨3, rfl⟩
    have hc₀ : c₀ • S.projectedAdaptedBasis f 0 ∈ P := by
      change (c₀O : K) • S.projectedAdaptedBasis f 0 ∈ P
      exact P.smul_mem c₀O hzero
    have hc₁ : c₁ • S.projectedAdaptedBasis f 1 ∈ P := by
      change (c₁O : K) • S.projectedAdaptedBasis f 1 ∈ P
      exact P.smul_mem c₁O hone
    have hsub := P.sub_mem (P.sub_mem hthree hc₀) hc₁
    have heq : S.projectedAdaptedBasis f 3 =
        S.orthogonalizedProjectedAdaptedBasis f 3 -
          c₀ • S.projectedAdaptedBasis f 0 -
          c₁ • S.projectedAdaptedBasis f 1 := by
      rw [S.orthogonalizedProjectedAdaptedBasis_apply,
        S.orthogonalizedProjectedAdaptedFamily_three,
        orthogonalizeAgainstProjectedFirstPlane]
      module
    rw [heq]
    exact hsub

/-- The orthogonalized vectors remain an integral basis of the target
head. -/
theorem orthogonalizedProjectedAdaptedBasisLattice_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    basisLattice (S.orthogonalizedProjectedAdaptedBasis f) =
      (S.targetJordan.component 0).lattice := by
  apply Lattice.ext
  apply le_antisymm
  · exact S.orthogonalizedProjectedAdaptedBasisLattice_le f
  · rw [← S.projectedAdaptedBasisLattice_eq f]
    change Submodule.span (IntegerRing K)
        (Set.range (S.projectedAdaptedBasis f)) ≤
      (basisLattice (S.orthogonalizedProjectedAdaptedBasis f)).toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change S.projectedAdaptedBasis f 0 ∈
        Submodule.span (IntegerRing K)
          (Set.range (S.orthogonalizedProjectedAdaptedBasis f))
      apply Submodule.subset_span
      refine ⟨0, ?_⟩
      rw [S.orthogonalizedProjectedAdaptedBasis_apply,
        S.orthogonalizedProjectedAdaptedFamily_zero]
    · change S.projectedAdaptedBasis f 1 ∈
        Submodule.span (IntegerRing K)
          (Set.range (S.orthogonalizedProjectedAdaptedBasis f))
      apply Submodule.subset_span
      refine ⟨1, ?_⟩
      rw [S.orthogonalizedProjectedAdaptedBasis_apply,
        S.orthogonalizedProjectedAdaptedFamily_one]
    · simpa using
        S.projectedAdaptedTail_mem_orthogonalizedBasisLattice f (0 : Fin 2)
    · simpa using
        S.projectedAdaptedTail_mem_orthogonalizedBasisLattice f (1 : Fin 2)

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.orthogonalizedProjectedAdaptedBasis f 0 =
      S.projectedAdaptedBasis f 0 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_apply,
    S.orthogonalizedProjectedAdaptedFamily_zero]

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.orthogonalizedProjectedAdaptedBasis f 1 =
      S.projectedAdaptedBasis f 1 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_apply,
    S.orthogonalizedProjectedAdaptedFamily_one]

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_two
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.orthogonalizedProjectedAdaptedBasis f 2 =
      S.orthogonalizeAgainstProjectedFirstPlane f
        (S.projectedAdaptedBasis f 2) := by
  rw [S.orthogonalizedProjectedAdaptedBasis_apply,
    S.orthogonalizedProjectedAdaptedFamily_two]

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_three
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.orthogonalizedProjectedAdaptedBasis f 3 =
      S.orthogonalizeAgainstProjectedFirstPlane f
        (S.projectedAdaptedBasis f 3) := by
  rw [S.orthogonalizedProjectedAdaptedBasis_apply,
    S.orthogonalizedProjectedAdaptedFamily_three]

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_bilin_zero_two
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
      (S.orthogonalizedProjectedAdaptedBasis f 0)
      (S.orthogonalizedProjectedAdaptedBasis f 2) = 0 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_zero,
    S.orthogonalizedProjectedAdaptedBasis_two]
  exact S.orthogonalizeAgainstProjectedFirstPlane_left f
    (S.projectedAdaptedBasis f 2)

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_bilin_zero_three
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
      (S.orthogonalizedProjectedAdaptedBasis f 0)
      (S.orthogonalizedProjectedAdaptedBasis f 3) = 0 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_zero,
    S.orthogonalizedProjectedAdaptedBasis_three]
  exact S.orthogonalizeAgainstProjectedFirstPlane_left f
    (S.projectedAdaptedBasis f 3)

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_bilin_one_two
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
      (S.orthogonalizedProjectedAdaptedBasis f 1)
      (S.orthogonalizedProjectedAdaptedBasis f 2) = 0 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_one,
    S.orthogonalizedProjectedAdaptedBasis_two]
  exact S.orthogonalizeAgainstProjectedFirstPlane_right f
    (S.projectedAdaptedBasis f 2)

@[simp]
theorem orthogonalizedProjectedAdaptedBasis_bilin_one_three
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
      (S.orthogonalizedProjectedAdaptedBasis f 1)
      (S.orthogonalizedProjectedAdaptedBasis f 3) = 0 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_one,
    S.orthogonalizedProjectedAdaptedBasis_three]
  exact S.orthogonalizeAgainstProjectedFirstPlane_right f
    (S.projectedAdaptedBasis f 3)

set_option maxHeartbeats 1000000 in
/-- Pairing two orthogonalized vectors differs from their original pairing
by an element of the coefficient ideal whenever the two correction
coefficients are in that ideal. -/
theorem orthogonalizedPairing_sub_mem_coefficientIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (I : CoefficientIdeal (K := K))
    (z w : (S.targetJordan.component 0).carrier)
    (hα : S.projectedOrthogonalCoefficientZero f z ∈ I)
    (hβ : S.projectedOrthogonalCoefficientOne f z ∈ I)
    (h₀w : Dyadic.IsIntegral K
      (S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0) w))
    (h₁w : Dyadic.IsIntegral K
      (S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1) w)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizeAgainstProjectedFirstPlane f z)
        (S.orthogonalizeAgainstProjectedFirstPlane f w) -
      S.targetFirstNormalized.bilin z w ∈ I := by
  have hαterm : S.projectedOrthogonalCoefficientZero f z *
      S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0) w ∈ I := by
    have h := Lattice.mul_mem_coefficientIdeal_of_isIntegral_left h₀w hα
    simpa only [mul_comm] using h
  have hβterm : S.projectedOrthogonalCoefficientOne f z *
      S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1) w ∈ I := by
    have h := Lattice.mul_mem_coefficientIdeal_of_isIntegral_left h₁w hβ
    simpa only [mul_comm] using h
  have hformula :
      S.targetFirstNormalized.bilin
          (S.orthogonalizeAgainstProjectedFirstPlane f z)
          (S.orthogonalizeAgainstProjectedFirstPlane f w) -
        S.targetFirstNormalized.bilin z w =
      S.projectedOrthogonalCoefficientZero f z *
          S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 0) w +
        S.projectedOrthogonalCoefficientOne f z *
          S.targetFirstNormalized.bilin (S.projectedAdaptedBasis f 1) w := by
    have h₀ := S.orthogonalizeAgainstProjectedFirstPlane_left f z
    have h₁ := S.orthogonalizeAgainstProjectedFirstPlane_right f z
    calc
      S.targetFirstNormalized.bilin
            (S.orthogonalizeAgainstProjectedFirstPlane f z)
            (S.orthogonalizeAgainstProjectedFirstPlane f w) -
          S.targetFirstNormalized.bilin z w =
        S.targetFirstNormalized.bilin
            (S.orthogonalizeAgainstProjectedFirstPlane f z) w -
          S.targetFirstNormalized.bilin z w := by
        rw [show S.orthogonalizeAgainstProjectedFirstPlane f w =
            w + S.projectedOrthogonalCoefficientZero f w •
                S.projectedAdaptedBasis f 0 +
              S.projectedOrthogonalCoefficientOne f w •
                S.projectedAdaptedBasis f 1 by rfl]
        simp only [LinearMap.BilinForm.add_right,
          LinearMap.BilinForm.smul_right]
        rw [S.targetFirstNormalized.isSymm.eq
            (S.orthogonalizeAgainstProjectedFirstPlane f z)
            (S.projectedAdaptedBasis f 0),
          S.targetFirstNormalized.isSymm.eq
            (S.orthogonalizeAgainstProjectedFirstPlane f z)
            (S.projectedAdaptedBasis f 1), h₀, h₁]
        ring
      _ = _ := by
        rw [show S.orthogonalizeAgainstProjectedFirstPlane f z =
            z + S.projectedOrthogonalCoefficientZero f z •
                S.projectedAdaptedBasis f 0 +
              S.projectedOrthogonalCoefficientOne f z •
                S.projectedAdaptedBasis f 1 by rfl]
        simp only [LinearMap.BilinForm.add_left,
          LinearMap.BilinForm.smul_left]
        ring
  rw [hformula]
  exact I.add_mem hαterm hβterm

/-- On the tail indices, the orthogonalized basis is obtained by applying
the binary Gram projection to the corresponding projected adapted vector. -/
theorem orthogonalizedProjectedAdaptedBasis_tail_apply
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i : Fin 2) :
    S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 i) =
      S.orthogonalizeAgainstProjectedFirstPlane f
        (S.projectedAdaptedBasis f (Fin.natAdd 2 i)) := by
  fin_cases i <;> simp

/-- The second binary Gram block before orthogonalization. -/
noncomputable def projectedAdaptedSecondGramMatrix
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Matrix (Fin 2) (Fin 2) K :=
  fun i j ↦ S.targetFirstNormalized.bilin
    (S.projectedAdaptedBasis f (Fin.natAdd 2 i))
    (S.projectedAdaptedBasis f (Fin.natAdd 2 j))

/-- The second binary Gram block after orthogonalization. -/
noncomputable def orthogonalizedSecondGramMatrix
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Matrix (Fin 2) (Fin 2) K :=
  fun i j ↦ S.targetFirstNormalized.bilin
    (S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 i))
    (S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 j))

/-- The corresponding second source Gram block. -/
noncomputable def sourceAdaptedSecondGramMatrix :
    Matrix (Fin 2) (Fin 2) K :=
  fun i j ↦ S.sourceFirstNormalized.bilin
    (S.sourceHeadAdaptedBasis (Fin.natAdd 2 i))
    (S.sourceHeadAdaptedBasis (Fin.natAdd 2 j))

theorem sourceAdaptedSecondGramMatrix_eq :
    S.sourceAdaptedSecondGramMatrix =
      !![(S.sourceHeadAdaptedModelData.secondCoefficient : K), 1;
         1, 0] := by
  ext i j
  rw [sourceAdaptedSecondGramMatrix,
    S.sourceHeadAdaptedBasis_bilin]
  fin_cases i <;> fin_cases j <;> rfl

theorem sourceAdaptedSecondGramMatrix_det :
    S.sourceAdaptedSecondGramMatrix.det = (-1 : K) := by
  rw [S.sourceAdaptedSecondGramMatrix_eq]
  simp [Matrix.det_fin_two]

/-- Orthogonalization changes every entry of the second binary block only
by an element of the relative second-scale ideal. -/
theorem orthogonalizedSecondGramMatrix_sub_projected_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 2) :
    S.orthogonalizedSecondGramMatrix f i j -
        S.projectedAdaptedSecondGramMatrix f i j ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  rw [orthogonalizedSecondGramMatrix,
    projectedAdaptedSecondGramMatrix,
    S.orthogonalizedProjectedAdaptedBasis_tail_apply f i,
    S.orthogonalizedProjectedAdaptedBasis_tail_apply f j]
  exact S.orthogonalizedPairing_sub_mem_coefficientIdeal f
    (principalIdeal (K := K) (S.relativeSecondScale : K))
    (S.projectedAdaptedBasis f (Fin.natAdd 2 i))
    (S.projectedAdaptedBasis f (Fin.natAdd 2 j))
    (S.projectedOrthogonalCoefficientZero_tail_mem f i)
    (S.projectedOrthogonalCoefficientOne_tail_mem f i)
    (S.projectedAdaptedGramEntry_isIntegral f 0 (Fin.natAdd 2 j))
    (S.projectedAdaptedGramEntry_isIntegral f 1 (Fin.natAdd 2 j))

/-- Projection changes every entry of the second binary block only by an
element of the relative second-scale ideal. -/
theorem projectedAdaptedSecondGramMatrix_sub_source_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 2) :
    S.projectedAdaptedSecondGramMatrix f i j -
        S.sourceAdaptedSecondGramMatrix i j ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  simpa only [projectedAdaptedSecondGramMatrix,
    sourceAdaptedSecondGramMatrix,
    projectedAdaptedBasis_apply, projectedHeadNormalizedGramMatrix,
    sourceHeadNormalizedGramMatrix, projectedHeadFamily,
    LinearMap.BilinForm.toMatrix_apply] using
      S.projectedHeadNormalizedGramMatrix_sub_source_mem_relativeSecondScaleIdeal
        S.sourceHeadAdaptedBasis S.sourceHeadAdaptedBasisLattice_eq f
        (Fin.natAdd 2 i) (Fin.natAdd 2 j)

/-- The orthogonalized second block remains congruent to the adapted source
block modulo the exact relative second-scale ideal. -/
theorem orthogonalizedSecondGramMatrix_sub_source_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 2) :
    S.orthogonalizedSecondGramMatrix f i j -
        S.sourceAdaptedSecondGramMatrix i j ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  have h₁ :=
    S.orthogonalizedSecondGramMatrix_sub_projected_mem_relativeSecondScaleIdeal
      f i j
  have h₂ :=
    S.projectedAdaptedSecondGramMatrix_sub_source_mem_relativeSecondScaleIdeal
      f i j
  convert (principalIdeal (K := K) (S.relativeSecondScale : K)).add_mem h₁ h₂
    using 1 <;> ring

theorem projectedAdaptedSecondGramMatrix_isIntegral
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 2) :
    Dyadic.IsIntegral K (S.projectedAdaptedSecondGramMatrix f i j) := by
  simpa only [projectedAdaptedSecondGramMatrix] using
    S.projectedAdaptedGramEntry_isIntegral f
      (Fin.natAdd 2 i) (Fin.natAdd 2 j)

theorem sourceAdaptedSecondGramMatrix_isIntegral (i j : Fin 2) :
    Dyadic.IsIntegral K (S.sourceAdaptedSecondGramMatrix i j) := by
  simpa only [sourceAdaptedSecondGramMatrix,
    sourceHeadNormalizedGramMatrix,
    LinearMap.BilinForm.toMatrix_apply] using
      S.sourceHeadNormalizedGramMatrix_isIntegral
        S.sourceHeadAdaptedBasis S.sourceHeadAdaptedBasisLattice_eq
        (Fin.natAdd 2 i) (Fin.natAdd 2 j)

theorem orthogonalizedSecondGramMatrix_isIntegral
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 2) :
    Dyadic.IsIntegral K (S.orthogonalizedSecondGramMatrix f i j) := by
  have hdiff : Dyadic.IsIntegral K
      (S.orthogonalizedSecondGramMatrix f i j -
        S.projectedAdaptedSecondGramMatrix f i j) :=
    (mem_integerRing_iff K).1
      (S.mem_integerRing_of_mem_relativeSecondScaleIdeal
        (S.orthogonalizedSecondGramMatrix_sub_projected_mem_relativeSecondScaleIdeal
          f i j))
  have hsum := isIntegral_add K hdiff
    (S.projectedAdaptedSecondGramMatrix_isIntegral f i j)
  convert hsum using 1 <;> ring

/-- The second binary determinant is congruent to `-1` at the exact
relative second-scale depth. -/
theorem orthogonalizedSecondGramDet_sub_negOne_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.orthogonalizedSecondGramMatrix f).det - (-1 : K) ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  rw [← S.sourceAdaptedSecondGramMatrix_det]
  exact mem_coefficientIdeal_det_sub_det
    (principalIdeal (K := K) (S.relativeSecondScale : K))
    (S.orthogonalizedSecondGramMatrix f)
    S.sourceAdaptedSecondGramMatrix
    (S.orthogonalizedSecondGramMatrix_isIntegral f)
    S.sourceAdaptedSecondGramMatrix_isIntegral
    (S.orthogonalizedSecondGramMatrix_sub_source_mem_relativeSecondScaleIdeal f)

/-- The first projected binary block is congruent to its adapted source
block modulo the exact relative second-scale ideal. -/
theorem projectedAdaptedFirstGramMatrix_sub_source_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (i j : Fin 2) :
    S.projectedAdaptedFirstGramMatrix f i j -
        S.sourceAdaptedFirstGramMatrix i j ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  simpa only [projectedAdaptedFirstGramMatrix,
    sourceAdaptedFirstGramMatrix, projectedAdaptedBasis_apply,
    projectedHeadNormalizedGramMatrix, sourceHeadNormalizedGramMatrix,
    projectedHeadFamily, LinearMap.BilinForm.toMatrix_apply] using
      S.projectedHeadNormalizedGramMatrix_sub_source_mem_relativeSecondScaleIdeal
        S.sourceHeadAdaptedBasis S.sourceHeadAdaptedBasisLattice_eq f
        (Fin.castAdd 2 i) (Fin.castAdd 2 j)

/-- The first binary determinant is also congruent to `-1` at the exact
relative second-scale depth. -/
theorem projectedAdaptedFirstGramDet_sub_negOne_mem_relativeSecondScaleIdeal
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.projectedAdaptedFirstGramMatrix f).det - (-1 : K) ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
  rw [← S.sourceAdaptedFirstGramMatrix_det]
  exact mem_coefficientIdeal_det_sub_det
    (principalIdeal (K := K) (S.relativeSecondScale : K))
    (S.projectedAdaptedFirstGramMatrix f)
    S.sourceAdaptedFirstGramMatrix
    (S.projectedAdaptedFirstGramMatrix_isIntegral f)
    S.sourceAdaptedFirstGramMatrix_isIntegral
    (S.projectedAdaptedFirstGramMatrix_sub_source_mem_relativeSecondScaleIdeal f)

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
