/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDiagonalExactBONG
import Bong.Bong.BeliLemma319

/-!
# Hyperbolicity of a binary diagonal model

A binary diagonal space with coefficients `first, second` is hyperbolic when
`-(first / second)` is a square.  We prove this directly: an explicit square
root produces two isotropic vectors with mixed coefficient one.  This is the
ambient-space calculation used in the even branch of Beli (2019), Lemma 9.8.
-/

namespace Bong

open Dyadic
open Module

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- If the signed ratio of the two diagonal coefficients is a square, the
explicit binary model is isometric to the hyperbolic plane with mixed
coefficient one. -/
theorem binaryDiagonalModel_isIsometric_hyperbolicPlane_one
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first))
    (hsquare : IsSquare (-(first / second))) :
    (binaryDiagonalModelSpace first second hadmissible).IsIsometric
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
  rcases hsquare with ⟨t, ht⟩
  let q := binaryDiagonalModelSpace first second hadmissible
  let b := binaryDiagonalOrthogonalBasis first second hadmissible
  let u : Fin 2 → K := b 0 + (t : K) • b 1
  let c : K := (2 * (first : K))⁻¹
  let w : Fin 2 → K := c • (b 0 - (t : K) • b 1)
  have hbzero : q.quadratic (b 0) = (first : K) := by
    have h := binaryDiagonalOrthogonalBasis_quadratic
      first second hadmissible (0 : Fin 2)
    change q.quadratic (b 0) = (first : K) at h
    exact h
  have hbone : q.quadratic (b 1) = (second : K) := by
    have h := binaryDiagonalOrthogonalBasis_quadratic
      first second hadmissible (1 : Fin 2)
    change q.quadratic (b 1) = (second : K) at h
    exact h
  have hbzeroBilin : q.bilin (b 0) (b 0) = (first : K) := hbzero
  have hboneBilin : q.bilin (b 1) (b 1) = (second : K) := hbone
  have hbzeroone : q.bilin (b 0) (b 1) = 0 := by
    exact (LinearMap.BilinForm.iIsOrtho_def.mp
      (binaryDiagonalOrthogonalBasis_isOrtho
        first second hadmissible)) (0 : Fin 2) (1 : Fin 2) (by decide)
  have hbonezero : q.bilin (b 1) (b 0) = 0 := by
    rw [q.isSymm.eq]
    exact hbzeroone
  have htK : -((first : K) / (second : K)) = (t : K) ^ 2 := by
    simpa [pow_two] using congrArg Units.val ht
  have hsecondNe : (second : K) ≠ 0 := Units.ne_zero second
  have hfirstNe : (first : K) ≠ 0 := Units.ne_zero first
  have htwoFirstNe : (2 : K) * (first : K) ≠ 0 :=
    mul_ne_zero (by norm_num) hfirstNe
  have htProduct :
      (t : K) * (-(t : K) * (second : K)) = (first : K) := by
    rw [show (t : K) * (-(t : K) * (second : K)) =
        -((t : K) ^ 2 * (second : K)) by ring, ← htK]
    field_simp [hsecondNe]
  have htProduct' :
      (t : K) * -((t : K) * (second : K)) = (first : K) := by
    simpa only [neg_mul] using htProduct
  have huQuadratic : q.quadratic u = 0 := by
    dsimp [u]
    rw [q.quadratic_add, q.quadratic_smul,
      LinearMap.BilinForm.smul_right, hbzero, hbone, hbzeroone]
    rw [← htK]
    field_simp [hsecondNe]
    ring
  have hinnerQuadratic :
      q.quadratic (b 0 - (t : K) • b 1) = 0 := by
    rw [show b 0 - (t : K) • b 1 =
        b 0 + (-(t : K)) • b 1 by module]
    rw [q.quadratic_add, q.quadratic_smul,
      LinearMap.BilinForm.smul_right, hbzero, hbone, hbzeroone]
    rw [show (-(t : K)) ^ 2 = (t : K) ^ 2 by ring, ← htK]
    field_simp [hsecondNe]
    ring
  have hwQuadratic : q.quadratic w = 0 := by
    dsimp [w]
    rw [q.quadratic_smul, hinnerQuadratic, mul_zero]
  have huwMixed : q.bilin u w = 1 := by
    dsimp [u, w, c]
    rw [LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_right,
      hbzeroBilin, hboneBilin, hbzeroone, hbonezero]
    simp only [mul_zero, sub_zero, zero_sub]
    rw [htProduct']
    field_simp [hsecondNe, htwoFirstNe]
    ring
  let family : Fin 2 → (Fin 2 → K) := ![u, w]
  have hfamilyLI : LinearIndependent K family := by
    rw [linearIndependent_fin2]
    constructor
    · intro hwzero
      change w = 0 at hwzero
      have honeZero : (1 : K) = 0 := by
        rw [← huwMixed, hwzero]
        simp
      exact one_ne_zero honeZero
    · intro a hau
      change a • w = u at hau
      have hwBilin : q.bilin w w = 0 := hwQuadratic
      have honeZero : (1 : K) = 0 := by
        rw [← huwMixed, ← hau,
          LinearMap.BilinForm.smul_left, hwBilin, mul_zero]
      exact one_ne_zero honeZero
  let isotropicBasis : Basis (Fin 2) K (Fin 2 → K) :=
    basisOfLinearIndependentOfCardEqFinrank' family hfamilyLI (by simp)
  have hisotropicBasis (i : Fin 2) : isotropicBasis i = family i := by
    simp [isotropicBasis]
  have hzero : q.quadratic (isotropicBasis 0) = 0 := by
    rw [hisotropicBasis]
    exact huQuadratic
  have hone : q.quadratic (isotropicBasis 1) = 0 := by
    rw [hisotropicBasis]
    exact hwQuadratic
  have hmixed : q.bilin (isotropicBasis 0) (isotropicBasis 1) = (1 : K) := by
    rw [hisotropicBasis, hisotropicBasis]
    exact huwMixed
  rcases Lattice.basisLattice_isIsometric_hyperbolicPlane
      q isotropicBasis (1 : Kˣ) hzero hone hmixed with ⟨f⟩
  exact ⟨f.toQuadraticSpaceIsometry⟩

/-- Two hyperbolic binary diagonal models are ambiently isometric. -/
theorem binaryDiagonalModel_isIsometric_of_signedRatioSquares
    (targetFirst targetSecond sourceFirst sourceSecond : Kˣ)
    (targetAdmissible :
      IsBinaryParameterAdmissible (targetSecond / targetFirst))
    (sourceAdmissible :
      IsBinaryParameterAdmissible (sourceSecond / sourceFirst))
    (htargetSquare : IsSquare (-(targetFirst / targetSecond)))
    (hsourceSquare : IsSquare (-(sourceFirst / sourceSecond))) :
    (binaryDiagonalModelSpace targetFirst targetSecond targetAdmissible).IsIsometric
        (binaryDiagonalModelSpace sourceFirst sourceSecond sourceAdmissible) := by
  rcases binaryDiagonalModel_isIsometric_hyperbolicPlane_one
      targetFirst targetSecond targetAdmissible htargetSquare with ⟨ftarget⟩
  rcases binaryDiagonalModel_isIsometric_hyperbolicPlane_one
      sourceFirst sourceSecond sourceAdmissible hsourceSquare with ⟨fsource⟩
  exact ⟨ftarget.trans fsource.symm⟩

end BONG

end Bong
