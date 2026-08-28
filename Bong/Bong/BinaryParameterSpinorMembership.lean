/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorSpinorInclusion
import Bong.Bong.Basis
import Bong.Lattice.Negation

/-!
# The binary parameter belongs to the spinor group

This file proves the second assertion of Beli (2003), paragraph 3.16.  In a
binary orthogonal BONG basis, the product of the two coordinate reflections is
the negative identity.  Its spinor norm is the square class of the binary
parameter.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

private theorem squareClass_mul (a c : Kˣ) :
    squareClass K a * squareClass K c = squareClass K (a * c) :=
  rfl

/-- Every ambient vector of a BONG is anisotropic. -/
theorem ambientVector_isAnisotropic
    {n : ℕ} (b : BONG V q L n) (i : Fin n) :
    q.IsAnisotropic (b.ambientVector i) := by
  rw [QuadraticSpace.IsAnisotropic, b.quadratic_ambientVector]
  exact b.value_ne_zero i

/-- In dimension two, the two coordinate reflections compose to `-id`. -/
theorem reflectionIsometry_zero_trans_one_eq_negOne
    (b : BONG V q L 2) :
    (q.reflectionIsometry (b.ambientVector 0)
        (b.ambientVector_isAnisotropic 0)).trans
      (q.reflectionIsometry (b.ambientVector 1)
        (b.ambientVector_isAnisotropic 1)) =
      QuadraticSpace.negOneIsometry q := by
  have h01 :
      q.bilin (b.ambientVector 0) (b.ambientVector 1) = 0 :=
    (LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho)
      0 1 (by decide)
  have h10 :
      q.bilin (b.ambientVector 1) (b.ambientVector 0) = 0 := by
    rw [q.isSymm.eq]
    exact h01
  let x1OrthogonalToX0 : q.vectorOrthogonal (b.ambientVector 0) :=
    ⟨b.ambientVector 1,
      (q.mem_vectorOrthogonal_iff
        (b.ambientVector 0) (b.ambientVector 1)).2 h01⟩
  let x0OrthogonalToX1 : q.vectorOrthogonal (b.ambientVector 1) :=
    ⟨b.ambientVector 0,
      (q.mem_vectorOrthogonal_iff
        (b.ambientVector 1) (b.ambientVector 0)).2 h10⟩
  have hlinear :
      ((q.reflectionIsometry (b.ambientVector 0)
          (b.ambientVector_isAnisotropic 0)).trans
        (q.reflectionIsometry (b.ambientVector 1)
          (b.ambientVector_isAnisotropic 1))).toLinearEquiv =
        (QuadraticSpace.negOneIsometry q).toLinearEquiv := by
    apply b.basis.ext'
    intro i
    fin_cases i
    · change
        q.reflectionLinearEquiv (b.ambientVector 1)
            (b.ambientVector_isAnisotropic 1)
          (q.reflectionLinearEquiv (b.ambientVector 0)
            (b.ambientVector_isAnisotropic 0) (b.ambientVector 0)) =
          -(b.ambientVector 0)
      rw [q.reflectionLinearEquiv_apply_self, map_neg]
      have hfix := q.reflectionLinearEquiv_apply_of_mem_vectorOrthogonal
        (b.ambientVector 1) (b.ambientVector_isAnisotropic 1)
        x0OrthogonalToX1
      change q.reflectionLinearEquiv (b.ambientVector 1)
          (b.ambientVector_isAnisotropic 1) (b.ambientVector 0) =
        b.ambientVector 0 at hfix
      rw [hfix]
    · change
        q.reflectionLinearEquiv (b.ambientVector 1)
            (b.ambientVector_isAnisotropic 1)
          (q.reflectionLinearEquiv (b.ambientVector 0)
            (b.ambientVector_isAnisotropic 0) (b.ambientVector 1)) =
          -(b.ambientVector 1)
      have hfix := q.reflectionLinearEquiv_apply_of_mem_vectorOrthogonal
        (b.ambientVector 0) (b.ambientVector_isAnisotropic 0)
        x1OrthogonalToX0
      change q.reflectionLinearEquiv (b.ambientVector 0)
          (b.ambientVector_isAnisotropic 0) (b.ambientVector 1) =
        b.ambientVector 1 at hfix
      rw [hfix, q.reflectionLinearEquiv_apply_self]
  apply QuadraticSpace.Isometry.ext
  intro x
  exact DFunLike.congr_fun hlinear x

/-- The spinor norm of integral `-id` on a binary BONG lattice is represented
by the binary parameter. -/
theorem integralSpinorNorm_negOneAutomorphism_eq_binaryParameter
    (b : BONG V q L 2) :
    Lattice.integralSpinorNorm (Lattice.negOneAutomorphism q L) =
      squareClass K b.binaryParameter := by
  letI : Module.Finite K V := L.moduleFinite
  change QuadraticSpace.spinorNorm
      (Lattice.negOneAutomorphism q L).toQuadraticSpaceIsometry =
    squareClass K b.binaryParameter
  rw [Lattice.negOneAutomorphism_toQuadraticSpaceIsometry]
  rw [← b.reflectionIsometry_zero_trans_one_eq_negOne]
  rw [QuadraticSpace.spinorNorm_trans]
  rw [QuadraticSpace.spinorNorm_reflection,
    QuadraticSpace.spinorNorm_reflection]
  have hvalueZero :
      Units.mk0 (q.quadratic (b.ambientVector 0))
          (b.ambientVector_isAnisotropic 0) = b.valueUnit 0 := by
    apply Units.ext
    rw [Units.val_mk0, b.quadratic_ambientVector, coe_valueUnit]
  have hvalueOne :
      Units.mk0 (q.quadratic (b.ambientVector 1))
          (b.ambientVector_isAnisotropic 1) = b.valueUnit 1 := by
    apply Units.ext
    rw [Units.val_mk0, b.quadratic_ambientVector, coe_valueUnit]
  rw [hvalueZero, hvalueOne, squareClass_mul]
  have hproduct :
      b.valueUnit 0 * b.valueUnit 1 =
        b.binaryParameter * b.valueUnit 0 ^ 2 := by
    unfold binaryParameter
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm]
  rw [hproduct]
  exact squareClass_mul_square K b.binaryParameter (b.valueUnit 0)

variable [BinarySpinorLocalLaws.{u, v} K]

/-- Beli (2003), paragraph 3.16: `a ∈ G(a)` for the parameter of every
binary BONG. -/
theorem binaryParameter_mem_beliSpinorGroup (b : BONG V q L 2) :
    squareClass K b.binaryParameter ∈
      beliSpinorGroup K b.binaryUnitSquareClass := by
  let negRotation : Lattice.IntegralRotation q L :=
    ⟨Lattice.negOneAutomorphism q L,
      Lattice.det_negOneAutomorphism_eq_one_of_finrank_two q L
        b.length_eq_finrank.symm⟩
  have hmem : squareClass K b.binaryParameter ∈
      Lattice.spinorNormImage (q := q) (L := L) :=
    ⟨negRotation,
      b.integralSpinorNorm_negOneAutomorphism_eq_binaryParameter⟩
  rw [b.spinorNormImage_eq_beliSpinorGroup] at hmem
  exact hmem

variable [BinaryNormGeneratorLocalLaws.{u, v} K]

/-- Both assertions recorded in Beli (2003), paragraph 3.16. -/
theorem beliParagraph316 (b : BONG V q L 2) :
    beliNormGeneratorSquareClassGroup K b.binaryParameter ≤
        beliSpinorGroup K b.binaryUnitSquareClass ∧
      squareClass K b.binaryParameter ∈
        beliSpinorGroup K b.binaryUnitSquareClass :=
  ⟨b.beliNormGeneratorSquareClassGroup_le_beliSpinorGroup,
    b.binaryParameter_mem_beliSpinorGroup⟩

end BONG

end Bong
