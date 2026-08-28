/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.WallReflectionReduction
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Multiplying the Wall spinor norm by one reflection

For an anisotropic residual vector `u` of `f`, the Wall matrix splits as a
lower block-triangular matrix with first diagonal entry `Q(u)` and remaining
block the Wall matrix of `f` followed by reflection in `u`.  Consequently
the two Wall determinants differ by `Q(u)` modulo squares.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {q : QuadraticSpace K V}

variable (f : Isometry q q) (u : V) (hu : q.IsAnisotropic u)
  (huResidual : u ∈ residualSpace f)

private noncomputable def residualKernelBasis :
    Module.Basis
      (Fin (Module.finrank K
        (LinearMap.ker
          (wallForm f (residualVector f u huResidual))))) K
      (LinearMap.ker
        (wallForm f (residualVector f u huResidual))) :=
  Module.finBasis K _

private theorem residualVector_linearIndependent_from_kernel
    (c : K) (x : residualSpace f)
    (hx : x ∈ LinearMap.ker
      (wallForm f (residualVector f u huResidual)))
    (heq : c • residualVector f u huResidual + x = 0)
    (hu' : q.IsAnisotropic u) :
    c = 0 := by
  have happly := congrArg
    (wallForm f (residualVector f u huResidual)) heq
  simp only [map_add, map_smul, map_zero] at happly
  rw [hx, add_zero, wallForm_self_eq_quadratic] at happly
  change c * q.quadratic u = 0 at happly
  exact (mul_eq_zero.mp happly).resolve_right hu'

private theorem residualVector_spans_mod_kernel
    (hu' : q.IsAnisotropic u) (z : residualSpace f) :
    ∃ c : K, z + c • residualVector f u huResidual ∈
      LinearMap.ker
        (wallForm f (residualVector f u huResidual)) := by
  let c : K :=
    -(wallForm f (residualVector f u huResidual) z / q.quadratic u)
  refine ⟨c, ?_⟩
  change wallForm f (residualVector f u huResidual)
      (z + c • residualVector f u huResidual) = 0
  rw [map_add, map_smul, wallForm_self_eq_quadratic]
  change wallForm f (residualVector f u huResidual) z +
      c * q.quadratic u = 0
  rw [show c * q.quadratic u =
      -wallForm f (residualVector f u huResidual) z by
        dsimp [c]
        rw [neg_mul, div_mul_cancel₀ _ hu']]
  exact add_neg_cancel _

private noncomputable def residualSplitBasis :
    Module.Basis
      (Fin
        (Module.finrank K
          (LinearMap.ker
            (wallForm f (residualVector f u huResidual))) + 1)) K
      (residualSpace f) :=
  Module.Basis.mkFinCons
    (residualVector f u huResidual)
    (residualKernelBasis f u huResidual)
    (fun c x hx heq =>
      residualVector_linearIndependent_from_kernel f u huResidual
        c x hx heq hu)
    (residualVector_spans_mod_kernel f u huResidual hu)

private noncomputable def reducedResidualBasis :
    Module.Basis
      (Fin (Module.finrank K
        (LinearMap.ker
          (wallForm f (residualVector f u huResidual))))) K
      (residualSpace (reflectAfter f u hu)) :=
  (residualKernelBasis f u huResidual).map
    (residualReflectAfterEquivKernel f u hu huResidual).symm

private theorem finrank_residualSpace_eq_kernel_add_one
    (hu' : q.IsAnisotropic u) :
    Module.finrank K (residualSpace f) =
      Module.finrank K
        (LinearMap.ker
          (wallForm f (residualVector f u huResidual))) + 1 := by
  simpa using Module.finrank_eq_card_basis
    (residualSplitBasis f u hu' huResidual)

private theorem finrank_reducedResidualSpace_eq_kernel :
    Module.finrank K (residualSpace (reflectAfter f u hu)) =
      Module.finrank K
        (LinearMap.ker
          (wallForm f (residualVector f u huResidual))) := by
  simpa using Module.finrank_eq_card_basis
    (reducedResidualBasis f u hu huResidual)

private theorem residualSplitBasis_zero :
    residualSplitBasis f u hu huResidual 0 =
      residualVector f u huResidual := by
  simp [residualSplitBasis]

private theorem residualSplitBasis_succ
    (i : Fin (Module.finrank K
      (LinearMap.ker
        (wallForm f (residualVector f u huResidual))))) :
    residualSplitBasis f u hu huResidual i.succ =
      ((residualKernelBasis f u huResidual i :
        LinearMap.ker
          (wallForm f (residualVector f u huResidual))) :
        residualSpace f) := by
  simp [residualSplitBasis]

private theorem reducedResidualBasis_apply
    (i : Fin (Module.finrank K
      (LinearMap.ker
        (wallForm f (residualVector f u huResidual))))) :
    reducedResidualBasis f u hu huResidual i =
      (residualReflectAfterEquivKernel f u hu huResidual).symm
        (residualKernelBasis f u huResidual i) := by
  rfl

/-- Exact determinant factorization for Wall's reflection reduction. -/
theorem wallDeterminant_reflection_reduction :
    Matrix.det
        (LinearMap.BilinForm.toMatrix
          (residualSplitBasis f u hu huResidual) (wallForm f)) =
      q.quadratic u *
        Matrix.det
          (LinearMap.BilinForm.toMatrix
            (reducedResidualBasis f u hu huResidual)
            (wallForm (reflectAfter f u hu))) := by
  let n := Module.finrank K
    (LinearMap.ker
      (wallForm f (residualVector f u huResidual)))
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    LinearMap.BilinForm.toMatrix
      (residualSplitBasis f u hu huResidual) (wallForm f)
  let D : Matrix (Fin n) (Fin n) K :=
    LinearMap.BilinForm.toMatrix
      (reducedResidualBasis f u hu huResidual)
      (wallForm (reflectAfter f u hu))
  have hA00 : A 0 0 = q.quadratic u := by
    dsimp only [A]
    rw [LinearMap.BilinForm.toMatrix_apply]
    change wallForm f (residualSplitBasis f u hu huResidual 0)
      (residualSplitBasis f u hu huResidual 0) = q.quadratic u
    rw [residualSplitBasis_zero, wallForm_self_eq_quadratic]
    rfl
  have hA0succ (j : Fin n) : A 0 j.succ = 0 := by
    dsimp only [A]
    rw [LinearMap.BilinForm.toMatrix_apply]
    change wallForm f (residualSplitBasis f u hu huResidual 0)
      (residualSplitBasis f u hu huResidual j.succ) = 0
    rw [residualSplitBasis_zero, residualSplitBasis_succ]
    exact (residualKernelBasis f u huResidual j).2
  have hsubmatrix : A.submatrix Fin.succ Fin.succ = D := by
    ext i j
    dsimp only [A, D, Matrix.submatrix_apply]
    rw [LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply]
    change wallForm f
      (residualSplitBasis f u hu huResidual i.succ)
      (residualSplitBasis f u hu huResidual j.succ) =
        wallForm (reflectAfter f u hu)
          (reducedResidualBasis f u hu huResidual i)
          (reducedResidualBasis f u hu huResidual j)
    rw [
      residualSplitBasis_succ, residualSplitBasis_succ,
      reducedResidualBasis_apply, reducedResidualBasis_apply]
    simpa using
      (wallForm_reflectAfter_restriction f u hu huResidual
        ((residualReflectAfterEquivKernel f u hu huResidual).symm
          (residualKernelBasis f u huResidual i))
        ((residualReflectAfterEquivKernel f u hu huResidual).symm
          (residualKernelBasis f u huResidual j)))
  change Matrix.det A = q.quadratic u * Matrix.det D
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hA00, hA0succ,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero,
    hsubmatrix]

/-- If `u` is an anisotropic residual vector of `f`, its Wall determinant
square class splits off from that of `f`. -/
theorem spinorNorm_eq_reflectionClass_mul_reduced
    (huResidual' : u ∈ residualSpace f) :
    spinorNorm f =
      squareClass K (Units.mk0 (q.quadratic u) hu) *
        spinorNorm (reflectAfter f u hu) := by
  let bF := residualSplitBasis f u hu huResidual'
  let bH := reducedResidualBasis f u hu huResidual'
  have hfinF := finrank_residualSpace_eq_kernel_add_one
    f u huResidual' hu
  have hfinH := finrank_reducedResidualSpace_eq_kernel f u hu huResidual'
  have hdet := wallDeterminant_reflection_reduction f u hu huResidual'
  let dF : K := Matrix.det
    (LinearMap.BilinForm.toMatrix bF (wallForm f))
  let dH : K := Matrix.det
    (LinearMap.BilinForm.toMatrix bH (wallForm (reflectAfter f u hu)))
  have hdF : dF ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bF).1
      (wallForm_nondegenerate f)
  have hdH : dH ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bH).1
      (wallForm_nondegenerate (reflectAfter f u hu))
  let a : Kˣ := Units.mk0 (q.quadratic u) hu
  let vF : Kˣ := Units.mk0 dF hdF
  let vH : Kˣ := Units.mk0 dH hdH
  have hv : vF = a * vH := by
    apply Units.ext
    exact hdet
  rw [spinorNorm_eq_basisDeterminantOfFinrankEq f hfinF bF,
    spinorNorm_eq_basisDeterminantOfFinrankEq
      (reflectAfter f u hu) hfinH bH]
  change squareClass K vF = squareClass K a * squareClass K vH
  rw [hv]
  rfl

/-- Multiplication by a reflection has the expected spinor-norm factor
whenever the reflection vector is residual. -/
theorem spinorNorm_reflectAfter_of_mem_residual
    (huResidual' : u ∈ residualSpace f) :
    spinorNorm (reflectAfter f u hu) =
      spinorNorm f * squareClass K (Units.mk0 (q.quadratic u) hu) := by
  let a : Kˣ := Units.mk0 (q.quadratic u) hu
  have hsplit := spinorNorm_eq_reflectionClass_mul_reduced
    f u hu huResidual'
  have haa : squareClass K a * squareClass K a = 1 := by
    change squareClass K (a * a) = 1
    rw [show a * a = (1 : Kˣ) * a ^ 2 by simp [pow_two],
      squareClass_mul_square]
    rfl
  calc
    spinorNorm (reflectAfter f u hu) =
        1 * spinorNorm (reflectAfter f u hu) := by simp
    _ = (squareClass K a * squareClass K a) *
        spinorNorm (reflectAfter f u hu) := by rw [haa]
    _ = squareClass K a *
        (squareClass K a * spinorNorm (reflectAfter f u hu)) := by
      rw [mul_assoc]
    _ = squareClass K a * spinorNorm f := by rw [hsplit]
    _ = spinorNorm f * squareClass K a := mul_comm _ _

/-- If `u` is not residual, some fixed vector pairs nontrivially with it.
This is the finite-dimensional double-orthogonal-complement argument behind
the complementary case of Wall's reflection reduction. -/
theorem exists_fixed_pair_ne_zero_of_not_mem_residual
    (hnot : u ∉ residualSpace f) :
    ∃ z : V, f.toLinearEquiv z = z ∧ q.bilin u z ≠ 0 := by
  by_contra h
  push_neg at h
  have huDouble :
      u ∈ q.bilin.orthogonal (q.bilin.orthogonal (residualSpace f)) := by
    intro z hz
    rw [q.isSymm.eq]
    exact h z ((mem_orthogonal_residualSpace_iff f z).1 hz)
  have huMem : u ∈ residualSpace f := by
    rw [q.bilin.orthogonal_orthogonal q.nondegenerate
      q.isSymm.isRefl] at huDouble
    exact huDouble
  exact hnot huMem

/-- In the complementary reflection case, the reflection vector enters the
new residual space. -/
theorem mem_residualSpace_reflectAfter_of_not_mem
    (hnot : u ∉ residualSpace f) :
    u ∈ residualSpace (reflectAfter f u hu) := by
  obtain ⟨z, hzfixed, hzpair⟩ :=
    exists_fixed_pair_ne_zero_of_not_mem_residual f u hnot
  let c : K := 2 * q.bilin u z / q.quadratic u
  have hc : c ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) hzpair) hu
  have hcz : c • u ∈ residualSpace (reflectAfter f u hu) := by
    refine ⟨z, ?_⟩
    rw [residualLinearMap_reflectAfter_apply,
      residualLinearMap_apply, hzfixed, sub_self, zero_add]
  have hscaled :=
    (residualSpace (reflectAfter f u hu)).smul_mem c⁻¹ hcz
  have hscale : c⁻¹ • (c • u) = u := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rwa [hscale] at hscaled

/-- Applying the same reflection twice cancels. -/
@[simp]
theorem reflectAfter_reflectAfter :
    reflectAfter (reflectAfter f u hu) u hu = f := by
  apply Isometry.ext
  intro y
  change q.reflectionLinearEquiv u hu
      (q.reflectionLinearEquiv u hu (f.toLinearEquiv y)) =
    f.toLinearEquiv y
  exact q.reflectionLinearEquiv_involutive u hu _

/-- The Wall spinor norm acquires the quadratic class of a reflection,
without a residual-space side condition. -/
theorem spinorNorm_reflectAfter :
    spinorNorm (reflectAfter f u hu) =
      spinorNorm f * squareClass K (Units.mk0 (q.quadratic u) hu) := by
  by_cases hmem : u ∈ residualSpace f
  · exact spinorNorm_reflectAfter_of_mem_residual f u hu hmem
  · let h := reflectAfter f u hu
    have huNew : u ∈ residualSpace h := by
      exact mem_residualSpace_reflectAfter_of_not_mem f u hu hmem
    have hsplit := spinorNorm_eq_reflectionClass_mul_reduced
      h u hu huNew
    rw [show reflectAfter h u hu = f by
      dsimp [h]
      exact reflectAfter_reflectAfter f u hu] at hsplit
    simpa only [h, mul_comm] using hsplit

end QuadraticSpace

end Bong
