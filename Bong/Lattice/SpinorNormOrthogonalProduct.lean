/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalProductIsometry
import Bong.Lattice.SpinorNorm
import Bong.Lattice.SpinorNormIsometry
import Bong.Lattice.SpinorNormMultiplicative

/-!
# Spinor norm under an orthogonal product with the identity

Extending an integral orthogonal automorphism by the identity on a second
orthogonal summand leaves its residual Wall space, and hence its spinor norm,
unchanged.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Orthogonal product with the identity preserves the integral spinor norm. -/
theorem integralSpinorNorm_orthogonalProductBasic_refl
    (f : IntegralOrthogonalGroup q L) :
    integralSpinorNorm
        (f.orthogonalProductBasic (Isometry.refl r M)) =
      integralSpinorNorm f := by
  letI : Module.Finite K V := L.moduleFinite
  letI : Module.Finite K W := M.moduleFinite
  let F :=
    (f.orthogonalProductBasic (Isometry.refl r M)).toQuadraticSpaceIsometry
  have hresidual (z : V × W) :
      QuadraticSpace.residualLinearMap F z =
        (QuadraticSpace.residualLinearMap f.toQuadraticSpaceIsometry z.1, 0) := by
    ext
    · rfl
    · change z.2 - z.2 = 0
      simp
  let inclusion : QuadraticSpace.residualSpace f.toQuadraticSpaceIsometry →ₗ[K]
      QuadraticSpace.residualSpace F := {
    toFun y := by
      refine ⟨((y : V), 0), ?_⟩
      rcases y.property with ⟨x, hx⟩
      refine ⟨(x, 0), ?_⟩
      rw [hresidual]
      exact Prod.ext hx rfl
    map_add' x y := by
      apply Subtype.ext
      simp
    map_smul' a x := by
      apply Subtype.ext
      simp
  }
  have hinjective : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : QuadraticSpace.residualSpace F => (z : V × W).1) hxy
  have hsurjective : Function.Surjective inclusion := by
    intro y
    rcases y.property with ⟨z, hz⟩
    have hfirst : QuadraticSpace.residualLinearMap
        f.toQuadraticSpaceIsometry z.1 = (y : V × W).1 := by
      rw [hresidual] at hz
      exact congrArg Prod.fst hz
    have hsecond : (y : V × W).2 = 0 := by
      rw [hresidual] at hz
      exact (congrArg Prod.snd hz).symm
    let x : QuadraticSpace.residualSpace f.toQuadraticSpaceIsometry :=
      ⟨(y : V × W).1, ⟨z.1, hfirst⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hsecond.symm
  let E : QuadraticSpace.residualSpace f.toQuadraticSpaceIsometry ≃ₗ[K]
      QuadraticSpace.residualSpace F :=
    LinearEquiv.ofBijective inclusion ⟨hinjective, hsurjective⟩
  have hEresidual (z : V) :
      E (QuadraticSpace.residualMap f.toQuadraticSpaceIsometry z) =
        QuadraticSpace.residualMap F (z, 0) := by
    apply Subtype.ext
    change
      (QuadraticSpace.residualLinearMap f.toQuadraticSpaceIsometry z, 0) =
        QuadraticSpace.residualLinearMap F (z, 0)
    rw [hresidual]
  have hwall (x y : QuadraticSpace.residualSpace f.toQuadraticSpaceIsometry) :
      QuadraticSpace.wallForm F (E x) (E y) =
        QuadraticSpace.wallForm f.toQuadraticSpaceIsometry x y := by
    rcases QuadraticSpace.residualMap_surjective
        f.toQuadraticSpaceIsometry x with ⟨z, rfl⟩
    rw [hEresidual, QuadraticSpace.wallForm_residualMap_left,
      QuadraticSpace.wallForm_residualMap_left]
    change 2 * (q.orthogonalSum r).bilin (z, 0) ((y : V), 0) =
      2 * q.bilin z (y : V)
    simp
  let b := QuadraticSpace.wallBasis f.toQuadraticSpaceIsometry
  let c := b.map E
  have hfin : Module.finrank K (QuadraticSpace.residualSpace F) =
      Module.finrank K
        (QuadraticSpace.residualSpace f.toQuadraticSpaceIsometry) :=
    E.symm.finrank_eq
  have hmatrix :
      LinearMap.BilinForm.toMatrix c (QuadraticSpace.wallForm F) =
        LinearMap.BilinForm.toMatrix b
          (QuadraticSpace.wallForm f.toQuadraticSpaceIsometry) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, c, Basis.map_apply]
    exact hwall (b i) (b j)
  change QuadraticSpace.spinorNorm F =
    QuadraticSpace.spinorNorm f.toQuadraticSpaceIsometry
  rw [QuadraticSpace.spinorNorm_eq_basisDeterminantOfFinrankEq F hfin c,
    QuadraticSpace.spinorNorm_eq_basisDeterminant
      f.toQuadraticSpaceIsometry b]
  apply congrArg (squareClass K)
  apply Units.ext
  exact congrArg Matrix.det hmatrix

/-- The spinor norm of a componentwise orthogonal product is the product
of the two component spinor norms. -/
theorem integralSpinorNorm_orthogonalProductBasic
    (f : IntegralOrthogonalGroup q L)
    (g : IntegralOrthogonalGroup r M) :
    integralSpinorNorm (f.orthogonalProductBasic g) =
      integralSpinorNorm f * integralSpinorNorm g := by
  let left : IntegralOrthogonalGroup (q.orthogonalSum r) (product L M) :=
    f.orthogonalProductBasic (Isometry.refl r M)
  let rightSwapped : IntegralOrthogonalGroup
      (r.orthogonalSum q) (product M L) :=
    g.orthogonalProductBasic (Isometry.refl q L)
  let swap : Isometry (r.orthogonalSum q) (q.orthogonalSum r)
      (product M L) (product L M) :=
    orthogonalProductSwap (q := r) (r := q) (L := M) (M := L)
  let right : IntegralOrthogonalGroup
      (q.orthogonalSum r) (product L M) :=
    swap.conjugateAutomorphism rightSwapped
  have hrightApply (x : V × W) :
      right.toLinearEquiv x = (x.1, g.toLinearEquiv x.2) := by
    rfl
  have hfactor : f.orthogonalProductBasic g = left * right := by
    apply Isometry.ext
    intro x
    simp only [IntegralOrthogonalGroup.mul_toLinearEquiv_apply,
      Isometry.orthogonalProductBasic_apply]
    rw [hrightApply]
    rfl
  rw [hfactor, integralSpinorNorm_mul]
  rw [integralSpinorNorm_orthogonalProductBasic_refl]
  have hrightSpinor : integralSpinorNorm right =
      integralSpinorNorm g := by
    calc
      integralSpinorNorm right = integralSpinorNorm rightSwapped :=
        integralSpinorNorm_conjugateAutomorphism swap rightSwapped
      _ = integralSpinorNorm g :=
        integralSpinorNorm_orthogonalProductBasic_refl g
  rw [hrightSpinor]

end Lattice

end Bong
