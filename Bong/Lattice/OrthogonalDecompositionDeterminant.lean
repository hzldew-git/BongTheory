/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionVolume
import Bong.Lattice.DeterminantIsometry

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

theorem unitSquareClass_gramUnit_eq_determinantClass_arbitrary
    {i : Type*} [Fintype i] [DecidableEq i]
    (q : QuadraticSpace K V) (b : Basis i K V) :
    unitSquareClass K (Units.mk0
      (LinearMap.BilinForm.toMatrix b q.bilin).det
      ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
        q.nondegenerate)) =
      determinantClass q (basisLattice b) := by
  let e : i ≃ Fin (finrank K V) :=
    Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let bFin : Basis (Fin (finrank K V)) K V := b.reindex e
  have hb : basisLattice bFin = basisLattice b :=
    basisLattice_reindex b e
  have hmatrix :
      LinearMap.BilinForm.toMatrix bFin q.bilin =
        Matrix.reindex e e
          (LinearMap.BilinForm.toMatrix b q.bilin) := by
    ext j k
    simp [bFin, LinearMap.BilinForm.toMatrix_apply]
  let u : Kˣ := Units.mk0
    (LinearMap.BilinForm.toMatrix b q.bilin).det
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
      q.nondegenerate)
  have hu : u = basisGramUnit q bFin := by
    apply Units.ext
    change (LinearMap.BilinForm.toMatrix b q.bilin).det =
      (LinearMap.BilinForm.toMatrix bFin q.bilin).det
    rw [hmatrix, Matrix.det_reindex_self]
  change unitSquareClass K u = _
  rw [hu, unitSquareClass_basisGramUnit_eq_determinantClass, hb]

theorem determinantClass_orthogonalProduct
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (L : Lattice K V) (M : Lattice K W) :
    determinantClass (q.orthogonalSum r) (product L M) =
      determinantClass q L * determinantClass r M := by
  classical
  let b := L.standardAmbientBasis
  let c := M.standardAmbientBasis
  have hbL : basisLattice b = L := basisLattice_standardAmbientBasis L
  have hcM : basisLattice c = M := basisLattice_standardAmbientBasis M
  have hprod : basisLattice (b.prod c) = product L M := by
    rw [basisLattice_prod, hbL, hcM]
  let A := LinearMap.BilinForm.toMatrix b q.bilin
  let B := LinearMap.BilinForm.toMatrix c r.bilin
  let P := LinearMap.BilinForm.toMatrix (b.prod c)
    (q.orthogonalSum r).bilin
  have hP : P = Matrix.fromBlocks A 0 0 B := by
    ext (i | i) (j | j) <;>
      simp [P, A, B, LinearMap.BilinForm.toMatrix_apply,
        QuadraticSpace.orthogonalSum_bilin_apply]
  let p : Kˣ := Units.mk0 P.det
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.prod c)).mp
      (q.orthogonalSum r).nondegenerate)
  let a : Kˣ := Units.mk0 A.det
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp q.nondegenerate)
  let d : Kˣ := Units.mk0 B.det
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp r.nondegenerate)
  have hp : p = a * d := by
    apply Units.ext
    change P.det = A.det * B.det
    rw [hP, Matrix.det_fromBlocks_zero₂₁]
  rw [← hprod,
    ← unitSquareClass_gramUnit_eq_determinantClass_arbitrary
      (q.orthogonalSum r) (b.prod c)]
  change unitSquareClass K p = _
  rw [hp, unitSquareClass_mul]
  rw [unitSquareClass_gramUnit_eq_determinantClass_arbitrary q b, hbL,
    unitSquareClass_gramUnit_eq_determinantClass_arbitrary r c, hcM]

theorem OrthogonalDecomposition.determinantClass_eq_mul_components
    {q : QuadraticSpace K V} {L : Lattice K V}
    (D : OrthogonalDecomposition q L 2) :
    determinantClass q L =
      determinantClass (D.component 0).space (D.component 0).lattice *
        determinantClass (D.component 1).space (D.component 1).lattice := by
  have h := determinantClass_eq_of_isometry D.pairProductLatticeIsometry
  rw [determinantClass_orthogonalProduct] at h
  exact h.symm

end Lattice

end Bong
