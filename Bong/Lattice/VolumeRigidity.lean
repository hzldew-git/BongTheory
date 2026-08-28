/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Determinant
import Bong.Lattice.NormGenerator
import Mathlib.LinearAlgebra.Determinant

/-!
# Volume rigidity for full lattices

For nested full lattices `L ≤ M`, the inclusion has a square integral matrix
in their chosen bases.  Changing basis in the Gram matrix shows that the
determinants differ by the square of the inclusion determinant.  If the two
volume ideals agree, that determinant is a unit, so the inclusion is an
isomorphism and the lattices coincide.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The matrix of an inclusion of full lattices in their chosen integral bases. -/
noncomputable def inclusionMatrix {L M : Lattice K V} (hLM : L ≤ M) :
    Matrix (Fin (finrank K V)) (Fin (finrank K V)) (IntegerRing K) :=
  LinearMap.toMatrix L.standardIntegralBasis M.standardIntegralBasis
    (Submodule.inclusion hLM)

/-- After extending scalars, the inclusion matrix is the ambient change-of-basis matrix. -/
theorem inclusionMatrix_map {L M : Lattice K V} (hLM : L ≤ M) :
    (algebraMap (IntegerRing K) K).mapMatrix (inclusionMatrix hLM) =
      M.standardAmbientBasis.toMatrix L.standardAmbientBasis := by
  ext i j
  simp [inclusionMatrix, LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply,
    algebraMap_standardIntegralBasis_repr]

/-- The Gram determinants of nested lattices differ by the squared index determinant. -/
theorem determinant_eq_mul_sq_inclusionMatrix_det (q : QuadraticSpace K V)
    {L M : Lattice K V} (hLM : L ≤ M) :
    determinant q L = determinant q M *
      (((inclusionMatrix hLM).det : IntegerRing K) : K) ^ 2 := by
  let A := inclusionMatrix hLM
  let P := M.standardAmbientBasis.toMatrix L.standardAmbientBasis
  have hP : (algebraMap (IntegerRing K) K).mapMatrix A = P :=
    inclusionMatrix_map hLM
  have hmatrix :
      P.transpose * integralGramMatrix q M * P = integralGramMatrix q L := by
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      M.standardAmbientBasis L.standardAmbientBasis q.bilin
  have hdet : determinant q L = determinant q M * P.det ^ 2 := by
    change (integralGramMatrix q L).det =
      (integralGramMatrix q M).det * P.det ^ 2
    rw [← hmatrix]
    simp only [Matrix.det_mul, Matrix.det_transpose]
    ring
  have hPdet : ((A.det : IntegerRing K) : K) = P.det := by
    change algebraMap (IntegerRing K) K A.det = P.det
    rw [RingHom.map_det, hP]
  rw [hdet, hPdet]

/-- Equal volume makes the determinant of a lattice inclusion a unit. -/
theorem isUnit_det_inclusionMatrix_of_volumeIdeal_eq
    (q : QuadraticSpace K V) {L M : Lattice K V} (hLM : L ≤ M)
    (hvolume : volumeIdeal q L = volumeIdeal q M) :
    IsUnit (inclusionMatrix hLM).det := by
  let d := (inclusionMatrix hLM).det
  have hdet :
      determinant q L = determinant q M * ((d : IntegerRing K) : K) ^ 2 :=
    determinant_eq_mul_sq_inclusionMatrix_det q hLM
  have hmem : determinant q M ∈ volumeIdeal q L := by
    rw [hvolume]
    exact determinant_mem_volumeIdeal q M
  rw [volumeIdeal, principalIdeal, Submodule.mem_span_singleton] at hmem
  rcases hmem with ⟨c, hc⟩
  have hc' : (c : K) * determinant q L = determinant q M := by
    simpa [Algebra.smul_def] using hc
  have hcd : (c : K) * (d : K) ^ 2 = 1 := by
    apply mul_left_cancel₀ (determinant_ne_zero q M)
    calc
      determinant q M * ((c : K) * (d : K) ^ 2) =
          (c : K) * (determinant q M * (d : K) ^ 2) := by ring
      _ = (c : K) * determinant q L := by rw [hdet]
      _ = determinant q M := hc'
      _ = determinant q M * 1 := by rw [mul_one]
  have hcd' : c * d ^ 2 = 1 := by
    apply Subtype.ext
    exact hcd
  apply IsUnit.of_mul_eq_one (c * d)
  calc
    d * (c * d) = c * d ^ 2 := by ring
    _ = 1 := hcd'

/-- Nested full lattices with the same volume ideal are equal. -/
theorem eq_of_le_of_volumeIdeal_eq (q : QuadraticSpace K V)
    (L M : Lattice K V) (hLM : L ≤ M)
    (hvolume : volumeIdeal q L = volumeIdeal q M) : L = M := by
  have hunit : IsUnit (inclusionMatrix hLM).det :=
    isUnit_det_inclusionMatrix_of_volumeIdeal_eq q hLM hvolume
  have hsurjective : Function.Surjective (Submodule.inclusion hLM) :=
    (LinearEquiv.ofIsUnitDet
      (v := L.standardIntegralBasis) (v' := M.standardIntegralBasis)
      (f := Submodule.inclusion hLM) hunit).surjective
  apply Lattice.ext
  apply le_antisymm hLM
  intro y hy
  rcases hsurjective ⟨y, hy⟩ with ⟨z, hz⟩
  have hzy : (z : V) = y := congrArg Subtype.val hz
  rw [← hzy]
  exact z.property

/-- Equal volume orders give equal principal volume ideals. -/
theorem volumeIdeal_eq_of_volumeOrder_eq (q : QuadraticSpace K V)
    (L M : Lattice K V)
    (hvolume : volumeOrder q L = volumeOrder q M) :
    volumeIdeal q L = volumeIdeal q M := by
  have hord : ord K (determinant q L) =
      ord K (determinant q M) := by
    rw [← coe_volumeOrder, ← coe_volumeOrder, hvolume]
  unfold volumeIdeal
  apply le_antisymm
  · exact (principalIdeal_le_iff_ord_ge
      (determinant_ne_zero q L) (determinant_ne_zero q M)).2 hord.ge
  · exact (principalIdeal_le_iff_ord_ge
      (determinant_ne_zero q M) (determinant_ne_zero q L)).2 hord.le

/-- Nested full lattices with the same volume order are equal. -/
theorem eq_of_le_of_volumeOrder_eq (q : QuadraticSpace K V)
    (L M : Lattice K V) (hLM : L ≤ M)
    (hvolume : volumeOrder q L = volumeOrder q M) : L = M :=
  eq_of_le_of_volumeIdeal_eq q L M hLM
    (volumeIdeal_eq_of_volumeOrder_eq q L M hvolume)

end Lattice

end Bong
