/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDual
import Bong.Bong.BinaryModelIsometry
import Bong.Bong.BinaryNormalForm
import Bong.Lattice.NormGeneratorValues
import Bong.QuadraticSpace.OrthogonalExtension

/-!
# Reverse duality for modular binary BONGs

This file begins the decreasing-order branch of Beli (2003), Lemma 4.8.
For a binary BONG, the recursive construction supplies an integral adapted
basis `(x, y)` whose orthogonal projection of `y` is the second BONG vector.
The bilinear dual of that integral basis, read in reverse order, therefore
generates the integral dual lattice and begins with the normalized second
BONG vector `x₂⁺`.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The BONG-adapted integral basis, reindexed by `Fin 2`. -/
noncomputable def binaryAdaptedFinBasis (b : BONG V q L 2) :
    Basis (Fin 2) K V :=
  b.binaryAdaptedAmbientBasis.reindex binaryModelAdaptedIndexEquiv.symm

@[simp]
theorem binaryAdaptedFinBasis_zero (b : BONG V q L 2) :
    b.binaryAdaptedFinBasis 0 = b.head := by
  simp [binaryAdaptedFinBasis]

@[simp]
theorem binaryAdaptedFinBasis_one (b : BONG V q L 2) :
    b.binaryAdaptedFinBasis 1 = b.binarySecondVector := by
  simp [binaryAdaptedFinBasis]

/-- The adapted `Fin 2` basis is still an integral basis of the BONG lattice. -/
theorem basisLattice_binaryAdaptedFinBasis (b : BONG V q L 2) :
    Lattice.basisLattice b.binaryAdaptedFinBasis = L := by
  rw [binaryAdaptedFinBasis, Lattice.basisLattice_reindex]
  exact b.basisLattice_binaryAdaptedAmbientBasis

/-- The normalized second BONG vector pairs to one with the adapted second
integral vector. -/
theorem bilin_reverseDualVector_zero_binarySecondVector
    (b : BONG V q L 2) :
    q.bilin (b.reverseDualVector 0) b.binarySecondVector = 1 := by
  have hhead : q.bilin (b.reverseDualVector 0) b.head = 0 := by
    rw [← b.ambientVector_zero_eq_head]
    simpa [BONG.reverseDualVector, Fin.rev] using
      b.bilin_dualVector_ambientVector (1 : Fin 2) (0 : Fin 2)
  have htail :
      q.orthogonalProjection b.head b.binarySecondVector =
        b.ambientVector 1 := by
    calc
      q.orthogonalProjection b.head b.binarySecondVector =
          (b.tail.head : V) := by
        simpa only [QuadraticSpace.projectionToOrthogonal_coe] using
          congrArg Subtype.val b.projectionToOrthogonal_binarySecondVector
      _ = (b.tail.ambientVector 0 : V) := by
        rw [b.tail.ambientVector_zero_eq_head]
      _ = b.ambientVector 1 := b.coe_ambientVector_tail 0
  have hsecond :
      q.bilin (b.reverseDualVector 0) (b.ambientVector 1) = 1 := by
    simpa [BONG.reverseDualVector, Fin.rev] using
      b.bilin_dualVector_ambientVector (1 : Fin 2) (1 : Fin 2)
  calc
    q.bilin (b.reverseDualVector 0) b.binarySecondVector =
        q.bilin (b.reverseDualVector 0)
          (q.lineProjection b.head b.binarySecondVector +
            q.orthogonalProjection b.head b.binarySecondVector) := by
      rw [q.lineProjection_add_orthogonalProjection]
    _ = q.bilin (b.reverseDualVector 0)
          (q.lineProjection b.head b.binarySecondVector) +
        q.bilin (b.reverseDualVector 0)
          (q.orthogonalProjection b.head b.binarySecondVector) := by
      rw [LinearMap.BilinForm.add_right]
    _ = 0 + 1 := by
      rw [q.lineProjection_apply, LinearMap.BilinForm.smul_right,
        hhead, mul_zero, htail, hsecond]
    _ = 1 := zero_add 1

/-- The normalized first BONG vector reads off the line coefficient of the
adapted second integral vector. -/
theorem bilin_reverseDualVector_one_binarySecondVector
    (b : BONG V q L 2) :
    q.bilin (b.reverseDualVector 1) b.binarySecondVector =
      q.bilin b.head b.binarySecondVector / q.quadratic b.head := by
  have hhead : q.bilin (b.reverseDualVector 1) b.head = 1 := by
    rw [← b.ambientVector_zero_eq_head]
    simpa [BONG.reverseDualVector, Fin.rev] using
      b.bilin_dualVector_ambientVector (0 : Fin 2) (0 : Fin 2)
  have htail :
      q.orthogonalProjection b.head b.binarySecondVector =
        b.ambientVector 1 := by
    calc
      q.orthogonalProjection b.head b.binarySecondVector =
          (b.tail.head : V) := by
        simpa only [QuadraticSpace.projectionToOrthogonal_coe] using
          congrArg Subtype.val b.projectionToOrthogonal_binarySecondVector
      _ = (b.tail.ambientVector 0 : V) := by
        rw [b.tail.ambientVector_zero_eq_head]
      _ = b.ambientVector 1 := b.coe_ambientVector_tail 0
  have hsecond :
      q.bilin (b.reverseDualVector 1) (b.ambientVector 1) = 0 := by
    simpa [BONG.reverseDualVector, Fin.rev] using
      b.bilin_dualVector_ambientVector (0 : Fin 2) (1 : Fin 2)
  calc
    q.bilin (b.reverseDualVector 1) b.binarySecondVector =
        q.bilin (b.reverseDualVector 1)
          (q.lineProjection b.head b.binarySecondVector +
            q.orthogonalProjection b.head b.binarySecondVector) := by
      rw [q.lineProjection_add_orthogonalProjection]
    _ = q.bilin (b.reverseDualVector 1)
          (q.lineProjection b.head b.binarySecondVector) +
        q.bilin (b.reverseDualVector 1)
          (q.orthogonalProjection b.head b.binarySecondVector) := by
      rw [LinearMap.BilinForm.add_right]
    _ = (q.bilin b.head b.binarySecondVector /
          q.quadratic b.head) * 1 + 0 := by
      rw [q.lineProjection_apply, LinearMap.BilinForm.smul_right,
        hhead, htail, hsecond]
    _ = q.bilin b.head b.binarySecondVector /
        q.quadratic b.head := by ring

/-- Reverse the bilinear dual of the adapted integral basis. -/
noncomputable def reverseDualBinaryAdaptedBasis (b : BONG V q L 2) :
    Basis (Fin 2) K V :=
  (q.bilin.dualBasis q.nondegenerate b.binaryAdaptedFinBasis).reindex
    Fin.revPerm

/-- The first vector of the reversed adapted dual basis is the normalized
second BONG vector. -/
@[simp]
theorem reverseDualBinaryAdaptedBasis_zero (b : BONG V q L 2) :
    b.reverseDualBinaryAdaptedBasis 0 = b.reverseDualVector 0 := by
  rw [reverseDualBinaryAdaptedBasis, Module.Basis.reindex_apply,
    Fin.revPerm_symm]
  change (q.bilin.dualBasis q.nondegenerate b.binaryAdaptedFinBasis) 1 =
    b.reverseDualVector 0
  apply (q.bilin.dualBasis q.nondegenerate
    b.binaryAdaptedFinBasis).ext_elem_iff.mpr
  intro j
  rw [LinearMap.BilinForm.dualBasis_repr_apply,
    LinearMap.BilinForm.dualBasis_repr_apply,
    LinearMap.BilinForm.apply_dualBasis_left]
  fin_cases j
  · change (0 : K) = q.bilin (b.reverseDualVector 0)
        (b.binaryAdaptedFinBasis 0)
    rw [binaryAdaptedFinBasis_zero, ← b.ambientVector_zero_eq_head]
    exact (b.bilin_dualVector_ambientVector
      (1 : Fin 2) (0 : Fin 2)).symm
  · change (1 : K) = q.bilin (b.reverseDualVector 0)
        (b.binaryAdaptedFinBasis 1)
    rw [binaryAdaptedFinBasis_one,
      b.bilin_reverseDualVector_zero_binarySecondVector]

/-- The second vector of the reversed adapted dual basis differs from the
normalized first BONG vector only by a multiple of its first vector. -/
theorem reverseDualBinaryAdaptedBasis_one (b : BONG V q L 2) :
    b.reverseDualBinaryAdaptedBasis 1 =
      b.reverseDualVector 1 -
        (q.bilin b.head b.binarySecondVector / q.quadratic b.head) •
          b.reverseDualVector 0 := by
  rw [reverseDualBinaryAdaptedBasis, Module.Basis.reindex_apply,
    Fin.revPerm_symm]
  change (q.bilin.dualBasis q.nondegenerate b.binaryAdaptedFinBasis) 0 = _
  apply (q.bilin.dualBasis q.nondegenerate
    b.binaryAdaptedFinBasis).ext_elem_iff.mpr
  intro j
  rw [LinearMap.BilinForm.dualBasis_repr_apply,
    LinearMap.BilinForm.dualBasis_repr_apply,
    LinearMap.BilinForm.apply_dualBasis_left]
  fin_cases j
  · change (1 : K) = q.bilin
        (b.reverseDualVector 1 -
          (q.bilin b.head b.binarySecondVector / q.quadratic b.head) •
            b.reverseDualVector 0)
        (b.binaryAdaptedFinBasis 0)
    have hone : q.bilin (b.reverseDualVector 1)
        (b.ambientVector 0) = 1 := by
      simpa [BONG.reverseDualVector, Fin.rev] using
        b.bilin_dualVector_ambientVector (0 : Fin 2) (0 : Fin 2)
    have hzero : q.bilin (b.reverseDualVector 0)
        (b.ambientVector 0) = 0 := by
      simpa [BONG.reverseDualVector, Fin.rev] using
        b.bilin_dualVector_ambientVector (1 : Fin 2) (0 : Fin 2)
    rw [binaryAdaptedFinBasis_zero, ← b.ambientVector_zero_eq_head,
      LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      hone, hzero]
    simp
  · change (0 : K) = q.bilin
        (b.reverseDualVector 1 -
          (q.bilin b.head b.binarySecondVector / q.quadratic b.head) •
            b.reverseDualVector 0)
        (b.binaryAdaptedFinBasis 1)
    rw [binaryAdaptedFinBasis_one, LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.smul_left,
      b.bilin_reverseDualVector_one_binarySecondVector,
      b.bilin_reverseDualVector_zero_binarySecondVector]
    ring

/-- Orthogonal projection of the second adapted dual basis vector is exactly
the normalized first BONG vector. -/
theorem orthogonalProjection_reverseDualBinaryAdaptedBasis_one
    (b : BONG V q L 2) :
    q.orthogonalProjection (b.reverseDualVector 0)
        (b.reverseDualBinaryAdaptedBasis 1) =
      b.reverseDualVector 1 := by
  let c : K :=
    q.bilin b.head b.binarySecondVector / q.quadratic b.head
  have horth : q.bilin (b.reverseDualVector 0)
      (b.reverseDualVector 1) = 0 := by
    have h := (LinearMap.BilinForm.iIsOrtho_def.mp
      b.reverseDualBasis_iIsOrtho) (0 : Fin 2) (1 : Fin 2) (by decide)
    simpa only [b.reverseDualBasis_apply, b.reverseDualBasis_apply] using h
  have hself : q.bilin (b.reverseDualVector 0)
      (b.reverseDualVector 0) =
        q.quadratic (b.reverseDualVector 0) := rfl
  have hne : q.quadratic (b.reverseDualVector 0) ≠ 0 :=
    b.quadratic_reverseDualVector_ne_zero 0
  rw [b.reverseDualBinaryAdaptedBasis_one]
  change q.orthogonalProjection (b.reverseDualVector 0)
      (b.reverseDualVector 1 - c • b.reverseDualVector 0) = _
  rw [q.orthogonalProjection_apply, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_right, horth, hself]
  have hcoeff :
      (0 - c * q.quadratic (b.reverseDualVector 0)) /
          q.quadratic (b.reverseDualVector 0) = -c := by
    field_simp [hne]
    ring
  rw [hcoeff]
  module

/-- The reversed adapted dual basis integrally generates the actual dual
lattice, independently of the order relation between the two BONG values. -/
theorem basisLattice_reverseDualBinaryAdaptedBasis
    (b : BONG V q L 2) :
    Lattice.basisLattice b.reverseDualBinaryAdaptedBasis =
      Lattice.dualLattice q L := by
  rw [reverseDualBinaryAdaptedBasis, Lattice.basisLattice_reindex]
  calc
    Lattice.basisLattice
        (q.bilin.dualBasis q.nondegenerate b.binaryAdaptedFinBasis) =
        Lattice.dualLattice q
          (Lattice.basisLattice b.binaryAdaptedFinBasis) :=
      (Lattice.dualLattice_basisLattice q
        b.binaryAdaptedFinBasis).symm
    _ = Lattice.dualLattice q L := by
      rw [b.basisLattice_binaryAdaptedFinBasis]

/-- The first reverse-dual vector belongs to the integral dual lattice. -/
theorem reverseDualVector_zero_mem_dualLattice
    (b : BONG V q L 2) :
    b.reverseDualVector 0 ∈ Lattice.dualLattice q L := by
  rw [← b.basisLattice_reverseDualBinaryAdaptedBasis,
    ← b.reverseDualBinaryAdaptedBasis_zero]
  exact Submodule.subset_span ⟨0, rfl⟩

/-- In the decreasing-order branch, the first reverse-dual vector is a norm
generator of the integral dual.  Modularity supplies one known dual norm
generator; equality of their quadratic orders shows that their value ratio is
a valuation unit. -/
theorem reverseDualVector_zero_isNormGenerator_dual_of_order_ge
    (b : BONG V q L 2) (horder : b.order 1 ≤ b.order 0) :
    Lattice.IsNormGenerator q (Lattice.dualLattice q L)
      (b.reverseDualVector 0) := by
  rcases b.exists_isModular_iff_order_one_le_order_zero.mpr horder with
    ⟨a, hmodular⟩
  let x : V := (a⁻¹ : Kˣ) • b.head
  let y : V := b.reverseDualVector 0
  have generatorX : Lattice.IsNormGenerator q
      (Lattice.dualLattice q L) x := by
    simpa [x] using
      b.inverseModularParameter_smul_head_isNormGenerator_dual a hmodular
  have hxOrder : ord K (q.quadratic x) =
      ((-b.order 1 : Int) : WithTop Int) := by
    change ord K (q.quadratic ((a⁻¹ : Kˣ) • b.head)) = _
    rw [Units.smul_def]
    exact b.ord_quadratic_inverseModularParameter_smul_head a hmodular
  have hyOrder : ord K (q.quadratic y) =
      ((-b.order 1 : Int) : WithTop Int) := by
    simpa [y, BONG.reverseDualVector, Fin.rev] using
      b.ord_quadratic_reverseDualVector 0
  have hx : q.IsAnisotropic x := by
    intro hzero
    rw [hzero, ord_zero] at hxOrder
    exact WithTop.top_ne_coe hxOrder
  have hy : q.IsAnisotropic y := by
    change q.quadratic y ≠ 0
    simpa only [y] using b.quadratic_reverseDualVector_ne_zero 0
  have hyL : y ∈ Lattice.dualLattice q L := by
    simpa [y] using b.reverseDualVector_zero_mem_dualLattice
  let xu : Kˣ := Units.mk0 (q.quadratic x) hx
  let yu : Kˣ := Units.mk0 (q.quadratic y) hy
  have hxuOrder : ordUnit K xu = -b.order 1 := by
    apply WithTop.coe_injective
    simpa [xu] using hxOrder
  have hyuOrder : ordUnit K yu = -b.order 1 := by
    apply WithTop.coe_injective
    simpa [yu] using hyOrder
  apply (generatorX.iff_isValuationUnit_valueRatio hx hyL hy).2
  change Dyadic.IsValuationUnit K (((yu / xu : Kˣ) : K))
  rw [isValuationUnit_iff_ordUnit_eq_zero]
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    hxuOrder, hyuOrder]
  ring

/-- The singleton reverse-dual tail in the orthogonal complement of the
first reverse-dual vector. -/
private noncomputable def reverseDualBinaryModularTailVector
    (b : BONG V q L 2) (i : Fin 1) :
    q.vectorOrthogonal (b.reverseDualVector 0) := by
  refine ⟨b.reverseDualVector i.succ, ?_⟩
  rw [q.mem_vectorOrthogonal_iff]
  simpa only [b.reverseDualBasis_apply, b.reverseDualBasis_apply] using
    (LinearMap.BilinForm.iIsOrtho_def.mp
      b.reverseDualBasis_iIsOrtho) 0 i.succ (Fin.succ_ne_zero i).symm

@[simp]
private theorem coe_reverseDualBinaryModularTailVector
    (b : BONG V q L 2) (i : Fin 1) :
    (b.reverseDualBinaryModularTailVector i : V) =
      b.reverseDualVector i.succ :=
  rfl

/-- The one-dimensional tail basis used by the modular reverse-dual
construction. -/
private noncomputable def reverseDualBinaryModularTailBasis
    (b : BONG V q L 2) :
    Basis (Fin 1) K (q.vectorOrthogonal (b.reverseDualVector 0)) := by
  letI := b.basis.finiteDimensional_of_finite
  have hne : b.reverseDualBinaryModularTailVector 0 ≠ 0 := by
    intro hzero
    have hcoe : b.reverseDualVector 1 = 0 := by
      simpa using congrArg Subtype.val hzero
    exact b.quadratic_reverseDualVector_ne_zero 1 (by simp [hcoe])
  have hli : LinearIndependent K b.reverseDualBinaryModularTailVector :=
    linearIndependent_unique_iff.mpr hne
  have hx : q.IsAnisotropic (b.reverseDualVector 0) :=
    b.quadratic_reverseDualVector_ne_zero 0
  have hdim := q.finrank_vectorOrthogonal hx
  have hbfin : Module.finrank K V = 2 := b.length_eq_finrank.symm
  have htailfin : Module.finrank K
      (q.vectorOrthogonal (b.reverseDualVector 0)) = 1 := by
    omega
  exact basisOfLinearIndependentOfCardEqFinrank'
    b.reverseDualBinaryModularTailVector hli (by simp [htailfin])

@[simp]
private theorem coe_reverseDualBinaryModularTailBasis
    (b : BONG V q L 2) (i : Fin 1) :
    (b.reverseDualBinaryModularTailBasis i : V) =
      b.reverseDualVector i.succ := by
  rw [reverseDualBinaryModularTailBasis]
  simp

private theorem reverseDualBinaryModularTailBasis_iIsOrtho
    (b : BONG V q L 2) :
    (q.orthogonalSpace (b.reverseDualVector 0)
      (b.quadratic_reverseDualVector_ne_zero 0)).bilin.iIsOrtho
        b.reverseDualBinaryModularTailBasis := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

private theorem reverseDualBinaryModularTailBasis_ne_zero
    (b : BONG V q L 2) :
    (q.orthogonalSpace (b.reverseDualVector 0)
      (b.quadratic_reverseDualVector_ne_zero 0)).quadratic
        (b.reverseDualBinaryModularTailBasis 0) ≠ 0 := by
  change q.quadratic
    (b.reverseDualBinaryModularTailBasis 0 : V) ≠ 0
  rw [coe_reverseDualBinaryModularTailBasis]
  exact b.quadratic_reverseDualVector_ne_zero 1

/-- The adapted dual basis, after projection away from its first vector,
generates exactly the singleton reverse-dual tail lattice. -/
private theorem projectedLattice_reverseDualBinaryAdaptedBasis
    (b : BONG V q L 2) :
    (Lattice.basisLattice b.reverseDualBinaryAdaptedBasis).projectedLattice
        q (b.reverseDualVector 0)
        (b.quadratic_reverseDualVector_ne_zero 0) =
      Lattice.basisLattice b.reverseDualBinaryModularTailBasis := by
  let hx : q.IsAnisotropic (b.reverseDualVector 0) :=
    b.quadratic_reverseDualVector_ne_zero 0
  have htail : ∀ i,
      q.projectionToOrthogonal (b.reverseDualVector 0) hx
          (b.reverseDualBinaryAdaptedBasis i.succ) =
        b.reverseDualBinaryModularTailBasis i := by
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    apply Subtype.ext
    simpa [hx,
      QuadraticSpace.projectionToOrthogonal_coe] using
        b.orthogonalProjection_reverseDualBinaryAdaptedBasis_one
  exact Lattice.projectedLattice_basisLattice_fin_succ_of_projection_eq
    q b.reverseDualBinaryAdaptedBasis (b.reverseDualVector 0) hx
      b.reverseDualBinaryModularTailBasis
      b.reverseDualBinaryAdaptedBasis_zero htail

/-- The reversed normalized vectors form a BONG of the adapted dual basis
lattice in the modular/decreasing-order branch. -/
private noncomputable def reverseDualBinaryAdaptedBONG
    (b : BONG V q L 2) (horder : b.order 1 ≤ b.order 0) :
    BONG V q (Lattice.basisLattice b.reverseDualBinaryAdaptedBasis) 2 := by
  let x := b.reverseDualVector 0
  have hx : q.IsAnisotropic x :=
    b.quadratic_reverseDualVector_ne_zero 0
  have generator : Lattice.IsNormGenerator q
      (Lattice.basisLattice b.reverseDualBinaryAdaptedBasis) x := by
    rw [b.basisLattice_reverseDualBinaryAdaptedBasis]
    exact b.reverseDualVector_zero_isNormGenerator_dual_of_order_ge horder
  let tailBasis := b.reverseDualBinaryModularTailBasis
  let tailQ := q.orthogonalSpace x hx
  let tailBONG : BONG (q.vectorOrthogonal x) tailQ
      (Lattice.basisLattice tailBasis) 1 :=
    BONG.ofOrthogonalBasisFinOne tailQ tailBasis
      b.reverseDualBinaryModularTailBasis_iIsOrtho
      b.reverseDualBinaryModularTailBasis_ne_zero
  have hprojection :
      (Lattice.basisLattice b.reverseDualBinaryAdaptedBasis).projectedLattice
          q x hx = Lattice.basisLattice tailBasis := by
    simpa [x, hx, tailBasis] using
      b.projectedLattice_reverseDualBinaryAdaptedBasis
  exact BONG.cons x generator hx
    (tailBONG.castLattice hprojection.symm)

@[simp]
private theorem ambientVector_reverseDualBinaryAdaptedBONG
    (b : BONG V q L 2) (horder : b.order 1 ≤ b.order 0)
    (i : Fin 2) :
    (b.reverseDualBinaryAdaptedBONG horder).ambientVector i =
      b.reverseDualVector i := by
  cases i using Fin.cases with
  | zero =>
      rw [reverseDualBinaryAdaptedBONG, ambientVector_cons_zero]
  | succ i =>
      rw [reverseDualBinaryAdaptedBONG, ambientVector_cons_succ,
        ambientVector_castLattice, ambientVector_ofOrthogonalBasisFinOne]
      exact b.coe_reverseDualBinaryModularTailBasis i

/-- The binary reverse-dual BONG in the modular/decreasing-order branch. -/
noncomputable def reverseDualBinaryOfOrderGe
    (b : BONG V q L 2) (horder : b.order 1 ≤ b.order 0) :
    BONG V q (Lattice.dualLattice q L) 2 :=
  (b.reverseDualBinaryAdaptedBONG horder).castLattice
    b.basisLattice_reverseDualBinaryAdaptedBasis

@[simp]
theorem ambientVector_reverseDualBinaryOfOrderGe
    (b : BONG V q L 2) (horder : b.order 1 ≤ b.order 0)
    (i : Fin 2) :
    (b.reverseDualBinaryOfOrderGe horder).ambientVector i =
      b.reverseDualVector i := by
  rw [reverseDualBinaryOfOrderGe, ambientVector_castLattice,
    ambientVector_reverseDualBinaryAdaptedBONG]

/-- The modular/decreasing binary reverse-dual construction is good. -/
noncomputable def reverseDualBinaryGoodOfOrderGe
    (b : BONG V q L 2) (horder : b.order 1 ≤ b.order 0) :
    GoodBONG q (Lattice.dualLattice q L) 2 where
  toBONG := b.reverseDualBinaryOfOrderGe horder
  good := b.reverseDualBinaryOfOrderGe horder |>.isGood_binary

@[simp]
theorem ambientVector_reverseDualBinaryGoodOfOrderGe
    (b : BONG V q L 2) (horder : b.order 1 ≤ b.order 0)
    (i : Fin 2) :
    (b.reverseDualBinaryGoodOfOrderGe horder).toBONG.ambientVector i =
      b.reverseDualVector i :=
  b.ambientVector_reverseDualBinaryOfOrderGe horder i

/-- Every binary BONG has a good BONG of the dual lattice whose vectors are
the reversed normalized dual vectors. -/
noncomputable def reverseDualBinaryGood (b : BONG V q L 2) :
    GoodBONG q (Lattice.dualLattice q L) 2 := by
  by_cases horder : b.order 0 ≤ b.order 1
  · exact b.reverseDualBinaryGoodOfOrderLe horder
  · exact b.reverseDualBinaryGoodOfOrderGe (le_of_not_ge horder)

@[simp]
theorem ambientVector_reverseDualBinaryGood
    (b : BONG V q L 2) (i : Fin 2) :
    b.reverseDualBinaryGood.toBONG.ambientVector i =
      b.reverseDualVector i := by
  rw [reverseDualBinaryGood]
  split
  · exact b.ambientVector_reverseDualBinaryGoodOfOrderLe _ i
  · exact b.ambientVector_reverseDualBinaryGoodOfOrderGe _ i

end BONG

end Bong
