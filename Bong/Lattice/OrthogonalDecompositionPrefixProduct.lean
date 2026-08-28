/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionPrefix
import Bong.Bong.BeliLemma41ProductModel

/-!
# Coordinate products for prefixes of orthogonal decompositions

Every nonempty prefix of an integral orthogonal decomposition is integrally
isometric to the coordinate product of the components occurring before the
cut.  The construction is basis-theoretic and therefore avoids identifying
dependent subspace carriers by hand.
-/

namespace Bong

open Dyadic Module

namespace Lattice
namespace OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}

/-- The order-preserving identification of `Fin k` with the indices of a
prefix of length `k`. -/
def prefixIndexEquiv (D : OrthogonalDecomposition q L t)
    (k : Nat) (hk : k ≤ t) : Fin k ≃ D.PrefixIndex k where
  toFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, i.isLt⟩
  invFun i := ⟨i.1.val, i.2⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

@[simp]
theorem prefixIndexEquiv_val
    (D : OrthogonalDecomposition q L t)
    (k : Nat) (hk : k ≤ t) (i : Fin k) :
    ((D.prefixIndexEquiv k hk i).1).val = i.val :=
  rfl

/-- Carrier of a component in the standard coordinate presentation of a
prefix. -/
abbrev prefixBlockCarrier
    (D : OrthogonalDecomposition q L t)
    (hk : n + 1 ≤ t) (i : Fin (n + 1)) : Type v :=
  (D.component (D.prefixIndexEquiv (n + 1) hk i).1).carrier

/-- Quadratic form of a component in the standard prefix presentation. -/
noncomputable abbrev prefixBlockSpace
    (D : OrthogonalDecomposition q L t)
    (hk : n + 1 ≤ t) (i : Fin (n + 1)) :=
  (D.component (D.prefixIndexEquiv (n + 1) hk i).1).space

/-- Lattice of a component in the standard prefix presentation. -/
noncomputable abbrev prefixBlockLattice
    (D : OrthogonalDecomposition q L t)
    (hk : n + 1 ≤ t) (i : Fin (n + 1)) :=
  (D.component (D.prefixIndexEquiv (n + 1) hk i).1).lattice

/-- Reindex the concatenated prefix basis by the standard finite ordinal. -/
def prefixBasisIndexEquiv
    (D : OrthogonalDecomposition q L t) (hk : n + 1 ≤ t) :
    (Σ i : Fin (n + 1),
        (D.prefixBlockLattice hk i).BasisIndex) ≃
      (Σ j : D.PrefixIndex (n + 1),
        (D.component j.1).lattice.BasisIndex) :=
  Equiv.sigmaCongr (D.prefixIndexEquiv (n + 1) hk)
    (fun _ => Equiv.refl _)

/-- The intrinsic prefix basis, reindexed by the coordinate-product basis
index. -/
noncomputable def prefixAmbientBasisReindexed
    (D : OrthogonalDecomposition q L t) (hk : n + 1 ≤ t) :
    Basis (Σ i : Fin (n + 1),
        (D.prefixBlockLattice hk i).BasisIndex) K
      (D.prefixCarrier (n + 1)) :=
  (D.prefixAmbientBasis (n + 1)).reindex
    (D.prefixBasisIndexEquiv hk).symm

@[simp]
theorem coe_prefixAmbientBasisReindexed_apply
    (D : OrthogonalDecomposition q L t) (hk : n + 1 ≤ t)
    (a : Σ i : Fin (n + 1),
      (D.prefixBlockLattice hk i).BasisIndex) :
    ((D.prefixAmbientBasisReindexed hk a : D.prefixCarrier (n + 1)) : V) =
      ((D.component
          (D.prefixIndexEquiv (n + 1) hk a.1).1).lattice.ambientBasis a.2 :
          (D.component
            (D.prefixIndexEquiv (n + 1) hk a.1).1).carrier) := by
  rw [prefixAmbientBasisReindexed, Basis.reindex_apply]
  exact D.coe_prefixAmbientBasis_apply (n + 1)
    (D.prefixBasisIndexEquiv hk a)

/-- The coordinate-product linear equivalence for a nonempty prefix. -/
noncomputable def prefixBlockProductLinearEquiv
    (D : OrthogonalDecomposition q L t) (hk : n + 1 ≤ t) :
    BONG.BlockProductSpace n (D.prefixBlockCarrier hk) ≃ₗ[K]
      D.prefixCarrier (n + 1) :=
  let sourceBasis := BONG.blockProductBasis n
    (D.prefixBlockCarrier hk) (D.prefixBlockLattice hk)
  sourceBasis.equiv (D.prefixAmbientBasisReindexed hk) (Equiv.refl _)

set_option maxHeartbeats 0 in
-- Basis-coordinate normalization for a dependent finite product is expensive.
/-- The coordinate product of the first `n+1` components is integrally
isometric to the explicit restricted-space presentation of the prefix. -/
noncomputable def prefixBlockProductCarrierIsometry
    (D : OrthogonalDecomposition q L t) (hk : n + 1 ≤ t) :
    Isometry
      (BONG.blockOrthogonalForm n (D.prefixBlockCarrier hk)
        (D.prefixBlockSpace hk))
      (q.restrict (D.prefixCarrier (n + 1))
        (D.prefixCarrier_nondegenerate (n + 1)))
      (BONG.blockProductLattice n (D.prefixBlockCarrier hk)
        (D.prefixBlockLattice hk))
      (D.prefixLattice (n + 1)) := by
  let sourceBasis := BONG.blockProductBasis n
    (D.prefixBlockCarrier hk) (D.prefixBlockLattice hk)
  let targetBasis := D.prefixAmbientBasisReindexed hk
  let f := D.prefixBlockProductLinearEquiv hk
  have hmapBasis : ∀ a, f (sourceBasis a) = targetBasis a := by
    intro a
    change
      (sourceBasis.equiv targetBasis (Equiv.refl _)) (sourceBasis a) = _
    simp
  refine
    { toLinearEquiv := f
      map_bilin := ?_
      map_mem := ?_ }
  · intro x y
    have hforms :
        (q.restrict (D.prefixCarrier (n + 1))
          (D.prefixCarrier_nondegenerate (n + 1))).bilin.comp
            f.toLinearMap f.toLinearMap =
          (BONG.blockOrthogonalForm n (D.prefixBlockCarrier hk)
            (D.prefixBlockSpace hk)).bilin := by
      apply LinearMap.BilinForm.ext_basis sourceBasis
      rintro ⟨i, ai⟩ ⟨j, aj⟩
      rw [LinearMap.BilinForm.comp_apply]
      change q.bilin
          (f (sourceBasis ⟨i, ai⟩) : V)
          (f (sourceBasis ⟨j, aj⟩) : V) = _
      rw [hmapBasis ⟨i, ai⟩, hmapBasis ⟨j, aj⟩]
      simp only [targetBasis,
        D.coe_prefixAmbientBasisReindexed_apply,
        BONG.blockOrthogonalForm_bilin_apply,
        sourceBasis, BONG.blockProductBasis, Pi.basis_apply]
      by_cases hij : i = j
      · subst j
        rw [Fintype.sum_eq_single i]
        · rw [Pi.single_eq_same, Pi.single_eq_same]
          rfl
        · intro k hki
          rw [Pi.single_eq_of_ne hki]
          simp
      · have hcomponent :
          (D.prefixIndexEquiv (n + 1) hk i).1 ≠
            (D.prefixIndexEquiv (n + 1) hk j).1 := by
          intro h
          apply hij
          exact (D.prefixIndexEquiv (n + 1) hk).injective
            (Subtype.ext h)
        rw [D.orthogonal _ _ hcomponent]
        symm
        apply Finset.sum_eq_zero
        intro k _
        by_cases hki : k = i
        · subst k
          rw [Pi.single_eq_of_ne hij]
          simp
        · rw [Pi.single_eq_of_ne hki]
          simp
    exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y
  · intro x
    change x ∈ Lattice.basisLattice sourceBasis ↔
      f x ∈ D.prefixLattice (n + 1)
    have htargetLattice :
        Lattice.basisLattice targetBasis = D.prefixLattice (n + 1) := by
      dsimp only [targetBasis, prefixAmbientBasisReindexed]
      exact (Lattice.basisLattice_reindex
        (D.prefixAmbientBasis (n + 1))
        (D.prefixBasisIndexEquiv hk).symm).trans rfl
    rw [← htargetLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    have hrepr : targetBasis.repr (f x) = sourceBasis.repr x := by
      change
        targetBasis.repr
          ((sourceBasis.equiv targetBasis (Equiv.refl _)) x) = _
      simp [Basis.equiv]
    rw [hrepr]

/-- The explicit restricted-space presentation is definitionally the
quadratic sublattice used by the prefix API. -/
noncomputable def prefixCarrierPresentationIsometry
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    Isometry
      (q.restrict (D.prefixCarrier k) (D.prefixCarrier_nondegenerate k))
      (D.prefixQuadraticSublattice k).space
      (D.prefixLattice k)
      (D.prefixQuadraticSublattice k).lattice := by
  unfold prefixQuadraticSublattice
  exact Isometry.refl _ _

/-- The coordinate product of the first `n+1` components is integrally
isometric to the actual prefix quadratic sublattice. -/
noncomputable def prefixBlockProductIsometry
    (D : OrthogonalDecomposition q L t) (hk : n + 1 ≤ t) :
    Isometry
      (BONG.blockOrthogonalForm n (D.prefixBlockCarrier hk)
        (D.prefixBlockSpace hk))
      (D.prefixQuadraticSublattice (n + 1)).space
      (BONG.blockProductLattice n (D.prefixBlockCarrier hk)
        (D.prefixBlockLattice hk))
      (D.prefixQuadraticSublattice (n + 1)).lattice :=
  (D.prefixBlockProductCarrierIsometry hk).trans
    (D.prefixCarrierPresentationIsometry (n + 1))

end OrthogonalDecomposition
end Lattice

end Bong
