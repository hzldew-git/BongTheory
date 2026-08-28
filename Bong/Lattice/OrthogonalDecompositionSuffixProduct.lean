import Bong.Lattice.OrthogonalDecompositionSuffix
import Bong.Bong.BeliLemma41ProductModel

/-!
# Coordinate products for exact suffixes of orthogonal decompositions

When `k + (n + 1) = t`, the suffix beginning at `k` is the coordinate
product of precisely `n + 1` components.  This is the suffix counterpart
of `OrthogonalDecompositionPrefixProduct`.
-/

namespace Bong

open Dyadic Module

namespace Lattice
namespace OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t n k : Nat}

/-- The order-preserving identification of `Fin (n+1)` with an exact
suffix beginning at `k`. -/
def suffixIndexEquiv (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) : Fin (n + 1) ≃ D.SuffixIndex k where
  toFun i := by
    have hi : k + i.val < t := by omega
    exact ⟨⟨k + i.val, hi⟩, Nat.le_add_right k i.val⟩
  invFun i := ⟨i.1.val - k, by omega⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    dsimp
    omega

@[simp]
theorem suffixIndexEquiv_val
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) (i : Fin (n + 1)) :
    ((D.suffixIndexEquiv hkn i).1).val = k + i.val :=
  rfl

abbrev suffixBlockCarrier
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) (i : Fin (n + 1)) : Type v :=
  (D.component (D.suffixIndexEquiv hkn i).1).carrier

noncomputable abbrev suffixBlockSpace
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) (i : Fin (n + 1)) :=
  (D.component (D.suffixIndexEquiv hkn i).1).space

noncomputable abbrev suffixBlockLattice
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) (i : Fin (n + 1)) :=
  (D.component (D.suffixIndexEquiv hkn i).1).lattice

def suffixBasisIndexEquiv
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) :
    (Σ i : Fin (n + 1), (D.suffixBlockLattice hkn i).BasisIndex) ≃
      (Σ j : D.SuffixIndex k, (D.component j.1).lattice.BasisIndex) :=
  Equiv.sigmaCongr (D.suffixIndexEquiv hkn) (fun _ ↦ Equiv.refl _)

noncomputable def suffixAmbientBasisReindexed
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) :
    Basis (Σ i : Fin (n + 1),
        (D.suffixBlockLattice hkn i).BasisIndex) K (D.suffixCarrier k) :=
  (D.suffixAmbientBasis k).reindex (D.suffixBasisIndexEquiv hkn).symm

@[simp]
theorem coe_suffixAmbientBasisReindexed_apply
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t)
    (a : Σ i : Fin (n + 1), (D.suffixBlockLattice hkn i).BasisIndex) :
    ((D.suffixAmbientBasisReindexed hkn a : D.suffixCarrier k) : V) =
      ((D.component (D.suffixIndexEquiv hkn a.1).1).lattice.ambientBasis a.2 :
        (D.component (D.suffixIndexEquiv hkn a.1).1).carrier) := by
  rw [suffixAmbientBasisReindexed, Basis.reindex_apply]
  rcases a with ⟨i, ai⟩
  simpa [suffixBasisIndexEquiv, Equiv.sigmaCongr,
    Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft] using
      D.coe_suffixAmbientBasis_apply k
        (D.suffixBasisIndexEquiv hkn ⟨i, ai⟩)

noncomputable def suffixBlockProductLinearEquiv
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) :
    BONG.BlockProductSpace n (D.suffixBlockCarrier hkn) ≃ₗ[K]
      D.suffixCarrier k :=
  let sourceBasis := BONG.blockProductBasis n
    (D.suffixBlockCarrier hkn) (D.suffixBlockLattice hkn)
  sourceBasis.equiv (D.suffixAmbientBasisReindexed hkn) (Equiv.refl _)

set_option maxHeartbeats 0 in
-- Basis-coordinate normalization for a dependent finite product is expensive.
noncomputable def suffixBlockProductCarrierIsometry
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) :
    Isometry
      (BONG.blockOrthogonalForm n (D.suffixBlockCarrier hkn)
        (D.suffixBlockSpace hkn))
      (q.restrict (D.suffixCarrier k) (D.suffixCarrier_nondegenerate k))
      (BONG.blockProductLattice n (D.suffixBlockCarrier hkn)
        (D.suffixBlockLattice hkn))
      (D.suffixLattice k) := by
  let sourceBasis := BONG.blockProductBasis n
    (D.suffixBlockCarrier hkn) (D.suffixBlockLattice hkn)
  let targetBasis := D.suffixAmbientBasisReindexed hkn
  let f := D.suffixBlockProductLinearEquiv hkn
  have hmapBasis : ∀ a, f (sourceBasis a) = targetBasis a := by
    intro a
    change (sourceBasis.equiv targetBasis (Equiv.refl _))
      (sourceBasis a) = _
    simp
  refine
    { toLinearEquiv := f
      map_bilin := ?_
      map_mem := ?_ }
  · intro x y
    have hforms :
        (q.restrict (D.suffixCarrier k)
          (D.suffixCarrier_nondegenerate k)).bilin.comp
            f.toLinearMap f.toLinearMap =
          (BONG.blockOrthogonalForm n (D.suffixBlockCarrier hkn)
            (D.suffixBlockSpace hkn)).bilin := by
      apply LinearMap.BilinForm.ext_basis sourceBasis
      rintro ⟨i, ai⟩ ⟨j, aj⟩
      rw [LinearMap.BilinForm.comp_apply]
      change q.bilin (f (sourceBasis ⟨i, ai⟩) : V)
          (f (sourceBasis ⟨j, aj⟩) : V) = _
      rw [hmapBasis ⟨i, ai⟩, hmapBasis ⟨j, aj⟩]
      simp only [targetBasis, D.coe_suffixAmbientBasisReindexed_apply,
        BONG.blockOrthogonalForm_bilin_apply,
        sourceBasis, BONG.blockProductBasis, Pi.basis_apply]
      by_cases hij : i = j
      · subst j
        rw [Fintype.sum_eq_single i]
        · rw [Pi.single_eq_same, Pi.single_eq_same]
          rfl
        · intro z hzi
          rw [Pi.single_eq_of_ne hzi]
          simp
      · have hcomponent :
          (D.suffixIndexEquiv hkn i).1 ≠
            (D.suffixIndexEquiv hkn j).1 := by
          intro h
          apply hij
          exact (D.suffixIndexEquiv hkn).injective (Subtype.ext h)
        rw [D.orthogonal _ _ hcomponent]
        symm
        apply Finset.sum_eq_zero
        intro z _
        by_cases hzi : z = i
        · subst z
          rw [Pi.single_eq_of_ne hij]
          simp
        · rw [Pi.single_eq_of_ne hzi]
          simp
    exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y
  · intro x
    change x ∈ Lattice.basisLattice sourceBasis ↔
      f x ∈ D.suffixLattice k
    have htargetLattice :
        Lattice.basisLattice targetBasis = D.suffixLattice k := by
      dsimp only [targetBasis, suffixAmbientBasisReindexed]
      exact (Lattice.basisLattice_reindex (D.suffixAmbientBasis k)
        (D.suffixBasisIndexEquiv hkn).symm).trans rfl
    rw [← htargetLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    have hrepr : targetBasis.repr (f x) = sourceBasis.repr x := by
      change targetBasis.repr
        ((sourceBasis.equiv targetBasis (Equiv.refl _)) x) = _
      simp [Basis.equiv]
    rw [hrepr]

noncomputable def suffixCarrierPresentationIsometry
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    Isometry
      (q.restrict (D.suffixCarrier k) (D.suffixCarrier_nondegenerate k))
      (D.suffixQuadraticSublattice k).space
      (D.suffixLattice k) (D.suffixQuadraticSublattice k).lattice := by
  unfold suffixQuadraticSublattice
  exact Isometry.refl _ _

noncomputable def suffixBlockProductIsometry
    (D : OrthogonalDecomposition q L t)
    (hkn : k + (n + 1) = t) :
    Isometry
      (BONG.blockOrthogonalForm n (D.suffixBlockCarrier hkn)
        (D.suffixBlockSpace hkn))
      (D.suffixQuadraticSublattice k).space
      (BONG.blockProductLattice n (D.suffixBlockCarrier hkn)
        (D.suffixBlockLattice hkn))
      (D.suffixQuadraticSublattice k).lattice :=
  (D.suffixBlockProductCarrierIsometry hkn).trans
    (D.suffixCarrierPresentationIsometry k)

end OrthogonalDecomposition
end Lattice

end Bong
