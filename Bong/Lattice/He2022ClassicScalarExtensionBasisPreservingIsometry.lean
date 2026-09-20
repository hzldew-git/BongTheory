/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2022ClassicScalarExtensionBONGIsometry

/-!
# Basis-preserving scalar-extension isometry

Equal exact BONG values give an integral isometry that sends each pure tensor
of a lower BONG basis vector to the corresponding upper BONG basis vector.
This explicit vector map is stronger than an unqualified isometry class.
-/

namespace Bong.Lattice

open Dyadic Module
open scoped TensorProduct

universe u v w z

variable {F : Type u} {E : Type v} {V : Type w} {W : Type z}
  [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [DyadicContext F]
  [Field E] [CharZero E] [ValuativeRel E] [TopologicalSpace E] [DyadicContext E]
  [Algebra F E] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module E W]

/-- The integral isometry induced by matching Gram matrices can be chosen to
map every pure tensor of a lower BONG vector to the corresponding upper BONG
vector. The lattices here are precisely the two displayed basis lattices. -/
theorem scalarExtension_basisLattice_isIsometric_of_mappedValues_with_vectors
    {n : Nat} {q : QuadraticSpace F V} {L : Lattice F V}
    {r : QuadraticSpace E W} {M : Lattice E W}
    (b : BONG V q L n) (c : BONG W r M n)
    (hvalues : ∀ i, c.valueUnit i =
      Units.map (algebraMap F E) (b.valueUnit i))
    (hIntegral : ∀ a : IntegerRing F,
      Dyadic.IsIntegral E (algebraMap F E (a : F))) :
    ∃ f : Isometry (q.scalarExtension (E := E)) r
        (scalarExtension (E := E) (basisLattice b.basis))
        (basisLattice c.basis),
      ∀ i, f.toLinearEquiv ((1 : E) ⊗ₜ[F] b.ambientVector i) =
        c.ambientVector i := by
  rw [scalarExtension_basisLattice b.basis hIntegral]
  let sourceBasis := b.basis.baseChange E
  let targetBasis := c.basis
  let f : (E ⊗[F] V) ≃ₗ[E] W :=
    sourceBasis.equiv targetBasis (Equiv.refl (Fin n))
  have hgram (i j : Fin n) :
      r.bilin (targetBasis i) (targetBasis j) =
        (q.scalarExtension (E := E)).bilin (sourceBasis i) (sourceBasis j) := by
    simp only [sourceBasis, targetBasis, Module.Basis.baseChange_apply]
    change r.bilin (c.ambientVector i) (c.ambientVector j) =
      (q.scalarExtension (E := E)).bilin
        ((1 : E) ⊗ₜ[F] b.ambientVector i)
        ((1 : E) ⊗ₜ[F] b.ambientVector j)
    rw [← c.gramMatrix_apply, c.gramMatrix_eq_diagonal,
      QuadraticSpace.scalarExtension_bilin_tmul,
      ← b.gramMatrix_apply, b.gramMatrix_eq_diagonal]
    by_cases hij : i = j
    · subst j
      have hv := congrArg Units.val (hvalues i)
      change c.value i = algebraMap F E (b.value i) at hv
      simpa [Matrix.diagonal_apply_eq, Algebra.smul_def] using hv
    · simp [hij]
  refine ⟨{
    toLinearEquiv := f
    map_bilin := ?_
    map_mem := ?_
  }, ?_⟩
  · intro x y
    have hforms :
        r.bilin.comp f.toLinearMap f.toLinearMap =
          (q.scalarExtension (E := E)).bilin := by
      apply LinearMap.BilinForm.ext_basis sourceBasis
      intro i j
      rw [LinearMap.BilinForm.comp_apply]
      simpa [f] using hgram i j
    exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y
  · intro x
    rw [mem_basisLattice_iff_repr_mem_integerRing,
      mem_basisLattice_iff_repr_mem_integerRing]
    have hrepr : targetBasis.repr (f x) = sourceBasis.repr x := by
      simp [f, Basis.equiv]
    rw [hrepr]
  · intro i
    have hmap : f (sourceBasis i) = targetBasis i := by
      simp [f, Basis.equiv]
    simpa [BONG.ambientVector, sourceBasis, targetBasis,
      Module.Basis.baseChange_apply] using hmap

end Bong.Lattice
