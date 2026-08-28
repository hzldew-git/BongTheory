/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Structural
import Bong.Bong.Map

/-!
# Isometries determined by BONG values

Two BONGs of the same length with identical quadratic-value sequences are
isometric as quadratic lattices.  The ambient isometry is the basis map, and
the recursive BONG reconstruction theorem identifies its image lattice with
the target lattice.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Equal BONG value sequences determine a canonical lattice isometry which
maps the `i`th BONG vector to the `i`th BONG vector. -/
noncomputable def latticeIsometryOfValueEq
    (b : BONG V q L n) (c : BONG W r M n)
    (hvalues : ∀ i, b.value i = c.value i) :
    Lattice.Isometry q r L M := by
  let e : V ≃ₗ[K] W :=
    b.basis.equiv c.basis (Equiv.refl (Fin n))
  have hforms : r.bilin.comp e.toLinearMap e.toLinearMap = q.bilin := by
    apply LinearMap.BilinForm.ext_basis b.basis
    intro i j
    rw [LinearMap.BilinForm.comp_apply]
    change r.bilin (e (b.basis i)) (e (b.basis j)) =
      q.bilin (b.basis i) (b.basis j)
    simp only [e, Module.Basis.equiv_apply]
    change r.bilin (c.ambientVector i) (c.ambientVector j) =
      q.bilin (b.ambientVector i) (b.ambientVector j)
    by_cases hij : i = j
    · subst j
      change r.quadratic (c.ambientVector i) =
        q.quadratic (b.ambientVector i)
      rw [c.quadratic_ambientVector, b.quadratic_ambientVector,
        hvalues]
    · rw [(LinearMap.BilinForm.iIsOrtho_def.mp
          c.ambientVector_iIsOrtho) i j hij,
        (LinearMap.BilinForm.iIsOrtho_def.mp
          b.ambientVector_iIsOrtho) i j hij]
  let ambient : QuadraticSpace.Isometry q r :=
    { toLinearEquiv := e
      map_bilin := by
        intro x y
        exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y }
  let mapped := b.map ambient
  have mappedVectors : ∀ i, mapped.ambientVector i = c.ambientVector i := by
    intro i
    rw [BONG.ambientVector_map]
    change e (b.basis i) = c.basis i
    simp [e, Module.Basis.equiv]
  have hmap : Lattice.map e L = M :=
    mapped.lattice_eq_of_ambientVector_eq c mappedVectors
  exact
    { toLinearEquiv := e
      map_bilin := ambient.map_bilin
      map_mem := by
        intro x
        rw [← hmap, Lattice.map_mem_map_iff] }

@[simp]
theorem latticeIsometryOfValueEq_apply_ambientVector
    (b : BONG V q L n) (c : BONG W r M n)
    (hvalues : ∀ i, b.value i = c.value i) (i : Fin n) :
    (b.latticeIsometryOfValueEq c hvalues).toLinearEquiv
        (b.ambientVector i) = c.ambientVector i := by
  change (b.basis.equiv c.basis (Equiv.refl (Fin n))) (b.basis i) = c.basis i
  simp [Module.Basis.equiv]

end BONG

end Bong
