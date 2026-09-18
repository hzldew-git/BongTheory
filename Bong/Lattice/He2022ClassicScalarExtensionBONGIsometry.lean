/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.BasisIsometry
import Bong.Lattice.He2022ClassicScalarExtensionLattice
import Bong.Bong.Basis
import Bong.Bong.BeliLemma43ConstructionProof
import Bong.Bong.MonotoneDiagonalization

/-!
# BONG bases and the scalar-extension lattice

This file compares the literal scalar extension of a BONG basis lattice with
any upper BONG basis lattice having the mapped values. The conclusion is a
quadratic-lattice isometry, not equality of two lattices in a common ambient.
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

/-- Mapped exact BONG values give an isometry between the literal extension
of the lower BONG basis lattice and the upper BONG basis lattice. -/
theorem scalarExtension_basisLattice_isIsometric_of_mappedValues
    {n : Nat} {q : QuadraticSpace F V} {L : Lattice F V}
    {r : QuadraticSpace E W} {M : Lattice E W}
    (b : BONG V q L n) (c : BONG W r M n)
    (hvalues : ∀ i, c.valueUnit i =
      Units.map (algebraMap F E) (b.valueUnit i))
    (hIntegral : ∀ a : IntegerRing F,
      Dyadic.IsIntegral E (algebraMap F E (a : F))) :
    IsIsometric (q.scalarExtension (E := E)) r
      (scalarExtension (E := E) (basisLattice b.basis))
      (basisLattice c.basis) := by
  rw [scalarExtension_basisLattice b.basis hIntegral]
  apply basisLattice_isIsometric_of_gram_eq
  intro i j
  simp only [Module.Basis.baseChange_apply]
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

/-- The basis-lattice result applies to specified lattices once both are
known to equal the integral spans of their BONG bases. -/
theorem scalarExtension_isIsometric_of_mappedValues
    {n : Nat} {q : QuadraticSpace F V} {L : Lattice F V}
    {r : QuadraticSpace E W} {M : Lattice E W}
    (b : BONG V q L n) (c : BONG W r M n)
    (hvalues : ∀ i, c.valueUnit i =
      Units.map (algebraMap F E) (b.valueUnit i))
    (hIntegral : ∀ a : IntegerRing F,
      Dyadic.IsIntegral E (algebraMap F E (a : F)))
    (hLower : L = basisLattice b.basis)
    (hUpper : M = basisLattice c.basis) :
    IsIsometric (q.scalarExtension (E := E)) r
      (scalarExtension (E := E) L) M := by
  simpa only [hLower, hUpper] using
    scalarExtension_basisLattice_isIsometric_of_mappedValues
      b c hvalues hIntegral

/-- A standard diagonal realization with nondecreasing BONG orders is
isometric to the literal scalar extension of the lower BONG lattice,
provided the lower BONG is an integral basis.  This is a generic bridge;
it does not identify a separately specified upper lattice. -/
theorem scalarExtension_isIsometric_diagonalRealization
    {n : Nat} {q : QuadraticSpace F V} {L : Lattice F V}
    (b : BONG V q L (n + 1))
    (R : BONG.DiagonalBONGRealization (K := E)
      (fun i ↦ Units.map (algebraMap F E) (b.valueUnit i)))
    (hIntegral : ∀ a : IntegerRing F,
      Dyadic.IsIntegral E (algebraMap F E (a : F)))
    (hLower : L = basisLattice b.basis)
    (hUpperMonotone : ∀ i j : Fin (n + 1), i ≤ j →
      R.bong.order i ≤ R.bong.order j) :
    IsIsometric (q.scalarExtension (E := E))
      (BONG.coefficientDiagonalSpace
        (fun i ↦ Units.map (algebraMap F E) (b.valueUnit i)))
      (scalarExtension (E := E) L) R.lattice := by
  exact scalarExtension_isIsometric_of_mappedValues b R.bong
    R.valueUnit_eq hIntegral hLower
    (R.bong.lattice_eq_basisLattice_of_order_monotone hUpperMonotone)

end Bong.Lattice
