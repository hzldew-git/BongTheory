/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.ValueIsometry
import Bong.Bong.UnaryBinaryModel

/-!
# The exact unary model BONG

The standard integral line with quadratic coefficient `a` has a canonical
unary BONG whose value is literally `a`.  Consequently every unary BONG is
canonically isometric to the standard line with its own value.  The chosen
isometry maps the BONG vector to the standard generator; this basis-level
compatibility is useful in consecutive-block replacement arguments.
-/

namespace Bong

open Dyadic
open Module

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The singleton basis of `K`, reindexed by `Fin 1`. -/
noncomputable def unaryModelBasisFinOne : Basis (Fin 1) K K :=
  (Basis.singleton Unit K).reindex finOneEquiv.symm

@[simp]
theorem unaryModelBasisFinOne_apply (i : Fin 1) :
    unaryModelBasisFinOne (K := K) i = 1 := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  simp [unaryModelBasisFinOne, Module.Basis.reindex_apply]

/-- Reindexing the singleton basis does not change its integral lattice. -/
theorem basisLattice_unaryModelBasisFinOne :
    Lattice.basisLattice (unaryModelBasisFinOne (K := K)) =
      unaryModelLattice (K := K) := by
  rw [unaryModelBasisFinOne, Lattice.basisLattice_reindex]
  rfl

/-- The exact one-entry BONG of the standard line with coefficient `a`. -/
noncomputable def unaryModelBONG (a : Kˣ) :
    BONG K (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K))
      (unaryModelLattice (K := K)) 1 := by
  let basis := unaryModelBasisFinOne (K := K)
  have horth :
      (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K)).bilin.iIsOrtho
        basis := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hne :
      (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K)).quadratic
          (basis 0) ≠ 0 := by
    simp [basis, QuadraticSpace.quadratic]
  exact (BONG.ofOrthogonalBasisFinOne
    (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K)) basis horth hne).castLattice
      basisLattice_unaryModelBasisFinOne

@[simp]
theorem unaryModelBONG_ambientVector (a : Kˣ) (i : Fin 1) :
    (unaryModelBONG a).ambientVector i = 1 := by
  rw [unaryModelBONG, ambientVector_castLattice,
    ambientVector_ofOrthogonalBasisFinOne, unaryModelBasisFinOne_apply]

@[simp]
theorem unaryModelBONG_value (a : Kˣ) (i : Fin 1) :
    (unaryModelBONG a).value i = (a : K) := by
  rw [← (unaryModelBONG a).quadratic_ambientVector i,
    unaryModelBONG_ambientVector]
  simp [QuadraticSpace.quadratic]

@[simp]
theorem unaryModelBONG_valueUnit (a : Kˣ) (i : Fin 1) :
    (unaryModelBONG a).valueUnit i = a := by
  apply Units.ext
  exact unaryModelBONG_value a i

/-- A unary BONG is isometric to the standard integral line carrying its
exact value. -/
noncomputable def unaryModelLatticeIsometry (b : BONG V q L 1) :
    Lattice.Isometry q
      (QuadraticSpace.rescaleUnit (b.valueUnit 0) (QuadraticSpace.line K))
      L (unaryModelLattice (K := K)) :=
  b.latticeIsometryOfValueEq (unaryModelBONG (b.valueUnit 0)) (by
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact congrArg Units.val (unaryModelBONG_valueUnit (b.valueUnit 0) 0).symm)

@[simp]
theorem unaryModelLatticeIsometry_apply_ambientVector
    (b : BONG V q L 1) (i : Fin 1) :
    b.unaryModelLatticeIsometry.toLinearEquiv (b.ambientVector i) = 1 := by
  rw [unaryModelLatticeIsometry,
    latticeIsometryOfValueEq_apply_ambientVector,
    unaryModelBONG_ambientVector]

end BONG

end Bong
