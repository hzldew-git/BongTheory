/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BasisLattice
import Bong.Bong.Dual
import Bong.Lattice.OrthogonalBasis

/-!
# Reverse duality for unary BONGs

This file proves the rank-one case of Beli (2003), Lemma 4.8 without any
structural-law assumption: the normalized dual vector is a BONG, hence a good
BONG, of the integral dual lattice.
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

private theorem reverseDualOrthogonal_subsingleton (b : BONG V q L 1) :
    Subsingleton (q.vectorOrthogonal (b.reverseDualVector 0)) := by
  letI := b.basis.finiteDimensional_of_finite
  apply (Module.finrank_zero_iff (R := K)).mp
  have hdim := q.finrank_vectorOrthogonal
    (b.quadratic_reverseDualVector_ne_zero 0)
  have hbfin : Module.finrank K V = 1 := b.length_eq_finrank.symm
  omega

/-- A unary reverse-dual basis generates the actual dual lattice. -/
theorem basisLattice_reverseDualBasis_eq_dualLattice_unary
    (b : BONG V q L 1) :
    Lattice.basisLattice b.reverseDualBasis =
      Lattice.dualLattice q L := by
  calc
    Lattice.basisLattice b.reverseDualBasis =
        Lattice.dualLattice q (Lattice.basisLattice b.basis) :=
      b.basisLattice_reverseDualBasis
    _ = Lattice.dualLattice q L :=
      (congrArg (Lattice.dualLattice q) b.lattice_eq_basisLattice).symm

/-- The reverse-dual vector as a BONG of its own basis lattice. -/
private noncomputable def reverseDualUnaryBasisBONG (b : BONG V q L 1) :
    BONG V q (Lattice.basisLattice b.reverseDualBasis) 1 := by
  let x := b.reverseDualVector 0
  have hx : q.IsAnisotropic x :=
    b.quadratic_reverseDualVector_ne_zero 0
  have generator : Lattice.IsNormGenerator q
      (Lattice.basisLattice b.reverseDualBasis) x := by
    simpa [x] using Lattice.isNormGenerator_basisLattice_fin_one
      q b.reverseDualBasis b.reverseDualBasis_iIsOrtho
  exact BONG.cons x generator hx
    (BONG.nil (q.orthogonalSpace x hx)
      ((Lattice.basisLattice b.reverseDualBasis).projectedLattice q x hx)
      b.reverseDualOrthogonal_subsingleton)

@[simp]
private theorem ambientVector_reverseDualUnaryBasisBONG
    (b : BONG V q L 1) :
    (reverseDualUnaryBasisBONG b).ambientVector 0 =
      b.reverseDualVector 0 := by
  rw [reverseDualUnaryBasisBONG, ambientVector_cons_zero]

/-- The unconditional reverse-dual unary BONG of the integral dual lattice. -/
noncomputable def reverseDualUnary (b : BONG V q L 1) :
    BONG V q (Lattice.dualLattice q L) 1 :=
  (reverseDualUnaryBasisBONG b).castLattice
    b.basisLattice_reverseDualBasis_eq_dualLattice_unary

@[simp]
theorem ambientVector_reverseDualUnary (b : BONG V q L 1) (i : Fin 1) :
    b.reverseDualUnary.ambientVector i = b.reverseDualVector i := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rw [reverseDualUnary, ambientVector_castLattice,
    ambientVector_reverseDualUnaryBasisBONG]

/-- The unary dual BONG value is the reciprocal original value. -/
@[simp]
theorem value_reverseDualUnary (b : BONG V q L 1) (i : Fin 1) :
    b.reverseDualUnary.value i =
      ((b.valueUnit (Fin.rev i))⁻¹ : K) := by
  rw [← b.reverseDualUnary.quadratic_ambientVector,
    b.ambientVector_reverseDualUnary,
    b.quadratic_reverseDualVector]

/-- The unary reverse-dual BONG is automatically good. -/
noncomputable def reverseDualUnaryGood (b : BONG V q L 1) :
    GoodBONG q (Lattice.dualLattice q L) 1 where
  toBONG := b.reverseDualUnary
  good := b.reverseDualUnary.isGood_of_length_le_two (by omega)

@[simp]
theorem ambientVector_reverseDualUnaryGood (b : BONG V q L 1)
    (i : Fin 1) :
    b.reverseDualUnaryGood.toBONG.ambientVector i =
      b.reverseDualVector i :=
  b.ambientVector_reverseDualUnary i

end BONG

end Bong
