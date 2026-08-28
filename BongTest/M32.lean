/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M32 orthogonal basis-lattice and binary diagonalization smoke tests
-/

namespace BongTest.M32

open Bong Bong.Dyadic
open Module

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L n) :
    Lattice.normIdeal q (Lattice.basisLattice b.basis) =
      Submodule.span (IntegerRing K) (Set.range b.value) :=
  b.normIdeal_basisLattice

example (b : BONG V q L (n + 1)) :
    (Lattice.basisLattice b.basis).projectedLattice q b.head
        b.head_isAnisotropic =
      Lattice.basisLattice b.tail.basis :=
  b.projectedLattice_basisLattice

example (b : BONG V q L 1) : L = Lattice.basisLattice b.basis :=
  b.lattice_eq_basisLattice

example (b : BONG V q L 2) (h : b.order 0 ≤ b.order 1) :
    L = Lattice.basisLattice b.basis :=
  b.lattice_eq_basisLattice_of_order_le h

#print axioms Bong.Lattice.normIdeal_basisLattice_of_iIsOrtho
#print axioms Bong.BONG.lattice_eq_basisLattice
#print axioms Bong.BONG.lattice_eq_basisLattice_of_order_le

end

end BongTest.M32
