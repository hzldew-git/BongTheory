/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M31 reverse-dual basis-lattice smoke tests
-/

namespace BongTest.M31

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L n) (i : Fin n) :
    b.reverseDualBasis i = b.reverseDualVector i :=
  b.reverseDualBasis_apply i

example (b : BONG V q L n) :
    Lattice.basisLattice b.reverseDualBasis =
      Lattice.dualLattice q (Lattice.basisLattice b.basis) :=
  b.basisLattice_reverseDualBasis

#print axioms Bong.BONG.dualBasis_eq_dualVector
#print axioms Bong.BONG.basisLattice_reverseDualBasis

end

end BongTest.M31
