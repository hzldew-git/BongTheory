/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M33 unary reverse-dual BONG smoke tests
-/

namespace BongTest.M33

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L 1) :
    BONG.GoodBONG q (Lattice.dualLattice q L) 1 :=
  b.reverseDualUnaryGood

example (b : BONG V q L 1) (i : Fin 1) :
    b.reverseDualUnaryGood.toBONG.ambientVector i =
      b.reverseDualVector i :=
  b.ambientVector_reverseDualUnaryGood i

example (b : BONG V q L 1) (i : Fin 1) :
    b.reverseDualUnary.value i =
      ((b.valueUnit (Fin.rev i))⁻¹ : K) :=
  b.value_reverseDualUnary i

example (b : BONG V q L n) (i : Fin n) :
    (q.quadratic (b.reverseDualVector (Fin.rev i)))⁻¹ •
        b.reverseDualVector (Fin.rev i) =
      b.ambientVector i :=
  b.normalize_reverseDualVector_rev i

#print axioms Bong.BONG.reverseDualUnary
#print axioms Bong.BONG.reverseDualUnaryGood
#print axioms Bong.BONG.normalize_reverseDualVector_rev

end

end BongTest.M33
