/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M34 diagonal binary reverse-dual BONG smoke tests
-/

namespace BongTest.M34

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (h : b.order 0 ≤ b.order 1) :
    BONG.GoodBONG q (Lattice.dualLattice q L) 2 :=
  b.reverseDualBinaryGoodOfOrderLe h

example (b : BONG V q L 2) (h : b.order 0 ≤ b.order 1)
    (i : Fin 2) :
    (b.reverseDualBinaryGoodOfOrderLe h).toBONG.ambientVector i =
      b.reverseDualVector i :=
  b.ambientVector_reverseDualBinaryGoodOfOrderLe h i

example (b : BONG V q L 2) (h : b.order 0 ≤ b.order 1)
    (i : Fin 2) :
    (b.reverseDualBinaryOfOrderLe h).value i =
      ((b.valueUnit (Fin.rev i))⁻¹ : K) :=
  b.value_reverseDualBinaryOfOrderLe h i

#print axioms Bong.Lattice.projectedLattice_basisLattice_fin_succ
#print axioms Bong.BONG.reverseDualBinaryOfOrderLe
#print axioms Bong.BONG.reverseDualBinaryGoodOfOrderLe

end

end BongTest.M34
