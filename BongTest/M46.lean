/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryStrictModular

/-!
# M46 complete binary modularity criterion smoke tests
-/

namespace BongTest.M46

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    2 * ordUnit K (b.binaryMixedPairingUnit hstrict) =
      b.order 0 + b.order 1 :=
  b.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict

example (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    Lattice.IsModular q L (b.binaryMixedPairingUnit hstrict) :=
  b.isModular_binaryMixedPairing_of_order_one_lt_order_zero hstrict

example (b : BONG V q L 2) :
    (∃ a : Kˣ, Lattice.IsModular q L a) ↔
      b.binaryOrderGap ≤ 0 :=
  b.exists_isModular_iff_binaryOrderGap_nonpos

example (b : BONG V q L 2) :
    (∃ a : Kˣ, Lattice.IsModular q L a) ↔
      b.order 1 ≤ b.order 0 :=
  b.exists_isModular_iff_order_one_le_order_zero

#print axioms Bong.Lattice.scaleIdeal_le_of_integralBasis
#print axioms Bong.BONG.two_mul_ordUnit_binaryMixedPairing_eq_order_add
#print axioms Bong.BONG.isModular_binaryMixedPairing_of_order_one_lt_order_zero
#print axioms Bong.BONG.exists_isModular_iff_binaryOrderGap_nonpos

end

end BongTest.M46
