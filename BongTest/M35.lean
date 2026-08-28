/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M35 unary rigidity and binary uniqueness smoke tests
-/

namespace BongTest.M35

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

example (b : BONG V q L 1) (c : BONG V q M 1)
    (h : b.order 0 = c.order 0) : L = M :=
  b.lattice_eq_of_order_eq c h

example (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head)
    (hgap : b.binaryOrderGap = c.binaryOrderGap) : L = M :=
  b.lattice_eq_of_head_eq_of_binaryOrderGap_eq c hhead hgap

#print axioms Bong.Lattice.principalIdeal_le_iff_ord_ge
#print axioms Bong.BONG.lattice_eq_of_order_eq
#print axioms Bong.BONG.lattice_eq_of_head_eq_of_binaryOrderGap_eq

end

end BongTest.M35
