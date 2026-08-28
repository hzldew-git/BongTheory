/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryModularInvariant

/-!
# M43 modular binary order smoke tests
-/

namespace BongTest.M43

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) :
    Lattice.normIdeal q L =
      Lattice.principalIdeal (K := K) (b.value 0) :=
  b.normIdeal_eq_principal_value_zero

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    b.order 0 ≡ b.order 1 [ZMOD 2] :=
  b.orders_modEq_two_of_isModular a hmodular

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    ordUnit K a ≤ b.order 0 :=
  b.modularOrder_le_order_zero a hmodular

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    b.binaryOrderGap ≤ 0 :=
  b.binaryOrderGap_nonpos_of_isModular a hmodular

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    b.order 1 ≤ b.order 0 :=
  b.order_one_le_order_zero_of_isModular a hmodular

#print axioms Bong.BONG.normIdeal_eq_principal_value_zero
#print axioms Bong.BONG.orders_modEq_two_of_isModular
#print axioms Bong.BONG.modularOrder_le_order_zero
#print axioms Bong.BONG.binaryOrderGap_nonpos_of_isModular

end

end BongTest.M43
