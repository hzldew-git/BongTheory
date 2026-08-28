/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ApproximationDual

/-!
# M127 Beli 2019, Corollary 3.3 dual approximation smoke tests
-/

namespace BongTest.M127

open Bong

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n N : Nat}

example (b : BONG V q L N) (c : BONG V q M N)
    (hvalues : ∀ i, c.valueUnit i = (b.valueUnit (Fin.rev i))⁻¹)
    (i : Nat) (hi : i ≤ N) :
    c.prefixProduct i * b.valueProduct = b.prefixProduct (N - i) :=
  b.prefixProduct_mul_valueProduct_of_reverseValues c hvalues i hi

example (b : BONG.GoodBONG q L (n + 1))
    (c : BONG.GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (halpha : ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i))
    (i : Nat) (hi : i ≤ n + 1) :
    c.prefixAlphaCap i = b.prefixAlphaCap (n + 1 - i) :=
  b.prefixAlphaCap_eq_reverseDual c halpha i hi

example [Beli2006AlphaLaws.{u, v} K] [BONGStructuralLaws.{u, v} K]
    (b : BONG.GoodBONG q L (n + 1)) (i : Nat) (hi : i ≤ n + 1)
    (X : Kˣ) (hX : b.IsPrefixApproximation (n + 1 - i) X) :
    ∃ c : BONG.GoodBONG q (Lattice.dualLattice q L) (n + 1),
      b.IsReverseDualGoodBONG c ∧
      c.IsPrefixApproximation i (X * b.prefixProduct (n + 1)) :=
  b.exists_reverseDual_prefixApproximation i hi X hX

#print axioms Bong.BONG.prefixProduct_mul_valueProduct_of_reverseValues
#print axioms Bong.BONG.GoodBONG.prefixAlphaCap_eq_reverseDual
#print axioms Bong.BONG.GoodBONG.isPrefixApproximation_reverseDual
#print axioms Bong.BONG.GoodBONG.exists_reverseDual_prefixApproximation

end BongTest.M127
