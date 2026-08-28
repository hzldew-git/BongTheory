/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixChange

/-!
# M123 Beli 2019, prefix-change law discharge smoke tests
-/

namespace BongTest.M123

open Bong

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  [GoodBONGClassificationLaws.{u, v, v} K]

example (a a' : BONG.GoodBONG q L (n + 1)) (i : Nat) :
    a.prefixAlphaCap i ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.prefixProduct i * a'.prefixProduct i) :=
  Beli2006PrefixChangeLaws.prefixChangeDefectBound a a' i

example (a a' : BONG.GoodBONG q L n) :
    IsSquare (a.toBONG.valueProduct * a'.toBONG.valueProduct) :=
  a.isSquare_valueProduct_mul a'

#print axioms Bong.BONG.exists_valueProduct_eq_mul_square
#print axioms Bong.BONG.GoodBONG.isSquare_valueProduct_mul
#print axioms Bong.BONG.GoodBONG.prefixChangeDefectBound_of_classification
#print axioms Bong.prefixChangeLawsOfClassification

end BongTest.M123
