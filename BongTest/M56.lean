/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryValueSet

/-!
# M56 norm-generator value-set smoke tests
-/

namespace BongTest.M56

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (hvalue : b.value 0 = 1) :
    Lattice.normGeneratorValueSet q L =
      Lattice.quadraticValueSet q L ∩
        {a | IsValuationUnit K a} :=
  b.normGeneratorValueSet_eq_quadraticValueSet_inter hvalue

example (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (hgap : 0 < b.binaryOrderGap) :
    Lattice.normGeneratorValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.principalIdeal (K := K) (b.value 1)) :=
  b.normGeneratorValueSet_subset_of_normalized_binaryOrderGap_pos
    hvalue hgap

#print axioms Bong.Lattice.principalIdeal_eq_iff_isValuationUnit_div
#print axioms Bong.Lattice.IsNormGenerator.iff_isValuationUnit_valueRatio
#print axioms Bong.Lattice.normGeneratorValueSet_eq_quadraticValueSet_inter
#print axioms Bong.BONG.normGeneratorValueSet_eq_quadraticValueSet_inter

end

end BongTest.M56
