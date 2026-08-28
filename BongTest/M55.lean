/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryValueSet

/-!
# M55 binary quadratic-value set smoke tests
-/

namespace BongTest.M55

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (hgap : 0 < b.binaryOrderGap) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.principalIdeal (K := K) (b.value 1)) :=
  b.quadraticValueSet_subset_of_normalized_binaryOrderGap_pos hvalue hgap

#print axioms Bong.BONG.quadratic_eq_binaryBasis_repr
#print axioms Bong.BONG.quadraticValueSet_subset_integralSquareResidueSet_value_one
#print axioms Bong.BONG.quadraticValueSet_subset_of_normalized_binaryOrderGap_pos

end

end BongTest.M55
