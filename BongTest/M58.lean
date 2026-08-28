/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAdaptedValues

/-!
# M58 error-ideal valuation criterion smoke tests
-/

namespace BongTest.M58

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (t : K) (ht : t ≠ 0)
    (hcross : ord K t ≤ ord K ((2 : K) * b.binaryMixedPairing))
    (hdiag : ord K t ≤
      ord K (q.quadratic b.binarySecondVector)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.principalIdeal (K := K) t) :=
  b.quadraticValueSet_subset_integralSquareResidueSet_of_error_ord_le
    hvalue t ht hcross hdiag

#print axioms Bong.BONG.binaryValueErrorIdeal_le_principalIdeal
#print axioms Bong.BONG.binaryValueErrorIdeal_le_principalIdeal_of_ord_le
#print axioms Bong.BONG.quadraticValueSet_subset_integralSquareResidueSet_of_error_ord_le

end

end BongTest.M58
