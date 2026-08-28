/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAdaptedValues

/-!
# M57 adapted binary value-formula smoke tests
-/

namespace BongTest.M57

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (hvalue : b.value 0 = 1) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet b.binaryValueErrorIdeal :=
  b.quadraticValueSet_subset_binaryValueErrorIdeal hvalue

example (b : BONG V q L 2) (hvalue : b.value 0 = 1) :
    Lattice.normGeneratorValueSet q L ⊆
      Lattice.integralSquareResidueSet b.binaryValueErrorIdeal :=
  b.normGeneratorValueSet_subset_binaryValueErrorIdeal hvalue

#print axioms Bong.BONG.exists_binaryIntegralBasis_coefficients
#print axioms Bong.BONG.quadratic_eq_of_binaryIntegralBasis_coefficients
#print axioms Bong.BONG.quadraticValueSet_subset_binaryValueErrorIdeal
#print axioms Bong.BONG.normGeneratorValueSet_subset_binaryValueErrorIdeal

end

end BongTest.M57
