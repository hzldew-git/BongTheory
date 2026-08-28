/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDefectAdaptedValues

/-!
# M70 Beli Corollary 3.10(b,c) smoke tests
-/

namespace BongTest.M70

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (hEven : Even b.binaryOrderGap)
    (hupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hdefect : (b.binaryCorollaryDefectCutoff : ℕ∞) ≤
      beliParameterDefect K b.binaryParameter) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.powerIdeal (K := K)
          (b.binaryCorollaryHighExponent : Int)) :=
  b.quadraticValueSet_subset_powerIdeal_of_high_defect
    hvalue hEven hupper hdefect

example (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (hEven : Even b.binaryOrderGap)
    (hupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K b.binaryParameter ≤
      (b.binaryCorollaryDefectCutoff : ℕ∞)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.powerIdeal (K := K)
          (b.binaryCorollaryLowExponent : Int)) :=
  b.quadraticValueSet_subset_powerIdeal_of_low_defect
    hvalue hEven hupper hdefect

#print axioms
  Bong.BONG.quadraticValueSet_subset_powerIdeal_of_high_defect
#print axioms
  Bong.BONG.quadraticValueSet_subset_powerIdeal_of_low_defect

end

end BongTest.M70
