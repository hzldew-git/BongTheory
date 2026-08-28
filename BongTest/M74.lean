/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryParameterSpinorMembership

/-!
# M74 Beli 2003, paragraph 3.16, complete smoke tests
-/

namespace BongTest.M74

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

variable [BinarySpinorLocalLaws.{u, v} K]
  [BinaryNormGeneratorLocalLaws.{u, v} K]

example (b : BONG V q L 2) :
    beliNormGeneratorSquareClassGroup K b.binaryParameter ≤
        beliSpinorGroup K b.binaryUnitSquareClass ∧
      squareClass K b.binaryParameter ∈
        beliSpinorGroup K b.binaryUnitSquareClass :=
  b.beliParagraph316

#print axioms Bong.BONG.reflectionIsometry_zero_trans_one_eq_negOne
#print axioms
  Bong.BONG.integralSpinorNorm_negOneAutomorphism_eq_binaryParameter
#print axioms Bong.BONG.beliParagraph316

end


end BongTest.M74
