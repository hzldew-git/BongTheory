/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorGroup

/-!
# M63 Beli Lemma 3.11 interface smoke tests
-/

namespace BongTest.M63

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (y : V)
    (hy : Lattice.IsNormGenerator q L y) :
    IsValuationUnit K (b.normGeneratorValueRatioUnit y hy : K) :=
  b.normGeneratorValueRatioUnit_isValuationUnit y hy

variable [BinaryNormGeneratorLocalLaws.{u, v} K]

example (b : BONG V q L 2) :
    b.normGeneratorValueRatioClassSet =
      (beliNormGeneratorGroup K b.binaryParameter :
        Set (ValuationUnitClass K)) :=
  b.normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup

#print axioms Bong.BONG.normGeneratorValueRatioUnit_isValuationUnit
#print axioms Bong.BONG.normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup

end

end BongTest.M63
