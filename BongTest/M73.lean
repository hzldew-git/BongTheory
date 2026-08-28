/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorSpinorInclusion

/-!
# M73 Beli 2003, paragraph 3.16, first assertion
-/

namespace BongTest.M73

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

variable [BinaryNormGeneratorLocalLaws.{u, v} K]
  [BinarySpinorLocalLaws.{u, v} K]

example (b : BONG V q L 2) :
    beliNormGeneratorSquareClassGroup K b.binaryParameter ≤
      beliSpinorGroup K b.binaryUnitSquareClass :=
  b.beliNormGeneratorSquareClassGroup_le_beliSpinorGroup

#print axioms
  Bong.BONG.beliNormGeneratorSquareClassGroup_le_beliSpinorGroup

end


end BongTest.M73
