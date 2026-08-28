/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremOneForward

/-!
# M92 Beli 2003, Theorem 1 forward-inclusion smoke tests
-/

namespace BongTest.M92

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L (n + 3)) (i : Fin (n + 1)) :
    b.theoremOneAlpha ≤ b.theoremOneTwoStepDepth i :=
  b.theoremOneAlpha_le_twoStepDepth i

variable [BeliLemma49Laws.{u, v} K]
  [BinarySpinorLocalLaws.{u, v} K]
  [BeliTheoremOneTernaryLaws.{u, v} K]

example (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    b.theoremOneRHS ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) :=
  b.theoremOneRHS_le_spinorNormImage hA

#print axioms Bong.BONG.theoremOneAlpha_le_twoStepDepth
#print axioms Bong.BONG.exists_ternarySegment_at_theoremOneAlpha
#print axioms Bong.BONG.theoremOneAdjacentFactor_le_spinorNormImage
#print axioms Bong.BONG.theoremOneCongruenceFactor_le_spinorNormImage
#print axioms Bong.BONG.theoremOneRHS_le_spinorNormImage

end

end BongTest.M92
