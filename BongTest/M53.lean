/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorInclusion

/-!
# M53 binary spinor-image inclusion smoke tests
-/

namespace BongTest.M53

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

example (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M) :
    Lattice.spinorNormImage (q := q) (L := L) ⊆
      Lattice.spinorNormImage (q := q) (L := M) :=
  Lattice.spinorNormImage_subset_of_binary_commonHead
    b c hhead hLM

#print axioms Bong.Lattice.integralSpinorNorm_binaryInclusionHom
#print axioms Bong.Lattice.spinorNormImage_subset_of_binary_commonHead

end

end BongTest.M53
