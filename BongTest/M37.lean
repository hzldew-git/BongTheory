/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M37 binary orthogonal-group inclusion smoke tests
-/

namespace BongTest.M37

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

example (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M) :
    Lattice.IntegralOrthogonalGroup q L →*
      Lattice.IntegralOrthogonalGroup q M :=
  Lattice.IntegralOrthogonalGroup.binaryInclusionHom b c hhead hLM

example (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M) :
    Function.Injective
      (Lattice.IntegralOrthogonalGroup.binaryInclusionHom
        b c hhead hLM) :=
  Lattice.IntegralOrthogonalGroup.binaryInclusionHom_injective
    b c hhead hLM

#print axioms Bong.BONG.map_eq_of_le_of_head_eq
#print axioms Bong.Lattice.IntegralOrthogonalGroup.binaryInclusionHom
#print axioms Bong.Lattice.IntegralOrthogonalGroup.binaryInclusionHom_injective

end

end BongTest.M37
