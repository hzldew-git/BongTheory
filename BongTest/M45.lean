/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAdaptedBasis

/-!
# M45 binary adapted integral basis smoke tests
-/

namespace BongTest.M45

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) : b.binarySecondVector ∈ L :=
  b.binarySecondVector_mem

example (b : BONG V q L 2) :
    q.projectionToOrthogonal b.head b.head_isAnisotropic
        b.binarySecondVector = b.tail.head :=
  b.projectionToOrthogonal_binarySecondVector

example (b : BONG V q L 2) :
    q.quadratic
        (q.orthogonalProjection b.head b.binarySecondVector) =
      b.value 1 :=
  b.quadratic_projection_binarySecondVector

#print axioms Bong.Lattice.splittingEquiv_spec
#print axioms Bong.Lattice.adaptedIntegralBasisOfProjectedBasis_inl
#print axioms Bong.BONG.integralBasisFinOne
#print axioms Bong.BONG.quadratic_projection_binarySecondVector

end

end BongTest.M45
