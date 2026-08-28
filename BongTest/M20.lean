/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M20 recursive-tail spinor smoke tests
-/

namespace BongTest.M20

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : ℕ}

example (b : BONG V q L (n + 1)) :
    Function.Injective b.tailAutomorphismHom :=
  b.tailAutomorphismHom_injective

example (b : BONG V q L (n + 1)) :
    Lattice.spinorNormImage
        (q := q.orthogonalSpace b.head b.head_isAnisotropic)
        (L := L.projectedLattice q b.head b.head_isAnisotropic) ⊆
      Lattice.spinorNormImage (q := q) (L := L) :=
  b.spinorNormImage_tail_subset

#print axioms Bong.BONG.tailAutomorphismHom_injective
#print axioms Bong.BONG.spinorNormImage_tail_subset
#print axioms Bong.BONG.integralSpinorNorm_tailAutomorphismHom

end

end BongTest.M20
