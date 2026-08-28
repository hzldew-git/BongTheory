/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorGroup

/-!
# M68 Beli Lemma 3.7 smoke tests
-/

namespace BongTest.M68

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

variable [BinarySpinorLocalLaws.{u, v} K]

example (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroup K b.binaryUnitSquareClass :
        Set (SquareClass K)) :=
  b.spinorNormImage_eq_beliSpinorGroup

example (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroup K b.binaryDeterminantInvariant :
        Set (SquareClass K)) :=
  b.spinorNormImage_eq_beliSpinorGroup_determinantInvariant

#print axioms Bong.BONG.spinorNormImage_eq_beliSpinorGroup
#print axioms
  Bong.BONG.spinorNormImage_eq_beliSpinorGroup_determinantInvariant

end

end BongTest.M68
