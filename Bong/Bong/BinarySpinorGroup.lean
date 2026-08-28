/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAuxiliarySpinorGroup
import Bong.Bong.BinarySpinorInclusion

/-!
# Binary integral spinor norms

Beli (2003), Lemma 3.7 combines several earlier local spinor-norm theorems of
Hsia and Xu.  That external local calculation is isolated in
`BinarySpinorLocalLaws`.  This file proves the conversion from its
representative formula to Definition 4 on the quotient and then to Beli's
intrinsic lattice invariant `a(L)`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The cited local binary spinor-norm calculation underlying Beli (2003),
Lemma 3.7. -/
class BinarySpinorLocalLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  spinorNormImage_eq_representative
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K))

variable [BinarySpinorLocalLaws.{u, v} K]

namespace BONG

/-- Beli (2003), Lemma 3.7 in terms of the BONG parameter class. -/
theorem spinorNormImage_eq_beliSpinorGroup
    (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroup K b.binaryUnitSquareClass :
        Set (SquareClass K)) := by
  calc
    Lattice.spinorNormImage (q := q) (L := L) =
        (beliSpinorGroupRepresentative K b.binaryParameter :
          Set (SquareClass K)) :=
      BinarySpinorLocalLaws.spinorNormImage_eq_representative b
    _ = (beliSpinorGroup K b.binaryUnitSquareClass :
        Set (SquareClass K)) := by
      rw [binaryUnitSquareClass, beliSpinorGroup_unitSquareClass]

/-- Lemma 3.7 in the paper's intrinsic notation `θ(L) = G(a(L))`. -/
theorem spinorNormImage_eq_beliSpinorGroup_determinantInvariant
    (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroup K b.binaryDeterminantInvariant :
        Set (SquareClass K)) := by
  rw [b.binaryDeterminantInvariant_eq_parameter]
  exact b.spinorNormImage_eq_beliSpinorGroup

end BONG

end Bong
