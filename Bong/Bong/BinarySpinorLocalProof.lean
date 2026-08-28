/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BinaryModularLowSpinor
import Bong.Bong.BinarySpinorNonnegative
import Bong.Bong.BinarySpinorGroup

/-!
# Unconditional proof of the local binary spinor formula

This file assembles the nonnegative diagonal calculation with the negative
modular calculation.  It discharges the former `BinarySpinorLocalLaws`
boundary used for Beli (2003), Lemma 3.7.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Beli (2003), Lemma 3.7 for every binary BONG, with no local-law
hypothesis. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_proved
    (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K)) := by
  by_cases hnonneg : 0 ≤ b.binaryOrderGap
  · exact b.spinorNormImage_eq_beliSpinorGroupRepresentative_of_nonnegative
      hnonneg
  · have hnegative : b.binaryOrderGap < 0 := lt_of_not_ge hnonneg
    exact b.spinorNormImage_eq_beliSpinorGroupRepresentative_of_negative
      hnegative

end BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The former binary local-law interface is now proved from the dyadic
field foundations. -/
noncomputable instance binarySpinorLocalLawsProved :
    BinarySpinorLocalLaws.{u, v} K where
  spinorNormImage_eq_representative b :=
    BONG.spinorNormImage_eq_beliSpinorGroupRepresentative_proved b

end Bong
