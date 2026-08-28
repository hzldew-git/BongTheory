/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIDefectComplete
import Bong.Bong.DiagonalTailCancellation

/-!
# Beli (2019), Lemma 9.12: common-tail prefix transfer for type III

The type-III construction replaces only the first three diagonal
coefficients.  The complete source and image diagonal spaces represent one
another, and all coefficients in their common tail agree literally.  Common
suffix cancellation therefore identifies every prefix of length at least
three in the direction needed for conditions 2.1(iii) and (iv).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

/-- Every source prefix of length at least three is represented by the
corresponding prefix of the literal type-III image. -/
theorem beli2019Lemma912_typeIII_sourcePrefix_represents_targetPrefix
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (k : Nat) (hkThree : 3 ≤ k) (hk : k ≤ T + 3) :
    DiagonalRepresents
      ((a.castLength hlength).prefixValues k hk)
      ((I.bong.castLength hlength).prefixValues k hk) := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hfull : DiagonalRepresents source.toBONG.value target.toBONG.value :=
    source.toBONG.diagonalRepresents_values target.toBONG
  have htail : ∀ i, k ≤ i.val → source.toBONG.value i =
      target.toBONG.value i := by
    intro i hi
    have hiThree : 3 ≤ i.val := hkThree.trans hi
    have hu :=
      beli2019Lemma912TypeIIIIndexPData_valueUnit_castLength_eq_source_of_three_le
        a D I hlength i hiThree
    have hv := congrArg Units.val hu
    simpa only [source, target, GoodBONG.coe_valueUnit,
      GoodBONG.value] using hv.symm
  have hcancelled := DiagonalRepresents.cancel_common_suffix
    source.toBONG.value target.toBONG.value hk
    source.toBONG.value_ne_zero target.toBONG.value_ne_zero htail hfull
  change DiagonalRepresents
    (fun i : Fin k => source.toBONG.value ⟨i.val, i.isLt.trans_le hk⟩)
    (fun i : Fin k => target.toBONG.value ⟨i.val, i.isLt.trans_le hk⟩)
  exact hcancelled

end BONG.GoodBONG

end Bong
