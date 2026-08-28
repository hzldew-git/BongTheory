/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIICentralComplete

/-!
# Beli (2019), Lemma 9.12: type-III condition (iv)

For a long trigger, the next order is already in the common tail.  The
current order is also unchanged except at the first possible index, where
the type-III image order is one larger.  Consequently the target trigger
implies the source trigger in every case.  Source condition (iv), followed
by common-tail prefix transfer, then gives condition (iv) for the image.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

/-- The numerical trigger in condition 2.1(iv) for the type-III image
implies the corresponding trigger for the source BONG. -/
theorem beli2019Lemma912_typeIII_longRepresentationTrigger_source_of_target
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (i : LongRepresentationIndex (T + 3) (T + 3))
    (htrigger :
      (I.bong.castLength hlength).longRepresentationTrigger c i) :
    (a.castLength hlength).longRepresentationTrigger c i := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hiOrdinary : i.val ≤ T + 3 := by
    have := i.succ_lt_large
    omega
  have hnext : target.order
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (T + 3)) =
      source.order (⟨i.val + 1, i.succ_lt_large⟩ : Fin (T + 3)) :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
      a D I hlength
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (T + 3)) (by
          change 3 ≤ i.val + 1
          have := i.one_lt
          omega)
  have hcurrentLe : source.order
        (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (T + 3)) ≤
      target.order
        (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (T + 3)) := by
    dsimp only [source, target]
    by_cases hiTwo : i.val = 2
    · have hindex :
          (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (T + 3)) =
            (2 : Fin (T + 3)) := by
        apply Fin.ext
        change i.val = 2 % (T + 3)
        rw [hiTwo, Nat.mod_eq_of_lt (by omega)]
      rw [hindex,
        beli2019Lemma912TypeIIIIndexPData_order_castLength_two
          a D I hlength]
      omega
    · have hiThree : 3 ≤ i.val := by
        have := i.one_lt
        omega
      have heq :=
        beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
          a D I hlength
            (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (T + 3)) (by
              change 3 ≤ i.val
              exact hiThree)
      exact heq.symm.le
  dsimp only [source, target] at hnext hcurrentLe
  unfold longRepresentationTrigger at htrigger ⊢
  rw [dif_pos hiOrdinary] at htrigger ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hnext] using htrigger.1
  · simpa only [hnext] using htrigger.2.1
  · omega

/-- Complete condition 2.1(iv) for the type-III image in Lemma 9.12. -/
theorem beli2019Lemma912_typeIII_longRepresentationConditions
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsourceLong :
      (a.castLength hlength).LongRepresentationConditions c) :
    (I.bong.castLength hlength).LongRepresentationConditions c := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  rw [target.longRepresentationConditions_iff_forall_generalTrigger c]
  intro i htrigger
  have hsourceTrigger :=
    beli2019Lemma912_typeIII_longRepresentationTrigger_source_of_target
      a c D I hlength i htrigger
  have hsourceRepresentation :=
    (source.longRepresentationConditions_iff_forall_generalTrigger c).mp
      hsourceLong i hsourceTrigger
  have hprefix :=
    beli2019Lemma912_typeIII_sourcePrefix_represents_targetPrefix
      a D I hlength (i.val + 1) (by
        have := i.one_lt
        omega) (by
          have := i.succ_lt_large
          omega)
  exact hsourceRepresentation.trans hprefix

end BONG.GoodBONG

end Bong
