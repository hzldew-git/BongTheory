/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary311
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.DiagonalHeadCancellation

/-!
# Beli (2019), Lemma 9.3: prefix conditions after deleting equal heads

The numerical triggers in conditions 2.1(iii) and 2.1(iv) shift by one after
deleting the first BONG entries.  Once an original prefix representation is
available, `DiagonalRepresents.cancel_common_head` removes the common first
coefficient and produces exactly the required tail-prefix representation.
-/

namespace Bong

open Dyadic

universe u v w

namespace CentralRepresentationIndex

/-- Shift a central tail index to the corresponding original index. -/
def tailShift {n : Nat}
    (i : CentralRepresentationIndex (n + 1) (n + 1)) :
    CentralRepresentationIndex (n + 2) (n + 2) where
  val := i.val + 1
  one_lt := by have := i.one_lt; omega
  lt_large := by have := i.lt_large; omega
  le_small_succ := by have := i.le_small_succ; omega

@[simp]
theorem tailShift_val {n : Nat}
    (i : CentralRepresentationIndex (n + 1) (n + 1)) :
    i.tailShift.val = i.val + 1 :=
  rfl

end CentralRepresentationIndex

namespace LongRepresentationIndex

/-- Shift a long-prefix tail index to the corresponding original index. -/
def tailShift {n : Nat}
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    LongRepresentationIndex (n + 2) (n + 2) where
  val := i.val + 1
  one_lt := by have := i.one_lt; omega
  succ_lt_large := by have := i.succ_lt_large; omega
  le_small_succ := by have := i.le_small_succ; omega

@[simp]
theorem tailShift_val {n : Nat}
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    i.tailShift.val = i.val + 1 :=
  rfl

end LongRepresentationIndex

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The representation-valued part of condition (iii) descends once its
tail trigger has been lifted to the shifted original trigger. -/
theorem centralRepresentationConditions_tail_of_trigger
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hcentral : a.CentralRepresentationConditions b)
    (hhead : a.value 0 = b.value 0)
    (htrigger : ∀ i : CentralRepresentationIndex (n + 1) (n + 1),
      a.tail.centralAlphaTrigger b.tail i →
        a.centralAlphaTrigger b i.tailShift) :
    a.tail.CentralRepresentationConditions b.tail := by
  rw [a.tail.centralRepresentationConditions_iff_forall_alphaTrigger b.tail]
  intro i hi
  have horiginal :=
    (a.centralRepresentationConditions_iff_forall_alphaTrigger b).mp
      hcentral i.tailShift (htrigger i hi)
  apply a.tailPrefix_represents_of_common_head b hhead
    (i.val - 1) i.val
      (by have := i.lt_large; omega)
      (by have := i.lt_large; omega)
  have hsourceLength : i.tailShift.val - 1 = i.val - 1 + 1 := by
    simp only [CentralRepresentationIndex.tailShift_val]
    have := i.one_lt
    omega
  have htargetLength : i.tailShift.val = i.val + 1 :=
    rfl
  exact b.prefixRepresents_cast a hsourceLength htargetLength horiginal

/-- The numerical trigger in condition (iv) is unchanged, up to shifting all
indices by one, after deleting the first entries. -/
theorem longRepresentationTrigger_tailShift
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    a.tail.longRepresentationTrigger b.tail i ↔
      a.longRepresentationTrigger b i.tailShift := by
  have hiTail : i.val ≤ n + 1 := by
    have := i.succ_lt_large
    omega
  have hiOriginal : i.tailShift.val ≤ n + 2 := by
    change i.val + 1 ≤ n + 2
    have := i.succ_lt_large
    omega
  have hANext :
      a.tail.order ⟨i.val + 1, i.succ_lt_large⟩ =
        a.order ⟨i.tailShift.val + 1, i.tailShift.succ_lt_large⟩ := by
    change a.toBONG.tail.order _ = a.toBONG.order _
    rw [a.toBONG.order_tail]
    congr 1
  have hBPrevious :
      b.tail.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.succ_lt_large
        omega⟩ =
        b.order ⟨i.tailShift.val - 1, by
          have := i.tailShift.one_lt
          have := i.tailShift.succ_lt_large
          omega⟩ := by
    change b.toBONG.tail.order _ = b.toBONG.order _
    rw [b.toBONG.order_tail]
    congr 1
    apply Fin.ext
    change (i.val - 1) + 1 = (i.val + 1) - 1
    have := i.one_lt
    omega
  have hBPreviousTwo :
      b.tail.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.succ_lt_large
        omega⟩ =
        b.order ⟨i.tailShift.val - 2, by
          have := i.tailShift.one_lt
          have := i.tailShift.succ_lt_large
          omega⟩ := by
    change b.toBONG.tail.order _ = b.toBONG.order _
    rw [b.toBONG.order_tail]
    congr 1
    apply Fin.ext
    change (i.val - 2) + 1 = (i.val + 1) - 2
    have := i.one_lt
    omega
  have hACurrent :
      a.tail.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ =
        a.order ⟨i.tailShift.val, by
          have := i.tailShift.succ_lt_large
          omega⟩ := by
    change a.toBONG.tail.order _ = a.toBONG.order _
    rw [a.toBONG.order_tail]
    congr 1
  unfold longRepresentationTrigger
  rw [dif_pos hiTail, dif_pos hiOriginal]
  rw [hANext, hBPrevious, hBPreviousTwo, hACurrent]

/-- Condition (iv) descends completely: its trigger shifts definitionally,
and the common diagonal head cancels from the original prefix embedding. -/
theorem longRepresentationConditions_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hlong : a.LongRepresentationConditions b)
    (hhead : a.value 0 = b.value 0) :
    a.tail.LongRepresentationConditions b.tail := by
  rw [a.tail.longRepresentationConditions_iff_forall_generalTrigger b.tail]
  intro i hi
  have horiginal :=
    (a.longRepresentationConditions_iff_forall_generalTrigger b).mp
      hlong i.tailShift
        ((a.longRepresentationTrigger_tailShift b i).mp hi)
  apply a.tailPrefix_represents_of_common_head b hhead
    (i.val - 1) (i.val + 1)
      (by have := i.succ_lt_large; omega)
      (by have := i.succ_lt_large; omega)
  have hsourceLength : i.tailShift.val - 1 = i.val - 1 + 1 := by
    simp only [LongRepresentationIndex.tailShift_val]
    have := i.one_lt
    omega
  have htargetLength : i.tailShift.val + 1 = i.val + 1 + 1 :=
    rfl
  exact b.prefixRepresents_cast a hsourceLength htargetLength horiginal

end BONG.GoodBONG

end Bong
