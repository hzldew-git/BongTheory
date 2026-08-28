/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96TailOrder
import Bong.Bong.Beli2019Lemma93TailRepresentation
import Bong.Bong.Beli2019RepresentationTransitivity

/-!
# Beli (2019), Lemma 9.6: projected-tail prefix representations

The exceptional BONG used in Lemma 9.6 is bad only across its new unary
head.  Its projected tail is good, and every prefix of length at least three
is isometric to the corresponding prefix of the original target BONG.

This file packages that checkable prefix transport and proves conditions
2.1(iii) and 2.1(iv) after the common head is cancelled.  For condition (iv)
the numerical trigger is proved to be exactly the shifted original trigger.
For condition (iii), the separate comparison-alpha calculation from lines
9629--9697 is retained as the single explicit trigger-lifting hypothesis.
-/

namespace Bong

open Dyadic

universe u v w x

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type x} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {P : Lattice K U}
  {N : Nat}

/-- Prefix-level content of the exceptional bad BONG.  The common first
coefficient is the actual source head, and the remaining coefficients are
the good BONG of the projected target lattice. -/
structure Beli2019Lemma96PrefixTransport
    (a : GoodBONG q L (N + 4))
    (b : GoodBONG r M (N + 4))
    (c : GoodBONG s P (N + 3)) : Prop where
  targetPrefix : ∀ (tailLength : Nat)
      (hkTwo : 2 ≤ tailLength) (hk : tailLength ≤ N + 3),
    DiagonalRepresents
      (a.prefixValues (tailLength + 1) (by omega))
      (Fin.cons (b.value 0)
        (c.prefixValues tailLength hk))

namespace Beli2019Lemma96PrefixTransport

variable {a : GoodBONG q L (N + 4)}
  {b : GoodBONG r M (N + 4)}
  {c : GoodBONG s P (N + 3)}

/-- Cancel the literal source head from a representation whose target is an
exceptional prefix `b_1 :: c`. -/
theorem cancel_sourceHead
    (sourceLength targetLength : Nat)
    (hsourceLength : sourceLength ≤ N + 3)
    (htargetLength : targetLength ≤ N + 3)
    (hrep : DiagonalRepresents
      (b.prefixValues (sourceLength + 1) (by omega))
      (Fin.cons (b.value 0)
        (c.prefixValues targetLength htargetLength))) :
    DiagonalRepresents
      (b.tail.prefixValues sourceLength hsourceLength)
      (c.prefixValues targetLength htargetLength) := by
  rw [b.prefixValues_succ_eq_cons_head_tail sourceLength hsourceLength] at hrep
  apply DiagonalRepresents.cancel_common_head
    (b.value 0)
    (b.tail.prefixValues sourceLength hsourceLength)
    (c.prefixValues targetLength htargetLength)
  · exact b.toBONG.value_ne_zero 0
  · intro i
    change b.tail.toBONG.value
      ⟨i.val, i.isLt.trans_le hsourceLength⟩ ≠ 0
    exact b.tail.toBONG.value_ne_zero _
  · intro i
    change c.toBONG.value
      ⟨i.val, i.isLt.trans_le htargetLength⟩ ≠ 0
    exact c.toBONG.value_ne_zero _
  · exact hrep

/-- The representation-valued conclusion of condition (iii) descends from
the original problem once its exceptional numerical trigger has been lifted
to the shifted index. -/
theorem centralRepresentationConditions
    (D : Beli2019Lemma96PrefixTransport a b c)
    (hcentral : a.CentralRepresentationConditions b)
    (htrigger : ∀ i : CentralRepresentationIndex (N + 3) (N + 3),
      c.centralAlphaTrigger b.tail i →
        a.centralAlphaTrigger b i.tailShift) :
    c.CentralRepresentationConditions b.tail := by
  rw [c.centralRepresentationConditions_iff_forall_alphaTrigger b.tail]
  intro i hi
  have horiginal :=
    (a.centralRepresentationConditions_iff_forall_alphaTrigger b).mp
      hcentral i.tailShift (htrigger i hi)
  have hsourceLength :
      i.tailShift.val - 1 = i.val - 1 + 1 := by
    simp only [CentralRepresentationIndex.tailShift_val]
    have := i.one_lt
    omega
  have htargetLength : i.tailShift.val = i.val + 1 := rfl
  have horiginal' : DiagonalRepresents
      (b.prefixValues (i.val - 1 + 1) (by have := i.lt_large; omega))
      (a.prefixValues (i.val + 1) (by have := i.lt_large; omega)) :=
    b.prefixRepresents_cast a hsourceLength htargetLength horiginal
  have htransport := D.targetPrefix i.val
    (by exact i.one_lt)
    (by have := i.lt_large; omega)
  have hfull := horiginal'.trans htransport
  apply cancel_sourceHead (b := b) (c := c) (i.val - 1) i.val
    (by have := i.lt_large; omega)
    (by have := i.lt_large; omega)
  exact hfull

/-- Under the exceptional order profile, condition (iv)'s numerical trigger
is unchanged after shifting the index by one.  Its smallest target index is
already in the unchanged `R'_i = R_i` part of the projected tail. -/
theorem longRepresentationTrigger_iff
    (Dorder : Beli2019Lemma96TailOrderProfile a c)
    (i : LongRepresentationIndex (N + 3) (N + 3)) :
    c.longRepresentationTrigger b.tail i ↔
      a.longRepresentationTrigger b i.tailShift := by
  have hiTail : i.val ≤ N + 3 := by
    have := i.succ_lt_large
    omega
  have hiOriginal : i.tailShift.val ≤ N + 4 := by
    change i.val + 1 ≤ N + 4
    have := i.succ_lt_large
    omega
  have hCNext :
      c.order ⟨i.val + 1, i.succ_lt_large⟩ =
        a.order ⟨i.tailShift.val + 1, i.tailShift.succ_lt_large⟩ := by
    have h := Dorder.laterOrders
      (⟨i.val + 1, i.succ_lt_large⟩ : Fin (N + 3)) (by
        change 2 ≤ i.val + 1
        have := i.one_lt
        omega)
    convert h using 1 <;> apply congrArg (fun j ↦ a.order j) <;>
      apply Fin.ext <;> rfl
  have hCCurrent :
      c.order ⟨i.val, by have := i.succ_lt_large; omega⟩ =
        a.order ⟨i.tailShift.val, by
          have := i.tailShift.succ_lt_large
          omega⟩ := by
    have h := Dorder.laterOrders
      (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (N + 3))
      (by change 2 ≤ i.val; exact i.one_lt)
    convert h using 1 <;> apply congrArg (fun j ↦ a.order j) <;>
      apply Fin.ext <;> rfl
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
  unfold longRepresentationTrigger
  rw [dif_pos hiTail, dif_pos hiOriginal]
  rw [hCNext, hCCurrent, hBPrevious, hBPreviousTwo]

/-- Condition 2.1(iv) for the projected pair.  The shifted original prefix
representation is transported to the exceptional prefix and the common
head is then cancelled. -/
theorem longRepresentationConditions
    (D : Beli2019Lemma96PrefixTransport a b c)
    (Dorder : Beli2019Lemma96TailOrderProfile a c)
    (hlong : a.LongRepresentationConditions b) :
    c.LongRepresentationConditions b.tail := by
  rw [c.longRepresentationConditions_iff_forall_generalTrigger b.tail]
  intro i hi
  have horiginal :=
    (a.longRepresentationConditions_iff_forall_generalTrigger b).mp
      hlong i.tailShift
        ((longRepresentationTrigger_iff (b := b) Dorder i).mp hi)
  have hsourceLength :
      i.tailShift.val - 1 = i.val - 1 + 1 := by
    simp only [LongRepresentationIndex.tailShift_val]
    have := i.one_lt
    omega
  have htargetLength :
      i.tailShift.val + 1 = (i.val + 1) + 1 := rfl
  have horiginal' : DiagonalRepresents
      (b.prefixValues (i.val - 1 + 1)
        (by have := i.succ_lt_large; omega))
      (a.prefixValues ((i.val + 1) + 1)
        (by have := i.succ_lt_large; omega)) :=
    b.prefixRepresents_cast a hsourceLength htargetLength horiginal
  have htransport := D.targetPrefix (i.val + 1)
    (by have := i.one_lt; omega)
    (by have := i.succ_lt_large; omega)
  have hfull := horiginal'.trans htransport
  apply cancel_sourceHead (b := b) (c := c) (i.val - 1) (i.val + 1)
    (by have := i.succ_lt_large; omega)
    (by have := i.succ_lt_large; omega)
  exact hfull

end Beli2019Lemma96PrefixTransport

end BONG.GoodBONG

end Bong
