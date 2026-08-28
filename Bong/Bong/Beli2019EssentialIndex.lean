/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Transitivity
import Bong.Bong.Beli2019SequenceDual

/-!
# Beli (2019), Definition 7: essential indices

The two inequalities are universally quantified over proofs that their
indices exist.  Consequently the endpoint conventions are built into the
definition, rather than represented by sentinel values.  Essentiality is
then proved invariant under the paper's reflected dual pair.
-/

namespace Bong

namespace BeliOrderSequence

/-- Definition 7 in zero-based coordinates.  The index `i` here represents
the paper's index `i + 1`. -/
def IsEssentialFor {N : Nat} (x y : BeliOrderSequence N Int)
    (i : Fin N) : Prop :=
  (∀ (hi0 : 0 < i.1) (hiNext : i.1 + 1 < N),
    y.entry (i.1 - 1) (by omega) < x.entry (i.1 + 1) hiNext) ∧
  (∀ (hiTwo : 1 < i.1) (hiNext : i.1 + 2 < N),
    y.entry (i.1 - 2) (by omega) + y.entry (i.1 - 1) (by omega) <
      x.entry (i.1 + 1) (by omega) + x.entry (i.1 + 2) hiNext)

theorem isEssentialFor_zero {N : Nat} (x y : BeliOrderSequence (N + 1) Int) :
    x.IsEssentialFor y 0 := by
  constructor
  · intro hi0
    simp at hi0
  · intro hiTwo
    simp at hiTwo

theorem isEssentialFor_last {N : Nat}
    (x y : BeliOrderSequence (N + 1) Int) :
    x.IsEssentialFor y (Fin.last N) := by
  constructor <;> intro <;> simp at *

private theorem isEssentialFor_reverseNegate
    {N : Nat} {x y : BeliOrderSequence N Int} {i : Fin N}
    (h : x.IsEssentialFor y i) :
    y.reverseNegate.IsEssentialFor x.reverseNegate (Fin.rev i) := by
  constructor
  · intro hj0 hjNext
    have hi0 : 0 < i.1 := by
      simp at hjNext
      omega
    have hiNext : i.1 + 1 < N := by
      simp at hj0
      omega
    have hforward := h.1 hi0 hiNext
    have hx : Fin.rev
        (⟨(Fin.rev i).1 - 1, by omega⟩ : Fin N) =
          (⟨i.1 + 1, hiNext⟩ : Fin N) := by
      apply Fin.ext
      simp
      omega
    have hy : Fin.rev
        (⟨(Fin.rev i).1 + 1, hjNext⟩ : Fin N) =
          (⟨i.1 - 1, by omega⟩ : Fin N) := by
      apply Fin.ext
      simp
      omega
    change -x.value (Fin.rev ⟨(Fin.rev i).1 - 1, by omega⟩) <
      -y.value (Fin.rev ⟨(Fin.rev i).1 + 1, hjNext⟩)
    rw [hx, hy]
    exact neg_lt_neg hforward
  · intro hjTwo hjNext
    have hiTwo : 1 < i.1 := by
      simp at hjNext
      omega
    have hiNext : i.1 + 2 < N := by
      simp at hjTwo
      omega
    have hforward := h.2 hiTwo hiNext
    have hxTwo : Fin.rev
        (⟨(Fin.rev i).1 - 2, by omega⟩ : Fin N) =
          (⟨i.1 + 2, hiNext⟩ : Fin N) := by
      apply Fin.ext
      simp
      omega
    have hxOne : Fin.rev
        (⟨(Fin.rev i).1 - 1, by omega⟩ : Fin N) =
          (⟨i.1 + 1, by omega⟩ : Fin N) := by
      apply Fin.ext
      simp
      omega
    have hyOne : Fin.rev
        (⟨(Fin.rev i).1 + 1, by omega⟩ : Fin N) =
          (⟨i.1 - 1, by omega⟩ : Fin N) := by
      apply Fin.ext
      simp
      omega
    have hyTwo : Fin.rev
        (⟨(Fin.rev i).1 + 2, hjNext⟩ : Fin N) =
          (⟨i.1 - 2, by omega⟩ : Fin N) := by
      apply Fin.ext
      simp
      omega
    change
      -x.value (Fin.rev ⟨(Fin.rev i).1 - 2, by omega⟩) +
          -x.value (Fin.rev ⟨(Fin.rev i).1 - 1, by omega⟩) <
        -y.value (Fin.rev ⟨(Fin.rev i).1 + 1, by omega⟩) +
          -y.value (Fin.rev ⟨(Fin.rev i).1 + 2, hjNext⟩)
    rw [hxTwo, hxOne, hyOne, hyTwo]
    change
      y.value ⟨i.1 - 2, by omega⟩ + y.value ⟨i.1 - 1, by omega⟩ <
        x.value ⟨i.1 + 1, by omega⟩ + x.value ⟨i.1 + 2, hiNext⟩
      at hforward
    linarith

/-- The duality remark after Definition 7. -/
theorem reverseNegate_isEssentialFor_iff
    {N : Nat} (x y : BeliOrderSequence N Int) (i : Fin N) :
    y.reverseNegate.IsEssentialFor x.reverseNegate (Fin.rev i) ↔
      x.IsEssentialFor y i := by
  constructor
  · intro h
    have hback := isEssentialFor_reverseNegate
      (x := y.reverseNegate) (y := x.reverseNegate)
      (i := Fin.rev i) h
    simpa using hback
  · exact isEssentialFor_reverseNegate

end BeliOrderSequence

namespace BONG.GoodBONG

open BeliOrderSequence
open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- Essentiality of a BONG boundary, expressed through its order sequence. -/
def IsEssentialFor (a : GoodBONG q L N) (b : GoodBONG r M N)
    (i : Fin N) : Prop :=
  a.orderSequence.IsEssentialFor b.orderSequence i

/-- Essentiality reverses when the two order sequences are dualized and
their roles are exchanged. -/
theorem reverseDualOrder_isEssentialFor_iff
    (a : GoodBONG q L N) (b : GoodBONG r M N) (i : Fin N) :
    b.orderSequence.reverseNegate.IsEssentialFor
        a.orderSequence.reverseNegate (Fin.rev i) ↔
      a.IsEssentialFor b i :=
  a.orderSequence.reverseNegate_isEssentialFor_iff b.orderSequence i

end BONG.GoodBONG

end Bong
