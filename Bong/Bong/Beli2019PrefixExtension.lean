/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019NormGeneratorGoodness

/-!
# Beli (2019), Corollary 5.10: prefix-extension induction data

Corollary 5.10 repeatedly removes a common first norm generator.  This file
formalizes the exact shift of its order hypotheses under that operation.  The
geometric one-step assertion that the prescribed head extends to a good BONG
is deliberately kept separate from this order-theoretic induction layer.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Delete the first coordinate of a nonempty Beli order sequence. -/
def tail {n : Nat} (x : BeliOrderSequence (n + 1) Gamma) :
    BeliOrderSequence n Gamma where
  value i := x.value i.succ
  twoStep i hi := by
    have h := x.twoStep (i + 1) (by omega)
    convert h using 1
    · apply congrArg x.value
      apply Fin.ext
      simp only [Fin.val_succ]
    · apply congrArg x.value
      apply Fin.ext
      simp only [Fin.val_succ]

omit [IsOrderedAddMonoid Gamma] in
/-- Extended-by-zero entries commute with deleting the first coordinate. -/
theorem tail_entryOrZero {n : Nat}
    (x : BeliOrderSequence (n + 1) Gamma) (i : Nat) :
    x.tail.entryOrZero i = x.entryOrZero (i + 1) := by
  by_cases hi : i < n
  · rw [entryOrZero_of_lt x.tail hi,
      entryOrZero_of_lt x (by omega)]
    rfl
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    rw [entryOrZero_of_le x.tail hni,
      entryOrZero_of_le x (by omega)]

/-- Two sequences agree on their first `p` coordinates, with explicit rank
bounds for that prefix. -/
structure PrefixAgreement {m n : Nat}
    (x : BeliOrderSequence m Gamma) (y : BeliOrderSequence n Gamma)
    (p : Nat) : Prop where
  leftBound : p ≤ m
  rightBound : p ≤ n
  entry_eq (j : Nat) (hj : j < p) :
    x.entryOrZero j = y.entryOrZero j

omit [IsOrderedAddMonoid Gamma] in
/-- Removing a common first coordinate shortens a common prefix by one. -/
theorem PrefixAgreement.tail {m n p : Nat}
    {x : BeliOrderSequence (m + 1) Gamma}
    {y : BeliOrderSequence (n + 1) Gamma}
    (h : PrefixAgreement x y (p + 1)) :
    PrefixAgreement x.tail y.tail p where
  leftBound := by
    have := h.leftBound
    omega
  rightBound := by
    have := h.rightBound
    omega
  entry_eq j hj := by
    rw [tail_entryOrZero, tail_entryOrZero]
    exact h.entry_eq (j + 1) (by omega)

omit [IsOrderedAddMonoid Gamma] in
/-- A common prefix remains common after shortening its length. -/
theorem PrefixAgreement.mono {m n p r : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : PrefixAgreement x y p) (hr : r ≤ p) :
    PrefixAgreement x y r where
  leftBound := hr.trans h.leftBound
  rightBound := hr.trans h.rightBound
  entry_eq j hj := h.entry_eq j (hj.trans_le hr)

end BeliOrderSequence

/-- The four alternatives in Beli (2019), Corollary 5.10, written with a
zero-based prefix length `p`. -/
inductive BeliPrefixExtensionTrigger (e : Int) {m n : Nat}
    (x : BeliOrderSequence m Int) (y : BeliOrderSequence n Int)
    (p : Nat) : Prop
  | terminal (h : m ≤ p + 1)
  | nextOrder (hxm : p < m) (hyn : p < n)
      (horder : x.entryOrZero p = y.entryOrZero p)
  | strictTwoStep (hxm : p + 1 < m)
      (hstrict : x.entryOrZero (p - 1) < x.entryOrZero (p + 1))
  | maximalGap (hxm : p < m)
      (hgap : x.entryOrZero p - x.entryOrZero (p - 1) = 2 * e)

namespace BeliPrefixExtensionTrigger

/-- Each of Corollary 5.10's four alternatives is preserved by deleting a
common first coordinate.  The assumption `0 < p` is the paper's induction
case `i > 1`. -/
theorem tail {m n p : Nat} {e : Int}
    {x : BeliOrderSequence (m + 1) Int}
    {y : BeliOrderSequence (n + 1) Int}
    (h : BeliPrefixExtensionTrigger e x y (p + 1)) (hp : 0 < p) :
    BeliPrefixExtensionTrigger e x.tail y.tail p := by
  cases h with
  | terminal hterminal =>
      exact BeliPrefixExtensionTrigger.terminal (by omega)
  | nextOrder hxm hyn horder =>
      apply BeliPrefixExtensionTrigger.nextOrder (by omega) (by omega)
      simpa only [BeliOrderSequence.tail_entryOrZero] using horder
  | strictTwoStep hxm hstrict =>
      apply BeliPrefixExtensionTrigger.strictTwoStep (by omega)
      rw [BeliOrderSequence.tail_entryOrZero,
        BeliOrderSequence.tail_entryOrZero]
      have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
      simpa only [hsub, Nat.add_sub_cancel, Nat.add_assoc,
        Nat.reduceAdd] using hstrict
  | maximalGap hxm hgap =>
      apply BeliPrefixExtensionTrigger.maximalGap (by omega)
      rw [BeliOrderSequence.tail_entryOrZero,
        BeliOrderSequence.tail_entryOrZero]
      have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
      simpa only [hsub, Nat.add_sub_cancel, Nat.add_assoc,
        Nat.reduceAdd] using hgap

end BeliPrefixExtensionTrigger

/-- The complete order hypothesis propagated in the induction proof of
Corollary 5.10. -/
structure BeliPrefixExtensionHypothesis (e : Int) {m n : Nat}
    (x : BeliOrderSequence m Int) (y : BeliOrderSequence n Int)
    (p : Nat) : Prop where
  agreement : x.PrefixAgreement y p
  trigger : BeliPrefixExtensionTrigger e x y p

namespace BeliPrefixExtensionHypothesis

/-- The complete Corollary 5.10 order package descends to the two tails. -/
theorem tail {m n p : Nat} {e : Int}
    {x : BeliOrderSequence (m + 1) Int}
    {y : BeliOrderSequence (n + 1) Int}
    (h : BeliPrefixExtensionHypothesis e x y (p + 1)) (hp : 0 < p) :
    BeliPrefixExtensionHypothesis e x.tail y.tail p where
  agreement := h.agreement.tail
  trigger := h.trigger.tail hp

end BeliPrefixExtensionHypothesis

namespace BONG.GoodBONG

open BeliOrderSequence

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Taking the tail of a good BONG agrees with taking the tail of its order
sequence. -/
theorem orderSequence_tail (b : GoodBONG q L (n + 1)) :
    b.orderSequence.tail = b.tail.orderSequence := by
  apply BeliOrderSequence.ext
  funext i
  change b.order i.succ = b.tail.order i
  exact (b.toBONG.order_tail i).symm

end BONG.GoodBONG

end Bong
