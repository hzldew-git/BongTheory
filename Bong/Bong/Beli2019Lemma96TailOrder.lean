/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96DeltaScaling
import Bong.Bong.Beli2019Lemma93TailOrder

/-!
# Beli (2019), Lemma 9.6: the projected-tail order condition

After the exceptional ternary block has been put in the normal form of
Lemma 9.5, deleting its matched unary head leaves a good BONG with orders

`R'_2 = R_2 + 1`, `R'_3 = R_3 - 1`, and `R'_i = R_i` for `i >= 4`.

This file proves condition 2.1(i) for that projected target and the ordinary
source tail.  It is the calculation in lines 9625--9627 of the revised-v2
paper.  The result is independent of the geometric construction of the
projected-tail BONG; that construction only has to provide the three
displayed, directly checkable order identities below.
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

/-- The exact order profile of the good projected target BONG constructed
from the exceptional (globally bad) BONG in Lemma 9.6. -/
structure Beli2019Lemma96TailOrderProfile
    (a : GoodBONG q L (N + 4)) (c : GoodBONG s P (N + 3)) : Prop where
  firstOrder :
    c.order (0 : Fin (N + 3)) =
      a.order (1 : Fin (N + 4)) + 1
  secondOrder :
    c.order (1 : Fin (N + 3)) =
      a.order (2 : Fin (N + 4)) - 1
  laterOrders : ∀ i : Fin (N + 3), 2 ≤ i.val →
    c.order i = a.order i.succ

namespace Beli2019Lemma96TailOrderProfile

variable {a : GoodBONG q L (N + 4)} {c : GoodBONG s P (N + 3)}

/-- Away from the new first entry, every exceptional-tail order is at most
the corresponding shifted original order. -/
theorem order_le_original_succ
    (D : Beli2019Lemma96TailOrderProfile a c)
    (i : Fin (N + 3)) (hi : 0 < i.val) :
    c.order i ≤ a.order i.succ := by
  by_cases hiOne : i.val = 1
  · have hiFin : i = (1 : Fin (N + 3)) := Fin.ext hiOne
    subst i
    rw [D.secondOrder]
    have hindex :
        Fin.succ (1 : Fin (N + 3)) = (2 : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    omega
  · have hiTwo : 2 ≤ i.val := by omega
    exact (D.laterOrders i hiTwo).le

/-- The adjacent-order sum used by the second alternative of condition (i)
can only decrease under the exceptional tail replacement. -/
theorem adjacentSum_le_original
    (D : Beli2019Lemma96TailOrderProfile a c)
    (i : Fin (N + 3)) (hi : 0 < i.val)
    (hiNext : i.val + 1 < N + 3) :
    c.order i + c.order ⟨i.val + 1, hiNext⟩ ≤
      a.order i.succ +
        a.order (⟨i.val + 1, hiNext⟩ : Fin (N + 3)).succ := by
  exact add_le_add
    (D.order_le_original_succ i hi)
    (D.order_le_original_succ ⟨i.val + 1, hiNext⟩ (by simp))

/-- Condition 2.1(i) for the projected pair in Lemma 9.6.  The new first
order is strictly below `S_2`; every later direct or adjacent-sum alternative
is inherited from the original representation conditions. -/
theorem representationOrderCondition
    (D : Beli2019Lemma96TailOrderProfile a c)
    (b : GoodBONG r M (N + 4))
    (horder : a.RepresentationOrderCondition b (Nat.le_refl (N + 3)))
    (hfirstGap :
      a.order (1 : Fin (N + 4)) - a.order (0 : Fin (N + 4)) =
        2 * (ramificationIndex K : Int) - 2)
    (hsourceFirstOrder :
      b.order (0 : Fin (N + 4)) = a.order (0 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4))) :
    c.RepresentationOrderCondition b.tail (Nat.le_refl (N + 2)) := by
  intro i
  by_cases hi : i.val = 0
  · left
    have hiFin : i = 0 := Fin.ext hi
    subst i
    change c.order (0 : Fin (N + 3)) ≤
      b.toBONG.tail.order (0 : Fin (N + 3))
    rw [D.firstOrder, b.toBONG.order_tail]
    have hindex :
        Fin.succ (0 : Fin (N + 3)) = (1 : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    change a.order (1 : Fin (N + 4)) + 1 ≤
      b.order (1 : Fin (N + 4))
    omega
  · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi
    have horiginal := horder i.succ
    rcases horiginal with hdirect | ⟨_, hlarge, hsum⟩
    · left
      change c.order i ≤ b.toBONG.tail.order i
      rw [b.toBONG.order_tail]
      exact (D.order_le_original_succ i hiPos).trans hdirect
    · right
      have hiLarge : i.val + 1 < N + 3 := by
        simp only [Fin.val_succ] at hlarge
        omega
      refine ⟨hiPos, hiLarge, ?_⟩
      change c.order i + c.order ⟨i.val + 1, hiLarge⟩ ≤
        b.toBONG.tail.order ⟨i.val - 1, by omega⟩ +
          b.toBONG.tail.order i
      rw [b.toBONG.order_tail, b.toBONG.order_tail]
      have hnext :
          (⟨i.val + 1, hiLarge⟩ : Fin (N + 3)).succ =
            (⟨i.succ.val + 1, hlarge⟩ : Fin (N + 4)) := by
        apply Fin.ext
        simp
      have hprevious :
          (⟨i.val - 1, by omega⟩ : Fin (N + 3)).succ =
            (⟨i.succ.val - 1, by omega⟩ : Fin (N + 4)) := by
        apply Fin.ext
        simp
        omega
      rw [hprevious]
      calc
        c.order i + c.order ⟨i.val + 1, hiLarge⟩ ≤
            a.order i.succ +
              a.order (⟨i.val + 1, hiLarge⟩ : Fin (N + 3)).succ :=
          D.adjacentSum_le_original i hiPos hiLarge
        _ = a.order i.succ +
              a.order ⟨i.succ.val + 1, hlarge⟩ := by rw [hnext]
        _ ≤ b.order ⟨i.succ.val - 1, by omega⟩ + b.order i.succ :=
          hsum

end Beli2019Lemma96TailOrderProfile

end BONG.GoodBONG

end Bong
