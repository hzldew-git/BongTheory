/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation

/-!
# Beli (2019), Lemma 9.3: condition (i) after deleting equal heads

For all tail indices except the first, condition 2.1(i) is exactly the
corresponding original condition with the index shifted by one.  At the first
tail index the two-step alternative is no longer available, so the separate
inequality `R₂ ≤ S₂` is required, exactly as in the paper.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The first line of the proof of Lemma 9.3: condition (i), equality of the
first orders, and goodness imply `R₂ ≤ S₂`. -/
theorem secondOrder_le_of_firstOrder_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (horder : a.RepresentationOrderCondition b (Nat.le_refl (n + 1)))
    (hfirst : a.order (0 : Fin (n + 2)) =
      b.order (0 : Fin (n + 2))) :
    a.order (⟨1, by omega⟩ : Fin (n + 2)) ≤
      b.order (⟨1, by omega⟩ : Fin (n + 2)) := by
  let second : Fin (n + 2) := ⟨1, by omega⟩
  have h := horder second
  rcases h with hdirect | ⟨hone, hlarge, hsum⟩
  · simpa only [second] using hdirect
  · have hgood : a.order (0 : Fin (n + 2)) ≤
        a.order (⟨2, by omega⟩ : Fin (n + 2)) := by
      let first : Fin (n + 2) := ⟨0, by omega⟩
      have hg := a.good first (by
        dsimp only [second] at hlarge
        simpa only [first] using hlarge)
      convert hg using 1 <;> apply congrArg a.order <;>
        apply Fin.ext <;> rfl
    dsimp only [second] at hsum
    change a.order (⟨1, by omega⟩ : Fin (n + 2)) +
        a.order (⟨2, by omega⟩ : Fin (n + 2)) ≤
      b.order (0 : Fin (n + 2)) +
        b.order (⟨1, by omega⟩ : Fin (n + 2)) at hsum
    omega

/-- Condition 2.1(i) descends to the projected tails once its new first
inequality is known. -/
theorem representationOrderCondition_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (horder : a.RepresentationOrderCondition b (Nat.le_refl (n + 1)))
    (hfirst : a.order ⟨1, by omega⟩ ≤ b.order ⟨1, by omega⟩) :
    a.tail.RepresentationOrderCondition b.tail (Nat.le_refl n) := by
  intro i
  by_cases hi : i.val = 0
  · left
    have hiFin : i = 0 := Fin.ext hi
    subst i
    change a.toBONG.tail.order 0 ≤ b.toBONG.tail.order 0
    rw [a.toBONG.order_tail, b.toBONG.order_tail]
    exact hfirst
  · have horiginal := horder i.succ
    rcases horiginal with hdirect | ⟨_, hlarge, hsum⟩
    · left
      change a.toBONG.tail.order i ≤ b.toBONG.tail.order i
      rw [a.toBONG.order_tail, b.toBONG.order_tail]
      exact hdirect
    · right
      have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi
      have hiLarge : i.val + 1 < n + 1 := by
        have hlarge' : i.val + 1 + 1 < n + 2 := by
          simpa using hlarge
        omega
      refine ⟨hiPos, hiLarge, ?_⟩
      change a.toBONG.tail.order i +
          a.toBONG.tail.order ⟨i.val + 1, hiLarge⟩ ≤
        b.toBONG.tail.order ⟨i.val - 1, by omega⟩ +
          b.toBONG.tail.order i
      rw [a.toBONG.order_tail, a.toBONG.order_tail,
        b.toBONG.order_tail, b.toBONG.order_tail]
      have hnext :
          (⟨i.val + 1, hiLarge⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val + 1, hlarge⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp
      have hprevious :
          (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val - 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp
        omega
      rw [hnext, hprevious]
      exact hsum

end BONG.GoodBONG

end Bong
