/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93TailOrder
import Bong.Bong.Beli2019EssentialIndex
import Bong.Bong.Beli2019Lemma93TailAlpha

/-!
# Beli (2019), Lemma 9.3: essential indices after deleting the heads

The order sequences of the two projected tails are the original order
sequences with their first entries removed.  Away from the new left endpoint,
essentiality therefore shifts by one.  The first nontrivial boundary is the
small exceptional index discussed separately in the proof of Lemma 9.3.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- For every tail boundary of zero-based value at least two, essentiality
is exactly essentiality of the next boundary in the original pair.  This is
the formal version of the sentence preceding the low-index discussion in the
proof of Lemma 9.3. -/
theorem isEssentialFor_tail_iff_succ_of_two_le
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : Fin (n + 1)) (hi : 2 ≤ i.val) :
    a.tail.IsEssentialFor b.tail i ↔ a.IsEssentialFor b i.succ := by
  unfold IsEssentialFor BeliOrderSequence.IsEssentialFor
  constructor
  · intro h
    constructor
    · intro _ hnext
      have hnext' : i.val + 1 < n + 1 := by
        simp only [Fin.val_succ] at hnext
        omega
      have ht := h.1 (by omega) hnext'
      change b.tail.order ⟨i.val - 1, by omega⟩ <
          a.tail.order ⟨i.val + 1, by omega⟩ at ht
      rw [b.order_goodTail, a.order_goodTail] at ht
      change b.order ⟨i.succ.val - 1, by omega⟩ <
        a.order ⟨i.succ.val + 1, by omega⟩
      convert ht using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp only [Fin.val_succ] <;> omega
    · intro _ hnext
      have hnext' : i.val + 2 < n + 1 := by
        simp only [Fin.val_succ] at hnext
        omega
      have ht := h.2 (by omega) hnext'
      change b.tail.order ⟨i.val - 2, by omega⟩ +
            b.tail.order ⟨i.val - 1, by omega⟩ <
          a.tail.order ⟨i.val + 1, by omega⟩ +
            a.tail.order ⟨i.val + 2, by omega⟩ at ht
      rw [b.order_goodTail, b.order_goodTail,
        a.order_goodTail, a.order_goodTail] at ht
      change b.order ⟨i.succ.val - 2, by omega⟩ +
            b.order ⟨i.succ.val - 1, by omega⟩ <
          a.order ⟨i.succ.val + 1, by omega⟩ +
            a.order ⟨i.succ.val + 2, by omega⟩
      have hminusTwo :
          (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val - 2, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      have hminusOne :
          (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val - 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      have hplusOne :
          (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val + 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [Fin.val_succ]
      have hplusTwo :
          (⟨i.val + 2, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val + 2, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [Fin.val_succ]
      rw [← hminusTwo, ← hminusOne, ← hplusOne, ← hplusTwo]
      exact ht
  · intro h
    constructor
    · intro _ hnext
      have hnext' : i.succ.val + 1 < n + 2 := by
        simp only [Fin.val_succ]
        omega
      have ho := h.1 (by simp) hnext'
      change b.order ⟨i.succ.val - 1, by omega⟩ <
          a.order ⟨i.succ.val + 1, by omega⟩ at ho
      change b.tail.order ⟨i.val - 1, by omega⟩ <
        a.tail.order ⟨i.val + 1, by omega⟩
      rw [b.order_goodTail, a.order_goodTail]
      convert ho using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp only [Fin.val_succ] <;> omega
    · intro _ hnext
      have hnext' : i.succ.val + 2 < n + 2 := by
        simp only [Fin.val_succ]
        omega
      have ho := h.2 (by simp only [Fin.val_succ]; omega) hnext'
      change b.order ⟨i.succ.val - 2, by omega⟩ +
            b.order ⟨i.succ.val - 1, by omega⟩ <
          a.order ⟨i.succ.val + 1, by omega⟩ +
            a.order ⟨i.succ.val + 2, by omega⟩ at ho
      change b.tail.order ⟨i.val - 2, by omega⟩ +
            b.tail.order ⟨i.val - 1, by omega⟩ <
          a.tail.order ⟨i.val + 1, by omega⟩ +
            a.tail.order ⟨i.val + 2, by omega⟩
      rw [b.order_goodTail, b.order_goodTail,
        a.order_goodTail, a.order_goodTail]
      have hminusTwo :
          (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val - 2, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      have hminusOne :
          (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val - 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      have hplusOne :
          (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val + 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [Fin.val_succ]
      have hplusTwo :
          (⟨i.val + 2, by omega⟩ : Fin (n + 1)).succ =
            (⟨i.succ.val + 2, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [Fin.val_succ]
      rw [hminusTwo, hminusOne, hplusOne, hplusTwo]
      exact ho

/-- At the first nontrivial tail boundary, the apparent extra two-step
essentiality condition in the original pair follows from equality of the
first orders and goodness.  In paper coordinates this is the equivalence
between essentiality of index `2` for `M*,N*` and index `3` for `M,N`.
-/
theorem isEssentialFor_tail_one_iff_original_two_of_firstOrder_eq
    (a : GoodBONG q L (n + 4)) (b : GoodBONG r M (n + 4))
    (hfirst : a.order (0 : Fin (n + 4)) =
      b.order (0 : Fin (n + 4))) :
    a.tail.IsEssentialFor b.tail (1 : Fin (n + 3)) ↔
      a.IsEssentialFor b (2 : Fin (n + 4)) := by
  let tailOne : Fin (n + 3) := ⟨1, by omega⟩
  let originalTwo : Fin (n + 4) := ⟨2, by omega⟩
  have htailOne : (1 : Fin (n + 3)) = tailOne := by
    apply Fin.ext
    simp [tailOne]
  have horiginalTwo : (2 : Fin (n + 4)) = originalTwo := by
    apply Fin.ext
    simp [originalTwo]
  rw [htailOne, horiginalTwo]
  unfold IsEssentialFor BeliOrderSequence.IsEssentialFor
  dsimp only [tailOne, originalTwo]
  constructor
  · intro h
    have hcross := h.1 (by omega) (by omega)
    change b.tail.order (0 : Fin (n + 3)) <
      a.tail.order (2 : Fin (n + 3)) at hcross
    rw [b.order_goodTail, a.order_goodTail] at hcross
    have hcross' : b.order ⟨1, by omega⟩ < a.order ⟨3, by omega⟩ := by
      convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
    constructor
    · intro _ _
      change b.order ⟨1, by omega⟩ < a.order ⟨3, by omega⟩
      exact hcross'
    · intro _ hnext
      change 4 < n + 4 at hnext
      have hn : 0 < n := by omega
      let o0 : Fin (n + 4) := ⟨0, by omega⟩
      let o1 : Fin (n + 4) := ⟨1, by omega⟩
      let o2 : Fin (n + 4) := ⟨2, by omega⟩
      let o3 : Fin (n + 4) := ⟨3, by omega⟩
      let o4 : Fin (n + 4) := ⟨4, by omega⟩
      have ha02 : a.order o0 ≤ a.order o2 := by
        have hg := a.good o0 (by simp only [o0]; omega)
        convert hg using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp only [o0, o2]
      have ha24 : a.order o2 ≤ a.order o4 := by
        have hg := a.good o2 (by simp only [o2]; omega)
        convert hg using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp only [o2, o4]
      have ha04 : a.order o0 ≤ a.order o4 := ha02.trans ha24
      have hfirst' : a.order o0 = b.order o0 := by
        convert hfirst using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp only [o0, Fin.val_zero]
      have hcross'' : b.order o1 < a.order o3 := by
        simpa only [o1, o3] using hcross'
      have hb04 : b.order o0 ≤ a.order o4 :=
        hfirst'.symm.le.trans ha04
      have hsum : b.order o0 + b.order o1 < a.order o3 + a.order o4 := by
        calc
          b.order o0 + b.order o1 < a.order o4 + a.order o3 :=
            add_lt_add_of_le_of_lt hb04 hcross''
          _ = a.order o3 + a.order o4 := add_comm _ _
      simpa only [BeliOrderSequence.entry, orderSequence, o0, o1, o3, o4,
        Nat.reduceSub, Nat.reduceAdd] using hsum
  · intro h
    constructor
    · intro _ _
      have hcross := h.1 (by omega) (by omega)
      change b.order ⟨1, by omega⟩ < a.order ⟨3, by omega⟩ at hcross
      change b.tail.order (0 : Fin (n + 3)) <
        a.tail.order (2 : Fin (n + 3))
      rw [b.order_goodTail, a.order_goodTail]
      convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
    · intro htwo
      omega

end BONG.GoodBONG

end Bong
