/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74

/-!
# Beli (2019), Lemma 7.5: arithmetic core

The hypotheses force the two parity classes of orders to be constant.  The
last adjacent gap is therefore exactly `-2e`, its alpha value vanishes, and
Lemma 7.4(i) gives the required capped-defect lower bound.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The numerical conclusions used in the proof of Beli (2019), Lemma 7.5.
Indices `i,j` are zero-based versions of the paper's `i,j`. -/
structure Lemma75ArithmeticConsequences
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (R : Int) : Prop where
  right_even_order : b.order j.castSucc = R
  right_alpha_zero : b.alphaValue j = 0
  defect_ge_two_mul_e :
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ ((j.val - i.val + 2) / 2)) i.val (j.val + 2)
  even_order (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j)
      (hparity : Even (k.val - i.val)) :
    b.order k.castSucc = R
  odd_order (k : Fin (n + 2))
      (hik : i.val + 1 ≤ k.val) (hkj : k.val ≤ j.val + 1)
      (hparity : Even (k.val - (i.val + 1))) :
    b.order k = R - 2 * (ramificationIndex K : Int)

/-- Beli (2019), Lemma 7.5 up to the subsequent binary-lattice and
quadratic-space classifications. -/
theorem beli2019Lemma75_arithmetic
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (R : Int)
    (hij : i ≤ j) (heven : Even (j.val - i.val))
    (hiOrder : b.order i.castSucc = R)
    (hterminal :
      b.order j.succ = R - 2 * (ramificationIndex K : Int)) :
    Lemma75ArithmeticConsequences b i j R := by
  have hijOrderEntry := b.orderSequence.entryOrZero_le_of_evenGap
    i.val j.val (by omega) (by omega) heven
  have hiRead :
      b.orderSequence.entryOrZero i.val = b.order i.castSucc := by
    simpa only [Fin.val_castSucc] using
      b.orderSequence_entryOrZero_eq_order i.castSucc
  have hjRead :
      b.orderSequence.entryOrZero j.val = b.order j.castSucc := by
    simpa only [Fin.val_castSucc] using
      b.orderSequence_entryOrZero_eq_order j.castSucc
  rw [hiRead, hjRead] at hijOrderEntry
  have hlastGap := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e
    j.castSucc (Nat.succ_lt_succ j.isLt)
  change -(2 * (ramificationIndex K : Int)) ≤
    b.order j.succ - b.order j.castSucc at hlastGap
  have hjOrder : b.order j.castSucc = R := by
    omega
  have hjGap : b.orderGap j =
      -(2 * (ramificationIndex K : Int)) := by
    unfold orderGap
    rw [hjOrder, hterminal]
    omega
  have hjAlpha : b.alphaValue j = 0 :=
    (b.alpha_p2 j).2.mpr hjGap
  have hdefectRaw := b.beli2019Lemma74_i i j hij heven
    (hiOrder.trans hjOrder.symm)
  have hcritical :
      ((b.order j.castSucc - b.order j.succ : Int) : ℚ) +
          b.alphaValue j = 2 * (ramificationIndex K : ℚ) := by
    rw [hjOrder, hterminal, hjAlpha]
    push_cast
    ring
  rw [hcritical] at hdefectRaw
  have hfirstOdd : b.order i.succ =
      R - 2 * (ramificationIndex K : Int) := by
    have hfirstGap := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e
      i.castSucc (Nat.succ_lt_succ i.isLt)
    change -(2 * (ramificationIndex K : Int)) ≤
      b.order i.succ - b.order i.castSucc at hfirstGap
    have hoddChain := b.orderSequence.entryOrZero_le_of_evenGap
      (i.val + 1) (j.val + 1) (by omega) (by omega) (by
        rcases heven with ⟨d, hd⟩
        exact ⟨d, by omega⟩)
    have hiSuccRead :
        b.orderSequence.entryOrZero (i.val + 1) = b.order i.succ := by
      simpa only [Fin.val_succ] using
        b.orderSequence_entryOrZero_eq_order i.succ
    have hjSuccRead :
        b.orderSequence.entryOrZero (j.val + 1) = b.order j.succ := by
      simpa only [Fin.val_succ] using
        b.orderSequence_entryOrZero_eq_order j.succ
    rw [hiSuccRead, hjSuccRead] at hoddChain
    omega
  refine {
    right_even_order := hjOrder
    right_alpha_zero := hjAlpha
    defect_ge_two_mul_e := hdefectRaw
    even_order := ?_
    odd_order := ?_ }
  · intro k hik hkj hkEven
    have hremaining : Even (j.val - k.val) := by
      rcases heven with ⟨d, hd⟩
      rcases hkEven with ⟨t, ht⟩
      exact ⟨d - t, by omega⟩
    have hkOrder := b.order_eq_of_evenGap_between_equal
      i.castSucc k.castSucc j.castSucc hik hkj hkEven hremaining
      (hiOrder.trans hjOrder.symm)
    exact hkOrder.trans hjOrder
  · intro k hik hkj hkEven
    have hremaining : Even ((j.val + 1) - k.val) := by
      rcases heven with ⟨d, hd⟩
      rcases hkEven with ⟨t, ht⟩
      exact ⟨d - t, by omega⟩
    have hkOrder := b.order_eq_of_evenGap_between_equal
      i.succ k j.succ
      (by
        change i.succ.val ≤ k.val
        simpa only [Fin.val_succ] using hik)
      (by
        change k.val ≤ j.succ.val
        simpa only [Fin.val_succ] using hkj)
      hkEven hremaining
      (hfirstOdd.trans hterminal.symm)
    exact hkOrder.trans hterminal

end BONG.GoodBONG

end Bong
