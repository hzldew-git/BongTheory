/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIBetaEvenGap
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityJumpBound
import Bong.Bong.Beli2019Lemma79CaseSixProfile
import Bong.Bong.Beli2019Lemma72Arithmetic

/-!
# Beli (2019), Lemma 9.12: parity tools for the type-III odd-gap branch

The last scalar branch of the type-III argument compares prefixes belonging
to two possibly different quadratic spaces.  This file records the mixed-space
product bounds and the elementary parity-chain lemma used in that argument.
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

/-- A prefix congruence propagates across a tail whose corresponding entries
are congruent. -/
theorem prefixSum_modEq_of_prefix_and_tail
    {m₁ m₂ : Nat} (x : BeliOrderSequence m₁ Int)
    (y : BeliOrderSequence m₂ Int) {first last : Nat}
    (hfirstLast : first ≤ last)
    (hfirst : Int.ModEq 2 (x.prefixSum first) (y.prefixSum first))
    (htail : ∀ k, first ≤ k → k < last →
      Int.ModEq 2 (x.entryOrZero k) (y.entryOrZero k)) :
    Int.ModEq 2 (x.prefixSum last) (y.prefixSum last) := by
  induction last, hfirstLast using Nat.le_induction with
  | base => exact hfirst
  | succ last hfirstLast ih =>
      rw [x.prefixSum_succ, y.prefixSum_succ]
      exact (ih fun k hfk hkl ↦
        htail k hfk (hkl.trans_le (Nat.le_succ last))).add
          (htail last hfirstLast (Nat.lt_succ_self last))

/-- The order of a signed product of mixed prefixes is the sum of their
prefix orders. -/
theorem signed_mixed_prefixProduct_order_odd_of_sum_odd
    (b : GoodBONG q L (n + 2)) (c : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd (b.orderSequence.prefixSum (i.val + 1) +
      c.orderSequence.prefixSum (i.val - 1))) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (i.val + 1) (Nat.succ_le_of_lt i.lt_large),
    c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (i.val - 1) ((Nat.sub_le i.val 1).trans i.lt_large.le)]
  exact hodd

/-- The primary odd-product estimate in the mixed-space form required by
Lemma 9.12. -/
theorem representationAlphaValue_le_order_sub_of_primaryProduct_odd_mixed
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (b : GoodBONG q L (n + 2)) (c : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int)
    (hodd : Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1))))
    (hcomparison : base ≤ c.order (evenTargetPreviousIndex i)) :
    b.representationAlphaValue c i ≤
      ((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) := by
  have hzero := truncatedPrefixDefect_eq_zero_of_odd_order_mixed
    (alphaV := alphaV) (alphaW := alphaW)
    b c (-1) (i.val + 1) (i.val - 1) hodd
  have hprevious :
      (⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : Fin (n + 2)) = evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  apply WithTop.coe_le_coe.mp
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
      b.representationAlpha_le_primary c i
    _ = (((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : Rat) :
          WithTop Rat) := by
      unfold representationPrimaryDefect
      rw [hzero, add_zero, hprevious]
    _ ≤ (((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) :
          WithTop Rat) := by
      norm_cast
      exact_mod_cast sub_le_sub_left hcomparison _

/-- A comparison alpha bound closes the primary candidate even when source
and comparison live in different quadratic spaces. -/
theorem representationAlphaValue_le_order_sub_of_comparisonAlpha_mixed
    (b : GoodBONG q L (n + 2)) (c : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int)
    (hiTwo : 2 ≤ i.val)
    (hcomparison : c.alphaValue (evenTargetPreviousAlphaIndex i) ≤
      ((c.order (evenTargetPreviousIndex i) - base : Int) : Rat)) :
    b.representationAlphaValue c i ≤
      ((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) := by
  have hcap := (b.representationAlpha_le_prime c i).trans
    (b.representationAlphaPrime_le_primaryRightCap c i)
  have hprevious :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
        evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  rw [hprevious, evenTarget_prefixAlphaCap c i hiTwo] at hcap
  apply WithTop.coe_le_coe.mp
  rw [b.coe_representationAlphaValue c i]
  apply hcap.trans
  norm_cast
  push_cast at hcomparison ⊢
  linarith

/-- If the orders at positions `1` and `i-1` have opposite parity, some
adjacent pair between them has odd order sum. -/
theorem exists_odd_adjacent_order_sum_of_endpoint_parity
    (c : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (hiThree : 3 ≤ i.val)
    (hfirstLast : Int.ModEq 2
      (c.order (evenTargetPreviousIndex i))
      (c.order (⟨1, by have hlt := i.lt_large; omega⟩ : Fin (n + 2)) + 1)) :
    ∃ j : Fin (n + 1), 1 ≤ j.val ∧ j.val + 1 < i.val ∧
      Odd (c.order j.castSucc + c.order j.succ) := by
  by_contra hnot
  push_neg at hnot
  let f : Nat → Int := fun k ↦
    if hk : k < n + 2 then c.order ⟨k, hk⟩ else 0
  have hchain := int_modEq_two_of_even_successive f
    (i := 1) (k := i.val - 1) (by omega) (by
      intro t htOne htLast
      have htBound : t < n + 1 := by
        have hlt := i.lt_large
        omega
      let j : Fin (n + 1) := ⟨t, htBound⟩
      have hnotOdd : ¬ Odd (c.order j.castSucc + c.order j.succ) := by
        exact hnot j (by change 1 ≤ t; exact htOne) (by
          change t + 1 < i.val
          omega)
      have hsumEven : Even (c.order j.castSucc + c.order j.succ) :=
        Int.not_odd_iff_even.mp hnotOdd
      rcases hsumEven with ⟨d, hd⟩
      have hdiffEven : Even (c.order j.succ - c.order j.castSucc) := by
        refine ⟨d - c.order j.castSucc, ?_⟩
        omega
      have htLarge : t < n + 2 := htBound.trans (Nat.lt_succ_self _)
      have htSuccLarge : t + 1 < n + 2 := by omega
      simp only [f, dif_pos htSuccLarge, dif_pos htLarge]
      convert hdiffEven using 1 <;> congr 1 <;> apply Fin.ext <;> rfl)
  have hlastIndex :
      (⟨i.val - 1, by have hlt := i.lt_large; omega⟩ : Fin (n + 2)) =
        evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  have honeIndex :
      (⟨1, by have hlt := i.lt_large; omega⟩ : Fin (n + 2)) =
        (⟨1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hlastBound : i.val - 1 < n + 2 := by
    have hlt := i.lt_large
    omega
  have honeBound : 1 < n + 2 := by omega
  simp only [f, dif_pos hlastBound, dif_pos honeBound,
    hlastIndex, honeIndex] at hchain
  have honeNot : ¬ Int.ModEq 2
      (c.order (⟨1, by have hlt := i.lt_large; omega⟩ : Fin (n + 2)))
      (c.order (⟨1, by have hlt := i.lt_large; omega⟩ : Fin (n + 2)) + 1) := by
    rw [Int.modEq_iff_dvd]
    intro hdvd
    rcases hdvd with ⟨z, hz⟩
    omega
  exact honeNot (hchain.symm.trans hfirstLast)

/-- Two-step monotonicity propagates lower bounds from positions `1` and
`2` to every later comparison order. -/
theorem comparison_order_ge_of_first_two_parity_anchors
    (c : GoodBONG r M (n + 2)) (base : Int) (hn : 0 < n)
    (hone : base ≤ c.order (⟨1, by omega⟩ : Fin (n + 2)))
    (htwo : base ≤ c.order (⟨2, by omega⟩ : Fin (n + 2)))
    (k : Fin (n + 2)) (hk : 1 ≤ k.val) : base ≤ c.order k := by
  rcases Nat.even_or_odd k.val with hkEven | hkOdd
  · have hkTwo : 2 ≤ k.val := by
      rcases hkEven with ⟨d, hd⟩
      omega
    have hgap : Even (k.val - 2) := by
      rcases hkEven with ⟨d, hd⟩
      refine ⟨d - 1, ?_⟩
      omega
    have hmono := c.orderSequence.entryOrZero_le_of_evenGap
      2 k.val hkTwo k.isLt hgap
    rw [c.orderSequence_entryOrZero_eq_order
      (⟨2, by omega⟩ : Fin (n + 2)),
      c.orderSequence_entryOrZero_eq_order k] at hmono
    exact htwo.trans hmono
  · have hgap : Even (k.val - 1) := by
      rcases hkOdd with ⟨d, hd⟩
      exact ⟨d, by omega⟩
    have hmono := c.orderSequence.entryOrZero_le_of_evenGap
      1 k.val hk k.isLt hgap
    rw [c.orderSequence_entryOrZero_eq_order
      (⟨1, by omega⟩ : Fin (n + 2)),
      c.orderSequence_entryOrZero_eq_order k] at hmono
    exact hone.trans hmono

end BONG.GoodBONG

end Bong
