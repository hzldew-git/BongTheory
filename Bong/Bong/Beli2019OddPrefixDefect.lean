/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixConsequences
import Bong.Bong.Beli2019OrderSums
import Bong.Bong.Beli2009BinaryRemarks

/-!
# Beli (2019), the odd prefix-product branch of Lemma 5.13

The proof of condition 2.1(ii) repeatedly observes that a one-unit jump in
the cumulative BONG orders makes the product `a_(1,i) b_(1,i)` have odd
valuation.  Its quadratic defect, and hence its capped prefix defect, is
then zero.  This file separates that reusable arithmetic from the later
Jordan-component case analysis.
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
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The valuation of a prefix product is the corresponding cumulative
order sum. -/
theorem ordUnit_prefixProduct_eq_orderSequence_prefixSum
    (a : GoodBONG q L n) (i : Nat) (hi : i ≤ n) :
    ordUnit K (a.prefixProduct i) = a.orderSequence.prefixSum i := by
  induction i with
  | zero =>
      have hone : ordUnit K (1 : Kˣ) = 0 := by
        have h := ordUnit_mul K (1 : Kˣ) 1
        simp only [mul_one] at h
        omega
      simpa [GoodBONG.prefixProduct] using hone
  | succ i ih =>
      have hin : i < n := by omega
      calc
        ordUnit K (a.prefixProduct (i + 1)) =
            ordUnit K (a.prefixProduct i) + a.order ⟨i, hin⟩ := by
          unfold GoodBONG.prefixProduct
          rw [a.toBONG.prefixProduct_succ i hin, ordUnit_mul]
          rfl
        _ = a.orderSequence.prefixSum i + a.order ⟨i, hin⟩ := by
          rw [ih (by omega)]
        _ = a.orderSequence.prefixSum (i + 1) := by
          rw [a.orderSequence.prefixSum_succ,
            BeliOrderSequence.entryOrZero_of_lt a.orderSequence hin]
          rfl

/-- If the second cumulative order sum is one larger, the product of the
two prefixes has odd valuation. -/
theorem comparisonPrefixProduct_order_odd_of_prefixSum_succ
    (a : GoodBONG q L m) (b : GoodBONG r M n)
    (i : Nat) (him : i ≤ m) (hin : i ≤ n)
    (hsum : b.orderSequence.prefixSum i =
      a.orderSequence.prefixSum i + 1) :
    Odd (ordUnit K (a.prefixProduct i * b.prefixProduct i)) := by
  rw [ordUnit_mul,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum i him,
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum i hin, hsum]
  refine ⟨a.orderSequence.prefixSum i, ?_⟩
  omega

/-- The form used in Lemma 5.13(ii): equal sums before the current entry
and a one-unit jump at that entry imply odd prefix-product valuation. -/
theorem comparisonPrefixProduct_order_odd_of_previous_prefix_eq
    (a : GoodBONG q L m) (b : GoodBONG r M n)
    (i : Nat) (hi0 : 0 < i) (him : i ≤ m) (hin : i ≤ n)
    (hprevious : a.orderSequence.prefixSum (i - 1) =
      b.orderSequence.prefixSum (i - 1))
    (hcurrent : b.orderSequence.entryOrZero (i - 1) =
      a.orderSequence.entryOrZero (i - 1) + 1) :
    Odd (ordUnit K (a.prefixProduct i * b.prefixProduct i)) := by
  apply a.comparisonPrefixProduct_order_odd_of_prefixSum_succ b i him hin
  rw [show i = (i - 1) + 1 by omega,
    b.orderSequence.prefixSum_succ, a.orderSequence.prefixSum_succ,
    ← hprevious, hcurrent]
  abel

/-- Defect orders are nonnegative. -/
theorem defectOrder_nonneg (x : Kˣ) :
    (0 : WithTop ℚ) ≤ defectOrder (K := K) x := by
  by_cases htop : quadraticDefect K x = ⊤
  · unfold defectOrder
    rw [htop]
    change (0 : WithTop ℚ) ≤ ⊤
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    unfold defectOrder
    rw [← hd]
    change (0 : WithTop ℚ) ≤ ((d : ℚ) : WithTop ℚ)
    exact_mod_cast Nat.zero_le d

/-- Prefix alpha caps are nonnegative, including their infinite endpoint
values. -/
theorem prefixAlphaCap_nonneg [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (i : Nat) :
    (0 : WithTop ℚ) ≤ a.prefixAlphaCap i := by
  unfold prefixAlphaCap
  split_ifs with hi
  · exact_mod_cast (a.alpha_p2 ⟨i - 1, by omega⟩).1
  · exact le_top

/-- Every capped prefix defect is nonnegative. -/
theorem truncatedPrefixDefect_nonneg
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (epsilon : Kˣ) (i j : Nat) :
    (0 : WithTop ℚ) ≤ a.truncatedPrefixDefect b epsilon i j := by
  have ha : (0 : WithTop ℚ) ≤ a.prefixAlphaCap i := by
    letI : Beli2006AlphaLaws.{u, v} K := alphaV
    exact a.prefixAlphaCap_nonneg i
  have hb : (0 : WithTop ℚ) ≤ b.prefixAlphaCap j := by
    letI : Beli2006AlphaLaws.{u, w} K := alphaW
    exact b.prefixAlphaCap_nonneg j
  unfold truncatedPrefixDefect
  exact le_min (defectOrder_nonneg _)
    (le_min ha hb)

/-- Odd valuation of a signed product of two arbitrary prefixes forces its
capped defect to be zero.  Unlike the older same-space variant used in
Lemma 7.9, this statement allows the two quadratic spaces to differ. -/
theorem truncatedPrefixDefect_eq_zero_of_odd_order_mixed
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (epsilon : Kˣ) (i j : Nat)
    (hodd : Odd (ordUnit K
      (epsilon * a.prefixProduct i * b.prefixProduct j))) :
    a.truncatedPrefixDefect b epsilon i j = 0 := by
  apply le_antisymm
  · calc
      a.truncatedPrefixDefect b epsilon i j ≤
          defectOrder (K := K)
            (epsilon * a.prefixProduct i * b.prefixProduct j) :=
        a.truncatedPrefixDefect_le_defect b epsilon i j
      _ = 0 := by
        unfold defectOrder
        rw [quadraticDefect_eq_zero_of_odd_ordUnit _ hodd]
        rfl
  · exact truncatedPrefixDefect_nonneg
      (alphaV := alphaV) (alphaW := alphaW) a b epsilon i j

/-- Odd valuation forces the capped comparison-prefix defect to be exactly
zero. -/
theorem truncatedPrefixDefect_eq_zero_of_odd_order
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : Nat)
    (hodd : Odd (ordUnit K (a.prefixProduct i * b.prefixProduct i))) :
    a.truncatedPrefixDefect b 1 i i = 0 := by
  apply le_antisymm
  · calc
      a.truncatedPrefixDefect b 1 i i ≤
          defectOrder (K := K)
            (1 * a.prefixProduct i * b.prefixProduct i) :=
        a.truncatedPrefixDefect_le_defect b 1 i i
      _ = defectOrder (K := K)
          (a.prefixProduct i * b.prefixProduct i) := by simp
      _ = 0 := by
        unfold defectOrder
        rw [quadraticDefect_eq_zero_of_odd_ordUnit _ hodd]
        rfl
  · have ha : (0 : WithTop ℚ) ≤ a.prefixAlphaCap i := by
      letI : Beli2006AlphaLaws.{u, v} K := alphaV
      exact a.prefixAlphaCap_nonneg i
    have hb : (0 : WithTop ℚ) ≤ b.prefixAlphaCap i := by
      letI : Beli2006AlphaLaws.{u, w} K := alphaW
      exact b.prefixAlphaCap_nonneg i
    unfold truncatedPrefixDefect
    exact le_min (defectOrder_nonneg _) (le_min ha hb)

/-- Lemma 5.13(ii)'s final conclusion, stated from its cumulative-order
input. -/
theorem truncatedPrefixDefect_eq_zero_of_prefixSum_succ
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : Nat) (him : i ≤ m + 1) (hin : i ≤ n + 1)
    (hsum : b.orderSequence.prefixSum i =
      a.orderSequence.prefixSum i + 1) :
    a.truncatedPrefixDefect b 1 i i = 0 := by
  apply truncatedPrefixDefect_eq_zero_of_odd_order
    (alphaV := alphaV) (alphaW := alphaW) a b i
  exact a.comparisonPrefixProduct_order_odd_of_prefixSum_succ b
    i him hin hsum

end BONG.GoodBONG

end Bong
