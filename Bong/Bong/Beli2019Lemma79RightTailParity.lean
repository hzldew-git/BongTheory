/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailProfile
import Bong.Bong.Beli2019Lemma79CaseSixProfile
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 7.9(ii), case 8: prefix parity

The source and intermediate prefix sums differ by two on the unchanged
tail.  Hence comparison with a third prefix gives either two even products
or two odd products.  A strict inequality between the corresponding capped
defects rules out the odd alternative, since both defects would vanish.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Adding two does not change an integer modulo two. -/
theorem caseEight_modEq_two_of_add_two_eq {x y : Int}
    (h : x + 2 = y) : Int.ModEq 2 x y := by
  apply int_modEq_two_of_even_sub
  exact ⟨-1, by omega⟩

/-- If two source prefixes have the same parity, comparison with a third
prefix produces either two even products or two odd products. -/
theorem caseEight_comparisonPrefix_parity_dichotomy
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hab : Int.ModEq 2 (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val)) :
    (Even (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)) ∧
        Even (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) ∨
      (Odd (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)) ∧
        Odd (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) := by
  let aSum := a.orderSequence.prefixSum i.val
  let bSum := b.orderSequence.prefixSum i.val
  let cSum := c.orderSequence.prefixSum i.val
  rcases modEq_two_or_add_one bSum cSum with hbc | hbc
  · apply Or.inl
    have hac : Int.ModEq 2 aSum cSum := hab.trans hbc
    exact ⟨
      b.comparisonPrefixProduct_order_even_of_prefixSum_modEq
        c i.val i.lt_large.le i.lt_large.le (by
          simpa only [bSum, cSum] using hbc),
      a.comparisonPrefixProduct_order_even_of_prefixSum_modEq
        c i.val i.lt_large.le i.lt_large.le (by
          simpa only [aSum, cSum] using hac)⟩
  · apply Or.inr
    have hac : Int.ModEq 2 aSum (cSum + 1) := hab.trans hbc
    exact ⟨
      b.comparisonPrefixProduct_order_odd_of_modEq_add_one c i (by
        simpa only [bSum, cSum] using hbc),
      a.comparisonPrefixProduct_order_odd_of_modEq_add_one c i (by
        simpa only [aSum, cSum] using hac)⟩

/-- In the strict case-8 branch, the intermediate and third prefix sums
must have the same parity. -/
theorem caseEight_prefixSum_modEq_comparison_of_strict_defect
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hab : Int.ModEq 2 (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val))
    (hstrict : b.truncatedPrefixDefect c 1 i.val i.val <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val) := by
  rcases modEq_two_or_add_one
      (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val) with hbc | hbc
  · exact hbc
  · have hac : Int.ModEq 2 (a.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val + 1) := hab.trans hbc
    have hbcOdd :=
      b.comparisonPrefixProduct_order_odd_of_modEq_add_one c i hbc
    have hacOdd :=
      a.comparisonPrefixProduct_order_odd_of_modEq_add_one c i hac
    have hbZero := b.truncatedPrefixDefect_eq_zero_of_odd_order
      c i.val hbcOdd
    have haZero := a.truncatedPrefixDefect_eq_zero_of_odd_order
      c i.val hacOdd
    rw [hbZero, haZero] at hstrict
    exact False.elim (lt_irrefl 0 hstrict)

/-- Type-I case-8 source and intermediate prefixes are congruent modulo
two. -/
theorem beli2019Lemma79_typeI_caseEight_prefix_modEq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last < i.val) :
    Int.ModEq 2 (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val) :=
  caseEight_modEq_two_of_add_two_eq
    (beli2019Lemma79_typeI_caseEight_prefixSum
      a b D htotal i.val hafter i.lt_large.le)

/-- Type-II case-8 source and intermediate prefixes are congruent modulo
two. -/
theorem beli2019Lemma79_typeII_caseEight_prefix_modEq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last < i.val) :
    Int.ModEq 2 (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val) :=
  caseEight_modEq_two_of_add_two_eq
    (beli2019Lemma79_typeII_caseEight_prefixSum
      a b D htotal i.val hafter i.lt_large.le)

/-- Type-III case-8 source and intermediate prefixes are congruent modulo
two. -/
theorem beli2019Lemma79_typeIII_caseEight_prefix_modEq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last < i.val) :
    Int.ModEq 2 (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val) :=
  caseEight_modEq_two_of_add_two_eq
    (beli2019Lemma79_typeIII_caseEight_prefixSum
      a b D htotal i.val hafter i.lt_large.le)

end BONG.GoodBONG

end Bong
