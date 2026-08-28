/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityCurrent

/-!
# Beli (2019), Lemma 7.9(ii), case 6: second-parity profile closure

The type-II profile makes the target prefix even once the reverse current
comparison forces the index to be even.  In type III the profile instead
forces the index to be odd, so that reverse comparison is impossible.  The
strict norm-ideal hypothesis supplies the common first-order upper bound.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Congruence modulo two transports evenness from the right side to the
left side. -/
theorem caseSix_even_of_modEq_two_of_even {x y : Int}
    (hmod : Int.ModEq 2 x y) (hy : Even y) : Even x := by
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨z, hz⟩
  rcases hy with ⟨d, hd⟩
  exact ⟨d - z, by omega⟩

/-- At an even index in the type-II case-6 parity class, Lemma 7.2(ii)
makes the target prefix sum even. -/
theorem beli2019Lemma79_typeII_caseSix_targetPrefix_even_of_index_even
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hiEven : Even i.val) :
    Even (b.orderSequence.prefixSum i.val) := by
  let base := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  let P := a.beli2019Lemma72_ii b D hfirst
  rcases hiEven with ⟨d, hd⟩
  have hiInt : (i.val : Int) = (d : Int) + (d : Int) := by
    exact_mod_cast hd
  by_cases hbefore : i.val < D.outer.transition.firstTwo
  · have hmod := P.target_before i.val hbefore
    apply caseSix_even_of_modEq_two_of_even
      (by simpa only [T] using hmod)
    refine ⟨(d : Int) * T, ?_⟩
    rw [hiInt]
    ring
  · rcases heven with ⟨e, he⟩
    have hbaseEven : Even base := ⟨d - e, by
      simp only [base]
      omega⟩
    rcases hbaseEven with ⟨f, hf⟩
    have hbaseInt : (base : Int) = (f : Int) + (f : Int) := by
      exact_mod_cast hf
    have hmod := P.target_after i.val (by omega) (by omega)
    apply caseSix_even_of_modEq_two_of_even
      (by simpa only [T, base] using hmod)
    refine ⟨(d : Int) * (T + 1) + (f : Int), ?_⟩
    rw [hiInt, hbaseInt]
    ring

/-- The strict norm-ideal comparison bounds a type-II case-6 target
current order by one above the third first order. -/
theorem beli2019Lemma79_typeII_caseSix_targetCurrent_le_thirdFirst_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero 0 + 1 := by
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hleftValue := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
  have hcurrent := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hrightValue := D.right_target
  omega

/-- In nonoverlapping type III, the source order at the right transition
does not exceed its order at the left transition. -/
theorem beli2019Lemma79_typeIII_caseSix_sourceRight_le_sourceLeft
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1) :
    a.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1) ≤
      a.orderSequence.entryOrZero D.outer.transition.lastZero := by
  let center : Fin (n + 1) := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have halpha := a.beli2019Lemma69_i_typeIII
    (alphaV := alpha) (alphaW := alpha) b D hfirst hdefect
  have halphaCenter : a.alphaValue center ≤ 1 := by
    simpa only [center] using halpha
  have hgapLe := a.orderGap_le_one_of_alphaValue_le_one
    center halphaCenter
  have hgapNe : a.orderGap center ≠ 1 := by
    simpa only [center] using hnotOverlap
  have hgapNonpositive : a.orderGap center ≤ 0 := by omega
  have hrightEq : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  have hgapFormula : a.orderGap center =
      a.orderSequence.entryOrZero
          (D.outer.transition.firstTwo - 1) -
        a.orderSequence.entryOrZero D.outer.transition.lastZero := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (show D.outer.transition.firstTwo - 1 < n + 2 by
          have hbound := D.outer.transition.firstTwo_le_rank
          omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (show D.outer.transition.lastZero < n + 2 by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega)]
    change a.order center.succ - a.order center.castSucc = _
    congr 1 <;> apply congrArg a.order <;> apply Fin.ext
    · change center.val + 1 = D.outer.transition.firstTwo - 1
      simpa only [center] using hrightEq.symm
  rw [hgapFormula] at hgapNonpositive
  omega

/-- The strict norm-ideal comparison supplies the same first-order bound
for a nonoverlapping type-III case-6 current order. -/
theorem beli2019Lemma79_typeIII_caseSix_targetCurrent_le_thirdFirst_add_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero 0 + 1 := by
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst D.outer.transition.lastZero le_rfl hleftEven
  have hsourceRight :=
    beli2019Lemma79_typeIII_caseSix_sourceRight_le_sourceLeft
      a b D hfirst hdefect hnotOverlap
  have hcurrent := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hrightBoundary := D.outer.transition.rightBoundary
  omega

/-- The type-III right-profile parity class consists of odd indices. -/
theorem beli2019Lemma79_typeIII_caseSix_index_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    Odd i.val := by
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  rcases hleftEven with ⟨p, hp⟩
  rcases heven with ⟨d, hd⟩
  have hbaseEq : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  refine ⟨p + d, ?_⟩
  rw [hbaseEq] at hd hright
  omega

/-- The same-current-parity subcase of the type-II second parity branch. -/
theorem beli2019Lemma79_typeII_caseSix_secondParity_sameCurrentParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hupper :=
    beli2019Lemma79_typeII_caseSix_targetCurrent_le_thirdFirst_add_one
      a b c D hfirst hnorm i hright hthroughLast heven
  by_cases hcurrent : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1)
  · exact lemma79_caseSix_secondParity_of_prefix_odd_orders_modEq_current_le
      b c i hcomparison horders hcurrent
  · have hstrict : c.orderSequence.entryOrZero (i.val - 1) <
        b.orderSequence.entryOrZero i.val := lt_of_not_ge hcurrent
    have hiEven := caseSix_index_even_of_current_lt_and_orders_modEq
      b c i hupper horders hstrict
    have htarget :=
      beli2019Lemma79_typeII_caseSix_targetPrefix_even_of_index_even
        a b D hfirst i hright hthroughLast heven hiEven
    exact lemma79_caseSix_secondParity_of_prefix_odd_target_even_orders_modEq
      b c i hcomparison htarget hupper horders

/-- The same-current-parity subcase of the nonoverlapping type-III second
parity branch. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_sameCurrentParity
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hupper :=
    beli2019Lemma79_typeIII_caseSix_targetCurrent_le_thirdFirst_add_one
      a b c D hfirst hdefect hnotOverlap hnorm i hright hthroughLast heven
  by_cases hcurrent : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1)
  · exact lemma79_caseSix_secondParity_of_prefix_odd_orders_modEq_current_le
      b c i hcomparison horders hcurrent
  · have hstrict : c.orderSequence.entryOrZero (i.val - 1) <
        b.orderSequence.entryOrZero i.val := lt_of_not_ge hcurrent
    have hiEven := caseSix_index_even_of_current_lt_and_orders_modEq
      b c i hupper horders hstrict
    have hiOdd := beli2019Lemma79_typeIII_caseSix_index_odd
      a b D hfirst i hright heven
    rcases hiEven with ⟨e, he⟩
    rcases hiOdd with ⟨o, ho⟩
    omega

end BONG.GoodBONG

end Bong
