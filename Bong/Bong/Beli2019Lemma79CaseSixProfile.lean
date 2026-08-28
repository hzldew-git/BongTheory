/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72TypeII
import Bong.Bong.Beli2019Lemma72TypeIII
import Bong.Bong.Beli2019Lemma79OrderRightAlternating
import Bong.Bong.Beli2019Remark613TypeIIRightAlpha
import Bong.Bong.Beli2019Remark613TypeIIIRightAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the right-even profile

Case 6 uses the parity class containing the coordinate immediately before
the right transition.  On this class the target order is one above the
source order, the target prefix cap is one, and the source and target prefix
sums have opposite parity.  This file extracts those common profile facts
for types II and III before any comparison with the third BONG.
-/

namespace Bong

open Dyadic

universe u v

namespace BeliOrderLE.NoGapTwoOuterConsequences

variable {n : Nat} {x y : BeliOrderSequence n Int}

/-- At even distance from the right transition, the target entry is exactly
one above the source entry. -/
theorem target_rightEven_eq_source_add_one
    (O : NoGapTwoOuterConsequences x y)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2)
    (k : Nat) (hright : O.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ O.last)
    (heven : Even (k - (O.transition.firstTwo - 1))) :
    y.entryOrZero k = x.entryOrZero k + 1 := by
  have htarget := O.target_rightEven_eq_boundary k hright hlast heven
  have hsource := O.source_rightEven_eq_boundary
    hnoTwo k hright hlast heven
  have hboundary := O.transition.rightBoundary
  omega

end BeliOrderLE.NoGapTwoOuterConsequences

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- An even natural-number distance gives congruent endpoints modulo two
after coercion to the integer order scale. -/
theorem modEq_two_of_even_nat_sub (base i : Nat) (hbase : base ≤ i)
    (heven : Even (i - base)) :
    Int.ModEq 2 (i : Int) (base : Int) := by
  apply int_modEq_two_of_even_sub
  rcases heven with ⟨d, hd⟩
  refine ⟨(d : Int), ?_⟩
  omega

/-- Any two integers are either congruent modulo two or differ by one
modulo two. -/
theorem modEq_two_or_add_one (x y : Int) :
    Int.ModEq 2 x y ∨ Int.ModEq 2 x (y + 1) := by
  rcases Int.even_or_odd (x - y) with heven | hodd
  · exact Or.inl (int_modEq_two_of_even_sub heven)
  · apply Or.inr
    apply int_modEq_two_of_even_sub
    rcases hodd with ⟨d, hd⟩
    exact ⟨d, by omega⟩

/-- Modulo two, moving a `+1` from the left side to the right side preserves
the congruence. -/
theorem modEq_two_add_one_left_iff_right {x y : Int}
    (h : Int.ModEq 2 (x + 1) y) : Int.ModEq 2 x (y + 1) := by
  rw [Int.modEq_iff_dvd] at h ⊢
  rcases h with ⟨d, hd⟩
  exact ⟨d + 1, by omega⟩

/-- If the source and target prefixes have opposite parity, comparison with
a third prefix gives exactly the two parity branches used in case 6. -/
theorem caseSix_comparisonPrefix_parity_dichotomy
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    {N : Lattice K V} (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hab : Int.ModEq 2 (a.orderSequence.prefixSum i.val + 1)
      (b.orderSequence.prefixSum i.val)) :
    (Even (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)) ∧
        Odd (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) ∨
      (Odd (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)) ∧
        Even (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) := by
  let aSum := a.orderSequence.prefixSum i.val
  let bSum := b.orderSequence.prefixSum i.val
  let cSum := c.orderSequence.prefixSum i.val
  have habShift : Int.ModEq 2 aSum (bSum + 1) := by
    apply modEq_two_add_one_left_iff_right
    simpa only [aSum, bSum] using hab
  rcases modEq_two_or_add_one bSum cSum with hbc | hbc
  · apply Or.inl
    have hac : Int.ModEq 2 aSum (cSum + 1) := by
      have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
      exact habShift.trans (hbc.add hone)
    exact ⟨
      b.comparisonPrefixProduct_order_even_of_prefixSum_modEq
        c i.val i.lt_large.le i.lt_large.le (by
          simpa only [bSum, cSum] using hbc),
      a.comparisonPrefixProduct_order_odd_of_modEq_add_one c i (by
        simpa only [aSum, cSum] using hac)⟩
  · apply Or.inr
    have hac : Int.ModEq 2 aSum cSum := by
      have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
      have habRaw : Int.ModEq 2 (aSum + 1) bSum := by
        simpa only [aSum, bSum] using hab
      have hshifted : Int.ModEq 2 (aSum + 1) (cSum + 1) := by
        exact habRaw.trans hbc
      simpa only [add_sub_cancel_right] using hshifted.sub hone
    exact ⟨
      b.comparisonPrefixProduct_order_odd_of_modEq_add_one c i (by
        simpa only [bSum, cSum] using hbc),
      a.comparisonPrefixProduct_order_even_of_prefixSum_modEq
        c i.val i.lt_large.le i.lt_large.le (by
          simpa only [aSum, cSum] using hac)⟩

/-- In type II, the source and target prefixes in the case-6 parity class
have opposite order parity. -/
theorem beli2019Lemma79_typeII_caseSix_prefix_opposite
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    Int.ModEq 2 (a.orderSequence.prefixSum i.val + 1)
      (b.orderSequence.prefixSum i.val) := by
  let base := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  let P := a.beli2019Lemma72_ii b D hfirst
  have hleftSource : D.outer.transition.lastZero + 1 ≤ i.val := by
    have hlong := D.long
    omega
  have hsource := P.source_after i.val hleftSource (by omega)
  have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
  have hsourceOne : Int.ModEq 2
      (a.orderSequence.prefixSum i.val + 1) ((i.val : Int) * T) := by
    have hadd := hsource.add hone
    simpa only [T, add_assoc, sub_add_cancel] using hadd
  by_cases hbeforeTransition : i.val < D.outer.transition.firstTwo
  · have htarget := P.target_before i.val hbeforeTransition
    exact hsourceOne.trans (by simpa only [T] using htarget.symm)
  · have hiBase : Int.ModEq 2 (i.val : Int) (base : Int) :=
      modEq_two_of_even_nat_sub base i.val (by simpa only [base] using hright)
        (by simpa only [base] using heven)
    have hbaseSelf : Int.ModEq 2 (base : Int) (base : Int) :=
      Int.ModEq.refl _
    have hsumRaw := hiBase.add hbaseSelf
    have hbaseDouble : Int.ModEq 2
        ((base : Int) + (base : Int)) 0 := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-(base : Int), by ring⟩
    have hsum : Int.ModEq 2
        ((i.val : Int) + (base : Int)) 0 :=
      hsumRaw.trans hbaseDouble
    have hproductSelf : Int.ModEq 2
        ((i.val : Int) * T) ((i.val : Int) * T) := Int.ModEq.refl _
    have hbridgeRaw := hproductSelf.add hsum
    have hbridge : Int.ModEq 2 ((i.val : Int) * T)
        ((i.val : Int) * (T + 1) + (base : Int)) := by
      symm
      convert hbridgeRaw using 1 <;> ring
    have htarget := P.target_after i.val (by omega) (by omega)
    exact hsourceOne.trans (hbridge.trans (by
      simpa only [T, base] using htarget.symm))

/-- In nonoverlapping type III, the source and target prefixes in the
case-6 parity class have opposite order parity. -/
theorem beli2019Lemma79_typeIII_caseSix_prefix_opposite
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    Int.ModEq 2 (a.orderSequence.prefixSum i.val + 1)
      (b.orderSequence.prefixSum i.val) := by
  let left := D.outer.transition.lastZero
  let base := D.outer.transition.firstTwo - 1
  let R := a.orderSequence.entryOrZero left
  let S := b.orderSequence.entryOrZero base
  let P := a.beli2019Lemma72_iii_of_defect
    (alphaV := alpha) (alphaW := alpha)
    b D hfirst hdefect hnotOverlap
  let C := a.lemma611TypeIII_of_defect
    (alphaV := alpha) (alphaW := alpha)
    b D hfirst hdefect hnotOverlap
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = D.outer.transition.lastZero
    · have hzero : left = 0 := by
        simpa only [left, hfirst] using heq.symm
      rw [hzero]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < D.outer.transition.lastZero :=
        lt_of_le_of_ne D.outer.first_le_left heq
      have hp := (D.outer.leftProfile hlt).1
      simpa only [left, hfirst, Nat.sub_zero] using hp
  rcases hleftEven with ⟨p, hp⟩
  rcases heven with ⟨d, hd⟩
  have hbaseEq : base = left + 1 := by
    simp only [base, left]
    rw [D.adjacent]
    omega
  have hiEqNat : i.val = 2 * (p + d) + 1 := by
    omega
  have hiEqInt : (i.val : Int) = 2 * ((p : Int) + (d : Int)) + 1 := by
    exact_mod_cast hiEqNat
  rcases C.central_gap_even with ⟨g, hg⟩
  have hrightBoundary := D.outer.transition.rightBoundary
  have hreference : S = R + 2 * g + 1 := by
    dsimp only [S, R, base, left]
    omega
  have hbridge : Int.ModEq 2 ((i.val : Int) * R + 1)
      ((i.val : Int) * S) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(i.val : Int) * g + (p : Int) + (d : Int), ?_⟩
    rw [hiEqInt, hreference]
    ring
  have hsource := P.source i.val (by omega)
  have htarget := P.target i.val (by omega)
  have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
  have hsourceOne : Int.ModEq 2
      (a.orderSequence.prefixSum i.val + 1)
      ((i.val : Int) * R + 1) := by
    simpa only [R] using hsource.add hone
  exact hsourceOne.trans (hbridge.trans (by
    simpa only [S] using htarget.symm))

/-- The target cap `beta_i` is one on the type-II parity class of case 6,
including the coordinate immediately before the right transition. -/
theorem beli2019Lemma79_typeII_caseSix_beta_eq_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.alphaValue ⟨i.val - 1, by omega⟩ = 1 := by
  by_cases hboundary : i.val = D.outer.transition.firstTwo - 1
  · have hvalue :=
      a.beli2019Lemma69_i_typeII_targetBoundary_eq_one b D
    have hindex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
        ⟨D.outer.transition.firstTwo - 2, by
          have hbound := D.outer.transition.firstTwo_le_rank
          have hlong := D.long
          omega⟩ := by
      apply Fin.ext
      change i.val - 1 = D.outer.transition.firstTwo - 2
      omega
    rw [hindex]
    exact hvalue
  · rcases heven with ⟨d, hd⟩
    have hdPositive : 0 < d := by omega
    have hiInterior : D.outer.transition.firstTwo ≤ i.val - 1 := by
      omega
    have hoddPrevious : Odd
        ((i.val - 1) - (D.outer.transition.firstTwo - 1)) :=
      ⟨d - 1, by omega⟩
    have hvalue := beli2019Remark613_typeII_targetRightAlpha_eq_one
      a b D hlast horder hdefect htotal (i.val - 1) hiInterior
        (by omega) hoddPrevious
    exact hvalue

/-- The target cap `beta_i` is one on the type-III parity class of case 6,
including its central boundary coordinate. -/
theorem beli2019Lemma79_typeIII_caseSix_beta_eq_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.alphaValue ⟨i.val - 1, by omega⟩ = 1 := by
  by_cases hboundary : i.val = D.outer.transition.firstTwo - 1
  · have hdata := a.beli2019Lemma78_alphas_and_gap
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
    have hindex : i.val - 1 = D.outer.transition.lastZero := by
      rw [hboundary, D.adjacent]
      omega
    simpa only [hindex] using hdata.2.1
  · rcases heven with ⟨d, hd⟩
    have hdPositive : 0 < d := by omega
    have hiInterior : D.outer.transition.firstTwo ≤ i.val - 1 := by
      omega
    have hoddPrevious : Odd
        ((i.val - 1) - (D.outer.transition.firstTwo - 1)) :=
      ⟨d - 1, by omega⟩
    have hvalue := beli2019Remark613_typeIII_targetRightAlpha_eq_one
      a b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        (i.val - 1) hiInterior (by omega) hoddPrevious
    exact hvalue

end BONG.GoodBONG

end Bong
