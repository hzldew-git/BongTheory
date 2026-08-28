/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderConditionDual
import Bong.Bong.Beli2019Lemma78Arithmetic

/-!
# Beli (2019), Lemma 7.8: the reverse-dual type-III branch

For a type-III pair, the complementary prefix-gap transition is again
type III after reverse-dualizing and swapping the lattices.  The proof
constructs the complementary transition explicitly, so its center remains
available when Lemma 6.9(i) is transferred back to the target lattice.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- A type-III pair remains type III after reverse-dualizing and swapping.
The first unequal order of the dual pair is the reflection of the last
unequal order of the original pair. -/
theorem exists_reverseDual_typeIII_local
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1)) :
    ∃ (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
      (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
      (Ddual : Lemma67TypeIII bDual aDual),
      (∀ j, aDual.order j = -a.order (Fin.rev j)) ∧
      (∀ j, bDual.order j = -b.order (Fin.rev j)) ∧
      (∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j)) ∧
      (∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j)) ∧
      (∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 → ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p)) ∧
      bDual.RepresentationDefectCondition aDual ∧
      Ddual.outer.first = n - D.outer.last ∧
      Ddual.outer.transition.lastZero =
        n + 1 - D.outer.transition.firstTwo ∧
      Ddual.outer.transition.firstTwo =
        n + 1 - D.outer.transition.lastZero := by
  rcases a.exists_reverseDualPair_with_representationDefectCondition
      b hdefect with
    ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha,
      hDefectDual, hconditionDual⟩
  have horderDual := a.representationOrderCondition_reverseDual_swap
    b aDual bDual haOrders hbOrders horder
  have htotalDual := a.totalOrderSum_reverseDual_swap
    b aDual bDual haOrders hbOrders htotal
  have hleDual :=
    (bDual.representationOrderCondition_iff aDual le_rfl).mp horderDual
  let leftDual := n + 1 - D.outer.transition.firstTwo
  let firstDual := n + 1 - D.outer.transition.lastZero
  have hfirstBound := D.outer.transition.firstTwo_le_rank
  have hleftLtFirst : leftDual < firstDual := by
    dsimp only [leftDual, firstDual]
    have hlt := D.outer.transition.lastZero_lt_firstTwo
    omega
  have hfirstDualBound : firstDual ≤ n + 1 :=
    Nat.sub_le _ _
  have hleftGap : bDual.orderSequence.prefixGap
      aDual.orderSequence leftDual = 0 := by
    have htransport := a.orderPrefixGap_reverseDual_swap
      b aDual bDual haOrders hbOrders htotal leftDual (Nat.sub_le _ _)
    have hcomplement : n + 1 - leftDual =
        D.outer.transition.firstTwo := by
      dsimp only [leftDual]
      omega
    rw [hcomplement, D.outer.transition.gap_firstTwo] at htransport
    omega
  have hfirstGap : bDual.orderSequence.prefixGap
      aDual.orderSequence firstDual = 2 := by
    have htransport := a.orderPrefixGap_reverseDual_swap
      b aDual bDual haOrders hbOrders htotal firstDual
        hfirstDualBound
    have hcomplement : n + 1 - firstDual =
        D.outer.transition.lastZero := by
      dsimp only [firstDual]
      have hlt := D.outer.transition.lastZero_lt_firstTwo
      omega
    rw [hcomplement, D.outer.transition.gap_lastZero] at htransport
    omega
  have hbetween (k : Nat) (hleft : leftDual < k)
      (hfirst : k < firstDual) :
      bDual.orderSequence.prefixGap aDual.orderSequence k = 1 := by
    have htransport := a.orderPrefixGap_reverseDual_swap
      b aDual bDual haOrders hbOrders htotal k (by omega)
    have hcomplementLeft : D.outer.transition.lastZero < n + 1 - k := by
      dsimp only [leftDual, firstDual] at hleft hfirst
      omega
    have hcomplementRight : n + 1 - k <
        D.outer.transition.firstTwo := by
      dsimp only [leftDual, firstDual] at hleft hfirst
      omega
    rw [D.outer.transition.gap_between (n + 1 - k)
      hcomplementLeft hcomplementRight] at htransport
    omega
  have hseparated : leftDual + 1 < firstDual := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    dsimp only [leftDual, firstDual]
    rw [D.adjacent]
    omega
  have hleftBoundary : aDual.orderSequence.entryOrZero leftDual =
      bDual.orderSequence.entryOrZero leftDual + 1 := by
    have hstep := bDual.orderSequence.prefixGap_succ
      aDual.orderSequence leftDual
    have hnext := hbetween (leftDual + 1) (by omega) hseparated
    rw [hnext, hleftGap] at hstep
    omega
  have hrightBoundary :
      aDual.orderSequence.entryOrZero (firstDual - 1) =
        bDual.orderSequence.entryOrZero (firstDual - 1) + 1 := by
    have hprevious : bDual.orderSequence.prefixGap
        aDual.orderSequence (firstDual - 1) = 1 := by
      apply hbetween (firstDual - 1)
      · omega
      · omega
    have hstep := bDual.orderSequence.prefixGap_succ
      aDual.orderSequence (firstDual - 1)
    have hindex : firstDual - 1 + 1 = firstDual := by omega
    rw [hindex, hfirstGap, hprevious] at hstep
    omega
  let Tdual : BeliOrderLE.PrefixGapTransitionConsequences
      bDual.orderSequence aDual.orderSequence := {
    lastZero := leftDual
    firstTwo := firstDual
    firstTwo_le_rank := hfirstDualBound
    lastZero_lt_firstTwo := hleftLtFirst
    gap_lastZero := hleftGap
    gap_firstTwo := hfirstGap
    gap_between := hbetween
    separated := hseparated
    leftBoundary := hleftBoundary
    rightBoundary := hrightBoundary
    middle := by
      intro k hleft hfirst
      exfalso
      dsimp only [leftDual, firstDual] at hleft hfirst
      rw [D.adjacent] at hleft
      omega }
  rcases hleDual.exists_noGapTwoOuterConsequences_of_transition
      htotalDual Tdual with ⟨Odual, htransition⟩
  have hnoTwoDual (k : Nat) (hk : k < n + 1) :
      aDual.orderSequence.entryOrZero k <
        bDual.orderSequence.entryOrZero k + 2 := by
    rw [BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence hk,
      BeliOrderSequence.entryOrZero_of_lt bDual.orderSequence hk]
    have horiginal := D.no_gap_two (Fin.rev (⟨k, hk⟩ : Fin (n + 1))).val
      (Fin.rev (⟨k, hk⟩ : Fin (n + 1))).isLt
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (Fin.rev (⟨k, hk⟩ : Fin (n + 1))).isLt,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (Fin.rev (⟨k, hk⟩ : Fin (n + 1))).isLt] at horiginal
    change b.order (Fin.rev ⟨k, hk⟩) <
      a.order (Fin.rev ⟨k, hk⟩) + 2 at horiginal
    change aDual.order ⟨k, hk⟩ < bDual.order ⟨k, hk⟩ + 2
    rw [haOrders, hbOrders]
    omega
  let Ddual : Lemma67TypeIII bDual aDual := {
    outer := Odual
    no_gap_two := hnoTwoDual
    adjacent := by
      rw [htransition]
      dsimp only [Tdual]
      dsimp only [leftDual, firstDual]
      rw [D.adjacent]
      omega }
  have hdualFirst : Ddual.outer.first = n - D.outer.last := by
    let reflectedLast := n - D.outer.last
    have hlastBound := D.outer.lastDifference.bound
    have hreflectedBound : reflectedLast < n + 1 := by
      simp only [reflectedLast]
      omega
    let reflected : Fin (n + 1) := ⟨reflectedLast, hreflectedBound⟩
    let originalLast : Fin (n + 1) := ⟨D.outer.last, hlastBound⟩
    have hreverseReflected : Fin.rev reflected = originalLast := by
      apply Fin.ext
      simp only [reflected, reflectedLast, originalLast, Fin.rev]
      omega
    have hreflectedNe :
        bDual.orderSequence.entryOrZero reflectedLast ≠
          aDual.orderSequence.entryOrZero reflectedLast := by
      rw [BeliOrderSequence.entryOrZero_of_lt bDual.orderSequence
          hreflectedBound,
        BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence
          hreflectedBound]
      change bDual.order reflected ≠ aDual.order reflected
      rw [hbOrders reflected, haOrders reflected, hreverseReflected]
      intro heq
      apply D.outer.lastDifference.ne
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hlastBound,
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence hlastBound]
      change a.order originalLast = b.order originalLast
      exact neg_injective heq.symm
    have hfirstLe : Ddual.outer.first ≤ reflectedLast := by
      by_contra hnot
      have hreflectedBefore : reflectedLast < Ddual.outer.first := by omega
      exact hreflectedNe
        (Ddual.outer.firstDifference.before reflectedLast hreflectedBefore)
    have hreflectedLe : reflectedLast ≤ Ddual.outer.first := by
      by_contra hnot
      have hfirstBefore : Ddual.outer.first < reflectedLast := by omega
      have hfirstBound := Ddual.outer.firstDifference.bound
      let dualFirst : Fin (n + 1) :=
        ⟨Ddual.outer.first, hfirstBound⟩
      have horiginalAfter : D.outer.last < (Fin.rev dualFirst).val := by
        simp only [dualFirst, Fin.rev, reflectedLast] at hfirstBefore ⊢
        omega
      have horiginalEq := D.outer.lastDifference.after
        (Fin.rev dualFirst).val horiginalAfter (Fin.rev dualFirst).isLt
      have hdualEq :
          bDual.orderSequence.entryOrZero Ddual.outer.first =
            aDual.orderSequence.entryOrZero Ddual.outer.first := by
        rw [BeliOrderSequence.entryOrZero_of_lt bDual.orderSequence
            hfirstBound,
          BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence
            hfirstBound]
        change bDual.order dualFirst = aDual.order dualFirst
        rw [hbOrders dualFirst, haOrders dualFirst]
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (Fin.rev dualFirst).isLt,
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (Fin.rev dualFirst).isLt] at horiginalEq
        change a.order (Fin.rev dualFirst) =
          b.order (Fin.rev dualFirst) at horiginalEq
        rw [horiginalEq]
      exact Ddual.outer.firstDifference.ne hdualEq
    exact le_antisymm hfirstLe hreflectedLe
  have hdualLeft : Ddual.outer.transition.lastZero = leftDual := by
    change Odual.transition.lastZero = leftDual
    rw [htransition]
  have hdualRight : Ddual.outer.transition.firstTwo = firstDual := by
    change Odual.transition.firstTwo = firstDual
    rw [htransition]
  exact ⟨aDual, bDual, Ddual, haOrders, hbOrders, haAlpha, hbAlpha,
    hDefectDual, hconditionDual, hdualFirst, by
      simpa only [leftDual] using hdualLeft, by
      simpa only [firstDual] using hdualRight⟩

/-- Compatibility wrapper for the normalized Section 7 case `u = n`. -/
theorem exists_reverseDual_typeIII
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (hlast : D.outer.last = n) :
    ∃ (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
      (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
      (Ddual : Lemma67TypeIII bDual aDual),
      (∀ j, aDual.order j = -a.order (Fin.rev j)) ∧
      (∀ j, bDual.order j = -b.order (Fin.rev j)) ∧
      (∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j)) ∧
      (∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j)) ∧
      (∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 → ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p)) ∧
      bDual.RepresentationDefectCondition aDual ∧
      Ddual.outer.first = 0 ∧
      Ddual.outer.transition.lastZero =
        n + 1 - D.outer.transition.firstTwo ∧
      Ddual.outer.transition.firstTwo =
        n + 1 - D.outer.transition.lastZero := by
  rcases a.exists_reverseDual_typeIII_local b D horder hdefect htotal with
    ⟨aDual, bDual, Ddual, haOrders, hbOrders, haAlpha, hbAlpha,
      hDefectDual, hconditionDual, hdualFirst, hdualLeft, hdualRight⟩
  have hdualFirstZero : Ddual.outer.first = 0 := by
    rw [hdualFirst, hlast]
    omega
  exact ⟨aDual, bDual, Ddual, haOrders, hbOrders, haAlpha, hbAlpha,
    hDefectDual, hconditionDual, hdualFirstZero, hdualLeft, hdualRight⟩

/-- The source and target central order gaps of a type-III pair agree. -/
theorem lemma78_typeIII_targetGap_eq_sourceGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b) :
    b.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ =
      a.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ := by
  let left := D.outer.transition.lastZero
  have hleftBound : left < n + 1 := by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hrightBound : left + 1 < n + 1 := by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hleftOrder : b.order ⟨left, hleftBound⟩ =
      a.order ⟨left, hleftBound⟩ + 1 := by
    have hboundary := D.outer.transition.leftBoundary
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hleftBound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
      at hboundary
    exact hboundary
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    dsimp only [left]
    rw [D.adjacent]
    omega
  have hrightOrder : b.order ⟨left + 1, hrightBound⟩ =
      a.order ⟨left + 1, hrightBound⟩ + 1 := by
    have hboundary := D.outer.transition.rightBoundary
    rw [hrightIndex] at hboundary
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hrightBound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound]
      at hboundary
    exact hboundary
  unfold orderGap
  change b.order ⟨left + 1, hrightBound⟩ -
      b.order ⟨left, hleftBound⟩ =
    a.order ⟨left + 1, hrightBound⟩ -
      a.order ⟨left, hleftBound⟩
  rw [hleftOrder, hrightOrder]
  omega

/-- Lemma 6.9(i) at the target type-III boundary, obtained from the
explicit swapped reverse-dual type-III pair. -/
theorem beli2019Lemma69_i_typeIII_target
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (hlast : D.outer.last = n) :
    b.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≤ 1 := by
  rcases a.exists_reverseDual_typeIII b D horder hdefect htotal hlast with
    ⟨aDual, bDual, Ddual, _, _, _, hbAlpha, _, hconditionDual,
      hdualFirst, hdualLeft, _⟩
  let dualCenter : Fin n := ⟨Ddual.outer.transition.lastZero, by
    have hbound := Ddual.outer.transition.firstTwo_le_rank
    rw [Ddual.adjacent] at hbound
    omega⟩
  let center : Fin n := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have hdualAlpha : bDual.alphaValue dualCenter ≤ 1 := by
    simpa only [dualCenter] using
      bDual.beli2019Lemma69_i_typeIII
        (alphaV := alpha) (alphaW := alpha)
        aDual Ddual hdualFirst hconditionDual
  have hreverse : Fin.rev dualCenter = center := by
    apply Fin.ext
    simp only [dualCenter, center, Fin.rev]
    rw [hdualLeft, D.adjacent]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hmap := hbAlpha dualCenter
  rw [hreverse] at hmap
  rw [← hmap]
  simpa only [center] using hdualAlpha

/-- Lemma 7.8's two central alpha equalities and numerical gap bound. -/
theorem beli2019Lemma78_alphas_and_gap
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
    a.alphaValue ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1 ∧
      b.alphaValue ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1 ∧
      3 - 2 * (ramificationIndex K : Int) ≤
        a.orderGap ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ + 1 := by
  let center : Fin n := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have hsource := a.beli2019Lemma78_sourceAlpha_and_gap
    (alphaV := alpha) (alphaW := alpha)
    b D hfirst hdefect hnotOverlap hinitial
  have htargetLe : b.alphaValue center ≤ 1 := by
    simpa only [center] using a.beli2019Lemma69_i_typeIII_target
      b D horder hdefect htotal hlast
  have hgapEq : b.orderGap center = a.orderGap center := by
    simpa only [center] using a.lemma78_typeIII_targetGap_eq_sourceGap b D
  have hsourceEven : Even (a.orderGap center) := by
    simpa only [center] using a.lemma78_typeIII_centralGap_even
      (alphaV := alpha) (alphaW := alpha)
      b D hfirst hdefect hnotOverlap
  have htargetEven : Even (b.orderGap center) := by
    rw [hgapEq]
    exact hsourceEven
  have hsourceGapBound :
      3 - 2 * (ramificationIndex K : Int) ≤
        a.orderGap center + 1 := by
    simpa only [center] using hsource.2
  have htargetGapGt : -(2 * (ramificationIndex K : Int)) <
      b.orderGap center := by
    rw [hgapEq]
    omega
  have htargetNe : b.alphaValue center ≠ 0 := by
    intro hzero
    have hgapZero := (b.alpha_p2 center).2.mp hzero
    omega
  have htargetIntegral : IsRationalInteger (b.alphaValue center) := by
    apply b.beli2009Corollary28_i center
    rintro ⟨hodd, _⟩
    exact (Int.not_odd_iff_even.mpr htargetEven) hodd
  have htargetEq : b.alphaValue center = 1 := by
    rcases htargetIntegral with ⟨z, hz⟩
    have hzNonnegative : (0 : Int) ≤ z := by
      exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
        simpa only [← hz] using (b.alpha_p2 center).1)
    have hzLe : z ≤ (1 : Int) := by
      exact_mod_cast (show (z : ℚ) ≤ 1 by
        simpa only [← hz] using htargetLe)
    have hzNe : z ≠ 0 := by
      intro hzZero
      apply htargetNe
      rw [hz, hzZero]
      norm_num
    have hzOne : z = 1 := by omega
    rw [hz, hzOne]
    norm_num
  exact ⟨by simpa only [center] using hsource.1,
    by simpa only [center] using htargetEq,
    by simpa only [center] using hsourceGapBound⟩

end BONG.GoodBONG

end Bong
