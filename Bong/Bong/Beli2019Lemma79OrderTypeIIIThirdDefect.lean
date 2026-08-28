/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIComplete
import Bong.Bong.Beli2019Lemma78TargetPropagation

/-!
# Beli (2019), Lemma 7.9(i): the third prefix in type III

In the hard type-III parity class, every alternating adjacent pair of the
third BONG has capped defect strictly above the central mixed shift.  Joining
those pairs by domination gives the strict prefix bound used in part 6 of
the paper's proof.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The self-prefix defect of the third BONG is strictly larger than the
central mixed shift throughout the hard type-III parity class. -/
theorem lemma79_typeIII_thirdPrefix_gt_mixedShift
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
    (k : Nat) (hk : k < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k) :
    ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
        a.orderSequence.entryOrZero
          (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ) <
      c.truncatedPrefixDefect c ((-1) ^ ((k + 1) / 2)) 0 (k + 1) := by
  let left := D.outer.transition.lastZero
  let center : Fin (n + 1) := ⟨left, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let C : Int := b.orderSequence.entryOrZero left -
    a.orderSequence.entryOrZero (left + 1)
  have halpha := a.beli2019Lemma69_i_typeIII
    (alphaV := alpha) (alphaW := alpha) b D hfirst hdefect
  have hgapLe : a.orderGap center ≤ 1 := by
    apply a.orderGap_le_one_of_alphaValue_le_one center
    simpa only [center, left] using halpha
  have hgapNe : a.orderGap center ≠ 1 := by
    simpa only [center, left] using hnotOverlap
  have hgapNonpositive : a.orderGap center ≤ 0 := by omega
  have hgapEven : Even (a.orderGap center) := by
    simpa only [center, left] using
      a.lemma78_typeIII_centralGap_even b D hfirst hdefect hnotOverlap
  have hleftBound : left < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hrightBound : left + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hgapEntries : a.orderGap center =
      a.orderSequence.entryOrZero (left + 1) -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
    rfl
  have hleftBoundary : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using D.outer.transition.leftBoundary
  have hCFormula : C = 1 - a.orderGap center := by
    dsimp only [C]
    rw [hleftBoundary, hgapEntries]
    ring
  have hCPos : 0 < C := by
    rw [hCFormula]
    omega
  have hCOdd : Odd C := by
    rw [hCFormula]
    exact odd_one.sub_even hgapEven
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst left le_rfl hleftEven
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : b.orderSequence.entryOrZero left ≤
      c.orderSequence.entryOrZero 0 := by
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
    rw [hleftBoundary, hsourceLeft]
    exact hfirstOrder
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    simp only [left]
    rw [D.adjacent]
    omega
  have hbCurrentBoundary := D.outer.target_rightEven_eq_boundary
    k hright hlast heven
  have hbCurrent : b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero (left + 1) + 1 := by
    rw [hbCurrentBoundary, D.outer.transition.rightBoundary, hrightIndex]
  have hcLastUpper : c.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero (left + 1) := by
    rw [hbCurrent] at hcurrent
    omega
  have hrightOdd : Odd (D.outer.transition.firstTwo - 1) := by
    rcases hleftEven with ⟨d, hd⟩
    rw [hrightIndex]
    exact ⟨d, by omega⟩
  have hkOdd : Odd k := by
    rcases hrightOdd with ⟨d, hd⟩
    rcases heven with ⟨e, he⟩
    exact ⟨d + e, by omega⟩
  rcases hkOdd with ⟨d, hd⟩
  have hjoined := c.truncatedPrefixDefect_alternating_ge
    0 d (by omega) (((C : ℚ) : WithTop ℚ) + 1) (by
      intro t ht
      let gap : Fin (n + 1) := ⟨2 * t, by omega⟩
      have hcurrentEven : Even (2 * t) := ⟨t, by omega⟩
      have hnextParity : Even (k - (2 * t + 1)) :=
        ⟨d - t, by omega⟩
      have hcEvenLower := c.orderSequence.entryOrZero_le_of_evenGap
        0 (2 * t) (Nat.zero_le _) (by omega) hcurrentEven
      have hcOddUpper := c.orderSequence.entryOrZero_le_of_evenGap
        (2 * t + 1) k (by omega) hk hnextParity
      have hdiffLower : C ≤
          c.orderSequence.entryOrZero (2 * t) -
            c.orderSequence.entryOrZero (2 * t + 1) := by
        dsimp only [C]
        omega
      have hdiffStrict : C <
          c.orderSequence.entryOrZero (2 * t) -
            c.orderSequence.entryOrZero (2 * t + 1) := by
        apply lt_of_le_of_ne hdiffLower
        intro heq
        have hgapFormula : c.orderGap gap = -C := by
          unfold orderGap
          rw [← c.orderSequence_entryOrZero_eq_order gap.succ,
            ← c.orderSequence_entryOrZero_eq_order gap.castSucc]
          simp only [gap, Fin.val_succ, Fin.val_castSucc]
          omega
        have hnegative : c.orderGap gap < 0 := by
          rw [hgapFormula]
          omega
        have hgapEven' := c.orderGap_even_of_negative gap hnegative
        have hgapOdd' : Odd (c.orderGap gap) := by
          rw [hgapFormula]
          rcases hCOdd with ⟨e, heC⟩
          exact ⟨-e - 1, by omega⟩
        exact (Int.not_even_iff_odd.mpr hgapOdd') hgapEven'
      have hdiffOrders : C <
          c.order gap.castSucc - c.order gap.succ := by
        rw [← c.orderSequence_entryOrZero_eq_order gap.castSucc,
          ← c.orderSequence_entryOrZero_eq_order gap.succ]
        simpa only [gap, Fin.val_castSucc, Fin.val_succ] using hdiffStrict
      have halphaNonnegative := (c.alpha_p2 gap).1
      have hcoefficient : (C : ℚ) + 1 ≤
          ((c.order gap.castSucc - c.order gap.succ : Int) : ℚ) +
            c.alphaValue gap := by
        have hdiffRational : (C : ℚ) <
            ((c.order gap.castSucc - c.order gap.succ : Int) : ℚ) := by
          exact_mod_cast hdiffOrders
        have hdiffStep : (C : ℚ) + 1 ≤
            ((c.order gap.castSucc - c.order gap.succ : Int) : ℚ) := by
          exact_mod_cast hdiffOrders
        linarith
      have hcoefficientTop : (((C : ℚ) : WithTop ℚ) + 1) ≤
          (((((c.order gap.castSucc - c.order gap.succ : Int) : ℚ) +
            c.alphaValue gap : ℚ)) : WithTop ℚ) := by
        exact_mod_cast hcoefficient
      exact hcoefficientTop.trans (by
        simpa only [gap, Nat.zero_add] using
          c.order_sub_add_alpha_le_cappedAdjacent gap))
  have hexponent : d + 1 = (k + 1) / 2 := by omega
  have hend : 2 * (d + 1) = k + 1 := by omega
  rw [Nat.zero_add, hend, hexponent] at hjoined
  change (((C : ℚ) : WithTop ℚ)) < _
  apply lt_of_lt_of_le _ hjoined
  norm_cast
  norm_num

end BONG.GoodBONG

end Bong
