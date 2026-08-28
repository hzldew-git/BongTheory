/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIIHalfGap

/-!
# Beli (2019), Lemma 7.9(i): the type-III primary candidate

If the primary defect candidate is at most the central mixed shift, its
nonnegative defect term forces equality in both bounding order inequalities.
The preceding third-lattice entry must then be strictly above its lower
bound: equality would create a negative odd good-BONG gap.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The type-III mixed shift is a positive odd integer in the
nonoverlapping branch. -/
theorem lemma79_typeIII_mixedShift_pos_and_odd
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
    0 < b.orderSequence.entryOrZero D.outer.transition.lastZero -
        a.orderSequence.entryOrZero
          (D.outer.transition.lastZero + 1) ∧
      Odd (b.orderSequence.entryOrZero D.outer.transition.lastZero -
        a.orderSequence.entryOrZero
          (D.outer.transition.lastZero + 1)) := by
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
  simpa only [C, left] using And.intro hCPos hCOdd

/-- If the primary candidate is at most the mixed shift, the adjacent-pair
alternative in condition (i) holds. -/
theorem lemma79_typeIII_pair_of_primary_le_mixedShift
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
    (k : Nat) (_hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k)
    (hprimary : a.representationPrimaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ)) :
    b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) ≤
      c.orderSequence.entryOrZero (k - 1) +
        c.orderSequence.entryOrZero k := by
  let left := D.outer.transition.lastZero
  let C : Int := b.orderSequence.entryOrZero left -
    a.orderSequence.entryOrZero (left + 1)
  let idx : RepresentationIndex (n + 2) (n + 2) := {
    val := k + 1
    pos := by omega
    lt_large := hkNext
    le_small := hkNext.le }
  change a.representationPrimaryDefect c idx ≤
    (((C : ℚ)) : WithTop ℚ) at hprimary
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    simp only [left]
    rw [D.adjacent]
    omega
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    k hright hlast heven
  have hrightBoundary := D.outer.transition.rightBoundary
  have hcurrentUpper : c.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero (left + 1) := by
    rw [hcurrentBoundary, hrightBoundary, hrightIndex] at hcurrent
    omega
  have hsourceNext := a.lemma79_typeIII_leftTarget_le_sourceNext
    b D k hkNext hright hlast heven
  have hdiffLower : C ≤ a.orderSequence.entryOrZero (k + 1) -
      c.orderSequence.entryOrZero k := by
    dsimp only [C, left] at hcurrentUpper hsourceNext ⊢
    omega
  have hdefectNonnegative := a.truncatedPrefixDefect_nonneg
    (alphaV := alpha) (alphaW := alpha)
    c (-1) (idx.val + 1) (idx.val - 1)
  have hcoefficientTop :
      (((a.order ⟨idx.val, idx.lt_large⟩ -
        c.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) ≤ (((C : ℚ)) : WithTop ℚ) := by
    calc
      (((a.order ⟨idx.val, idx.lt_large⟩ -
        c.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) ≤
          (((a.order ⟨idx.val, idx.lt_large⟩ -
            c.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.truncatedPrefixDefect c (-1)
              (idx.val + 1) (idx.val - 1) :=
        le_add_of_nonneg_right hdefectNonnegative
      _ = a.representationPrimaryDefect c idx := by rfl
      _ ≤ (((C : ℚ)) : WithTop ℚ) := hprimary
  norm_cast at hcoefficientTop
  have hcoefficient :
      a.order ⟨idx.val, idx.lt_large⟩ -
        c.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ ≤ C := by
    exact_mod_cast hcoefficientTop
  have haIdx : a.order ⟨idx.val, idx.lt_large⟩ =
      a.orderSequence.entryOrZero (k + 1) := by
    simpa only [idx] using
      (a.orderSequence_entryOrZero_eq_order
        ⟨idx.val, idx.lt_large⟩).symm
  have hcIdx : c.order ⟨idx.val - 1, by
        have := idx.le_small
        omega⟩ = c.orderSequence.entryOrZero k := by
    simpa only [idx, Nat.add_sub_cancel] using
      (c.orderSequence_entryOrZero_eq_order
        ⟨idx.val - 1, by have := idx.le_small; omega⟩).symm
  rw [haIdx, hcIdx] at hcoefficient
  have hdiffEq : a.orderSequence.entryOrZero (k + 1) -
      c.orderSequence.entryOrZero k = C := by omega
  have hsourceNextEq : a.orderSequence.entryOrZero (k + 1) =
      b.orderSequence.entryOrZero left := by
    dsimp only [C, left] at hdiffEq hsourceNext hcurrentUpper ⊢
    omega
  have hcurrentEq : c.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero (left + 1) := by
    calc
      c.orderSequence.entryOrZero k =
          a.orderSequence.entryOrZero (k + 1) - C := by omega
      _ = b.orderSequence.entryOrZero left - C := by
        rw [hsourceNextEq]
      _ = a.orderSequence.entryOrZero (left + 1) := by
        dsimp only [C]
        omega
  have htargetNextLe := a.lemma79_typeIII_targetNext_le_sourceNext
    b D k hkNext hright hlast heven
  rcases heven with ⟨d, hd⟩
  have hleftNextEven : Even (k + 1 - left) := ⟨d + 1, by omega⟩
  have htargetNextLower := b.orderSequence.entryOrZero_le_of_evenGap
    left (k + 1) (by omega) hkNext hleftNextEven
  have htargetNextEq : b.orderSequence.entryOrZero (k + 1) =
      b.orderSequence.entryOrZero left := by omega
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
    have hleftBoundary := D.outer.transition.leftBoundary
    rw [hleftBoundary, hsourceLeft]
    exact hfirstOrder
  have hrightOdd : Odd (D.outer.transition.firstTwo - 1) := by
    rcases hleftEven with ⟨e, he⟩
    rw [hrightIndex]
    exact ⟨e, by omega⟩
  have hkOdd : Odd k := by
    rcases hrightOdd with ⟨e, he⟩
    exact ⟨e + d, by omega⟩
  have hkPos : 0 < k := by
    rcases hkOdd with ⟨e, he⟩
    omega
  have hprevEven : Even (k - 1) := by
    rcases hkOdd with ⟨e, he⟩
    exact ⟨e, by omega⟩
  have hprevFromFirst := c.orderSequence.entryOrZero_le_of_evenGap
    0 (k - 1) (Nat.zero_le _) (by omega) hprevEven
  have hprevLower : b.orderSequence.entryOrZero left ≤
      c.orderSequence.entryOrZero (k - 1) :=
    hfirstLower.trans hprevFromFirst
  have hshift := a.lemma79_typeIII_mixedShift_pos_and_odd
    b D hfirst hdefect hnotOverlap
  have hCPos : 0 < C := by simpa only [C, left] using hshift.1
  have hCOdd : Odd C := by simpa only [C, left] using hshift.2
  have hprevStrict : b.orderSequence.entryOrZero left <
      c.orderSequence.entryOrZero (k - 1) := by
    apply lt_of_le_of_ne hprevLower
    intro heq
    let gap : Fin (n + 1) := ⟨k - 1, by omega⟩
    have hgapFormula : c.orderGap gap =
        c.orderSequence.entryOrZero k -
          c.orderSequence.entryOrZero (k - 1) := by
      unfold orderGap
      rw [← c.orderSequence_entryOrZero_eq_order gap.succ,
        ← c.orderSequence_entryOrZero_eq_order gap.castSucc]
      simp only [gap, Fin.val_succ, Fin.val_castSucc]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hgapEq : c.orderGap gap = -C := by
      rw [hgapFormula, hcurrentEq, ← heq]
      dsimp only [C]
      omega
    have hnegative : c.orderGap gap < 0 := by
      rw [hgapEq]
      omega
    have hgapEven := c.orderGap_even_of_negative gap hnegative
    have hgapOdd : Odd (c.orderGap gap) := by
      rw [hgapEq]
      rcases hCOdd with ⟨e, he⟩
      exact ⟨-e - 1, by omega⟩
    exact (Int.not_even_iff_odd.mpr hgapOdd) hgapEven
  have hcurrentTarget : b.orderSequence.entryOrZero k =
      c.orderSequence.entryOrZero k + 1 := by
    rw [hcurrentBoundary, hrightBoundary, hrightIndex, hcurrentEq]
  omega

end BONG.GoodBONG

end Bong
