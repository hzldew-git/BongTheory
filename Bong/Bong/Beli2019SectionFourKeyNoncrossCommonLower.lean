/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectMin
import Bong.Bong.Beli2019SectionFourKeyNoncrossPrimaryLower

/-!
# Beli (2019), Lemma 4.2: the noncrossed common lower bound

This file formalizes lines 2266--2274.  Lemma 1.4(b) replaces the
middle--target comparison defect under the three-term minimum.  Each of the
three resulting terms then dominates the common shifted value containing
`A_i`.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- Lines 2266--2274.  Under a strict failure of the desired source bound,
the source primary candidate dominates the common shifted `A_i` term. -/
theorem commonNextSourceAlpha_bounds_of_noncross_failure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩)
    (hfailure : ¬a.representationAlpha c j ≤
      a.representationAlpha b j) :
    (((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
        a.representationPrimaryDefect b j ∧
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        b.representationAlpha c j := by
  let next := nextRepresentationIndex j hi.2
  let y : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let commonShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sourceShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let da := a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let db := b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let dc := a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1)
  let beta : WithTop ℚ := b.alphaValue ⟨j.val, by omega⟩
  let qTerm : WithTop ℚ := (commonShift : WithTop ℚ) + beta
  let sourceTerm : WithTop ℚ :=
    (sourceShift : WithTop ℚ) + a.representationAlpha b next
  obtain ⟨_, hprimary⟩ := a.leftDirect_sourceFailure_eq_primary
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hnormalRaw :=
    a.shiftedMiddleAlpha_eq_min_primary_sourceAlpha_of_noncross
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab hbcOrder hbcDefect j hi hessential hdirect hnoncross
  have hnormal :
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          b.representationAlpha c j =
        min ((y : WithTop ℚ) + db) qTerm := by
    simpa only [y, commonShift, db, beta, qTerm] using hnormalRaw
  have hlowerRaw := a.min_shifted_middle_next_le_sourcePrimary
    (middleLaws := middleLaws) b c habDefect hbcDefect j hi
  have hlower :
      min
          ((((a.order ⟨j.val, j.lt_large⟩ -
            b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
            b.representationAlpha c j)
          sourceTerm ≤ a.representationPrimaryDefect b j := by
    simpa only [next, sourceShift, sourceTerm] using hlowerRaw
  have hthree :
      min ((y : WithTop ℚ) + db) (min qTerm sourceTerm) ≤
        a.representationPrimaryDefect b j := by
    calc
      min ((y : WithTop ℚ) + db) (min qTerm sourceTerm) =
          min (min ((y : WithTop ℚ) + db) qTerm) sourceTerm := by
        ac_rfl
      _ = min
          ((((a.order ⟨j.val, j.lt_large⟩ -
            b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
            b.representationAlpha c j)
          sourceTerm := by rw [← hnormal]
      _ ≤ a.representationPrimaryDefect b j := hlower
  have htargetCap : a.representationAlpha c j ≤
      (y : WithTop ℚ) + da := by
    simpa only [y, da, representationPrimaryDefect] using
      a.representationAlpha_le_primary c j
  have hbound : min ((y : WithTop ℚ) + db) (min qTerm sourceTerm) <
      (y : WithTop ℚ) + da :=
    (hthree.trans_lt hprimary).trans_le htargetCap
  have hforward : min da db ≤ dc := by
    have h := a.truncatedPrefixDefect_domination c b
      (-1) (-1) (j.val + 1) (j.val - 1) (j.val + 1)
    rw [← b.truncatedPrefixDefect_comm c (-1)
      (j.val + 1) (j.val - 1)] at h
    simpa only [da, db, dc, neg_mul_neg, one_mul] using h
  have hreverse : min da dc ≤ db := by
    have h := c.truncatedPrefixDefect_domination a b
      (-1) 1 (j.val - 1) (j.val + 1) (j.val + 1)
    rw [c.truncatedPrefixDefect_comm a (-1)
      (j.val - 1) (j.val + 1),
      c.truncatedPrefixDefect_comm b (-1 * 1)
        (j.val - 1) (j.val + 1)] at h
    simpa only [da, db, dc, neg_mul, one_mul] using h
  have hreplace :
      min ((y : WithTop ℚ) + db) (min qTerm sourceTerm) =
        min ((y : WithTop ℚ) + dc) (min qTerm sourceTerm) :=
    withTop_shifted_min_eq_of_lt_cut_of_domination y
      (min qTerm sourceTerm) da db dc hforward hreverse hbound
  have hnextCap : a.representationAlpha b next ≤ dc := by
    have hcondition := habDefect next
    rw [a.coe_representationAlphaValue b next] at hcondition
    simpa only [next, nextRepresentationIndex, dc] using hcondition
  have hbeta : a.representationAlpha b next ≤ beta := by
    have h := a.representationAlpha_le_rightAlpha b habDefect next
    simpa only [next, nextRepresentationIndex, beta, Nat.add_sub_cancel] using h
  have hpair :=
    b.middlePrevious_add_current_le_targetPreviousPair_of_noncross
      c hbcOrder j hi hnoncross
  have hcommonY : commonShift ≤ y := by
    dsimp only [commonShift, y]
    push_cast
    have hcast :
        (b.order ⟨j.val, j.lt_large⟩ : ℚ) ≤
          (c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) := by
      exact_mod_cast hnoncross.le
    linarith
  have hcommonSource : commonShift ≤ sourceShift := by
    dsimp only [commonShift, sourceShift]
    push_cast
    have hcast :
        ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) ≤
        ((c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) := by
      exact_mod_cast hpair
    push_cast at hcast
    linarith
  have hcommonDc :
      (commonShift : WithTop ℚ) + a.representationAlpha b next ≤
        (y : WithTop ℚ) + dc := by
    exact add_le_add (by exact_mod_cast hcommonY) hnextCap
  have hcommonBeta :
      (commonShift : WithTop ℚ) + a.representationAlpha b next ≤
        qTerm := by
    exact add_le_add le_rfl hbeta
  have hcommonNext :
      (commonShift : WithTop ℚ) + a.representationAlpha b next ≤
        sourceTerm := by
    exact add_le_add (by exact_mod_cast hcommonSource) le_rfl
  have hcommonMin :
      (commonShift : WithTop ℚ) + a.representationAlpha b next ≤
        min ((y : WithTop ℚ) + dc) (min qTerm sourceTerm) :=
    le_min hcommonDc (le_min hcommonBeta hcommonNext)
  have hcommonOriginal :
      (commonShift : WithTop ℚ) + a.representationAlpha b next ≤
        min ((y : WithTop ℚ) + db) (min qTerm sourceTerm) := by
    rw [hreplace]
    exact hcommonMin
  constructor
  · change (commonShift : WithTop ℚ) + a.representationAlpha b next ≤ _
    exact hcommonOriginal.trans hthree
  · change (commonShift : WithTop ℚ) + a.representationAlpha b next ≤ _
    calc
      (commonShift : WithTop ℚ) + a.representationAlpha b next ≤
          min ((y : WithTop ℚ) + db) (min qTerm sourceTerm) :=
        hcommonOriginal
      _ ≤ min ((y : WithTop ℚ) + db) qTerm := by
        apply le_min
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (min_le_left _ _)
      _ = (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          b.representationAlpha c j := hnormal.symm

/-- The first component of the two common lower bounds at lines 2272--2274. -/
theorem commonNextSourceAlpha_le_sourcePrimary_of_noncross_failure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩)
    (hfailure : ¬a.representationAlpha c j ≤
      a.representationAlpha b j) :
    (((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
        a.representationPrimaryDefect b j :=
  (a.commonNextSourceAlpha_bounds_of_noncross_failure
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
      hnoncross hfailure).1

end BONG.GoodBONG

end Bong
