/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyMiddleFailureBasic

/-!
# Beli (2019), Lemma 4.2: replacement in the middle-bound failure branch

Lines 2312--2317 apply Lemma 1.4(b) to the two remaining candidates for
`B_(i-1)`.  The middle--target prefix defect is replaced by the
source--middle prefix defect, after which condition 2.1(ii) supplies the
common lower value containing `A_i`.
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

/-- Lines 2312--2317.  If the desired middle bound fails strictly, the
two-term minimum obtained from `B_(i-1)` dominates the same two shifts of
the next source invariant `A_i`. -/
theorem min_shifted_nextSourceAlpha_le_middleTargetAlpha_of_leftDirect_failure
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
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    min
        ((((b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (nextRepresentationIndex j hi.2)
        )
        ((((2 * b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (nextRepresentationIndex j hi.2)) ≤
      b.representationAlpha c j := by
  let next := nextRepresentationIndex j hi.2
  let x : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let y : ℚ := ((b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sourceShift : ℚ := ((2 * b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let da := a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let db := b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let dc := a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1)
  let beta : WithTop ℚ := b.alphaValue ⟨j.val, by omega⟩
  let sourceTerm : WithTop ℚ := (sourceShift : WithTop ℚ) + beta
  have hnormalRaw :=
    a.middleTargetAlpha_eq_min_primary_source_of_leftDirect_failure
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hnormal : b.representationAlpha c j =
      min ((y : WithTop ℚ) + db) sourceTerm := by
    simpa only [y, sourceShift, db, beta, sourceTerm,
      representationPrimaryDefect, representationSecondarySourceAlpha]
      using hnormalRaw
  have hcurrent := a.keyLemmaLeftDirect_sourceCurrent_le_middleCurrent
    b c hab hbcOrder j hi.1 hi.2 hessential hdirect
  have hxy : x ≤ y := by
    dsimp only [x, y]
    exact_mod_cast sub_le_sub_right hcurrent _
  have htargetCap : a.representationAlpha c j ≤
      (x : WithTop ℚ) + da := by
    simpa only [x, da, representationPrimaryDefect] using
      a.representationAlpha_le_primary c j
  have hbound : min ((y : WithTop ℚ) + db) sourceTerm <
      (x : WithTop ℚ) + da := by
    rw [← hnormal]
    exact (lt_of_not_ge hfailure).trans_le htargetCap
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
      min ((y : WithTop ℚ) + db) sourceTerm =
        min ((y : WithTop ℚ) + dc) sourceTerm :=
    withTop_shifted_min_eq_of_le_of_lt_cut_of_domination
      x y sourceTerm da db dc hxy hforward hreverse hbound
  have hnextCap : a.representationAlpha b next ≤ dc := by
    have hcondition := habDefect next
    rw [a.coe_representationAlphaValue b next] at hcondition
    simpa only [next, nextRepresentationIndex, dc] using hcondition
  have hbeta : a.representationAlpha b next ≤ beta := by
    have h := a.representationAlpha_le_rightAlpha b habDefect next
    simpa only [next, nextRepresentationIndex, beta, Nat.add_sub_cancel] using h
  have hlower :
      min ((y : WithTop ℚ) + a.representationAlpha b next)
          ((sourceShift : WithTop ℚ) + a.representationAlpha b next) ≤
        min ((y : WithTop ℚ) + dc) sourceTerm := by
    exact min_le_min (add_le_add le_rfl hnextCap)
      (add_le_add le_rfl hbeta)
  have hresult :
      min ((y : WithTop ℚ) + a.representationAlpha b next)
          ((sourceShift : WithTop ℚ) + a.representationAlpha b next) ≤
        b.representationAlpha c j := by
    calc
      min ((y : WithTop ℚ) + a.representationAlpha b next)
          ((sourceShift : WithTop ℚ) + a.representationAlpha b next) ≤
        min ((y : WithTop ℚ) + dc) sourceTerm := hlower
      _ = min ((y : WithTop ℚ) + db) sourceTerm := hreplace.symm
      _ = b.representationAlpha c j := hnormal.symm
  simpa only [y, sourceShift, next] using hresult

end BONG.GoodBONG

end Bong
