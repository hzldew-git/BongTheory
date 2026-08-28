/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyNoncrossHalfGap

/-!
# Beli (2019), Lemma 4.2: the next noncrossed source alpha is primary

The target-alpha candidate at the next boundary is strictly larger than
the shifted `B_(i-1)` bound.  Together with the preceding half-gap
exclusion, this leaves only the primary candidate.  These are lines
2280--2287.
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

/-- Lines 2280--2283: the target-alpha candidate at the next source
boundary contradicts the second common lower bound. -/
theorem nextSourceAlpha_ne_targetAlpha_of_noncross_failure
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
      a.representationAlpha b j)
    (hinterior : 1 < (nextRepresentationIndex j hi.2).val ∧
      (nextRepresentationIndex j hi.2).val + 1 < n + 1) :
    a.representationAlpha b (nextRepresentationIndex j hi.2) ≠
      a.representationSecondaryTargetAlpha b
        (nextRepresentationIndex j hi.2) hinterior
          (nextRepresentationIndex j hi.2).lt_large := by
  intro htarget
  let next := nextRepresentationIndex j hi.2
  let outerShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  let commonShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let targetShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 1, hi.2⟩ +
    a.order ⟨j.val + 2, by
      dsimp only [next, nextRepresentationIndex] at hinterior
      omega⟩ - b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let beta : WithTop ℚ :=
    b.alphaValue ⟨j.val - 1, by have := j.lt_large; omega⟩
  have hcommon :=
    (a.commonNextSourceAlpha_bounds_of_noncross_failure
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
        hnoncross hfailure).2
  have hbeta : b.representationAlpha c j ≤ beta := by
    have h := b.representationAlpha_le_leftAlpha c hbcDefect j
    simpa only [beta] using h
  have hessentialRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.2 hi.1 (by
      dsimp only [next, nextRepresentationIndex] at hinterior
      simpa only [nextEssentialIndex] using hinterior.2)
  simp only [orderSequence_at, nextEssentialIndex] at hessentialRaw
  have hshift : outerShift < targetShift := by
    dsimp only [outerShift, targetShift]
    push_cast
    have hpairQ :
        (c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) +
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
          a.order ⟨j.val + 1, hi.2⟩ +
            a.order ⟨j.val + 2, by
              dsimp only [next, nextRepresentationIndex] at hinterior
              omega⟩ := by
      exact_mod_cast hessentialRaw
    linarith
  have hstrict : (outerShift : WithTop ℚ) +
      b.representationAlpha c j < (targetShift : WithTop ℚ) + beta := by
    exact (add_le_add le_rfl hbeta).trans_lt
      (WithTop.add_lt_add_right WithTop.coe_ne_top
        (WithTop.coe_lt_coe.mpr hshift))
  have hexpand :
      (commonShift : WithTop ℚ) +
          a.representationAlpha b next =
        (targetShift : WithTop ℚ) + beta := by
    rw [htarget]
    unfold representationSecondaryTargetAlpha
    simp only [next, nextRepresentationIndex, Nat.add_sub_cancel]
    rw [← add_assoc]
    congr 1
    norm_cast
    dsimp only [commonShift, targetShift]
    push_cast
    ring
  have hcontradiction :
      (outerShift : WithTop ℚ) + b.representationAlpha c j <
        (commonShift : WithTop ℚ) + a.representationAlpha b next := by
    rw [hexpand]
    exact hstrict
  exact (not_lt_of_ge (by simpa only [next, outerShift, commonShift]
    using hcommon)) hcontradiction

/-- Lines 2283--2287: after the two exclusions, `A_i` is its primary
defect candidate. -/
theorem nextSourceAlpha_eq_primary_of_noncross_failure
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
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
    a.representationAlpha b (nextRepresentationIndex j hi.2) =
      a.representationPrimaryDefect b (nextRepresentationIndex j hi.2) := by
  have hhalf := a.nextSourceAlpha_ne_halfGap_of_noncross_failure
    (sourceLaws := sourceLaws)
    (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect
      j hi hessential hdirect hnoncross hfailure
  rcases a.nextSourceAlpha_noncross_candidates
      (sourceLaws := sourceLaws) (middleLaws := middleLaws)
      b c habDefect hbcOrder j hi hessential hdirect hnoncross with
    hhalf' | hprimary | ⟨hinterior, htarget⟩
  · exact False.elim (hhalf hhalf')
  · exact hprimary
  · exact False.elim
      (a.nextSourceAlpha_ne_targetAlpha_of_noncross_failure
        (middleLaws := middleLaws) (targetLaws := targetLaws)
        b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
          hnoncross hfailure hinterior htarget)

end BONG.GoodBONG

end Bong
