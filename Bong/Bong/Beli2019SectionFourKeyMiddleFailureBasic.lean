/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyNoncrossComplete

/-!
# Beli (2019), Lemma 4.2: first exclusions for the middle bound

After the source bound has been proved, assume strictly that
`C_(i-1) > B_(i-1)`.  Lines 2299--2311 first remove the target-alpha and
half-gap candidates in the four-term reduced formula for `B_(i-1)`.
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

/-- Lines 2304--2306: the target-alpha candidate in the reduced formula
for `B_(i-1)` is strictly larger than `C_(i-1)`. -/
theorem targetAlpha_lt_middleTargetTargetAlpha_of_leftDirect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j) :
    a.representationAlpha c j <
      b.representationSecondaryTargetAlpha c j hi j.lt_large := by
  let targetPair : Fin n := ⟨j.val - 2, by omega⟩
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let middleShift : ℚ :=
    ((b.order ⟨j.val, j.lt_large⟩ + b.order ⟨j.val + 1, hi.2⟩ -
      2 * c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  have htarget : a.representationAlpha c j ≤
      (targetShift : WithTop ℚ) +
        (c.alphaValue targetPair : WithTop ℚ) := by
    have hprimary := a.representationAlpha_le_primary c j
    have hcap := a.truncatedPrefixDefect_le_rightCap c (-1)
      (j.val + 1) (j.val - 1)
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hcap' :
        a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) ≤
          (c.alphaValue targetPair : WithTop ℚ) := by
      simpa only [targetPair, show j.val - 1 - 1 = j.val - 2 by omega]
        using hcap
    unfold representationPrimaryDefect at hprimary
    exact hprimary.trans (by
      simpa only [targetShift] using add_le_add_right hcap' _)
  have hpairRaw :=
    ((a.representationOrderCondition_iff b le_rfl).mp hab).pairSum_le
      j.val hi.2
  have hpair :
      a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ ≤
        b.order ⟨j.val, j.lt_large⟩ + b.order ⟨j.val + 1, hi.2⟩ := by
    simpa only [orderSequence_at] using hpairRaw
  have hessentialRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.1 j.pos hi.2
  simp only [orderSequence_at, nextEssentialIndex] at hessentialRaw
  have hshift : targetShift < middleShift := by
    dsimp only [targetShift, middleShift]
    push_cast
    have hpairQ :
        (a.order ⟨j.val, j.lt_large⟩ : ℚ) +
            a.order ⟨j.val + 1, hi.2⟩ ≤
          b.order ⟨j.val, j.lt_large⟩ +
            b.order ⟨j.val + 1, hi.2⟩ := by
      exact_mod_cast hpair
    have hessentialQ :
        (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
          a.order ⟨j.val + 1, hi.2⟩ := by
      exact_mod_cast hessentialRaw
    linarith
  calc
    a.representationAlpha c j ≤
        (targetShift : WithTop ℚ) +
          (c.alphaValue targetPair : WithTop ℚ) := htarget
    _ < (middleShift : WithTop ℚ) +
          (c.alphaValue targetPair : WithTop ℚ) :=
      WithTop.add_lt_add_right WithTop.coe_ne_top (by exact_mod_cast hshift)
    _ = b.representationSecondaryTargetAlpha c j hi j.lt_large := by
      rfl

/-- Lines 2307--2311: the half-gap candidate is impossible once
`C_(i-1) > B_(i-1)`, because the first direct order consequence is
`R_i ≤ S_i`. -/
theorem middleTargetAlpha_ne_halfGap_of_leftDirect_failure
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    b.representationAlpha c j ≠ b.representationHalfGap c j := by
  intro hhalf
  have hbound := a.representationAlpha_le_middleHalfGap_of_sourceCurrent_le
    b c j hcurrent
  rw [← hhalf] at hbound
  exact hfailure hbound

/-- After the first two exclusions, the reduced invariant `B_(i-1)` is
either its primary defect or its source-alpha candidate. -/
theorem middleTargetAlpha_primary_or_source_of_leftDirect_failure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    b.representationAlpha c j = b.representationPrimaryDefect c j ∨
      b.representationAlpha c j =
        b.representationSecondarySourceAlpha c j hi := by
  have hcurrent := a.keyLemmaLeftDirect_sourceCurrent_le_middleCurrent
    b c hab hbcOrder j hi.1 hi.2 hessential hdirect
  have hhalf := a.middleTargetAlpha_ne_halfGap_of_leftDirect_failure
    b c j hcurrent hfailure
  have htarget := a.targetAlpha_lt_middleTargetTargetAlpha_of_leftDirect
    b c hab j hi hessential
  rcases a.middleTargetAlpha_reduced_four_candidates
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab hbcDefect j hi hessential hdirect with
    hhalf' | hprimary | hsource | htarget'
  · exact False.elim (hhalf hhalf')
  · exact Or.inl hprimary
  · exact Or.inr hsource
  · exact False.elim (hfailure (by rw [htarget']; exact htarget.le))

/-- Lines 2304--2311 remove the two inactive candidates not only as an
equality split, but from the reduced minimum itself.  The resulting exact
two-term normal form is the input required by Lemma 1.4(b). -/
theorem middleTargetAlpha_eq_min_primary_source_of_leftDirect_failure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    b.representationAlpha c j =
      min (b.representationPrimaryDefect c j)
        (b.representationSecondarySourceAlpha c j hi) := by
  have hnormal := a.middleTargetAlpha_eq_reduced_of_leftDirect
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab hbcDefect j hi hessential hdirect
  have hprimaryUpper : b.representationAlpha c j ≤
      b.representationPrimaryDefect c j := by
    rw [hnormal]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hsourceUpper : b.representationAlpha c j ≤
      b.representationSecondarySourceAlpha c j hi := by
    rw [hnormal]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  rcases a.middleTargetAlpha_primary_or_source_of_leftDirect_failure
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab hbcOrder hbcDefect j hi hessential hdirect hfailure with
    hprimary | hsource
  · rw [hprimary, min_eq_left (hprimary ▸ hsourceUpper)]
  · rw [hsource, min_eq_right (hsource ▸ hprimaryUpper)]

end BONG.GoodBONG

end Bong
