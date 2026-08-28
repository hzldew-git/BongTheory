/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyPrimaryTriangle
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Lemma 4.2: the first secondary-defect triangle

In the secondary-candidate branch, condition 2.1(i) compares the preceding
middle and target pairs.  Cancelling the resulting order shifts gives the
strict defect comparison used in the paper.  The strict triangle law then
identifies that source-to-middle defect with a middle-to-target defect.
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

/-- A strict failure at the current-prefix secondary candidate implies the
paper's strict comparison
`d[-a_(1,i+1)b_(1,i-1)] < d[a_(1,i+1)c_(1,i-3)]`.

The only order input is the adjacent-pair consequence of condition 2.1(i)
for the middle-to-target representation. -/
theorem secondaryCurrentSourceDefect_lt_targetSecondaryDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val <
      a.truncatedPrefixDefect c 1 (j.val + 2) (j.val - 2) := by
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sourceDefect :=
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  let targetDefect :=
    a.truncatedPrefixDefect c 1 (j.val + 2) (j.val - 2)
  have hshifted : (sourceShift : WithTop ℚ) + sourceDefect <
      (targetShift : WithTop ℚ) + targetDefect := by
    have hcandidate :=
      hsecondary.trans_le (a.representationAlpha_le_secondary c j hi)
    simpa only [sourceShift, targetShift, sourceDefect, targetDefect,
      representationSecondaryCurrentDefect, representationSecondaryDefect]
      using hcandidate
  have hpairRaw :=
    ((b.representationOrderCondition_iff c le_rfl).mp hbc).pairSum_le
      (j.val - 2) (by omega)
  have hpair :
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
    simpa only [orderSequence_at, show j.val - 2 + 1 = j.val - 1 by omega]
      using hpairRaw
  have hshift : targetShift ≤ sourceShift := by
    dsimp only [targetShift, sourceShift]
    norm_cast
    omega
  have hshifted' : (sourceShift : WithTop ℚ) + sourceDefect <
      (sourceShift : WithTop ℚ) + targetDefect := by
    exact hshifted.trans_le (add_le_add (by exact_mod_cast hshift) le_rfl)
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted'

/-- The first strict triangle in the secondary branch:
`d[-a_(1,i+1)b_(1,i-1)] = d[-b_(1,i-1)c_(1,i-3)]`. -/
theorem secondaryCurrentSourceDefect_eq_middleTargetPreviousDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
      b.truncatedPrefixDefect c (-1) j.val (j.val - 2) := by
  have hstrict :=
    a.secondaryCurrentSourceDefect_lt_targetSecondaryDefect
      b c hbc j hi hsecondary
  exact a.truncatedPrefixDefect_neg_eq_neg_of_lt_pos b c
    (j.val + 2) j.val (j.val - 2) hstrict

/-- The next comparison in the paper: the source secondary defect is
strictly smaller than the capped adjacent defect of the target pair
`c_(i-2), c_(i-1)`.

The strictness is exactly essentiality (`T_(i-1) < R_(i+1)`).  Remark 1.1
supplies the lower bound on the adjacent defect; condition 2.1(i) moves the
target order shift back to the middle order shift. -/
theorem secondaryCurrentSourceDefect_lt_targetAdjacentDefect
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val <
      c.truncatedPrefixDefect c (-1) (j.val - 2) j.val := by
  let previousPair : Fin n := ⟨j.val - 2, by omega⟩
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let primaryShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let adjacentLower : ℚ :=
    ((c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) +
      c.alphaValue previousPair
  let sourceDefect :=
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  let adjacentDefect :=
    c.truncatedPrefixDefect c (-1) (j.val - 2) j.val
  have hcross :
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    have hraw := hessential.1 (by
      simp only [nextEssentialIndex]
      omega) (by
        simpa only [nextEssentialIndex] using hi.2)
    simpa only [orderSequence_at, nextEssentialIndex] using hraw
  have htargetCap :
      a.representationAlpha c j ≤
        (primaryShift : WithTop ℚ) +
          (c.alphaValue previousPair : WithTop ℚ) := by
    have hprimary := a.representationAlpha_le_primary c j
    have hcap := a.truncatedPrefixDefect_le_rightCap c (-1)
      (j.val + 1) (j.val - 1)
    have hcap' :
        a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) ≤
          (c.alphaValue previousPair : WithTop ℚ) := by
      rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
      simpa only [previousPair, show j.val - 1 - 1 = j.val - 2 by omega]
        using hcap
    unfold representationPrimaryDefect at hprimary
    exact hprimary.trans (by
      simpa only [primaryShift] using add_le_add_right hcap' _)
  have hadjacent : (adjacentLower : WithTop ℚ) ≤ adjacentDefect := by
    have hraw := c.order_sub_add_alpha_le_cappedAdjacent previousPair
    have hcast : previousPair.castSucc =
        (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hsucc : previousPair.succ =
        (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [previousPair, Fin.val_succ]
      omega
    rw [hcast, hsucc] at hraw
    simpa only [adjacentLower, adjacentDefect, previousPair,
      show j.val - 2 + 2 = j.val by omega] using hraw
  have hcapStrict :
      (primaryShift : WithTop ℚ) +
          (c.alphaValue previousPair : WithTop ℚ) <
        (targetShift : WithTop ℚ) + (adjacentLower : WithTop ℚ) := by
    have hcrossQ :
        (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
          (a.order ⟨j.val + 1, hi.2⟩ : ℚ) := by
      exact_mod_cast hcross
    exact_mod_cast (show
      primaryShift + c.alphaValue previousPair <
        targetShift + adjacentLower by
      dsimp only [primaryShift, targetShift, adjacentLower]
      push_cast
      linarith)
  have hpairRaw :=
    ((b.representationOrderCondition_iff c le_rfl).mp hbc).pairSum_le
      (j.val - 2) (by omega)
  have hpair :
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
    simpa only [orderSequence_at, show j.val - 2 + 1 = j.val - 1 by omega]
      using hpairRaw
  have hshift : targetShift ≤ sourceShift := by
    dsimp only [targetShift, sourceShift]
    norm_cast
    omega
  have hcandidate : (sourceShift : WithTop ℚ) + sourceDefect <
      (sourceShift : WithTop ℚ) + adjacentDefect := by
    calc
      (sourceShift : WithTop ℚ) + sourceDefect <
          a.representationAlpha c j := by
        simpa only [sourceShift, sourceDefect,
          representationSecondaryCurrentDefect] using hsecondary
      _ ≤ (primaryShift : WithTop ℚ) +
          (c.alphaValue previousPair : WithTop ℚ) := htargetCap
      _ < (targetShift : WithTop ℚ) + (adjacentLower : WithTop ℚ) :=
        hcapStrict
      _ ≤ (targetShift : WithTop ℚ) + adjacentDefect :=
        add_le_add le_rfl hadjacent
      _ ≤ (sourceShift : WithTop ℚ) + adjacentDefect :=
        add_le_add (by exact_mod_cast hshift) le_rfl
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hcandidate

/-- The second strict triangle in the secondary branch identifies the
secondary source defect with the same-prefix middle-to-target defect. -/
theorem secondaryCurrentSourceDefect_eq_middleTargetCurrentDefect
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
      b.truncatedPrefixDefect c 1 j.val j.val := by
  have hfirst :=
    a.secondaryCurrentSourceDefect_eq_middleTargetPreviousDefect
      b c hbc j hi hsecondary
  have hadjacent :=
    a.secondaryCurrentSourceDefect_lt_targetAdjacentDefect
      b c hbc j hi hessential hsecondary
  have hstrict :
      c.truncatedPrefixDefect b (-1) (j.val - 2) j.val <
        c.truncatedPrefixDefect c (-1) (j.val - 2) j.val := by
    rw [c.truncatedPrefixDefect_comm b (-1) (j.val - 2) j.val]
    rw [← hfirst]
    exact hadjacent
  have htriangle := c.truncatedPrefixDefect_neg_eq_pos_of_lt_neg
    b c (j.val - 2) j.val j.val hstrict
  calc
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
        b.truncatedPrefixDefect c (-1) j.val (j.val - 2) := hfirst
    _ = c.truncatedPrefixDefect b (-1) (j.val - 2) j.val :=
      (c.truncatedPrefixDefect_comm b (-1) (j.val - 2) j.val).symm
    _ = b.truncatedPrefixDefect c 1 j.val j.val := htriangle

/-- Consequently the source secondary defect is bounded below by the
middle-to-target representation alpha `B_(i-1)`. -/
theorem middleTargetAlpha_le_secondaryCurrentSourceDefect
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j) :
    b.representationAlpha c j ≤
      a.truncatedPrefixDefect b (-1) (j.val + 2) j.val := by
  have htriangle :=
    a.secondaryCurrentSourceDefect_eq_middleTargetCurrentDefect
      b c hbcOrder j hi hessential hsecondary
  have hdefect := hbcDefect j
  rw [b.coe_representationAlphaValue c j] at hdefect
  rw [htriangle]
  exact hdefect

/-- Shifted form of the preceding lower bound, exactly the inequality used
when the paper expands the possible values of `B_(i-1)`. -/
theorem shift_middleTargetAlpha_le_secondaryCurrentSource
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j) :
    (((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) + b.representationAlpha c j ≤
      a.representationSecondaryCurrentDefect b j hi := by
  have hbound := a.middleTargetAlpha_le_secondaryCurrentSourceDefect
    b c hbcOrder hbcDefect j hi hessential hsecondary
  unfold representationSecondaryCurrentDefect
  exact add_le_add_right hbound _

end BONG.GoodBONG

end Bong
