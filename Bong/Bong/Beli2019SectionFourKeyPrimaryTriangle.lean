/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyCandidate

/-!
# Beli (2019), Lemma 4.2: the first primary-defect triangle

This is the common first step in the two primary-candidate subcases of
Lemma 4.2(i).  Under `T_(i-2) ≤ S_i`, condition 2.1(i) gives
`S_(i-1) ≤ T_(i-1)`.  A strict failure at the primary candidate then
identifies its defect with the middle-to-target comparison defect by the
strict defect triangle.
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

/-- Condition 2.1(i) for the middle-to-target pair turns
`T_(i-2) ≤ S_i` into `S_(i-1) ≤ T_(i-1)`. -/
theorem middlePrevious_le_targetPrevious_of_targetTwoPrevious_le_middleCurrent
    (b : GoodBONG r M (n + 1)) (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1)) (hiTwo : 1 < j.val)
    (hcross : c.order ⟨j.val - 2, by
        have := j.lt_large
        omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩) :
    b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
  rcases hbc ⟨j.val - 1, by have := j.lt_large; omega⟩ with
    hcurrent | ⟨_, _, hpair⟩
  · exact hcurrent
  · have hpair' :
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
            b.order ⟨j.val, j.lt_large⟩ ≤
          c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ +
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
      simpa only [Fin.val_mk, Nat.sub_add_cancel (show 1 ≤ j.val by omega),
        Nat.sub_sub] using hpair
    omega

/-- If the target alpha is strictly above the source primary candidate,
the two negative defects in that comparison are strictly ordered. -/
theorem primarySourceDefect_lt_targetDefect_of_targetPrevious_ge
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (htargetPrevious : b.order ⟨j.val - 1, by
        have := j.lt_large
        omega⟩ ≤
      c.order ⟨j.val - 1, by
        have := j.lt_large
        omega⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1) <
      a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) := by
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sourceDefect :=
    a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1)
  let targetDefect :=
    a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  have hshifted : (sourceShift : WithTop ℚ) + sourceDefect <
      (targetShift : WithTop ℚ) + targetDefect := by
    exact hprimary.trans_le (a.representationAlpha_le_primary c j)
  have hshift : targetShift ≤ sourceShift := by
    dsimp only [targetShift, sourceShift]
    norm_cast
    omega
  have hshifted' : (sourceShift : WithTop ℚ) + sourceDefect <
      (sourceShift : WithTop ℚ) + targetDefect := by
    exact hshifted.trans_le (add_le_add (by exact_mod_cast hshift) le_rfl)
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted'

/-- The strict triangle identifies the source primary defect with the
middle-to-target comparison defect at the preceding prefix. -/
theorem primarySourceDefect_eq_middleTargetDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1)) (hiTwo : 1 < j.val)
    (hcross : c.order ⟨j.val - 2, by
        have := j.lt_large
        omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1) =
      b.truncatedPrefixDefect c 1 (j.val - 1) (j.val - 1) := by
  have htargetPrevious :=
    b.middlePrevious_le_targetPrevious_of_targetTwoPrevious_le_middleCurrent
      c hbc j hiTwo hcross
  have hstrict := a.primarySourceDefect_lt_targetDefect_of_targetPrevious_ge
    b c j htargetPrevious hprimary
  exact a.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b c
    (j.val + 1) (j.val - 1) (j.val - 1) hstrict

/-- Condition 2.1(ii) for the middle-to-target pair turns the triangle
identity into the paper's bound
`A_(i-1) ≥ R_i-S_(i-1)+B_(i-2)`. -/
theorem shift_previousMiddleAlpha_le_sourcePrimary
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1)) (hiTwo : 1 < j.val)
    (hcross : c.order ⟨j.val - 2, by
        have := j.lt_large
        omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j) :
    (((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
        b.representationAlpha c (previousRepresentationIndex j hiTwo) ≤
      a.representationPrimaryDefect b j := by
  have htriangle := a.primarySourceDefect_eq_middleTargetDefect
    b c hbcOrder j hiTwo hcross hprimary
  have hdefect := hbcDefect (previousRepresentationIndex j hiTwo)
  have hdefect' :
      b.representationAlpha c (previousRepresentationIndex j hiTwo) ≤
        b.truncatedPrefixDefect c 1 (j.val - 1) (j.val - 1) := by
    rw [b.coe_representationAlphaValue c
      (previousRepresentationIndex j hiTwo)] at hdefect
    simpa only [previousRepresentationIndex] using hdefect
  unfold representationPrimaryDefect
  rw [htriangle]
  exact add_le_add_right hdefect' _

end BONG.GoodBONG

end Bong
