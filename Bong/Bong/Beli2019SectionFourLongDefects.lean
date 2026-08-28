/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectTriangle
import Bong.Bong.Beli2019SectionFourLongMiddle
import Bong.Bong.Beli2019Lemma27
import Bong.Bong.Beli2009TwoAdic

/-!
# Beli (2019), Section 4(iv): the two strict mixed-defect bounds

This is the scalar core of the middle branch on lines 2743--2769.  The
negative-square outer defect is first shown to be larger than `2e`.  Strict
defect triangles then identify each small mixed defect with the appropriate
equal-prefix defect.  Condition (ii), the Lemma 2.7 normal forms, and the
good-BONG adjacent-gap bounds give the final contradiction.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The ordinary boundary `i - 1` attached to a long representation
index. -/
def longPreviousRepresentationIndex
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    RepresentationIndex (n + 1) (n + 1) where
  val := i.val - 1
  pos := Nat.sub_pos_of_lt i.one_lt
  lt_large := lt_of_le_of_lt (Nat.sub_le i.val 1)
    (lt_trans (Nat.lt_succ_self i.val) i.succ_lt_large)
  le_small := le_trans (Nat.sub_le i.val 1)
    (Nat.le_of_lt (lt_trans (Nat.lt_succ_self i.val) i.succ_lt_large))

@[simp]
theorem longPreviousRepresentationIndex_val
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    (longPreviousRepresentationIndex i).val = i.val - 1 := rfl

/-- The ordinary boundary `i + 1` attached to a long representation
index. -/
def longNextRepresentationIndex
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    RepresentationIndex (n + 1) (n + 1) where
  val := i.val + 1
  pos := Nat.zero_lt_succ i.val
  lt_large := i.succ_lt_large
  le_small := Nat.le_of_lt i.succ_lt_large

@[simp]
theorem longNextRepresentationIndex_val
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    (longNextRepresentationIndex i).val = i.val + 1 := rfl

/-- If condition (ii) bounds the representation alpha by `C`, while the
half-gap and primary candidates are both larger than `C`, the boundary is
interior and Lemma 2.7(ii)'s current-secondary candidate is at most `C`.
This also implements Definition 4's endpoint convention: at an endpoint
the two displayed inequalities are contradictory. -/
theorem representationSecondaryCurrentDefect_le_of_two_candidates_gt
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (p : RepresentationIndex (n + 1) (n + 1)) (C : WithTop ℚ)
    (hcomparison : a.truncatedPrefixDefect b 1 p.val p.val ≤ C)
    (hhalf : C < a.representationHalfGap b p)
    (hprimary : C < a.representationPrimaryDefect b p)
    (hcross : ∀ hi : 1 < p.val ∧ p.val + 1 < n + 1,
      b.order ⟨p.val - 1, by omega⟩ ≤
        a.order ⟨p.val + 1, hi.2⟩) :
    ∃ hi : 1 < p.val ∧ p.val + 1 < n + 1,
      a.representationSecondaryCurrentDefect b p hi ≤
        a.truncatedPrefixDefect b 1 p.val p.val := by
  have halphaComparison : a.representationAlpha b p ≤
      a.truncatedPrefixDefect b 1 p.val p.val := by
    rw [← a.coe_representationAlphaValue b p]
    exact hdefect p
  have halpha : a.representationAlpha b p ≤ C := by
    exact halphaComparison.trans hcomparison
  have hi : 1 < p.val ∧ p.val + 1 < n + 1 := by
    by_contra hnot
    rw [a.representationAlpha_eq_min_halfGap_prime b p,
      a.representationAlphaPrime_eq_primary_of_not_interior b p hnot]
      at halpha
    exact (not_le_of_gt (lt_min hhalf hprimary)) halpha
  refine ⟨hi, ?_⟩
  rw [a.representationAlpha_eq_min_halfGap_prime b p,
    a.representationAlphaPrime_eq_min_primary_current b p hi (hcross hi)]
    at halphaComparison
  rcases min_le_iff.mp halphaComparison with hhalfLe | hprimeLe
  · exact False.elim ((not_le_of_gt hhalf) (hhalfLe.trans hcomparison))
  · rcases min_le_iff.mp hprimeLe with hprimaryLe | hsecondaryLe
    · exact False.elim ((not_le_of_gt hprimary) (hprimaryLe.trans hcomparison))
    · exact hsecondaryLe

/-- The reverse form of the preceding extraction, using Lemma 2.7(i)'s
previous-secondary candidate. -/
theorem representationSecondaryPreviousDefect_le_of_two_candidates_gt
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (p : RepresentationIndex (n + 1) (n + 1)) (C : WithTop ℚ)
    (hcomparison : a.truncatedPrefixDefect b 1 p.val p.val ≤ C)
    (hhalf : C < a.representationHalfGap b p)
    (hprimary : C < a.representationPrimaryDefect b p)
    (hcross : ∀ hi : 1 < p.val ∧ p.val + 1 < n + 1,
      b.order ⟨p.val - 2, by omega⟩ ≤
        a.order ⟨p.val, p.lt_large⟩) :
    ∃ hi : 1 < p.val ∧ p.val + 1 < n + 1,
      a.representationSecondaryPreviousDefect b p hi ≤
        a.truncatedPrefixDefect b 1 p.val p.val := by
  have halphaComparison : a.representationAlpha b p ≤
      a.truncatedPrefixDefect b 1 p.val p.val := by
    rw [← a.coe_representationAlphaValue b p]
    exact hdefect p
  have halpha : a.representationAlpha b p ≤ C := by
    exact halphaComparison.trans hcomparison
  have hi : 1 < p.val ∧ p.val + 1 < n + 1 := by
    by_contra hnot
    rw [a.representationAlpha_eq_min_halfGap_prime b p,
      a.representationAlphaPrime_eq_primary_of_not_interior b p hnot]
      at halpha
    exact (not_le_of_gt (lt_min hhalf hprimary)) halpha
  refine ⟨hi, ?_⟩
  rw [a.representationAlpha_eq_min_halfGap_prime b p,
    a.representationAlphaPrime_eq_min_primary_previous b p hi (hcross hi)]
    at halphaComparison
  rcases min_le_iff.mp halphaComparison with hhalfLe | hprimeLe
  · exact False.elim ((not_le_of_gt hhalf) (hhalfLe.trans hcomparison))
  · rcases min_le_iff.mp hprimeLe with hprimaryLe | hsecondaryLe
    · exact False.elim ((not_le_of_gt hprimary) (hprimaryLe.trans hcomparison))
    · exact hsecondaryLe

/-- In the exceptional square class, both boundary alphas in the outer
mixed defect are larger than `2e`; hence so is the capped defect itself. -/
theorem sectionFourLong_outerDefect_gt_twoE
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1))) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
  rcases htrigger with ⟨houterOrder, hcrossOrder, hbaseOrder⟩
  let sourceGap : Fin n := ⟨i.val, by
    have := i.succ_lt_large
    omega⟩
  let targetGap : Fin n := ⟨i.val - 2, by
    have := i.succ_lt_large
    omega⟩
  have hsourceGap : 2 * (ramificationIndex K : Int) <
      a.orderGap sourceGap := by
    unfold orderGap
    have hsucc : sourceGap.succ =
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hcast : sourceGap.castSucc =
        (⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
    omega
  have htargetGap : 2 * (ramificationIndex K : Int) <
      c.orderGap targetGap := by
    unfold orderGap
    have hsucc : targetGap.succ =
        (⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [targetGap, Fin.val_succ]
      have := i.one_lt
      omega
    have hcast : targetGap.castSucc =
        (⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
    omega
  have hsourceAlpha : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue sourceGap := (a.alpha_p5 sourceGap).2.2.mpr hsourceGap
  have htargetAlpha : 2 * (ramificationIndex K : ℚ) <
      c.alphaValue targetGap := (c.alpha_p5 targetGap).2.2.mpr htargetGap
  have hraw : IsSquare
      ((-1 : Kˣ) * a.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1)) := by
    simpa only [neg_one_mul] using hsquare
  unfold truncatedPrefixDefect
  rw [defectOrder_eq_top_of_isSquare hraw,
    min_eq_right (show min (a.prefixAlphaCap (i.val + 1))
      (c.prefixAlphaCap (i.val - 1)) ≤ (⊤ : WithTop ℚ) from le_top)]
  have htargetPrefixPos : 0 < i.val - 1 := Nat.sub_pos_of_lt i.one_lt
  have hiValLt : i.val < n + 1 :=
    lt_trans (Nat.lt_succ_self i.val) i.succ_lt_large
  have htargetPrefixLt : i.val - 1 < n + 1 :=
    lt_of_le_of_lt (Nat.sub_le i.val 1) hiValLt
  rw [a.prefixAlphaCap_of_internal (by omega) i.succ_lt_large,
    c.prefixAlphaCap_of_internal htargetPrefixPos htargetPrefixLt]
  apply lt_min
  · have hsourceAlpha' :
        ((((2 * ramificationIndex K : Nat) : ℚ)) : WithTop ℚ) <
          (a.alphaValue sourceGap : WithTop ℚ) := by
      exact_mod_cast hsourceAlpha
    simpa only [sourceGap, show i.val + 1 - 1 = i.val by omega] using
      hsourceAlpha'
  · have htargetAlpha' :
        ((((2 * ramificationIndex K : Nat) : ℚ)) : WithTop ℚ) <
          (c.alphaValue targetGap : WithTop ℚ) := by
      exact_mod_cast htargetAlpha
    simpa only [targetGap, show i.val - 1 - 1 = i.val - 2 by omega] using
      htargetAlpha'

/-- The half-gap candidate in `B_(i-1)` is strictly above the left
middle-branch threshold. -/
theorem sectionFourLong_leftThreshold_lt_halfGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩) :
    (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ) <
      b.representationHalfGap c
        (longPreviousRepresentationIndex i) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  unfold representationHalfGap
  norm_cast
  simp only [longPreviousRepresentationIndex, Rat.divInt_eq_div,
    show i.val - 1 - 1 = i.val - 2 by omega]
  push_cast
  have hcrossQ :
      (c.order ⟨i.val - 2, by omega⟩ : ℚ) +
          2 * (ramificationIndex K : ℚ) <
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) := by
    exact_mod_cast htrigger.2.1
  have hleftQ :
      (b.order ⟨i.val - 1, by omega⟩ : ℚ) <
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) := by
    exact_mod_cast hleft
  linarith

/-- The primary candidate in `B_(i-1)` is strictly above the left
middle-branch threshold. -/
theorem sectionFourLong_leftThreshold_lt_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i) :
    (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ) <
      b.representationPrimaryDefect c
        (longPreviousRepresentationIndex i) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  let p := longPreviousRepresentationIndex i
  rcases htrigger with ⟨houterOrder, hcrossOrder, hbaseOrder⟩
  have hgapInt :
      2 * (ramificationIndex K : Int) +
          b.order ⟨i.val - 1, by omega⟩ -
          a.order ⟨i.val + 1, i.succ_lt_large⟩ <
        b.order ⟨i.val - 1, by omega⟩ -
          c.order ⟨i.val - 2, by omega⟩ := by
    omega
  have hgap :
      (((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
          (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
          WithTop ℚ) <
        ((((b.order ⟨i.val - 1, by omega⟩ -
          c.order ⟨i.val - 2, by omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
    exact_mod_cast hgapInt
  have hnonnegative := b.truncatedPrefixDefect_nonneg
    c (-1) (p.val + 1) (p.val - 1)
  unfold representationPrimaryDefect
  simpa only [p, longPreviousRepresentationIndex,
    show i.val - 1 - 1 = i.val - 2 by omega] using
    hgap.trans_le (le_add_of_nonneg_right hnonnegative)

/-- The half-gap candidate in `A_(i+1)` is strictly above the right
middle-branch threshold. -/
theorem sectionFourLong_rightThreshold_lt_halfGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩) :
    (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : ℚ) : ℚ)) : WithTop ℚ) <
      a.representationHalfGap b (longNextRepresentationIndex i) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  unfold representationHalfGap
  norm_cast
  simp only [longNextRepresentationIndex, Rat.divInt_eq_div,
    show i.val + 1 - 1 = i.val by omega]
  push_cast
  have hcrossQ :
      (c.order ⟨i.val - 2, by omega⟩ : ℚ) +
          2 * (ramificationIndex K : ℚ) <
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) := by
    exact_mod_cast htrigger.2.1
  have hrightQ :
      (c.order ⟨i.val - 2, by omega⟩ : ℚ) <
        (b.order ⟨i.val, by omega⟩ : ℚ) := by
    exact_mod_cast hright
  linarith

/-- The primary candidate in `A_(i+1)` is strictly above the right
middle-branch threshold. -/
theorem sectionFourLong_rightThreshold_lt_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i) :
    (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : ℚ) : ℚ)) : WithTop ℚ) <
      a.representationPrimaryDefect b (longNextRepresentationIndex i) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  let p := longNextRepresentationIndex i
  rcases htrigger with ⟨houterOrder, hcrossOrder, hbaseOrder⟩
  have hgapInt :
      2 * (ramificationIndex K : Int) +
          c.order ⟨i.val - 2, by omega⟩ -
          b.order ⟨i.val, by omega⟩ <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ -
          b.order ⟨i.val, by omega⟩ := by
    omega
  have hgap :
      (((2 * (ramificationIndex K : ℚ) +
          (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
          (b.order ⟨i.val, by omega⟩ : ℚ) : ℚ)) : WithTop ℚ) <
        ((((a.order ⟨i.val + 1, i.succ_lt_large⟩ -
          b.order ⟨i.val, by omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
    exact_mod_cast hgapInt
  have hnonnegative := a.truncatedPrefixDefect_nonneg
    b (-1) (p.val + 1) (p.val - 1)
  unfold representationPrimaryDefect
  simpa only [p, longNextRepresentationIndex,
    show i.val + 1 - 1 = i.val by omega] using
    hgap.trans_le (le_add_of_nonneg_right hnonnegative)

/-- If the left mixed defect were at most its middle-branch threshold,
the strict capped-defect triangle identifies it with the equal-prefix
defect controlling `B_(i-1)`. -/
theorem sectionFourLong_leftMixed_eq_middleComparison_of_le_threshold
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)))
    (hsmall : a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ)) :
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) =
      b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) := by
  have hthresholdTwoE :
      (((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 1, by
            have := i.succ_lt_large
            omega⟩ : ℚ) -
          (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
          WithTop ℚ) <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    have hthresholdInt :
        2 * (ramificationIndex K : Int) +
            b.order ⟨i.val - 1, by
              have := i.succ_lt_large
              omega⟩ -
            a.order ⟨i.val + 1, i.succ_lt_large⟩ <
          2 * (ramificationIndex K : Int) := by
      omega
    exact_mod_cast hthresholdInt
  have houter := a.sectionFourLong_outerDefect_gt_twoE c i htrigger hsquare
  exact a.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b c
    (i.val + 1) (i.val - 1) (i.val - 1)
    (hsmall.trans_lt (hthresholdTwoE.trans houter))

/-- The right-hand analogue, used when deriving the simultaneous
contradiction for the two mixed defects. -/
theorem sectionFourLong_rightMixed_eq_middleComparison_of_le_threshold
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)))
    (hsmall : b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : ℚ) : ℚ)) : WithTop ℚ)) :
    b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) =
      a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) := by
  have hthresholdTwoE :
      (((2 * (ramificationIndex K : ℚ) +
          (c.order ⟨i.val - 2, by
            have := i.succ_lt_large
            omega⟩ : ℚ) -
          (b.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ : ℚ) : ℚ)) : WithTop ℚ) <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    have hthresholdInt :
        2 * (ramificationIndex K : Int) +
            c.order ⟨i.val - 2, by
              have := i.succ_lt_large
              omega⟩ -
            b.order ⟨i.val, by
              have := i.succ_lt_large
              omega⟩ <
          2 * (ramificationIndex K : Int) := by
      omega
    exact_mod_cast hthresholdInt
  have houter := a.sectionFourLong_outerDefect_gt_twoE c i htrigger hsquare
  have htriangle := c.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b a
    (i.val - 1) (i.val + 1) (i.val + 1) (by
      rw [c.truncatedPrefixDefect_comm b (-1) (i.val - 1) (i.val + 1),
        c.truncatedPrefixDefect_comm a (-1) (i.val - 1) (i.val + 1)]
      exact hsmall.trans_lt (hthresholdTwoE.trans houter))
  calc
    b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) =
        c.truncatedPrefixDefect b (-1) (i.val - 1) (i.val + 1) :=
      (c.truncatedPrefixDefect_comm b (-1)
        (i.val - 1) (i.val + 1)).symm
    _ = b.truncatedPrefixDefect a 1 (i.val + 1) (i.val + 1) := htriangle
    _ = a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) :=
      (a.truncatedPrefixDefect_comm b 1
        (i.val + 1) (i.val + 1)).symm

/-- Candidate relation extracted from a small left mixed defect. -/
theorem sectionFourLong_middleSecondaryCurrent_le_leftMixed
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)))
    (hsmall : a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ)) :
    ∃ hi : 1 < (longPreviousRepresentationIndex i).val ∧
        (longPreviousRepresentationIndex i).val + 1 < n + 1,
      b.representationSecondaryCurrentDefect c
          (longPreviousRepresentationIndex i) hi ≤
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  let p := longPreviousRepresentationIndex i
  let X : ℚ := 2 * (ramificationIndex K : ℚ) +
    (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
    (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ)
  have htriangle := a.sectionFourLong_leftMixed_eq_middleComparison_of_le_threshold
    b c i htrigger hleft hsquare (by simpa only [X] using hsmall)
  have hcomparison : b.truncatedPrefixDefect c 1 p.val p.val ≤
      (X : WithTop ℚ) := by
    change b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) ≤ _
    rw [← htriangle]
    simpa only [X] using hsmall
  have hhalf : (X : WithTop ℚ) < b.representationHalfGap c p := by
    simpa only [p, X] using
      a.sectionFourLong_leftThreshold_lt_halfGap b c i htrigger hleft
  have hprimary : (X : WithTop ℚ) <
      b.representationPrimaryDefect c p := by
    simpa only [p, X] using
      a.sectionFourLong_leftThreshold_lt_primary b c i htrigger
  rcases b.representationSecondaryCurrentDefect_le_of_two_candidates_gt
      c hbc.defectCondition p (X : WithTop ℚ) hcomparison hhalf hprimary
      (by
        intro hi
        simpa only [p, longPreviousRepresentationIndex,
          show i.val - 1 - 1 = i.val - 2 by omega,
          show i.val - 1 + 1 = i.val by omega] using hright.le) with
    ⟨hi, hsecondary⟩
  refine ⟨hi, hsecondary.trans_eq ?_⟩
  change b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) = _
  exact htriangle.symm

/-- Candidate relation extracted from a small right mixed defect. -/
theorem sectionFourLong_sourceSecondaryPrevious_le_rightMixed
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)))
    (hsmall : b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : ℚ) : ℚ)) : WithTop ℚ)) :
    ∃ hi : 1 < (longNextRepresentationIndex i).val ∧
        (longNextRepresentationIndex i).val + 1 < n + 1,
      a.representationSecondaryPreviousDefect b
          (longNextRepresentationIndex i) hi ≤
        b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  let p := longNextRepresentationIndex i
  let Y : ℚ := 2 * (ramificationIndex K : ℚ) +
    (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
    (b.order ⟨i.val, by omega⟩ : ℚ)
  have htriangle := a.sectionFourLong_rightMixed_eq_middleComparison_of_le_threshold
    b c i htrigger hright hsquare (by simpa only [Y] using hsmall)
  have hcomparison : a.truncatedPrefixDefect b 1 p.val p.val ≤
      (Y : WithTop ℚ) := by
    change a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) ≤ _
    rw [← htriangle]
    simpa only [Y] using hsmall
  have hhalf : (Y : WithTop ℚ) < a.representationHalfGap b p := by
    simpa only [p, Y] using
      a.sectionFourLong_rightThreshold_lt_halfGap b c i htrigger hright
  have hprimary : (Y : WithTop ℚ) <
      a.representationPrimaryDefect b p := by
    simpa only [p, Y] using
      a.sectionFourLong_rightThreshold_lt_primary b c i htrigger
  rcases a.representationSecondaryPreviousDefect_le_of_two_candidates_gt
      b hab.defectCondition p (Y : WithTop ℚ) hcomparison hhalf hprimary
      (by
        intro hi
        simpa only [p, longNextRepresentationIndex,
          show i.val + 1 - 2 = i.val - 1 by omega] using hleft.le) with
    ⟨hi, hsecondary⟩
  refine ⟨hi, hsecondary.trans_eq ?_⟩
  change a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) = _
  exact htriangle.symm

/-- The first half of the contradiction on lines 2743--2758: a small
left mixed defect forces the right mixed defect below its own threshold. -/
theorem sectionFourLong_rightMixed_le_of_leftMixed_le
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)))
    (hsmall : a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ)) :
    b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : ℚ) : ℚ)) : WithTop ℚ) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  let p := longPreviousRepresentationIndex i
  let X : ℚ := 2 * (ramificationIndex K : ℚ) +
    (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
    (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ)
  let Y : ℚ := 2 * (ramificationIndex K : ℚ) +
    (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
    (b.order ⟨i.val, by omega⟩ : ℚ)
  let DAB := a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
  let DBC := b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)
  have htriangle := a.sectionFourLong_leftMixed_eq_middleComparison_of_le_threshold
    b c i htrigger hleft hsquare (by simpa only [DAB, X] using hsmall)
  have hcomparison : b.truncatedPrefixDefect c 1 p.val p.val ≤
      (X : WithTop ℚ) := by
    change b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) ≤ _
    rw [← htriangle]
    simpa only [DAB, X] using hsmall
  have hhalf : (X : WithTop ℚ) < b.representationHalfGap c p := by
    simpa only [p, X] using
      a.sectionFourLong_leftThreshold_lt_halfGap b c i htrigger hleft
  have hprimary : (X : WithTop ℚ) <
      b.representationPrimaryDefect c p := by
    simpa only [p, X] using
      a.sectionFourLong_leftThreshold_lt_primary b c i htrigger
  rcases b.representationSecondaryCurrentDefect_le_of_two_candidates_gt
      c hbc.defectCondition p (X : WithTop ℚ) hcomparison hhalf hprimary
      (by
        intro hi
        change c.order ⟨i.val - 2, by omega⟩ ≤
          b.order ⟨i.val - 1 + 1, hi.2⟩
        simpa only [show i.val - 1 + 1 = i.val by omega] using hright.le) with
    ⟨hi, hsecondary⟩
  have hiThree : 3 ≤ i.val := by
    have hip : 1 < i.val - 1 := by
      simpa only [p, longPreviousRepresentationIndex] using hi.1
    omega
  let shift : ℚ :=
    ((b.order ⟨i.val - 1, by omega⟩ +
      b.order ⟨i.val, by omega⟩ -
      c.order ⟨i.val - 3, by omega⟩ -
      c.order ⟨i.val - 2, by omega⟩ : Int) : ℚ)
  have hshifted : (shift : WithTop ℚ) + DBC ≤ DAB := by
    calc
      (shift : WithTop ℚ) + DBC =
          b.representationSecondaryCurrentDefect c p hi := by
        change (shift : WithTop ℚ) + DBC =
          (((((b.order ⟨i.val - 1, by omega⟩ +
            b.order ⟨i.val - 1 + 1, hi.2⟩ -
            c.order ⟨i.val - 1 - 2, by omega⟩ -
            c.order ⟨i.val - 1 - 1, by omega⟩ : Int) : ℚ)) :
              WithTop ℚ) +
            b.truncatedPrefixDefect c (-1)
              (i.val - 1 + 2) (i.val - 1))
        simp only [shift, DBC,
          show i.val - 1 + 1 = i.val by omega,
          show i.val - 1 + 2 = i.val + 1 by omega,
          show i.val - 1 - 1 = i.val - 2 by omega,
          show i.val - 1 - 2 = i.val - 3 by omega]
      _ ≤ b.truncatedPrefixDefect c 1 p.val p.val := hsecondary
      _ = DAB := by
        change b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) = DAB
        simpa only [DAB] using htriangle.symm
  have hDABne : DAB ≠ ⊤ := by
    intro htop
    have hsmall' : DAB ≤ (X : WithTop ℚ) := by
      simpa only [DAB, X] using hsmall
    rw [htop] at hsmall'
    simp at hsmall'
  have hDBCne : DBC ≠ ⊤ := by
    intro htop
    have htopDAB : DAB = ⊤ := by
      rw [htop] at hshifted
      simpa using hshifted
    exact hDABne htopDAB
  have hsmallQ : DAB.untop hDABne ≤ X := by
    have hsmall' : DAB ≤ (X : WithTop ℚ) := by
      simpa only [DAB, X] using hsmall
    rw [← WithTop.coe_untop DAB hDABne] at hsmall'
    norm_cast at hsmall'
  have hshiftedQ : shift + DBC.untop hDBCne ≤ DAB.untop hDABne := by
    rw [← WithTop.coe_untop DAB hDABne,
      ← WithTop.coe_untop DBC hDBCne] at hshifted
    norm_cast at hshifted
  let gap : Fin n := ⟨i.val - 3, by
    omega⟩
  have hgapLower := c.orderGap_ge_neg_two_mul_e gap
  have hgapDef : c.orderGap gap =
      c.order ⟨i.val - 2, by omega⟩ -
        c.order ⟨i.val - 3, by omega⟩ := by
    unfold orderGap
    have hsucc : gap.succ = (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [gap, Fin.val_succ]
      omega
    have hcast : gap.castSucc =
        (⟨i.val - 3, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  rw [hgapDef] at hgapLower
  have hcrossOrder := htrigger.2.1
  have hpreviousStrict :
      c.order ⟨i.val - 3, by omega⟩ <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    omega
  have hDBCQ : DBC.untop hDBCne ≤ Y := by
    dsimp only [shift, X, Y] at hshiftedQ hsmallQ ⊢
    push_cast at hshiftedQ hsmallQ ⊢
    have hpreviousStrictQ :
        (c.order ⟨i.val - 3, by omega⟩ : ℚ) <
          (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) := by
      exact_mod_cast hpreviousStrict
    linarith
  have hDBCtop : DBC ≤ (Y : WithTop ℚ) := by
    rw [← WithTop.coe_untop DBC hDBCne]
    exact_mod_cast hDBCQ
  simpa only [DBC, Y] using hDBCtop

/-- The reverse implication on lines 2759--2763: a small right mixed
defect forces the left mixed defect below its threshold. -/
theorem sectionFourLong_leftMixed_le_of_rightMixed_le
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)))
    (hsmall : b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : ℚ) : ℚ)) : WithTop ℚ)) :
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  let X : ℚ := 2 * (ramificationIndex K : ℚ) +
    (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
    (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ)
  let Y : ℚ := 2 * (ramificationIndex K : ℚ) +
    (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
    (b.order ⟨i.val, by omega⟩ : ℚ)
  let DAB := a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
  let DBC := b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)
  rcases a.sectionFourLong_sourceSecondaryPrevious_le_rightMixed
      b c hab i htrigger hleft hright hsquare (by
        simpa only [DBC, Y] using hsmall) with ⟨hi, hsecondary⟩
  have hnextBound : i.val + 2 < n + 1 := by
    simpa only [longNextRepresentationIndex] using hi.2
  let shift : ℚ :=
    ((a.order ⟨i.val + 1, i.succ_lt_large⟩ +
      a.order ⟨i.val + 2, hnextBound⟩ -
      b.order ⟨i.val - 1, by omega⟩ -
      b.order ⟨i.val, by omega⟩ : Int) : ℚ)
  have hshifted : (shift : WithTop ℚ) + DAB ≤ DBC := by
    simpa only [shift, DAB, DBC, longNextRepresentationIndex,
      representationSecondaryPreviousDefect,
      show i.val + 1 - 1 = i.val by omega,
      show i.val + 1 - 2 = i.val - 1 by omega,
      show i.val + 1 + 1 = i.val + 2 by omega] using hsecondary
  have hDBCne : DBC ≠ ⊤ := by
    intro htop
    have hsmall' : DBC ≤ (Y : WithTop ℚ) := by
      simpa only [DBC, Y] using hsmall
    rw [htop] at hsmall'
    have hne : (Y : WithTop ℚ) ≠ ⊤ := WithTop.coe_ne_top
    exact hne (top_unique hsmall')
  have hDABne : DAB ≠ ⊤ := by
    intro htop
    have htopDBC : DBC = ⊤ := by
      rw [htop] at hshifted
      exact top_unique (by simpa using hshifted)
    exact hDBCne htopDBC
  have hsmallQ : DBC.untop hDBCne ≤ Y := by
    have hsmall' : DBC ≤ (Y : WithTop ℚ) := by
      simpa only [DBC, Y] using hsmall
    rw [← WithTop.coe_untop DBC hDBCne] at hsmall'
    norm_cast at hsmall'
  have hshiftedQ : shift + DAB.untop hDABne ≤ DBC.untop hDBCne := by
    rw [← WithTop.coe_untop DAB hDABne,
      ← WithTop.coe_untop DBC hDBCne] at hshifted
    norm_cast at hshifted
  let gap : Fin n := ⟨i.val + 1, by omega⟩
  have hgapLower := a.orderGap_ge_neg_two_mul_e gap
  have hgapDef : a.orderGap gap =
      a.order ⟨i.val + 2, hnextBound⟩ -
        a.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    unfold orderGap
    have hsucc : gap.succ =
        (⟨i.val + 2, hnextBound⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hcast : gap.castSucc =
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  rw [hgapDef] at hgapLower
  have hcrossOrder := htrigger.2.1
  have hnextStrict :
      c.order ⟨i.val - 2, by omega⟩ <
        a.order ⟨i.val + 2, hnextBound⟩ := by
    omega
  have hDABQ : DAB.untop hDABne ≤ X := by
    dsimp only [shift, X, Y] at hshiftedQ hsmallQ ⊢
    push_cast at hshiftedQ hsmallQ ⊢
    have hnextStrictQ :
        (c.order ⟨i.val - 2, by omega⟩ : ℚ) <
          (a.order ⟨i.val + 2, hnextBound⟩ : ℚ) := by
      exact_mod_cast hnextStrict
    linarith
  have hDABtop : DAB ≤ (X : WithTop ℚ) := by
    rw [← WithTop.coe_untop DAB hDABne]
    exact_mod_cast hDABQ
  simpa only [DAB, X] using hDABtop

/-- The two mixed defects cannot simultaneously lie below their respective
middle-branch thresholds.  Expanding the two forced secondary candidates
cancels the defects and contradicts the long trigger after the two adjacent
good-BONG gap bounds are applied. -/
theorem sectionFourLong_not_bothMixed_le_threshold
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)))
    (hsmallAB : a.truncatedPrefixDefect b (-1)
      (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ))
    (hsmallBC : b.truncatedPrefixDefect c (-1)
      (i.val + 1) (i.val - 1) ≤
      (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : ℚ) : ℚ)) : WithTop ℚ)) : False := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  rcases a.sectionFourLong_middleSecondaryCurrent_le_leftMixed
      b c hbc i htrigger hleft hright hsquare hsmallAB with
    ⟨hiPrevious, hprevious⟩
  rcases a.sectionFourLong_sourceSecondaryPrevious_le_rightMixed
      b c hab i htrigger hleft hright hsquare hsmallBC with
    ⟨hiNext, hnext⟩
  let DAB := a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
  let DBC := b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)
  let previousShift : ℚ :=
    ((b.order ⟨i.val - 1, by omega⟩ +
      b.order ⟨i.val, by omega⟩ -
      c.order ⟨i.val - 3, by omega⟩ -
      c.order ⟨i.val - 2, by omega⟩ : Int) : ℚ)
  let nextShift : ℚ :=
    ((a.order ⟨i.val + 1, i.succ_lt_large⟩ +
      a.order ⟨i.val + 2, by
        simpa only [longNextRepresentationIndex] using hiNext.2⟩ -
      b.order ⟨i.val - 1, by omega⟩ -
      b.order ⟨i.val, by omega⟩ : Int) : ℚ)
  have hiThree : 3 ≤ i.val := by
    have h : 1 < i.val - 1 := by
      simpa only [longPreviousRepresentationIndex] using hiPrevious.1
    omega
  have hnextBound : i.val + 2 < n + 1 := by
    simpa only [longNextRepresentationIndex] using hiNext.2
  have hpreviousExpanded :
      (previousShift : WithTop ℚ) + DBC ≤ DAB := by
    simpa only [previousShift, DAB, DBC,
      longPreviousRepresentationIndex,
      representationSecondaryCurrentDefect,
      show i.val - 1 + 1 = i.val by omega,
      show i.val - 1 + 2 = i.val + 1 by omega,
      show i.val - 1 - 1 = i.val - 2 by omega,
      show i.val - 1 - 2 = i.val - 3 by omega] using hprevious
  have hnextExpanded : (nextShift : WithTop ℚ) + DAB ≤ DBC := by
    simpa only [nextShift, DAB, DBC, longNextRepresentationIndex,
      representationSecondaryPreviousDefect,
      show i.val + 1 - 1 = i.val by omega,
      show i.val + 1 - 2 = i.val - 1 by omega,
      show i.val + 1 + 1 = i.val + 2 by omega] using hnext
  have hDABne : DAB ≠ ⊤ := by
    intro htop
    have hfinite := hsmallAB
    change DAB ≤ (show WithTop ℚ from
      (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ)) at hfinite
    rw [htop] at hfinite
    have hne : ((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ) :
        WithTop ℚ) ≠ ⊤ := WithTop.coe_ne_top
    exact hne (top_unique hfinite)
  have hDBCne : DBC ≠ ⊤ := by
    intro htop
    have hfinite := hsmallBC
    change DBC ≤ (show WithTop ℚ from
      (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
        (b.order ⟨i.val, by omega⟩ : ℚ) : ℚ)) : WithTop ℚ)) at hfinite
    rw [htop] at hfinite
    have hne : ((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
        (b.order ⟨i.val, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) ≠ ⊤ :=
      WithTop.coe_ne_top
    exact hne (top_unique hfinite)
  have hpreviousQ : previousShift + DBC.untop hDBCne ≤
      DAB.untop hDABne := by
    rw [← WithTop.coe_untop DAB hDABne,
      ← WithTop.coe_untop DBC hDBCne] at hpreviousExpanded
    norm_cast at hpreviousExpanded
  have hnextQ : nextShift + DAB.untop hDABne ≤
      DBC.untop hDBCne := by
    rw [← WithTop.coe_untop DAB hDABne,
      ← WithTop.coe_untop DBC hDBCne] at hnextExpanded
    norm_cast at hnextExpanded
  have hsumQ :
      (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) +
          (a.order ⟨i.val + 2, hnextBound⟩ : ℚ) ≤
        (c.order ⟨i.val - 3, by omega⟩ : ℚ) +
          (c.order ⟨i.val - 2, by omega⟩ : ℚ) := by
    dsimp only [previousShift, nextShift] at hpreviousQ hnextQ
    push_cast at hpreviousQ hnextQ
    linarith
  let sourceGap : Fin n := ⟨i.val + 1, by omega⟩
  have hsourceGap := a.orderGap_ge_neg_two_mul_e sourceGap
  have hsourceGapDef : a.orderGap sourceGap =
      a.order ⟨i.val + 2, hnextBound⟩ -
        a.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    unfold orderGap
    have hsucc : sourceGap.succ =
        (⟨i.val + 2, hnextBound⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hcast : sourceGap.castSucc =
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  rw [hsourceGapDef] at hsourceGap
  let targetGap : Fin n := ⟨i.val - 3, by omega⟩
  have htargetGap := c.orderGap_ge_neg_two_mul_e targetGap
  have htargetGapDef : c.orderGap targetGap =
      c.order ⟨i.val - 2, by omega⟩ -
        c.order ⟨i.val - 3, by omega⟩ := by
    unfold orderGap
    have hsucc : targetGap.succ =
        (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [targetGap, Fin.val_succ]
      omega
    have hcast : targetGap.castSucc =
        (⟨i.val - 3, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  rw [htargetGapDef] at htargetGap
  have hsumInt :
      a.order ⟨i.val + 1, i.succ_lt_large⟩ +
          a.order ⟨i.val + 2, hnextBound⟩ ≤
        c.order ⟨i.val - 3, by omega⟩ +
          c.order ⟨i.val - 2, by omega⟩ := by
    exact_mod_cast hsumQ
  exact (not_lt_of_ge (show
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
        c.order ⟨i.val - 2, by omega⟩ +
          2 * (ramificationIndex K : Int) by omega)) htrigger.2.1

/-- Section 4(iv), first strict mixed-defect estimate. -/
theorem sectionFourLong_leftMixed_gt_threshold
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1))) :
    (((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (a.order ⟨i.val + 1, i.succ_lt_large⟩ : ℚ) : ℚ)) :
        WithTop ℚ) <
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) := by
  by_contra hnot
  have hsmallAB := le_of_not_gt hnot
  have hsmallBC := a.sectionFourLong_rightMixed_le_of_leftMixed_le
    b c hbc i htrigger hleft hright hsquare hsmallAB
  exact a.sectionFourLong_not_bothMixed_le_threshold b c hab hbc i
    htrigger hleft hright hsquare hsmallAB hsmallBC

/-- Section 4(iv), second strict mixed-defect estimate. -/
theorem sectionFourLong_rightMixed_gt_threshold
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1))) :
    (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ : ℚ) -
        (b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : ℚ) : ℚ)) : WithTop ℚ) <
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
  by_contra hnot
  have hsmallBC := le_of_not_gt hnot
  have hsmallAB := a.sectionFourLong_leftMixed_le_of_rightMixed_le
    b c hab i htrigger hleft hright hsquare hsmallBC
  exact a.sectionFourLong_not_bothMixed_le_threshold b c hab hbc i
    htrigger hleft hright hsquare hsmallAB hsmallBC

/-- Section 4(iv), completed middle-branch representation certificate. -/
theorem sectionFourLongCertificate_throughCurrent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hleft : b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ < a.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hright : c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ < b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1))) :
    LongRepresentationCertificate a b c i := by
  apply a.sectionFourLongCertificate_throughCurrent_of_defectBounds
    b c hab hbc i hleft hright
  · exact a.sectionFourLong_leftMixed_gt_threshold b c hab hbc i
      htrigger hleft hright hsquare
  · exact a.sectionFourLong_rightMixed_gt_threshold b c hab hbc i
      htrigger hleft hright hsquare

end BONG.GoodBONG

end Bong
