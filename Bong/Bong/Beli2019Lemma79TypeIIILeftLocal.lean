/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenLeftComplete
import Bong.Bong.Beli2019Lemma79DefectTypeIIIOdd
import Bong.Bong.Beli2019Lemma78AlphasLocal
import Bong.Bong.Beli2019Lemma79NextAlphaLocal
import Bong.Bong.Beli2019Lemma69TypeIIIRightValueLocal

/-!
# Beli (2019), Lemma 7.9(ii): local type-III left branches

The statements in this file replace the former full-rank hypothesis on the
last unequal order by the local central alpha equalities of Lemma 7.8 and the
local tails of Lemma 6.9.  All profile combinatorics and candidate assembly
are inherited from the existing type-III proof.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Local form of Lemma 6.9(ii) on the even source part of a nonoverlapping
type-III profile. -/
theorem beli2019Lemma69_ii_typeIII_sourceLeftValue_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : Nat) (hiTwo : 2 ≤ i)
    (hiLeft : i ≤ D.outer.transition.lastZero) (hiEven : Even i) :
    a.representationAlphaValue b
        ⟨i, by omega, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ =
      a.alphaValue ⟨i - 1, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ := by
  have hcenter :=
    (a.beli2019Lemma78_alphas_and_gap_local b D hfirst horder hdefect
      htotal hnotOverlap hinitial).1
  exact a.beli2019Lemma69_ii_typeIII_sourceLeftValue_of_center
    b D hfirst hcenter hdefect i hiTwo hiLeft hiEven

/-- Local neighboring-alpha estimate on the nonoverlapping type-III left
profile. -/
theorem beli2019Lemma79_typeIII_even_left_alphaClose_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  have hcenter :=
    (a.beli2019Lemma78_alphas_and_gap_local b D hfirst horder hdefect
      htotal hnotOverlap hinitial).1
  apply lemma79_even_alphaClose_of_noGap_leftOuter
    a b D.outer hfirst D.no_gap_two i hiTwo hiEven hleft
  · exact a.lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
      b D hfirst hcenter i.val hiTwo hleft hiEven
  · apply a.beli2019Lemma69_i_typeIII_targetLeftTail_local
      b D hfirst horder hdefect htotal (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩

/-- Local alpha-shift identity on the nonoverlapping type-III left profile. -/
theorem beli2019Lemma79_typeIII_even_left_alphaShift_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero)
    (hsmall : b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ < 2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  have hcenter :=
    (a.beli2019Lemma78_alphas_and_gap_local b D hfirst horder hdefect
      htotal hnotOverlap hinitial).1
  apply lemma79_even_alphaShift_of_noGap_leftOuter
    a b D.outer hfirst D.no_gap_two i hiTwo hiEven hleft
  · exact a.lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
      b D hfirst hcenter i.val hiTwo hleft hiEven
  · apply a.beli2019Lemma69_i_typeIII_targetLeftTail_local
      b D hfirst horder hdefect htotal (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  · exact hsmall

/-- Lemma 7.9(ii), odd left branch, with no full-rank hypothesis on the last
unequal order. -/
theorem beli2019Lemma79_ii_typeIII_odd_left_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hbefore : i.val < D.outer.transition.lastZero + 1) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let k := i.val - 1
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  rcases hodd with ⟨d, hd⟩
  rcases hleftEven with ⟨e, he⟩
  have hkEven : Even k := ⟨d, by simp only [k]; omega⟩
  have hfarEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hfarLeft : i.val + 1 ≤ D.outer.transition.lastZero := by omega
  have hkLeft : k ≤ D.outer.transition.lastZero := by
    simp only [k]
    omega
  have hiNext : i.val + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hkBound : k < n + 2 := by
    simp only [k]
    omega
  have hkNextBound : k + 1 < n + 2 := by
    simp only [k]
    omega
  have hbPrevious := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two k hkLeft hkEven
  have hbFar := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two (i.val + 1) hfarLeft hfarEven
  have htwoStep : b.orderSequence.entryOrZero (i.val + 1) =
      b.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [k] using hbFar.trans hbPrevious.symm
  have hpreviousAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail_local
    b D hfirst hab hdefectAB htotal k hkLeft hkEven
  let alphaIndex : Fin (n + 1) := ⟨i.val, by omega⟩
  have hnextAlpha := b.nextAlphaValue_le_of_twoStep_eq
    alphaIndex i.pos (by simpa only [alphaIndex] using htwoStep) (by
      simpa only [alphaIndex, k] using hpreviousAlpha)
  have hnextAlpha' : b.alphaValue ⟨i.val, by omega⟩ ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ) := by
    simpa only [alphaIndex] using hnextAlpha
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
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
  have hreferenceFirst : b.orderSequence.entryOrZero k ≤
      c.orderSequence.entryOrZero 0 := by
    rw [hbPrevious]
    exact hfirstOrder
  have hcMonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 k (Nat.zero_le k) hkBound hkEven
  have hcurrentK : b.orderSequence.entryOrZero k ≤
      c.orderSequence.entryOrZero k := hreferenceFirst.trans hcMonotone
  have hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≤
      c.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [k] using hcurrentK
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  have hpairACRaw := hacSequence.pairSum_le k (by omega)
  have hpairAC : a.orderSequence.entryOrZero k +
        a.orderSequence.entryOrZero (k + 1) ≤
      c.orderSequence.entryOrZero k +
        c.orderSequence.entryOrZero (k + 1) := by
    simpa only [BeliOrderSequence.entryOrZero_of_lt _ hkBound,
      BeliOrderSequence.entryOrZero_of_lt _ hkNextBound,
      orderSequence_at] using hpairACRaw
  have hpairParity : Even (D.outer.transition.lastZero - k) :=
    ⟨e - d, by simp only [k]; omega⟩
  have hpairAB := D.outer.leftPairEq k (by omega) hpairParity
  have hpairK : b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) ≤
      c.orderSequence.entryOrZero k +
        c.orderSequence.entryOrZero (k + 1) := by
    rw [← hpairAB]
    exact hpairAC
  have hpair : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero i.val := by
    simpa only [k, Nat.sub_add_cancel i.pos] using hpairK
  let T := b.orderSequence.entryOrZero k
  have hbZero := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two 0 (Nat.zero_le _) ⟨0, by omega⟩
  have htargetFirst : T ≤ b.orderSequence.entryOrZero 0 := by
    dsimp only [T]
    rw [hbPrevious, hbZero]
  have hparity : b.orderSequence.entryOrZero (i.val - 1) =
      c.orderSequence.entryOrZero (i.val - 1) →
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
    intro heqCurrent
    have hbParity := b.prefixSum_modEq_mul_of_current_le_reference_le_first
      T k hkBound htargetFirst le_rfl
    have hcCurrent : c.orderSequence.entryOrZero k ≤ T := by
      dsimp only [T]
      simpa only [k] using heqCurrent.symm.le
    have hcParity := c.prefixSum_modEq_mul_of_current_le_reference_le_first
      T k hkBound hreferenceFirst hcCurrent
    have hcombined := hbParity.trans hcParity.symm
    simpa only [k, Nat.sub_add_cancel i.pos] using hcombined
  have heven : b.orderSequence.entryOrZero (i.val - 1) =
      c.orderSequence.entryOrZero (i.val - 1) →
      Even (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)) := by
    intro heqCurrent
    exact b.comparisonPrefixProduct_order_even_of_prefixSum_modEq
      c i.val i.lt_large.le i.lt_large.le (hparity heqCurrent)
  exact b.lemma79_ii_of_odd_coordinate c i hiNext hnextAlpha'
    hcurrent hpair heven

/-- Local shifted secondary comparison in the strict even left interior. -/
theorem beli2019Lemma79_typeIII_even_left_secondary_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hfarBound : i.val + 2 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarEven : Even farIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hAlpha : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by
        have hb := farIdx.lt_large
        omega⟩ := by
    simpa only [farIdx] using
      (a.beli2019Lemma69_ii_typeIII_sourceLeftValue_local
        b D hfirst horder hdefect htotal hnotOverlap hinitial
          (i.val + 2) (by omega) hfarLeft hfarEven)
  have hclose := beli2019Lemma79_typeIII_even_left_alphaClose_local
    a b D hfirst horder hdefect htotal hnotOverlap hinitial
      farIdx (by simp only [farIdx]; omega) hfarEven hfarLeft
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefect i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlpha)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose)
  exact lemma79_even_leftOuter_secondary_le_add_two_of_prefix
    a b c D.outer hfirst i hi hiEven hfarLeft hprefix

/-- Local shifted secondary comparison at the even left transition. -/
theorem beli2019Lemma79_typeIII_even_leftBoundary_secondary_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hleftRaw := D.outer.transition.leftBoundary
  have hrightRaw := D.outer.transition.rightBoundary
  have hleft : b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero i.val + 1 := by
    simpa only [hboundary] using hleftRaw
  have hright : b.orderSequence.entryOrZero (i.val + 1) =
      a.orderSequence.entryOrZero (i.val + 1) + 1 := by
    rw [D.adjacent] at hrightRaw
    simpa only [hboundary,
      show D.outer.transition.lastZero + 2 - 1 =
        D.outer.transition.lastZero + 1 by omega] using hrightRaw
  have hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val +
        b.orderSequence.entryOrZero (i.val + 1) =
      a.orderSequence.entryOrZero i.val +
        a.orderSequence.entryOrZero (i.val + 1) + 2
    omega
  have hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤
    a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
    by_cases hfull : i.val + 2 = n + 2
    · simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change
          a b c 1 (i.val - 2)).le
    · have hfarBound : i.val + 2 < n + 2 := by omega
      let farIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
      have hfarStart : D.outer.transition.firstTwo ≤ farIdx.val := by
        simp only [farIdx]
        rw [D.adjacent, hboundary]
      have hfarParity :
          Odd (farIdx.val - (D.outer.transition.firstTwo - 1)) := by
        exact ⟨0, by simp only [farIdx]; rw [D.adjacent, hboundary]; omega⟩
      have hAlpha : a.representationAlphaValue b farIdx =
          b.alphaValue ⟨farIdx.val - 1, by
            have hb := farIdx.lt_large
            omega⟩ := by
        by_cases hafter : D.outer.last < farIdx.val
        · have hsuffix : ∀ k, farIdx.val ≤ k → k < n + 2 →
              a.orderSequence.entryOrZero k =
                b.orderSequence.entryOrZero k := by
            intro k hk hkn
            exact D.outer.lastDifference.after k (by omega) hkn
          exact a.beli2019Lemma63_sameRank_right_value
            b hdefect farIdx hsuffix
        · have hfarLast : farIdx.val < D.outer.last := by
            have hfarLE : farIdx.val ≤ D.outer.last := Nat.le_of_not_gt hafter
            by_contra hnot
            have hlastLE : D.outer.last ≤ farIdx.val := Nat.le_of_not_gt hnot
            have hfarEq : farIdx.val = D.outer.transition.firstTwo := by
              simp only [farIdx]
              rw [D.adjacent, hboundary]
            have hlastParity := D.outer.right_even_distance
            rcases hlastParity with ⟨d, hd⟩
            have hseparated := D.outer.transition.separated
            omega
          have htargetCenter :=
            (a.beli2019Lemma78_alphas_and_gap_local b D hfirst horder
              hdefect htotal hnotOverlap hinitial).2.1
          exact
            a.beli2019Lemma69_ii_typeIII_targetRightValue_of_center_local
              b D horder hdefect htotal htargetCenter farIdx.val
                hfarStart hfarParity hfarLast
      have hformula := beli2019Remark616_rightMixedPrefix_at
        a b c hdefect farIdx hAlpha 1 (i.val - 2)
      calc
        b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) =
            min (a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2))
              (b.alphaValue ⟨i.val + 1, by omega⟩ : WithTop ℚ) := by
          simpa only [farIdx,
            show i.val + 2 - 1 = i.val + 1 by omega] using hformula
        _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
          min_le_left _ _
  exact representationSecondaryDefect_le_add_two_of_orderSum_eq_add_two
    a b c i hi hsum hprefix

set_option maxHeartbeats 4000000 in
/-- Local beta estimate in the strict even left interior. -/
theorem beli2019Lemma79_typeIII_even_left_beta_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ := by
  have hiTwo : 2 ≤ i.val := by omega
  have hleft : i.val ≤ D.outer.transition.lastZero := by omega
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hbPrevious := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two (i.val - 2) (by omega) hpreviousEven
  have hbCurrent := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two i.val hleft hiEven
  have htwo : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hbPrevious.trans hbCurrent.symm
  have hsourceLe := b.orderGap_previous_le_twoE_of_twoStep
    i hiTwo htwo
  have hcross :=
    crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
      b c horderBC i hsourceLe
  by_cases hlarge : 2 * (ramificationIndex K : Int) ≤
      b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩
  · exact lemma79_even_beta_bound_of_large_sourceGap
      b c i hcross hlarge
  · have hsmall : b.orderGap ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ < 2 * (ramificationIndex K : Int) :=
      lt_of_not_ge hlarge
    have halpha := beli2019Lemma79_typeIII_even_left_alphaShift_local
      a b D hfirst horderAB hdefectAB htotal hnotOverlap
        hinitial i hiTwo hiEven hleft hsmall
    have hhalf := lemma79_even_leftOuter_halfGap_le_add_two
      a b c D.outer hfirst D.no_gap_two i hiEven hleft
    have hcurrentAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail_local
      b D hfirst horderAB hdefectAB htotal i.val hleft hiEven
    have hprimary := lemma79_even_leftOuter_primary_le_add_two
      a b c D.outer hfirst D.no_gap_two i hi.2 hiEven hleft
        hcurrentAlpha
    have hsecondary : ∀
        (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
        b.representationSecondaryDefect c i hi' ≤
          a.representationSecondaryDefect c i hi' +
            ((2 : ℚ) : WithTop ℚ) := by
      intro hi'
      exact beli2019Lemma79_typeIII_even_left_secondary_local
        a b c D hfirst horderAB hdefectAB htotal hnotOverlap
          hinitial i hi' hiEven hfarLeft
    exact lemma79_even_beta_bound_of_candidate_shifts
      a b c hdefectAC i halpha hhalf hprimary hsecondary

/-- Lemma 7.9(ii) in the strict even type-III left interior, locally. -/
theorem beli2019Lemma79_ii_typeIII_even_left_interior_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hbeta := beli2019Lemma79_typeIII_even_left_beta_local
    a b c D hfirst horderAB hdefectAB htotal hnotOverlap
      hinitial hdefectAC horderBC i hi hiEven hfarLeft
  exact beli2019Lemma79_ii_typeIII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven (by omega) hbeta

set_option maxHeartbeats 4000000 in
/-- Local beta estimate at the even type-III left transition. -/
theorem beli2019Lemma79_typeIII_even_leftBoundary_beta_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ := by
  have hiTwo : 2 ≤ i.val := by omega
  have hleft : i.val ≤ D.outer.transition.lastZero := hboundary.le
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hbPrevious := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two (i.val - 2) (by omega) hpreviousEven
  have hbCurrent := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two i.val hleft hiEven
  have htwo : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hbPrevious.trans hbCurrent.symm
  have hcurrentAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail_local
    b D hfirst horderAB hdefectAB htotal i.val hleft hiEven
  apply lemma79_even_leftOuter_beta_of_secondary
    a b c D.outer hfirst D.no_gap_two hdefectAC horderBC
      i hi hiEven hleft htwo hcurrentAlpha
  · intro hsmall
    exact beli2019Lemma79_typeIII_even_left_alphaShift_local
      a b D hfirst horderAB hdefectAB htotal hnotOverlap
        hinitial i hiTwo hiEven hleft hsmall
  · intro hi'
    exact beli2019Lemma79_typeIII_even_leftBoundary_secondary_local
      a b c D hfirst horderAB hdefectAB htotal hnotOverlap
        hinitial i hi' hiEven hboundary

/-- Lemma 7.9(ii) at the even type-III left transition, locally. -/
theorem beli2019Lemma79_ii_typeIII_even_leftBoundary_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hbeta := beli2019Lemma79_typeIII_even_leftBoundary_beta_local
    a b c D hfirst horderAB hdefectAB htotal hnotOverlap
      hinitial hdefectAC horderBC i hi hiEven hboundary
  exact beli2019Lemma79_ii_typeIII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven hboundary.le hbeta

/-- Lemma 7.9(ii) on the complete even type-III left interval, locally. -/
theorem beli2019Lemma79_ii_typeIII_even_left_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hi : 1 < i.val ∧ i.val + 1 < n + 2 := ⟨by omega, hiNext⟩
  by_cases hfar : i.val + 2 ≤ D.outer.transition.lastZero
  · exact beli2019Lemma79_ii_typeIII_even_left_interior_local
      a b c D hfirst horderAB hdefectAB htotal hnotOverlap
        hinitial hdefectAC horderBC hnorm i hi hiEven hfar
  · have hlastEven := D.outer.left_even_of_first_eq_zero hfirst
    rcases hiEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    have hboundary : i.val = D.outer.transition.lastZero := by omega
    exact beli2019Lemma79_ii_typeIII_even_leftBoundary_local
      a b c D hfirst horderAB hdefectAB htotal hnotOverlap
        hinitial hdefectAC horderBC hnorm i hi ⟨d, hd⟩ hboundary

end BONG.GoodBONG

end Bong
