/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenBoundarySecondary
import Bong.Bong.Beli2019Lemma69TypeIIIRightValueOfCenter
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapLeftAlpha

/-!
# Beli (2019), Lemma 7.9(ii): overlapping type-III left secondary terms

The strict-interior proof uses the source central alpha equality, and the
transition proof uses its target counterpart through reverse duality.  Both
are available in the central gap-one branch without the nonoverlap hypothesis.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
/-- The shifted secondary candidate in the strict left interior of an
overlapping type-III profile. -/
theorem beli2019Lemma79_typeIII_overlap_even_left_secondary
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
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
  have hcenter :=
    a.beli2019Lemma79_typeIII_overlap_sourceCenterAlpha_eq_one
      b D hfirst hdefect hoverlap
  have hAlpha : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by
        have hb := farIdx.lt_large
        omega⟩ := by
    simpa only [farIdx] using
      (a.beli2019Lemma69_ii_typeIII_sourceLeftValue_of_center
        b D hfirst hcenter hdefect (i.val + 2) (by omega)
          hfarLeft hfarEven)
  have hclose :=
    beli2019Lemma79_typeIII_overlap_even_left_alphaClose
      a b D hfirst hlast horder hdefect htotal hoverlap farIdx
        (by simp only [farIdx]; omega) hfarEven hfarLeft
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefect i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlpha)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose)
  exact lemma79_even_leftOuter_secondary_le_add_two_of_prefix
    a b c D.outer hfirst i hi hiEven hfarLeft hprefix

set_option maxHeartbeats 4000000 in
/-- The shifted secondary candidate at the left transition of an overlapping
type-III profile. -/
theorem beli2019Lemma79_typeIII_overlap_even_leftBoundary_secondary
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
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
      have hfarEven : Even farIdx.val := by
        rcases hiEven with ⟨d, hd⟩
        exact ⟨d + 1, by simp only [farIdx]; omega⟩
      have hAlpha :=
        a.beli2019Lemma69_ii_typeIII_targetRightValue_of_overlap
          b D hfirst hlast horder hdefect htotal hoverlap
            farIdx.val (by simp only [farIdx]; omega)
            hfarEven hfarBound
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

end BONG.GoodBONG

end Bong
