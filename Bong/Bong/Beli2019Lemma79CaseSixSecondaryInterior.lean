/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixPrimaryCandidates

/-!
# Beli (2019), Lemma 7.9(ii), case 6: secondary candidates

Before the last right-profile difference, the current target order is one
above the source and the following source order is one above the target.
Thus the adjacent sums agree.  The far target alpha is one, so its mixed
prefix is at most one and hence at most the nonnegative source prefix plus
one.  Even-distance parity also covers the endpoint where the far boundary
is the last difference.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At a case-6 coordinate whose next coordinate remains in the right
profile, the source and target adjacent order sums agree. -/
theorem lemma79_caseSix_profile_adjacentSum_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hright : O.transition.firstTwo - 1 ≤ i.val)
    (hnextLast : i.val + 1 ≤ O.last)
    (heven : Even (i.val - (O.transition.firstTwo - 1))) :
    b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ := by
  have hcurrent := O.target_rightEven_eq_source_add_one
    hnoTwo i.val hright (by omega) heven
  have hnextOdd : Odd
      (i.val + 1 - (O.transition.firstTwo - 1)) := by
    rcases heven with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hnext := O.source_rightOdd_eq_target_add_one hnoTwo
    (i.val + 1) (by omega) hnextLast hnextOdd
  have hcurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrent
  have hnextOrder : a.order ⟨i.val + 1, hi.2⟩ =
      b.order ⟨i.val + 1, hi.2⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hnext
  omega

/-- Equal adjacent sums and a far target alpha equal to one give the
one-unit secondary comparison through the last right-profile difference.
-/
theorem lemma79_caseSix_profile_secondary_le_add_one
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hright : O.transition.firstTwo - 1 ≤ i.val)
    (hfarThrough : i.val + 2 ≤ O.last)
    (heven : Even (i.val - (O.transition.firstTwo - 1)))
    (hbetaFar : b.alphaValue ⟨i.val + 1, by
      have hbound := O.lastDifference.bound
      omega⟩ = 1) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  have hsum := lemma79_caseSix_profile_adjacentSum_eq
    a b O hnoTwo i hi hright (by omega) heven
  have hfarBound : i.val + 2 < n + 2 :=
    hfarThrough.trans_lt O.lastDifference.bound
  have htarget := b.truncatedPrefixDefect_le_leftCap
    c 1 (i.val + 2) (i.val - 2)
  rw [b.prefixAlphaCap_of_internal (by omega) hfarBound] at htarget
  have htargetOne : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤ ((1 : ℚ) : WithTop ℚ) := by
    exact htarget.trans (by exact_mod_cast hbetaFar.le)
  have hsource := a.truncatedPrefixDefect_nonneg
    c 1 (i.val + 2) (i.val - 2)
  have hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤
    a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) +
      ((1 : ℚ) : WithTop ℚ) := by
    calc
      _ ≤ ((1 : ℚ) : WithTop ℚ) := htargetOne
      _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) +
          ((1 : ℚ) : WithTop ℚ) := by
        simpa only [add_comm] using
          (le_add_of_nonneg_right hsource :
            ((1 : ℚ) : WithTop ℚ) ≤
              ((1 : ℚ) : WithTop ℚ) +
                a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2))
  exact representationSecondaryDefect_le_add_one_of_orderSum_eq
    a b c i hi hsum hprefix

set_option maxHeartbeats 3000000 in
-- Dependent far-boundary indices make the profile instantiation expensive.
/-- The nonterminal secondary comparison for type II. -/
theorem beli2019Lemma79_typeII_caseSix_secondary_le_add_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  have hfarThrough : i.val + 2 ≤ D.outer.last := by
    rcases heven with ⟨d, hd⟩
    rcases D.outer.right_even_distance with ⟨e, he⟩
    omega
  have hfarBound : i.val + 2 < n + 2 := by
    rw [hlast] at hfarThrough
    omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarRight : D.outer.transition.firstTwo - 1 ≤ farIdx.val := by
    simp only [farIdx]
    omega
  have hfarEven : Even
      (farIdx.val - (D.outer.transition.firstTwo - 1)) := by
    rcases heven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hbeta := beli2019Lemma79_typeII_caseSix_beta_eq_one
    a b D hlast horder hdefect htotal farIdx hfarRight
      (by simpa only [farIdx] using hfarThrough) hfarEven
  apply lemma79_caseSix_profile_secondary_le_add_one
    a b c D.outer D.no_gap_two i hi hright hfarThrough heven
  simpa only [farIdx, show i.val + 2 - 1 = i.val + 1 by omega]
    using hbeta

set_option maxHeartbeats 4000000 in
-- The type-III endpoint data add a second layer of dependent indices.
/-- The nonterminal secondary comparison for nonoverlapping type III.
-/
theorem beli2019Lemma79_typeIII_caseSix_secondary_le_add_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
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
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  have hfarThrough : i.val + 2 ≤ D.outer.last := by
    rcases heven with ⟨d, hd⟩
    rcases D.outer.right_even_distance with ⟨e, he⟩
    omega
  have hfarBound : i.val + 2 < n + 2 := by
    rw [hlast] at hfarThrough
    omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarRight : D.outer.transition.firstTwo - 1 ≤ farIdx.val := by
    simp only [farIdx]
    omega
  have hfarEven : Even
      (farIdx.val - (D.outer.transition.firstTwo - 1)) := by
    rcases heven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hbeta := beli2019Lemma79_typeIII_caseSix_beta_eq_one
    a b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      farIdx hfarRight (by simpa only [farIdx] using hfarThrough) hfarEven
  apply lemma79_caseSix_profile_secondary_le_add_one
    a b c D.outer D.no_gap_two i hi hright hfarThrough heven
  simpa only [farIdx, show i.val + 2 - 1 = i.val + 1 by omega]
    using hbeta

end BONG.GoodBONG

end Bong
