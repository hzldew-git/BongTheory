/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIIRight
import Bong.Bong.Beli2019Remark613TypeIIIRightAlphaOfCenter
import Bong.Bong.Beli2019Lemma69TypeIIIRightValueOfCenter
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapPrefix

/-!
# Beli (2019), Lemma 7.9(ii): overlap case 7

The right-profile candidate comparisons use the overlap central alpha
equalities, while the strict comparison-order branch uses the type-II prefix
parity supplied by the central-gap-one profile.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- Coercions through `WithTop` meet the one-unit right-profile shift here.
/-- The comparison primary candidate is bounded by the source primary
candidate in overlap case 7. -/
theorem lemma79_typeIII_overlap_right_primary_le_sourcePrimary
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hlast : D.outer.last = n + 1)
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
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i := by
  have horderEntry := D.outer.source_rightOdd_eq_target_add_one
    D.no_gap_two i.val (by omega) hbeforeLast.le hodd
  have hgapOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact horderEntry
  have hnextAlpha :=
    a.beli2019Remark613_typeIII_overlap_targetRightAlpha_eq_one
      b D hlast horder hdefect htotal hoverlap
        i.val hright hbeforeLast hodd
  have hfarBound : i.val + 1 < n + 2 := by
    rw [hlast] at hbeforeLast
    omega
  have hprefixOne :
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
        ((1 : ℚ) : WithTop ℚ) := by
    calc
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
          b.prefixAlphaCap (i.val + 1) :=
        b.truncatedPrefixDefect_le_leftCap c (-1) (i.val + 1)
          (i.val - 1)
      _ = (b.alphaValue ⟨i.val, by omega⟩ : WithTop ℚ) :=
        b.prefixAlphaCap_of_internal (by omega) hfarBound
      _ = ((1 : ℚ) : WithTop ℚ) := by rw [hnextAlpha]
  have hsourceNonneg := a.truncatedPrefixDefect_nonneg
    c (-1) (i.val + 1) (i.val - 1)
  have hcoefficientInt :
      (b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) + 1 =
        a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ := by
    omega
  have hcoefficient :
      (((b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((1 : ℚ) : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationPrimaryDefect
  calc
    _ ≤ (((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := add_le_add_right hprefixOne _
    _ = (((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) :=
      hcoefficient
    _ ≤ _ := le_add_of_nonneg_right hsourceNonneg

set_option maxHeartbeats 3000000 in
-- The nonterminal branch transports the alpha index through Remark 6.16.
/-- The comparison secondary candidate is bounded by the source secondary
candidate in overlap case 7. -/
theorem lemma79_typeIII_overlap_right_secondary_le_sourceSecondary
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
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi := by
  have hpairEntries := D.outer.rightOdd_pair_eq i.val
    (by omega) hbeforeLast.le hodd
  have hsumOrders :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hpairEntries
  have hprefix :
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
    by_cases hfull : i.val + 2 = n + 2
    · simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change a b c 1 (i.val - 2)).le
    · have hfarBound : i.val + 2 < n + 2 := by omega
      let farIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
      have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
      rcases hleftEven with ⟨e, he⟩
      rcases hodd with ⟨d, hd⟩
      have hfarEven : Even farIdx.val := by
        refine ⟨e + d + 2, ?_⟩
        simp only [farIdx]
        rw [D.adjacent] at hd
        omega
      have hfarStart : D.outer.transition.lastZero + 2 ≤ farIdx.val := by
        simp only [farIdx]
        rw [← D.adjacent]
        omega
      have hAlpha : a.representationAlphaValue b farIdx =
          b.alphaValue ⟨farIdx.val - 1, by
            simp only [farIdx]
            omega⟩ := by
        simpa only [farIdx] using
          (a.beli2019Lemma69_ii_typeIII_targetRightValue_of_overlap
            b D hfirst hlast horder hdefect htotal hoverlap
              farIdx.val hfarStart hfarEven hfarBound)
      have hformula := beli2019Remark616_rightMixedPrefix_at
        a b c hdefect farIdx hAlpha 1 (i.val - 2)
      calc
        b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) =
            min (a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2))
              (b.alphaValue ⟨i.val + 1, by omega⟩ : WithTop ℚ) := by
          simpa only [farIdx, show i.val + 2 - 1 = i.val + 1 by omega]
            using hformula
        _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
          min_le_left _ _
  have hcoefficientInt :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ := by
    omega
  have hcoefficient :
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationSecondaryDefect
  rw [← hcoefficient]
  exact add_le_add_right hprefix _

set_option maxHeartbeats 3000000 in
-- The three candidate comparisons contain many dependent Fin coercions.
/-- In overlap case 7, the comparison representation invariant is no larger
than the corresponding source invariant. -/
theorem lemma79_typeIII_overlap_right_alpha_le_sourceAlpha
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
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) := by
  have hhalf := lemma79_typeIII_right_halfGap_le_sourceHalfGap
    a b c D i hright hbeforeLast hodd
  have hprimary := lemma79_typeIII_overlap_right_primary_le_sourcePrimary
    a b c D hlast horder hdefect htotal hoverlap
      i hright hbeforeLast hodd
  rw [b.coe_representationAlphaValue c i,
    a.coe_representationAlphaValue c i,
    b.representationAlpha_eq_min_halfGap_prime c i,
    a.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min hhalf
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 2
  · rw [b.representationAlphaPrime_eq_min_primary_secondary c i hi,
      a.representationAlphaPrime_eq_min_primary_secondary c i hi]
    exact min_le_min hprimary
      (lemma79_typeIII_overlap_right_secondary_le_sourceSecondary
        a b c D hfirst hlast horder hdefect htotal hoverlap
          i hi hright hbeforeLast hodd)
  · rw [b.representationAlphaPrime_eq_primary_of_not_interior c i hi,
      a.representationAlphaPrime_eq_primary_of_not_interior c i hi]
    exact hprimary

set_option maxHeartbeats 3000000 in
-- The strict branch combines the source comparison with two parity zeros.
/-- Lemma 7.9(ii), case 7, for an overlapping type-II/III profile. -/
theorem beli2019Lemma79_ii_typeIII_overlap_caseSeven
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  rcases hleftEven with ⟨e, he⟩
  rcases hodd with ⟨d, hd⟩
  have hiEven : Even i.val := by
    refine ⟨e + d + 1, ?_⟩
    rw [D.adjacent] at hd
    omega
  have hiStart : D.outer.transition.lastZero + 2 ≤ i.val := by
    rw [← D.adjacent]
    omega
  have hAlpha : a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
    simpa only using
      (a.beli2019Lemma69_ii_typeIII_targetRightValue_of_overlap
        b D hfirst hlast horderAB hdefectAB htotal hoverlap
          i.val hiStart hiEven i.lt_large)
  by_cases hcurrent : b.order ⟨i.val - 1, by omega⟩ ≤
      c.order ⟨i.val - 1, by omega⟩
  · apply lemma79_ii_of_rightMixedPrefix_branches
      a b c hdefectAB hdefectAC i hAlpha
    · intro _
      exact lemma79_typeIII_overlap_right_alpha_le_sourceAlpha
        a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
          i hright hbeforeLast ⟨d, hd⟩
    · intro _
      exact lemma79_rightProfile_beta_bound_of_target_le_comparison
        a b c D.outer i hright hbeforeLast ⟨d, hd⟩ hcurrent
  · have hstrict : c.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val - 1, by omega⟩ := lt_of_not_ge hcurrent
    have heq :=
      lemma79_typeIII_overlap_right_comparisonPrefixes_eq_of_comparison_lt_target
        a b c D hfirst hoverlap hnorm i hright hbeforeLast
          ⟨d, hd⟩ hstrict
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤
          (a.representationAlphaValue c i : WithTop ℚ) :=
        lemma79_typeIII_overlap_right_alpha_le_sourceAlpha
          a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
            i hright hbeforeLast ⟨d, hd⟩
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val := hdefectAC i
      _ = b.truncatedPrefixDefect c 1 i.val i.val := heq.symm

end BONG.GoodBONG

end Bong
