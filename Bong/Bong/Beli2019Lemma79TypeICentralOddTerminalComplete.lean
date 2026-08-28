/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeICentralTerminalComplete
import Bong.Bong.Beli2019Lemma79TypeISourceCentral
import Bong.Bong.Beli2019Lemma79TypeIRightSource
import Bong.Bong.Beli2019Lemma79TypeIRightSourceSecondary

/-!
# Beli (2019), Lemma 7.9(ii): terminal-complete odd central type-I branch

The complete central values from Lemma 6.9 control the primary mixed prefix.
For the secondary mixed prefix, the two-step boundary is either still central
or is the first coordinate after the right switch; both values are now
available without assuming that the right switch precedes the last unequal
order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Case 4 after discharging the target mixed-prefix branch, including a
terminal type-I profile. -/
theorem lemma79_ii_typeI_of_source_branch_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch)
    (hsource : a.truncatedPrefixDefect c 1 i.val i.val ≤
        (b.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : WithTop ℚ) →
      (b.representationAlphaValue c i : WithTop ℚ) ≤
        (a.representationAlphaValue c i : WithTop ℚ)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hAlpha :=
    beli2019Lemma69_ii_typeI_targetValue_from_conditions_complete
      a b D C hfirst horderAB hdefectAB i hodd hleft hright
  apply lemma79_ii_of_rightMixedPrefix_branches
    a b c hdefectAB hdefectAC i hAlpha hsource
  intro _
  exact lemma79_typeI_beta_bound_from_profile
    a b c D C hfirst horderBC hnorm i hodd hleft hright

set_option maxHeartbeats 3000000 in
-- Dependent indices at `i`, `i + 1`, and `i - 1` meet in this comparison.
/-- The primary source-candidate comparison on the complete odd central
type-I interval. -/
theorem lemma79_typeI_primary_le_sourcePrimary_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i := by
  rcases hodd with ⟨d, hd⟩
  rcases C.right_even with ⟨e, he⟩
  have hiRight : i.val < C.rightSwitch := by omega
  have hiNextBound : i.val + 1 < n + 2 := by
    have hr := C.right_le_last
    have hb := D.profile.lastDifference.bound
    omega
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNextBound, hiNextBound.le⟩
  have hnextEven : Even nextIdx.val :=
    ⟨d + 1, by simp only [nextIdx]; omega⟩
  have hnextValue :=
    (lemma69_typeI_central_values_from_conditions_complete
      a b D C hfirst horder hdefect nextIdx
        (by simp only [nextIdx]; omega)
        (by simp only [nextIdx]; omega)).2 hnextEven
  have hAlpha : a.representationAlphaValue b nextIdx =
      a.alphaValue ⟨nextIdx.val - 1, by
        have hi := nextIdx.lt_large
        omega⟩ := by
    apply WithTop.coe_injective
    rw [a.coe_representationAlphaValue b nextIdx]
    exact hnextValue
  have hclose := beli2019Lemma79_typeI_central_even_alphaShift_complete
    a b D C hfirst horder hdefect nextIdx hnextEven
      (by simp only [nextIdx]; omega) (by simp only [nextIdx]; omega)
  have hcloseNext : b.alphaValue ⟨nextIdx.val - 1, by
        have hi := nextIdx.lt_large
        omega⟩ ≤
      a.alphaValue ⟨nextIdx.val - 1, by
        have hi := nextIdx.lt_large
        omega⟩ + 2 := hclose.le
  have hprefixRaw :=
    beli2019Remark616_leftMixedPrefix_right_le_add_two
      a b c hdefect nextIdx hAlpha hcloseNext (-1) (i.val - 1)
  have hprefix :
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) +
          ((2 : ℚ) : WithTop ℚ) := by
    simpa only [nextIdx] using hprefixRaw
  have hgapEntries := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst i.val ⟨d, hd⟩ (by omega) hiRight.le
  have hgapOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hgapEntries
  have hcoefficientInt :
      a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ =
        (b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩) + 2 := by
    omega
  have hcoefficient :
      (((a.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((2 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationPrimaryDefect
  calc
    _ ≤ (((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        (a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) +
          ((2 : ℚ) : WithTop ℚ)) := add_le_add_right hprefix _
    _ = ((((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        ((2 : ℚ) : WithTop ℚ)) +
          a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
      ac_rfl
    _ = _ := by rw [← hcoefficient]

set_option maxHeartbeats 3000000 in
-- The two possible two-step boundaries share the same mixed-prefix formula.
/-- The secondary source-candidate comparison on the complete odd central
type-I interval. -/
theorem lemma79_typeI_secondary_le_sourceSecondary_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val < C.rightSwitch) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi := by
  rcases hodd with ⟨d, hd⟩
  have hprefix :
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
    by_cases hfull : i.val + 2 = n + 2
    · simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change
          a b c 1 (i.val - 2)).le
    · have hfarBound : i.val + 2 < n + 2 := by omega
      let farIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
      have hfarOdd : Odd farIdx.val :=
        ⟨d + 1, by simp only [farIdx]; omega⟩
      have hAlpha : a.representationAlphaValue b farIdx =
          b.alphaValue ⟨farIdx.val - 1, by
            have hf := farIdx.lt_large
            omega⟩ := by
        by_cases hnext : i.val + 1 < C.rightSwitch
        · exact
            beli2019Lemma69_ii_typeI_targetValue_from_conditions_complete
              a b D C hfirst horder hdefect farIdx hfarOdd
                (by simp only [farIdx]; omega)
                (by simp only [farIdx]; omega)
        · have hnextEq : i.val + 1 = C.rightSwitch := by
            rcases C.right_even with ⟨e, he⟩
            omega
          exact
            a.beli2019Lemma69_ii_typeI_rightSuccessorTargetValue_complete
              b D C hfirst hdefect farIdx (by
                simp only [farIdx]
                omega)
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
  have hsumEntries := lemma69_v_typeI_adjacent_entry_sum_eq
    a b D C hfirst i.val (by omega) (by omega)
  have hsumOrders :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hsumEntries
  have hcoefficientInt :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ - c.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ - c.order ⟨i.val - 1, by omega⟩ := by
    omega
  have hcoefficient :
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        c.order ⟨i.val - 2, by omega⟩ - c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) =
        (((b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ - c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationSecondaryDefect
  rw [hcoefficient]
  exact add_le_add_right hprefix _

set_option maxHeartbeats 5000000 in
-- All representation candidates are compared at dependent odd indices.
/-- The comparison representation invariant is no larger than the source
one on the complete odd central type-I interval. -/
theorem lemma79_typeI_alpha_le_sourceAlpha_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) := by
  have hcurrentRight : i.val < C.rightSwitch := by
    rcases hodd with ⟨d, hd⟩
    rcases C.right_even with ⟨e, he⟩
    omega
  have hhalf := lemma79_typeI_halfGap_le_sourceHalfGap
    a b c D C hfirst i hodd hleft hright
  have hprimary := lemma79_typeI_primary_le_sourcePrimary_complete
    a b c D C hfirst horder hdefect i hodd hleft hright
  rw [b.coe_representationAlphaValue c i,
    a.coe_representationAlphaValue c i,
    b.representationAlpha_eq_min_halfGap_prime c i,
    a.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min hhalf
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 2
  · rw [b.representationAlphaPrime_eq_min_primary_secondary c i hi,
      a.representationAlphaPrime_eq_min_primary_secondary c i hi]
    exact min_le_min hprimary
      (lemma79_typeI_secondary_le_sourceSecondary_complete
        a b c D C hfirst horder hdefect i hi hodd hleft hcurrentRight)
  · rw [b.representationAlphaPrime_eq_primary_of_not_interior c i hi,
      a.representationAlphaPrime_eq_primary_of_not_interior c i hi]
    exact hprimary

/-- Lemma 7.9(ii), case 4, at every odd coordinate of the canonical central
type-I interval, including a terminal profile. -/
theorem beli2019Lemma79_ii_typeI_centralOdd_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  apply lemma79_ii_typeI_of_source_branch_complete
    a b c D C hfirst horderAB hdefectAB hdefectAC horderBC hnorm
      i hodd hleft hright
  intro _
  exact lemma79_typeI_alpha_le_sourceAlpha_complete
    a b c D C hfirst horderAB hdefectAB i hodd hleft hright

/-- Lemma 7.9(ii), case 4, on the whole odd type-I interval before the last
unequal order, including a terminal canonical profile. -/
theorem beli2019Lemma79_ii_typeI_caseFour_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hlast : i.val < D.profile.last) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hcentral : i.val - 1 < C.rightSwitch
  · exact beli2019Lemma79_ii_typeI_centralOdd_complete
      a b c D C hfirst horderAB hdefectAB hdefectAC horderBC
        hnorm i hodd hleft hcentral
  · have hright : C.rightSwitch < i.val := by
      have hipos := i.pos
      omega
    have hrightLast : C.rightSwitch < D.profile.last :=
      hright.trans hlast
    exact beli2019Lemma79_ii_typeI_rightOdd
      a b c D C hfirst hrightLast hdefectAB hdefectAC horderBC
        hnorm i hright hlast hodd

end BONG.GoodBONG

end Bong
