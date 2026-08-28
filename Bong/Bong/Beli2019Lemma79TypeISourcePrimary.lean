/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeICentralSeedsComplete
import Bong.Bong.Beli2019Remark616LeftMixed

/-!
# Beli (2019), Lemma 7.9(ii): type-I source candidates

This file compares the half-gap and primary candidates defining `B_i` and
`C_i` in the source-defect branch of case 4.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The two-unit order gap makes the comparison half-gap candidate no
larger than the source half-gap candidate. -/
theorem lemma79_typeI_halfGap_le_sourceHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    b.representationHalfGap c i ≤ a.representationHalfGap c i := by
  have hgapEntries := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst i.val hodd (by omega) (by omega)
  have hgapOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hgapEntries
  unfold representationHalfGap
  exact_mod_cast (show
    ((b.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, by
        have hi := i.lt_large
        have hp := i.pos
        omega⟩ : Int) : ℚ) / 2 + (ramificationIndex K : ℚ) ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : Int) : ℚ) / 2 + (ramificationIndex K : ℚ) by
    rw [hgapOrder]
    push_cast
    linarith)

set_option maxHeartbeats 2000000 in
-- Dependent indices at `i`, `i + 1`, and `i - 1` meet in this comparison.
/-- Remark 6.16's two-unit estimate exactly compensates for the two-unit
order gap in the primary candidate. -/
theorem lemma79_typeI_primary_le_sourcePrimary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
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
  have hiNextRight : i.val + 1 ≤ C.rightSwitch := by omega
  have hiNextBound : i.val + 1 < n + 2 := by
    have hr := C.right_le_last
    have hb := D.profile.lastDifference.bound
    omega
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNextBound, by omega⟩
  have hnextEven : Even nextIdx.val := by
    exact ⟨d + 1, by simp only [nextIdx]; omega⟩
  have hnextValue :=
    (lemma69_typeI_central_values_from_conditions
      a b D C hfirst hrightLast horder hdefect nextIdx
        (by simp only [nextIdx]; omega)
        (by simp only [nextIdx]; omega)).2 hnextEven
  have hAlpha : a.representationAlphaValue b nextIdx =
      a.alphaValue ⟨nextIdx.val - 1, by
        have hi := nextIdx.lt_large
        have hp := nextIdx.pos
        omega⟩ := by
    apply WithTop.coe_injective
    rw [a.coe_representationAlphaValue b nextIdx]
    exact hnextValue
  have hgapEntries := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst i.val ⟨d, hd⟩ (by omega) hiRight.le
  have hgapOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hgapEntries
  let p : Fin (n + 1) := ⟨i.val, by omega⟩
  have hpCast : p.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hweight := beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
    a b D C hfirst hrightLast horder hdefect i.val (by omega) hiRight
  have hclose : b.alphaValue p = a.alphaValue p + 2 := by
    apply alpha_eq_add_two_of_leftEndpoint_eq b a p
    · rw [hpCast]
      exact hgapOrder
    · simpa only [p] using hweight.symm
  have hcloseNext : b.alphaValue ⟨nextIdx.val - 1, by
        have hi := nextIdx.lt_large
        have hp := nextIdx.pos
        omega⟩ ≤
      a.alphaValue ⟨nextIdx.val - 1, by
        have hi := nextIdx.lt_large
        have hp := nextIdx.pos
        omega⟩ + 2 := by
    simpa only [nextIdx, show i.val + 1 - 1 = i.val by omega, p]
      using hclose.le
  have hprefixRaw :=
    beli2019Remark616_leftMixedPrefix_right_le_add_two
      a b c hdefect nextIdx hAlpha hcloseNext (-1) (i.val - 1)
  have hprefix :
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) +
          ((2 : ℚ) : WithTop ℚ) := by
    simpa only [nextIdx] using hprefixRaw
  have hcoefficientInt :
      a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hi := i.lt_large
            have hp := i.pos
            omega⟩ =
        (b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hi := i.lt_large
            have hp := i.pos
            omega⟩) + 2 := by
    omega
  have hcoefficient :
      (((a.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hi := i.lt_large
            have hp := i.pos
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((2 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationPrimaryDefect
  calc
    _ ≤ (((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hi := i.lt_large
            have hp := i.pos
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
        (a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) +
          ((2 : ℚ) : WithTop ℚ)) := add_le_add_right hprefix _
    _ = ((((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hi := i.lt_large
            have hp := i.pos
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
        ((2 : ℚ) : WithTop ℚ)) +
          a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
      ac_rfl
    _ = _ := by rw [← hcoefficient]

end BONG.GoodBONG

end Bong
