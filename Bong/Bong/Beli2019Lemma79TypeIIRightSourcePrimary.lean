/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightProfileAlpha
import Bong.Bong.Beli2019Remark613TypeIIRightAlpha

/-!
# Beli (2019), Lemma 7.9(ii): type-II case-7 source candidates

The one-unit source/target shift compares the half-gap candidates.  The
target alpha equal to one bounds the mixed prefix in the primary candidate
and compensates exactly for the same order shift.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The comparison half-gap is bounded by the source half-gap in the
type-II case-7 interval. -/
theorem lemma79_typeII_right_halfGap_le_sourceHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationHalfGap c i ≤ a.representationHalfGap c i := by
  have horderEntry := D.outer.source_rightOdd_eq_target_add_one
    D.no_gap_two i.val (by omega) hbeforeLast.le hodd
  have hgapOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact horderEntry
  have hiPrevious : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  unfold representationHalfGap
  exact_mod_cast (show
    ((b.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) by
    rw [hgapOrder]
    push_cast
    linarith)

set_option maxHeartbeats 2000000 in
-- Coercions through `WithTop` meet the one-unit right-profile shift here.
/-- The comparison primary candidate is bounded by the source primary
candidate in the type-II case-7 interval. -/
theorem lemma79_typeII_right_primary_le_sourcePrimary
    [Beli2006AlphaLaws.{u, v} K]
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
  have hnextAlpha := beli2019Remark613_typeII_targetRightAlpha_eq_one
    a b D hlast horder hdefect htotal i.val hright hbeforeLast hodd
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

end BONG.GoodBONG

end Bong
