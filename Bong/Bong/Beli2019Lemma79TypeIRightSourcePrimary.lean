/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightComplete

/-!
# Beli (2019), Lemma 7.9(ii): right-tail source candidates

On the odd type-I right tail, the source current order is one above the
target current order. This directly compares the half-gap candidates. For
the primary candidates, Lemma 6.9(i) bounds the target mixed prefix by one,
which exactly compensates for that order shift.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- On the odd type-I right tail, the comparison half-gap candidate is no
larger than the source half-gap candidate. -/
theorem lemma79_typeI_right_halfGap_le_sourceHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    b.representationHalfGap c i ≤ a.representationHalfGap c i := by
  have horders := lemma69_typeI_rightOdd_orders
    a b D C hfirst i.val hright hlast hodd
  have hgapOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact horders.1
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
-- Several coercions through `WithTop` meet the one-unit order shift here.
/-- On the odd type-I right tail, the comparison primary candidate is no
larger than the source primary candidate. -/
theorem lemma79_typeI_right_primary_le_sourcePrimary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i := by
  have horders := lemma69_typeI_rightOdd_orders
    a b D C hfirst i.val hright hlast hodd
  have hgapOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact horders.1
  have hnextAlpha := beli2019Lemma69_i_typeI_targetRightTail
    a b D C hfirst hrightLast hdefect i.val hright hlast hodd
  have hfarBound : i.val + 1 < n + 2 := by
    have hb := D.profile.lastDifference.bound
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
      _ ≤ ((1 : ℚ) : WithTop ℚ) := by
        exact_mod_cast hnextAlpha
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
