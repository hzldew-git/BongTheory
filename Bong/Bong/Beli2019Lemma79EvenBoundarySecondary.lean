/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeIIIInterior
import Bong.Bong.Beli2019Remark616RightMixedGeneral
import Bong.Bong.Beli2019Lemma79TypeIRightSourceSecondary

/-!
# Beli (2019), Lemma 7.9(ii), case 3: transition secondary candidates

At the last even coordinate of the left profile, the type-II target
adjacent sum is one larger and its far alpha is one.  In type III the sum
is two larger, while Remark 6.16 gives an unshifted mixed-prefix bound.
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
-- The target prefix is capped by the first core alpha, which is one.
/-- The shifted secondary-candidate comparison at the type-II left
transition. -/
theorem beli2019Lemma79_typeII_even_leftBoundary_secondary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hboundary : i.val = D.outer.transition.lastZero) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hcurrentRaw := D.outer.transition.leftBoundary
  have hnextRaw := D.outer.transition.middle (i.val + 1) (by omega) (by
    have hlong := D.long
    omega)
  have hcurrent : b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero i.val + 1 := by
    simpa only [hboundary] using hcurrentRaw
  have hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val +
        b.orderSequence.entryOrZero (i.val + 1) =
      a.orderSequence.entryOrZero i.val +
        a.orderSequence.entryOrZero (i.val + 1) + 1
    omega
  have hfarBound : i.val + 2 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    omega
  have hfarAlpha := a.beli2019Lemma69_i_typeII_targetCore_eq_one
    b D hfirst (i.val + 1) (by omega) (by
      have hlong := D.long
      omega)
  have htarget := b.truncatedPrefixDefect_le_leftCap
    c 1 (i.val + 2) (i.val - 2)
  rw [b.prefixAlphaCap_of_internal (by omega) hfarBound] at htarget
  have htargetOne : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤ ((1 : ℚ) : WithTop ℚ) := by
    exact htarget.trans (by exact_mod_cast hfarAlpha.le)
  have hsource := a.truncatedPrefixDefect_nonneg
    c 1 (i.val + 2) (i.val - 2)
  exact representationSecondaryDefect_le_add_two_of_orderSum_eq_add_one
    a b c i hi hsum htargetOne hsource

set_option maxHeartbeats 4000000 in
-- At full rank use product equivalence; otherwise use the right-alpha form
-- of Remark 6.16 at the first right boundary.
/-- The shifted secondary-candidate comparison at the type-III left
transition. -/
theorem beli2019Lemma79_typeIII_even_leftBoundary_secondary
    [Beli2006AlphaLaws.{u, v} K]
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
      have hfarEven : Even farIdx.val := by
        rcases hiEven with ⟨d, hd⟩
        exact ⟨d + 1, by simp only [farIdx]; omega⟩
      have hAlpha := a.beli2019Lemma69_ii_typeIII_targetRightValue
        b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
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
