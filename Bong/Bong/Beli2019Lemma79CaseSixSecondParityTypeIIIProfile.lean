/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIAssembly
import Bong.Bong.Beli2019Lemma611TypeIII

/-!
# Beli (2019), Lemma 7.9(ii), case 6: type-III arithmetic profile

In the opposite-current-parity branch the preceding order of the third
BONG is congruent to the source order at the left transition.  Its norm
lower bound is already one unit larger, hence parity improves this to a
two-unit lower bound.  This is the inequality `T_i ≥ R + 2` in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Opposite current parity identifies the preceding third order modulo two
with the source order at the left type-III transition. -/
theorem beli2019Lemma79_typeIII_caseSix_thirdPrevious_modEq_sourceLeft
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hthroughLast : i.val ≤ D.outer.last)
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    Int.ModEq 2 (c.orderSequence.entryOrZero (i.val - 1))
      (a.orderSequence.entryOrZero D.outer.transition.lastZero) := by
  have P := a.lemma611TypeIII_of_defect b D hfirst hdefect hnotOverlap
  have htarget := P.target i.val hthroughLast
  have hcentral : Int.ModEq 2
      (a.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1))
      (a.orderSequence.entryOrZero D.outer.transition.lastZero) :=
    int_modEq_two_of_even_sub P.central_gap_even
  have hboundary : Int.ModEq 2
      (b.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1))
      (a.orderSequence.entryOrZero D.outer.transition.lastZero + 1) := by
    rw [D.outer.transition.rightBoundary]
    exact hcentral.add (Int.ModEq.refl 1)
  have hcurrent : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (a.orderSequence.entryOrZero D.outer.transition.lastZero + 1) :=
    htarget.trans hboundary
  have hshifted := horders.symm.trans hcurrent
  simpa only [add_sub_cancel_right] using
    hshifted.sub (Int.ModEq.refl 1)

/-- The preceding third order is at least two above the source order at the
left transition. -/
theorem beli2019Lemma79_typeIII_caseSix_sourceLeft_add_two_le_thirdPrevious
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    a.orderSequence.entryOrZero D.outer.transition.lastZero + 2 ≤
      c.orderSequence.entryOrZero (i.val - 1) := by
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst D.outer.transition.lastZero le_rfl hleftEven
  have hiOdd := beli2019Lemma79_typeIII_caseSix_index_odd
    a b D hfirst i hright heven
  rcases hiOdd with ⟨d, hd⟩
  have hpreviousEven : Even (i.val - 1) := ⟨d, by omega⟩
  have hpreviousBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  have hthirdMonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 (i.val - 1) (Nat.zero_le _) hpreviousBound hpreviousEven
  have hlower :
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 ≤
        c.orderSequence.entryOrZero (i.val - 1) := by
    rw [hsourceLeft]
    exact hfirstLower.trans hthirdMonotone
  have hmod :=
    beli2019Lemma79_typeIII_caseSix_thirdPrevious_modEq_sourceLeft
      a b c D hfirst hdefect hnotOverlap i hthroughLast horders
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨z, hz⟩
  omega

/-- The current order shift plus the type-III central mixed shift is
nonpositive. -/
theorem beli2019Lemma79_typeIII_caseSix_primaryShift_add_mixedShift_nonpos
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    b.orderSequence.entryOrZero i.val -
        c.orderSequence.entryOrZero (i.val - 1) +
        (b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1)) ≤ 0 := by
  have hthirdLower :=
    beli2019Lemma79_typeIII_caseSix_sourceLeft_add_two_le_thirdPrevious
      a b c D hfirst hdefect hnotOverlap hnorm i hright hthroughLast
        heven horders
  have hcurrent := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hrightIndex : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  have hleftBoundary := D.outer.transition.leftBoundary
  have hrightBoundary := D.outer.transition.rightBoundary
  rw [hrightBoundary, hrightIndex] at hcurrent
  omega

/-- If the shifted mixed prefix has defect at most `R - S + 2`, the primary
candidate is nonpositive and condition 2.1(ii) follows immediately. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_of_mixed_le
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1))
    (hmixed : b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
        WithTop ℚ)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let shift : Int := b.orderSequence.entryOrZero i.val -
    c.orderSequence.entryOrZero (i.val - 1)
  let central : Int :=
    b.orderSequence.entryOrZero D.outer.transition.lastZero -
      a.orderSequence.entryOrZero (D.outer.transition.lastZero + 1)
  have hnonpos : shift + central ≤ 0 := by
    simpa only [shift, central] using
      beli2019Lemma79_typeIII_caseSix_primaryShift_add_mixedShift_nonpos
        a b c D hfirst hdefect hnotOverlap hnorm i hright hthroughLast
          heven horders
  have hiPrevious : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  have hshiftOrder : b.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, hiPrevious⟩ = shift := by
    simp only [shift]
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
  have hprimary : b.representationPrimaryDefect c i ≤
      ((((shift + central : Int) : ℚ)) : WithTop ℚ) := by
    unfold representationPrimaryDefect
    rw [hshiftOrder]
    calc
      (((shift : ℚ) : WithTop ℚ) +
          b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) ≤
          ((shift : ℚ) : WithTop ℚ) + (central : ℚ) :=
        add_le_add le_rfl (by simpa only [central] using hmixed)
      _ = ((((shift + central : Int) : ℚ)) : WithTop ℚ) := by
        rw [← WithTop.coe_add]
        norm_cast
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
      b.representationAlpha_le_primary c i
    _ ≤ ((((shift + central : Int) : ℚ)) : WithTop ℚ) := hprimary
    _ ≤ 0 := by
      exact_mod_cast hnonpos
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
      b.truncatedPrefixDefect_nonneg c 1 i.val i.val

end BONG.GoodBONG

end Bong
