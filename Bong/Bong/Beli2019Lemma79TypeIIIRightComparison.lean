/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIIComparisonDefect

/-!
# Beli (2019), Lemma 7.9(ii): the strict type-III case-7 subbranch

In the strict comparison-order subcase, Lemma 7.8 gives the same self-prefix
defect for the source and target BONGs.  The third BONG has strictly larger
self-prefix defect, so sharp comparison identifies both mixed prefixes with
the common value `R - S + 2`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The target/comparison prefix has defect `R - S + 2` in the strict
type-III parity subcase. -/
theorem lemma79_typeIII_targetComparisonPrefix_eq_mixedShift
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlastK : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k) :
    b.truncatedPrefixDefect c 1 (k + 1) (k + 1) =
      ((((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hrightIndex : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  have hrightOdd : Odd (D.outer.transition.firstTwo - 1) := by
    rcases hleftEven with ⟨d, hd⟩
    rw [hrightIndex]
    exact ⟨d, by omega⟩
  have hkOdd : Odd k := by
    rcases hrightOdd with ⟨d, hd⟩
    rcases heven with ⟨e, he⟩
    exact ⟨d + e, by omega⟩
  have hiEven : Even (k + 1) := by
    rcases hkOdd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hiStart : D.outer.transition.lastZero + 2 ≤ k + 1 := by
    omega
  have hiLast : k + 1 ≤ D.outer.last + 1 := by omega
  have htarget :=
    (a.beli2019Lemma78_typeIII b D hfirst hlast horder hdefect
      htotal hnotOverlap hinitial (k + 1) hiStart hiLast hiEven).2.1
  have hthird := c.lemma79_typeIII_thirdPrefix_gt_mixedShift
    (a := a) (b := b) D hfirst hdefect hnotOverlap hnorm
    k hk hright hlastK heven hcurrent
  have hthird' : b.truncatedPrefixDefect b
      ((-1) ^ ((k + 1) / 2)) 0 (k + 1) <
        c.truncatedPrefixDefect c
          ((-1) ^ ((k + 1) / 2)) 0 (k + 1) := by
    rw [htarget]
    have hleftBound : D.outer.transition.lastZero < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    have hrightBound : D.outer.transition.lastZero + 1 < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    rw [b.orderSequence_entryOrZero_eq_order
      ⟨D.outer.transition.lastZero, hleftBound⟩,
      a.orderSequence_entryOrZero_eq_order
        ⟨D.outer.transition.lastZero + 1, hrightBound⟩] at hthird
    exact hthird
  exact b.comparisonPrefixDefect_eq_of_self_lt_self c
    ((-1) ^ ((k + 1) / 2)) (k + 1) hthird' |>.trans htarget

/-- Under the strict comparison order in type-III case 7, replacing the
source by the target does not change the mixed prefix defect. -/
theorem lemma79_typeIII_right_comparisonPrefixes_eq_of_comparison_lt_target
    [Beli2006AlphaLaws.{u, v} K]
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.order ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ < b.order ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩) :
    b.truncatedPrefixDefect c 1 i.val i.val =
      a.truncatedPrefixDefect c 1 i.val i.val := by
  let k := i.val - 1
  have hk : k < n + 2 := by
    dsimp only [k]
    omega
  have hrightK : D.outer.transition.firstTwo - 1 ≤ k := by
    dsimp only [k]
    omega
  have hlastK : k ≤ D.outer.last := by
    dsimp only [k]
    omega
  have hevenK : Even (k - (D.outer.transition.firstTwo - 1)) := by
    rcases hodd with ⟨d, hd⟩
    exact ⟨d, by
      dsimp only [k]
      omega⟩
  have hcurrentEntries : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k := by
    dsimp only [k]
    rw [c.orderSequence.entryOrZero_of_lt (by omega),
      b.orderSequence.entryOrZero_of_lt (by omega)]
    exact hcurrent
  have hsource := lemma79_typeIII_comparisonPrefix_eq_mixedShift
    a b c D hfirst hdefect hnotOverlap hinitial
      hnorm k hk hrightK hlastK hevenK hcurrentEntries
  have htarget := lemma79_typeIII_targetComparisonPrefix_eq_mixedShift
    a b c D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      hnorm k hk hrightK hlastK hevenK hcurrentEntries
  have hkSucc : k + 1 = i.val := by
    dsimp only [k]
    have hiPos := i.pos
    omega
  simpa only [hkSucc] using htarget.trans hsource.symm

end BONG.GoodBONG

end Bong
