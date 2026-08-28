/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78Local
import Bong.Bong.Beli2019Lemma79OrderTypeIIIThirdDefect

/-!
# Beli (2019), Lemma 7.9(i): the nonoverlapping type-III endpoint

At full rank condition 2.1(i) has no adjacent-pair alternative.  If the
direct comparison failed, the pairwise domination argument in the paper
would make the third BONG's full self-defect strictly larger than the central
mixed shift.  Lemma 7.8 identifies the source full self-defect with that
shift, while the full determinant square class identifies the two self-
defects.  This gives the required contradiction without an out-of-range
coefficient convention.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The full-rank direct comparison in the nonoverlapping type-III branch
of Lemma 7.9(i). -/
theorem beli2019Lemma79_i_typeIII_nonoverlap_terminal
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hdefectAB : a.RepresentationDefectCondition b)
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.orderSequence.entry (n + 1) (by omega) ≤
      c.orderSequence.entry (n + 1) (by omega) := by
  by_contra hnot
  let k := n + 1
  let left := D.outer.transition.lastZero
  let shift : WithTop ℚ :=
    ((((b.orderSequence.entryOrZero left -
      a.orderSequence.entryOrZero (left + 1) : Int) : ℚ)) : WithTop ℚ)
  have hright : D.outer.transition.firstTwo - 1 ≤ k := by
    dsimp only [k]
    have hrightLast := D.outer.right_le_last
    omega
  have hkLast : k ≤ D.outer.last := by
    dsimp only [k]
    omega
  have hkEven : Even
      (k - (D.outer.transition.firstTwo - 1)) := by
    simpa only [k, hlast] using D.outer.right_even_distance
  have hcurrent : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k := by
    rw [b.orderSequence.entryOrZero_of_lt (by simp only [k]; omega),
      c.orderSequence.entryOrZero_of_lt (by simp only [k]; omega)]
    exact lt_of_not_ge hnot
  have hthird : shift <
      c.truncatedPrefixDefect c ((-1) ^ ((n + 2) / 2)) 0 (n + 2) := by
    have hraw := a.lemma79_typeIII_thirdPrefix_gt_mixedShift
      b c D hfirst hdefectAB hnotOverlap hnorm k (by
        simp only [k]
        omega) hright hkLast hkEven hcurrent
    simpa only [shift, left, k] using hraw
  have hleftTwo : D.outer.transition.lastZero + 2 ≤ n + 2 := by
    have hrightLast := D.outer.right_le_last
    rw [D.adjacent, hlast] at hrightLast
    omega
  have hlengthEven : Even (n + 2) := by
    rcases D.outer.right_even_distance with ⟨d, hd⟩
    have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
    rcases hleftEven with ⟨e, he⟩
    rw [D.adjacent, hlast] at hd
    exact ⟨e + d + 1, by omega⟩
  have hsourceRaw := a.beli2019Lemma78_sourcePrefixDefect_local
    b D hfirst hdefectAB hnotOverlap hinitial
      (n + 2) hleftTwo (by omega) hlengthEven
  have hsource :
      a.truncatedPrefixDefect a ((-1) ^ ((n + 2) / 2)) 0 (n + 2) =
        shift := by
    have hleftBound : left < n + 2 := by
      simp only [left]
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    have hrightBound : left + 1 < n + 2 := by
      simp only [left]
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    rw [← b.orderSequence_entryOrZero_eq_order ⟨left, hleftBound⟩,
      ← a.orderSequence_entryOrZero_eq_order ⟨left + 1, hrightBound⟩]
      at hsourceRaw
    simpa only [shift, left] using hsourceRaw
  have hfull := a.truncatedPrefixDefect_self_full_eq
    c ((-1) ^ ((n + 2) / 2))
  rw [hfull, hsource] at hthird
  exact (lt_irrefl shift) hthird

end BONG.GoodBONG

end Bong
