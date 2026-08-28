/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha
import Bong.Bong.Beli2019Lemma79OrderTypeIIIPrimary

/-!
# Beli (2019), Lemma 7.9(i): the hard interior type-III class

At an interior coordinate in the hard parity class, Lemma 7.8 excludes the
half-gap candidate.  Lemma 2.7 replaces the remaining secondary candidate
by its current-defect form, and the source branch of Lemma 2.9 reduces it
to the source alpha.  The primary and source-alpha branches both imply the
required adjacent-pair inequality.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 600000 in
-- Normalizing the nested candidate minima and four boundary indices is expensive.
/-- The adjacent-pair alternative in the interior hard parity class of the
type-III proof of Lemma 7.9(i). -/
theorem lemma79_typeIII_interiorPair
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
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
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkNextNext : k + 2 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hbeforeLast : k < D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k) :
    b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) ≤
      c.orderSequence.entryOrZero (k - 1) +
        c.orderSequence.entryOrZero k := by
  let left := D.outer.transition.lastZero
  let C : Int := b.orderSequence.entryOrZero left -
    a.orderSequence.entryOrZero (left + 1)
  let idx : RepresentationIndex (n + 2) (n + 2) := {
    val := k + 1
    pos := by omega
    lt_large := hkNext
    le_small := hkNext.le }
  have hi : 1 < idx.val ∧ idx.val + 1 < n + 2 := by
    have hseparated := D.outer.transition.separated
    dsimp only [idx]
    omega
  have hkPos : 0 < k := by
    have hseparated := D.outer.transition.separated
    omega
  have hleftBound : left < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    dsimp only [left]
    rw [D.adjacent] at hbound
    omega
  have hrightBound : left + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    dsimp only [left]
    rw [D.adjacent] at hbound
    omega
  have hcomparisonRaw := a.lemma79_typeIII_comparisonPrefix_eq_mixedShift
    b c D hfirst hdefectAB hnotOverlap hinitial hnorm
      k hk hright hbeforeLast.le heven hcurrent
  have hcomparison : a.truncatedPrefixDefect c 1 idx.val idx.val =
      (((C : ℚ)) : WithTop ℚ) := by
    rw [← b.orderSequence_entryOrZero_eq_order ⟨left, hleftBound⟩,
      ← a.orderSequence_entryOrZero_eq_order ⟨left + 1, hrightBound⟩]
      at hcomparisonRaw
    simpa only [idx, C, left] using hcomparisonRaw
  have hAlpha : (a.representationAlphaValue c idx : WithTop ℚ) ≤
      (((C : ℚ)) : WithTop ℚ) :=
    (hdefectAC idx).trans_eq hcomparison
  have hgap := (a.beli2019Lemma78_sourceAlpha_and_gap
    b D hfirst hdefectAB hnotOverlap hinitial).2
  have hhalf := a.lemma79_typeIII_mixedShift_lt_representationHalfGap
    b c D hgap k hk hkNext hright hbeforeLast.le heven hcurrent
  have hprime := a.representationAlphaPrime_le_of_alphaValue_le_of_lt_halfGap
    c idx (((C : ℚ)) : WithTop ℚ) hAlpha (by
      simpa only [idx, C, left] using hhalf)
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    simp only [left]
    rw [D.adjacent]
    omega
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    k hright hbeforeLast.le heven
  have hrightBoundary := D.outer.transition.rightBoundary
  have hcurrentUpper : c.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero (left + 1) := by
    rw [hcurrentBoundary, hrightBoundary, hrightIndex] at hcurrent
    omega
  rcases heven with ⟨d, hd⟩
  have hsourceParity : Even (k + 2 - (left + 1)) := ⟨d + 1, by
    rw [← hrightIndex]
    omega⟩
  have hsourceMonotone := a.orderSequence.entryOrZero_le_of_evenGap
    (left + 1) (k + 2) (by omega) hkNextNext hsourceParity
  have hcrossEntries : c.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero (k + 2) :=
    hcurrentUpper.trans hsourceMonotone
  have hcross : c.order ⟨idx.val - 1, by
        have := idx.le_small
        omega⟩ ≤ a.order ⟨idx.val + 1, hi.2⟩ := by
    rw [← c.orderSequence_entryOrZero_eq_order
        ⟨idx.val - 1, by have := idx.le_small; omega⟩,
      ← a.orderSequence_entryOrZero_eq_order ⟨idx.val + 1, hi.2⟩]
    simpa only [idx, Nat.add_sub_cancel] using hcrossEntries
  rw [a.representationAlphaPrime_eq_min_primary_current c idx hi hcross]
    at hprime
  rcases min_le_iff.mp hprime with hprimary | hsecondary
  · exact a.lemma79_typeIII_pair_of_primary_le_mixedShift
      b c D hfirst hdefectAB hnotOverlap hnorm k hk hkNext hright
        hbeforeLast.le ⟨d, hd⟩ hcurrent (by
          simpa only [idx, C, left] using hprimary)
  · by_cases hpair : b.orderSequence.entryOrZero k +
          b.orderSequence.entryOrZero (k + 1) ≤
        c.orderSequence.entryOrZero (k - 1) +
          c.orderSequence.entryOrZero k
    · exact hpair
    · have htargetTwoParity : Even
          (k + 2 - (D.outer.transition.firstTwo - 1)) := ⟨d + 1, by omega⟩
      have htargetTwo := D.outer.target_rightEven_eq_boundary
        (k + 2) (by omega) (by
          rcases D.outer.right_even_distance with ⟨e, he⟩
          omega) htargetTwoParity
      have htargetCurrent := D.outer.target_rightEven_eq_boundary
        k hright hbeforeLast.le ⟨d, hd⟩
      have htargetTwoEq : b.orderSequence.entryOrZero (k + 2) =
          b.orderSequence.entryOrZero k := htargetTwo.trans htargetCurrent.symm
      have hpairParity : Even
          (k + 1 - D.outer.transition.firstTwo) := ⟨d, by omega⟩
      have hsourceTargetPair := D.outer.rightPairEq
        (k + 1) (by omega) (by omega) hpairParity
      have hsourcePairEq :
          a.orderSequence.entryOrZero (k + 1) +
              a.orderSequence.entryOrZero (k + 2) =
            b.orderSequence.entryOrZero k +
              b.orderSequence.entryOrZero (k + 1) := by
        rw [hsourceTargetPair, htargetTwoEq]
        omega
      have hshift : 0 <
          a.order ⟨idx.val, idx.lt_large⟩ +
              a.order ⟨idx.val + 1, hi.2⟩ -
            c.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
              c.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ := by
        rw [← a.orderSequence_entryOrZero_eq_order
            ⟨idx.val, idx.lt_large⟩,
          ← a.orderSequence_entryOrZero_eq_order ⟨idx.val + 1, hi.2⟩,
          ← c.orderSequence_entryOrZero_eq_order
            ⟨idx.val - 2, by have := idx.le_small; omega⟩,
          ← c.orderSequence_entryOrZero_eq_order
            ⟨idx.val - 1, by have := idx.le_small; omega⟩]
        have hprevVal : idx.val - 2 = k - 1 := by
          dsimp only [idx]
          omega
        simp only [idx, Nat.add_sub_cancel]
        rw [hprevVal, hsourcePairEq]
        omega
      have hsourceAlpha :=
        a.representationSecondarySourceAlpha_le_of_current_le_comparison
          c idx hi C hsecondary hcomparison hshift
      exact a.lemma79_typeIII_pair_of_sourceAlpha_le_mixedShift
        b c D hfirst hinitial k hk hkPos hkNext hkNextNext hright
          hbeforeLast.le
          ⟨d, hd⟩ (by simpa only [idx, C, left] using hsourceAlpha)

end BONG.GoodBONG

end Bong
