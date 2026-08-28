/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyFallbackFinalBounds

/-!
# Beli (2019), Lemma 4.2: final fallback triangles

The final two candidate exclusions in the fallback paragraph use strict
triangles against adjacent source defects.  The resulting prefix defects
are controlled respectively by `A_i` and by the primary formula for `A_i`.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- The primary candidate of `A_(i+1)`, if it lay below `C_(i-1)`, has
its negative source-middle defect equal to the current positive
source-middle defect. -/
theorem nextNextPrimaryDefect_eq_currentSourceDefect_of_fallback
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hnextNextPrimary :
      let nextNext : RepresentationIndex (n + 1) (n + 1) :=
        ⟨j.val + 2, by omega, hiNextNext, by omega⟩
      a.representationAlpha b nextNext =
        a.representationPrimaryDefect b nextNext)
    (hstrict :
      let nextNext : RepresentationIndex (n + 1) (n + 1) :=
        ⟨j.val + 2, by omega, hiNextNext, by omega⟩
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext <
        a.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 3) (j.val + 1) =
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
  let nextNext : RepresentationIndex (n + 1) (n + 1) :=
    ⟨j.val + 2, by omega, hiNextNext, by omega⟩
  let commonShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 2, hiNextNext⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b (-1)
    (j.val + 3) (j.val + 1)
  let adjacentDefect := a.truncatedPrefixDefect a (-1)
    (j.val + 1) (j.val + 3)
  have hsource :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext =
        (commonShift : WithTop ℚ) + sourceDefect := by
    rw [hnextNextPrimary]
    unfold representationPrimaryDefect
    dsimp only [nextNext, commonShift, sourceDefect]
    rw [← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  have htarget := a.targetAlpha_le_shiftedNextNextPrimaryAdjacent
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    c j hi hiNextNext
  have hdefect : sourceDefect < adjacentDefect := by
    have hshifted : (commonShift : WithTop ℚ) + sourceDefect <
        (commonShift : WithTop ℚ) + adjacentDefect := by
      rw [← hsource]
      exact hstrict.trans_le (by
        simpa only [commonShift, adjacentDefect] using htarget)
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted
  have hdefect' : sourceDefect <
      a.truncatedPrefixDefect a (-1) (j.val + 3) (j.val + 1) := by
    rw [a.truncatedPrefixDefect_comm a (-1)
      (j.val + 3) (j.val + 1)]
    exact hdefect
  have htriangle := a.truncatedPrefixDefect_neg_eq_pos_of_lt_neg
    b a (j.val + 3) (j.val + 1) (j.val + 1) hdefect'
  calc
    a.truncatedPrefixDefect b (-1) (j.val + 3) (j.val + 1) =
        b.truncatedPrefixDefect a 1 (j.val + 1) (j.val + 1) :=
      htriangle
    _ = a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) :=
      b.truncatedPrefixDefect_comm a 1 (j.val + 1) (j.val + 1)

/-- After the primary triangle, its shifted candidate is strictly larger
than the desired fallback bound. -/
theorem nextFallback_lt_shiftedNextNextPrimary_of_fallback
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hnextNextPrimary :
      let nextNext : RepresentationIndex (n + 1) (n + 1) :=
        ⟨j.val + 2, by omega, hiNextNext, by omega⟩
      a.representationAlpha b nextNext =
        a.representationPrimaryDefect b nextNext)
    (hreplace : a.truncatedPrefixDefect b (-1)
      (j.val + 3) (j.val + 1) =
        a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1)) :
    a.nextFallbackBound b j hi.2 <
      let nextNext : RepresentationIndex (n + 1) (n + 1) :=
        ⟨j.val + 2, by omega, hiNextNext, by omega⟩
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext := by
  let next := nextRepresentationIndex j hi.2
  let nextNext : RepresentationIndex (n + 1) (n + 1) :=
    ⟨j.val + 2, by omega, hiNextNext, by omega⟩
  let fallbackShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ)
  let primaryShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 2, hiNextNext⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  have hnextDefect : a.representationAlpha b next ≤
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
    have hcondition := habDefect next
    rw [a.coe_representationAlphaValue b next] at hcondition
    simpa only [next, nextRepresentationIndex] using hcondition
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hpairRaw := hessential.2 hi.1 hiNextNext
  have hpair :
      c.order ⟨j.val - 2, by omega⟩ +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ +
          a.order ⟨j.val + 2, hiNextNext⟩ := by
    simpa only [orderSequence_at, nextEssentialIndex] using hpairRaw
  have hshift : fallbackShift < primaryShift := by
    dsimp only [fallbackShift, primaryShift]
    push_cast
    have hpairQ :
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
            (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
          (a.order ⟨j.val + 1, hi.2⟩ : ℚ) +
            (a.order ⟨j.val + 2, hiNextNext⟩ : ℚ) := by
      exact_mod_cast hpair
    linarith
  have hnextFinite : a.representationAlpha b next ≠ ⊤ :=
    a.representationAlpha_ne_top b next
  dsimp only
  calc
    a.nextFallbackBound b j hi.2 =
        (fallbackShift : WithTop ℚ) + a.representationAlpha b next := by
      rfl
    _ < (primaryShift : WithTop ℚ) + a.representationAlpha b next :=
      WithTop.add_lt_add_right hnextFinite (by exact_mod_cast hshift)
    _ ≤ (primaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) :=
      add_le_add_right hnextDefect _
    _ = (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val + 1, hi.2⟩ -
          c.order ⟨j.val - 2, by omega⟩ -
          c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext := by
      rw [hnextNextPrimary]
      unfold representationPrimaryDefect
      change (primaryShift : WithTop ℚ) +
          a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) =
        (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val + 1, hi.2⟩ -
          c.order ⟨j.val - 2, by omega⟩ -
          c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((((a.order ⟨j.val + 2, hiNextNext⟩ -
            b.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ) : WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) (j.val + 3) (j.val + 1))
      rw [hreplace, ← add_assoc]
      congr 1
      norm_cast
      dsimp only [primaryShift]
      push_cast
      ring

/-- The secondary candidate of `A_(i+1)`, if it lay below `C_(i-1)`, has
its positive long-prefix defect equal to the preceding negative
source-middle defect. -/
theorem nextNextSecondaryDefect_eq_previousSourceDefect_of_fallback
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hiNextNextNext : j.val + 3 < n + 1)
    (hessential : a.IsNextEssential c j)
    (htriggerFailure :
      ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnextNextSecondary : a.representationAlpha b
      (⟨j.val + 2, by omega, hiNextNext, by omega⟩ :
        RepresentationIndex (n + 1) (n + 1)) =
      a.representationSecondaryDefect b
        (⟨j.val + 2, by omega, hiNextNext, by omega⟩ :
          RepresentationIndex (n + 1) (n + 1))
        (by
          change 1 < j.val + 2 ∧ j.val + 2 + 1 < n + 1
          omega))
    (hstrict :
      let nextNext : RepresentationIndex (n + 1) (n + 1) :=
        ⟨j.val + 2, by omega, hiNextNext, by omega⟩
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext <
        a.representationAlpha c j) :
    a.truncatedPrefixDefect b 1 (j.val + 4) j.val =
      a.truncatedPrefixDefect b (-1) (j.val + 2) j.val := by
  let nextNext : RepresentationIndex (n + 1) (n + 1) :=
    ⟨j.val + 2, by omega, hiNextNext, by omega⟩
  let hinterior : 1 < nextNext.val ∧ nextNext.val + 1 < n + 1 :=
    ⟨by dsimp only [nextNext]; omega,
      by dsimp only [nextNext]; omega⟩
  let commonShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 2, hiNextNext⟩ +
    a.order ⟨j.val + 3, hiNextNextNext⟩ -
    b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b 1
    (j.val + 4) j.val
  let adjacentDefect := a.truncatedPrefixDefect a (-1)
    (j.val + 2) (j.val + 4)
  have hsource :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext =
        (commonShift : WithTop ℚ) + sourceDefect := by
    rw [hnextNextSecondary]
    unfold representationSecondaryDefect
    dsimp only [nextNext, hinterior, commonShift, sourceDefect]
    simp only [Nat.add_sub_cancel]
    rw [← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  have htarget :=
    a.targetAlpha_lt_shiftedNextNextSecondaryAdjacent_of_fallback
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b c j hi hiNextNext hiNextNextNext hessential htriggerFailure
  have hdefect : sourceDefect < adjacentDefect := by
    have hshifted : (commonShift : WithTop ℚ) + sourceDefect <
        (commonShift : WithTop ℚ) + adjacentDefect := by
      rw [← hsource]
      exact hstrict.trans htarget
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted
  have hdefect' : sourceDefect <
      a.truncatedPrefixDefect a (-1) (j.val + 4) (j.val + 2) := by
    rw [a.truncatedPrefixDefect_comm a (-1)
      (j.val + 4) (j.val + 2)]
    exact hdefect
  have htriangle := a.truncatedPrefixDefect_eq_middle_of_lt_composite
    b a 1 (-1) (by simp) (by simp) (j.val + 4) j.val
      (j.val + 2) (by simpa only [one_mul] using hdefect')
  calc
    a.truncatedPrefixDefect b 1 (j.val + 4) j.val =
        b.truncatedPrefixDefect a (-1) j.val (j.val + 2) := htriangle
    _ = a.truncatedPrefixDefect b (-1) (j.val + 2) j.val :=
      b.truncatedPrefixDefect_comm a (-1) j.val (j.val + 2)

/-- After the secondary triangle, its shifted candidate is strictly larger
than the desired fallback bound. -/
theorem nextFallback_lt_shiftedNextNextSecondary_of_fallback
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hiNextNextNext : j.val + 3 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hnextPrimary : a.representationAlpha b
      (nextRepresentationIndex j hi.2) =
        a.representationPrimaryDefect b
          (nextRepresentationIndex j hi.2))
    (hnextNextSecondary : a.representationAlpha b
      (⟨j.val + 2, by omega, hiNextNext, by omega⟩ :
        RepresentationIndex (n + 1) (n + 1)) =
      a.representationSecondaryDefect b
        (⟨j.val + 2, by omega, hiNextNext, by omega⟩ :
          RepresentationIndex (n + 1) (n + 1))
        (by
          change 1 < j.val + 2 ∧ j.val + 2 + 1 < n + 1
          omega))
    (hreplace : a.truncatedPrefixDefect b 1 (j.val + 4) j.val =
      a.truncatedPrefixDefect b (-1) (j.val + 2) j.val) :
    a.nextFallbackBound b j hi.2 <
      let nextNext : RepresentationIndex (n + 1) (n + 1) :=
        ⟨j.val + 2, by omega, hiNextNext, by omega⟩
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext := by
  let next := nextRepresentationIndex j hi.2
  let nextNext : RepresentationIndex (n + 1) (n + 1) :=
    ⟨j.val + 2, by omega, hiNextNext, by omega⟩
  let hinterior : 1 < nextNext.val ∧ nextNext.val + 1 < n + 1 :=
    ⟨by dsimp only [nextNext]; omega,
      by dsimp only [nextNext]; omega⟩
  let fallbackShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ)
  let secondaryShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 2, hiNextNext⟩ +
    a.order ⟨j.val + 3, hiNextNextNext⟩ -
    a.order ⟨j.val + 1, hi.2⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hpairRaw := hessential.2 hi.1 hiNextNext
  have hpair :
      c.order ⟨j.val - 2, by omega⟩ +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ +
          a.order ⟨j.val + 2, hiNextNext⟩ := by
    simpa only [orderSequence_at, nextEssentialIndex] using hpairRaw
  have htwoStep : a.order ⟨j.val + 1, hi.2⟩ ≤
      a.order ⟨j.val + 3, hiNextNextNext⟩ := by
    exact a.good ⟨j.val + 1, hi.2⟩ (by omega)
  have hsum :
      c.order ⟨j.val - 2, by omega⟩ +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 2, hiNextNext⟩ +
          a.order ⟨j.val + 3, hiNextNextNext⟩ := by
    omega
  have hshift : fallbackShift < secondaryShift := by
    dsimp only [fallbackShift, secondaryShift]
    push_cast
    have hsumQ :
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
            (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
          (a.order ⟨j.val + 2, hiNextNext⟩ : ℚ) +
            (a.order ⟨j.val + 3, hiNextNextNext⟩ : ℚ) := by
      exact_mod_cast hsum
    linarith
  have hnextFinite : a.representationAlpha b next ≠ ⊤ :=
    a.representationAlpha_ne_top b next
  dsimp only
  calc
    a.nextFallbackBound b j hi.2 =
        (fallbackShift : WithTop ℚ) + a.representationAlpha b next := by
      rfl
    _ < (secondaryShift : WithTop ℚ) +
        a.representationAlpha b next :=
      WithTop.add_lt_add_right hnextFinite (by exact_mod_cast hshift)
    _ = (secondaryShift : WithTop ℚ) +
        a.representationPrimaryDefect b next := by rw [hnextPrimary]
    _ = (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val + 1, hi.2⟩ -
          c.order ⟨j.val - 2, by omega⟩ -
          c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext := by
      rw [hnextNextSecondary]
      unfold representationPrimaryDefect representationSecondaryDefect
      simp only [next, nextNext, hinterior, nextRepresentationIndex,
        Nat.add_sub_cancel]
      rw [hreplace, ← add_assoc, ← add_assoc]
      congr 1
      norm_cast
      dsimp only [secondaryShift]
      push_cast
      ring

end BONG.GoodBONG

end Bong
