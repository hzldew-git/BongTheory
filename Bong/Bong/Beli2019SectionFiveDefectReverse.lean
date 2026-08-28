/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveOddBound

/-!
# Beli (2019), Section 5: reverse-order defect certificates

This file completes the two reverse-order subcases in the proof of
condition 2.1(ii), after the collision-free profile calculation in
`Beli2019SectionFiveOddBound`.
-/

namespace Bong

open Dyadic Module

universe u v

namespace Lattice.Beli2019Lemma51Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- In the one-step reverse-order branch `R_i = S_i + 1`, Lemma 5.13(ii)
at the preceding boundary gives an odd comparison prefix.  The even source
Jordan pair preserves oddness after shifting the primary prefix lengths;
P3 and Corollary 2.8 then give `A_i ≤ alpha_i`. -/
theorem noCollision_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1) :
    a.representationAlphaValue b i ≤
      a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change a.representationAlphaValue b i ≤ a.alphaValue g
  change a.order g.castSucc = b.order g.castSucc + 1 at hcurrent
  have hgt : b.order g.castSucc < a.order g.castSucc := by omega
  rcases D.noCollision_source_previous_twoStep_eq_before_selected_of_current_gt
      hsmall hlarge hselected a b g hbefore hgt with
    ⟨hpos, hnext, htwo, hpreviousStrict, hcurrentCases,
      hgapEquality, hevenPair, hgapEven, hgapLt⟩
  have hiPrevious : 1 < i.val := by
    change 0 < i.val - 1 at hpos
    omega
  have hiLarge := i.lt_large
  have hiSmall := i.le_small
  have hpreviousCurrent :
      b.order ⟨g.val - 1, by omega⟩ =
        a.order ⟨g.val - 1, by omega⟩ + 1 := by
    omega
  let j : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val - 1, by omega, by omega, by omega⟩
  have hj : D.Lemma517Range j := by
    change j.val ≤ D.lemma517Cutoff
    change i.val ≤ D.lemma517Cutoff at hi
    dsimp only [j]
    omega
  have hentryIndex :
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 2)) =
        ⟨g.val - 1, by omega⟩ := by
    apply Fin.ext
    rfl
  have hpreviousEntry :
      b.orderSequence.entryOrZero (j.val - 1) =
        a.orderSequence.entryOrZero (j.val - 1) + 1 := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := j.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := j.lt_large; omega),
      BONG.GoodBONG.orderSequence_at, BONG.GoodBONG.orderSequence_at,
      hentryIndex]
    exact hpreviousCurrent
  let localData := D.noCollision_aligned_lemma513LocalData
    hsmall hlarge hselected a b
  have hpreviousSum :=
    localData.previousPrefixSum_eq j hj hpreviousEntry
  have hprefixOddRaw :=
    a.comparisonPrefixProduct_order_odd_of_previous_prefix_eq b
      j.val j.pos j.lt_large.le j.lt_large.le hpreviousSum hpreviousEntry
  have hprefixOdd : Odd (ordUnit K
      (a.prefixProduct (i.val - 1) * b.prefixProduct (i.val - 1))) := by
    simpa only [j] using hprefixOddRaw
  have hnextIndex :
      (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hcurrentIndex : g.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hevenCurrentNext : Even
      (a.order ⟨i.val - 1, by omega⟩ +
        a.order ⟨i.val, i.lt_large⟩) := by
    have hpair := hevenPair
    rw [htwo, hnextIndex, hcurrentIndex] at hpair
    simpa only [add_comm] using hpair
  have hshiftOdd :=
    a.shiftedPrimaryProduct_odd_of_previousPrefix_odd_of_sourcePair_even
      b i hiPrevious hprefixOdd hevenCurrentNext
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed b
    (-1) (i.val + 1) (i.val - 1) hshiftOdd
  have hcandidate :=
    a.representationAlphaValue_le_primaryCoefficient_of_defect_zero b i hzero
  have halphaLower :=
    a.orderGap_add_one_le_alphaValue_of_even_of_lt_twoE g hgapEven hgapLt
  have hnextGapIndex : g.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hcurrentGapIndex : g.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := hcurrentIndex
  push_cast at hcandidate
  push_cast at halphaLower
  unfold BONG.GoodBONG.orderGap at halphaLower
  rw [hnextGapIndex, hcurrentGapIndex] at halphaLower
  push_cast at halphaLower
  have hcurrentQ : (a.order g.castSucc : ℚ) =
      (b.order g.castSucc : ℚ) + 1 := by exact_mod_cast hcurrent
  rw [hcurrentGapIndex] at hcurrentQ
  linarith

end Lattice.Beli2019Lemma51Data

end Bong
