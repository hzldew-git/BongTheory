/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29ReducedNormalForm
import Bong.Bong.Beli2019Lemma29ComparisonReduction
import Bong.Bong.Beli2019AlphaLocalFormula

/-!
# Beli (2019), Lemma 2.9: equality with the reduced invariant

The positive secondary coefficient gives three order cases.  If both
crossing inequalities hold, Lemma 2.7(iii) replaces the secondary defect
by the comparison defect.  In either one-sided case, Remark 1.1 expands
the remaining alpha candidate and capped Lemma 1.4(a) performs the same
replacement.  This file first proves the two one-sided normal forms.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Lemma 2.7(ii) written with the common half-gap/primary cut outside
the current-prefix secondary candidate. -/
theorem representationAlpha_eq_min_common_secondaryCurrent
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hright : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationAlpha b i =
      min
        (min (a.representationHalfGap b i)
          (a.representationPrimaryDefect b i))
        (a.representationSecondaryCurrentDefect b i hi) := by
  rw [a.representationAlpha_eq_min_halfGap_prime b i,
    a.representationAlphaPrime_eq_min_primary_current b i hi hright,
    min_assoc]

/-- In the right-crossing branch, the reduced invariant is the minimum
of the common cut and the shifted source adjacent defect. -/
theorem representationAlphaReduced_eq_min_common_sourceAdjacent
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hright : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩) :
    a.representationAlphaReduced b i hi hsmall =
      min
        (min (a.representationHalfGap b i)
          (a.representationPrimaryDefect b i))
        ((((a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.truncatedPrefixDefect a (-1) i.val (i.val + 2)) := by
  let sourceIndex : Fin m := ⟨i.val, by omega⟩
  let targetIndex : Fin n := ⟨i.val - 2, by omega⟩
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let sourceShift : ℚ :=
    ((2 * a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let sourceGap : ℚ :=
    ((a.order ⟨i.val + 1, hi.2⟩ -
      a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ)
  let primaryShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let common := min (a.representationHalfGap b i)
    (a.representationPrimaryDefect b i)
  let sourceAdjacent :=
    a.truncatedPrefixDefect a (-1) i.val (i.val + 2)
  have hsourceSucc : sourceIndex.succ =
      (⟨i.val + 1, hi.2⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hsourceCast : sourceIndex.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetIndex.succ =
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetIndex, Fin.val_succ]
    omega
  have htargetCast : targetIndex.castSucc =
      (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have halpha := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact a.alpha_eq_min_halfGap_add_cappedAdjacent sourceIndex
  rw [hsourceSucc, hsourceCast] at halpha
  have hshiftEq : sourceShift + sourceGap = shift := by
    dsimp only [sourceShift, sourceGap, shift]
    push_cast
    ring
  have hsourceForm :
      a.representationSecondarySourceAlpha b i hi =
        min
          ((sourceShift : WithTop ℚ) +
            a.halfGapCandidate sourceIndex)
          ((shift : WithTop ℚ) + sourceAdjacent) := by
    unfold representationSecondarySourceAlpha
    change (sourceShift : WithTop ℚ) +
        (a.alphaValue sourceIndex : WithTop ℚ) = _
    rw [halpha, add_min]
    congr 1
    calc
      (sourceShift : WithTop ℚ) +
          ((sourceGap : WithTop ℚ) + sourceAdjacent) =
        ((sourceShift + sourceGap : ℚ) : WithTop ℚ) +
          sourceAdjacent := by norm_num [add_assoc]
      _ = (shift : WithTop ℚ) + sourceAdjacent := by rw [hshiftEq]
  have hprimaryCap : a.representationPrimaryDefect b i ≤
      (primaryShift : WithTop ℚ) +
        (b.alphaValue targetIndex : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
      (i.val + 1) (i.val - 1)
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hcap' :
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
          (b.alphaValue targetIndex : WithTop ℚ) := by
      simpa only [targetIndex,
        show i.val - 1 - 1 = i.val - 2 by omega] using hcap
    unfold representationPrimaryDefect
    simpa only [primaryShift] using add_le_add_right hcap' _
  have htargetHalf : (b.alphaValue targetIndex : WithTop ℚ) ≤
      b.halfGapCandidate targetIndex := by
    rw [← b.coe_halfGapValue targetIndex]
    exact_mod_cast b.alphaValue_le_halfGapValue targetIndex
  have hprimaryTargetHalf : a.representationPrimaryDefect b i ≤
      (primaryShift : WithTop ℚ) +
        b.halfGapCandidate targetIndex :=
    hprimaryCap.trans (add_le_add le_rfl htargetHalf)
  have hhalfStrict :
      (primaryShift : WithTop ℚ) + b.halfGapCandidate targetIndex <
        (sourceShift : WithTop ℚ) +
          a.halfGapCandidate sourceIndex := by
    unfold halfGapCandidate
    rw [hsourceSucc, hsourceCast, htargetSucc, htargetCast]
    norm_cast
    simp only [Rat.divInt_eq_div]
    have hshiftQ : (0 : ℚ) < shift := by
      dsimp only [shift]
      exact_mod_cast hshift
    dsimp only [primaryShift, sourceShift, shift] at *
    push_cast at *
    linarith
  have hcommonHalf : common ≤
      (sourceShift : WithTop ℚ) +
        a.halfGapCandidate sourceIndex := by
    exact (min_le_right _ _).trans
      (hprimaryTargetHalf.trans hhalfStrict.le)
  rw [a.representationAlphaReduced_eq_min_halfGap_primary_source_of_cross
    b i hi hsmall hright]
  rw [hsourceForm]
  rw [← min_assoc (a.representationHalfGap b i)
    (a.representationPrimaryDefect b i),
    ← min_assoc
      (min (a.representationHalfGap b i)
        (a.representationPrimaryDefect b i))
      ((sourceShift : WithTop ℚ) + a.halfGapCandidate sourceIndex),
    min_eq_left hcommonHalf]

/-- Lemma 2.9 in the right-crossing branch.  Capped Lemma 1.4(a)
replaces the current-prefix secondary defect by the source adjacent
defect under the common half-gap/primary cut. -/
theorem representationAlpha_eq_reduced_of_rightCross
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hright : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hcomparison : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val) :
    a.representationAlpha b i =
      a.representationAlphaReduced b i hi hsmall := by
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let common := min (a.representationHalfGap b i)
    (a.representationPrimaryDefect b i)
  let comparison := a.truncatedPrefixDefect b 1 i.val i.val
  let current :=
    a.truncatedPrefixDefect b (-1) (i.val + 2) i.val
  let sourceAdjacent :=
    a.truncatedPrefixDefect a (-1) i.val (i.val + 2)
  have hnormal :=
    a.representationAlpha_eq_min_common_secondaryCurrent b i hi hright
  have hnormal' : a.representationAlpha b i =
      min common ((shift : WithTop ℚ) + current) := by
    simpa only [common, shift, current,
      representationSecondaryCurrentDefect] using hnormal
  have hreduced :=
    a.representationAlphaReduced_eq_min_common_sourceAdjacent
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b i hi hsmall hright hshift
  have hreduced' : a.representationAlphaReduced b i hi hsmall =
      min common ((shift : WithTop ℚ) + sourceAdjacent) := by
    simpa only [common, shift, sourceAdjacent] using hreduced
  have hforward : min comparison current ≤ sourceAdjacent := by
    have hdom := a.truncatedPrefixDefect_domination b a
      1 (-1) i.val i.val (i.val + 2)
    rw [b.truncatedPrefixDefect_comm a (-1)
      i.val (i.val + 2)] at hdom
    simpa only [comparison, current, sourceAdjacent, one_mul] using hdom
  have hreverse : min comparison sourceAdjacent ≤ current := by
    have hdom := b.truncatedPrefixDefect_domination a a
      1 (-1) i.val i.val (i.val + 2)
    rw [b.truncatedPrefixDefect_comm a 1 i.val i.val,
      b.truncatedPrefixDefect_comm a (1 * (-1))
        i.val (i.val + 2)] at hdom
    simpa only [comparison, current, sourceAdjacent, one_mul] using hdom
  have hbound : min ((shift : WithTop ℚ) + current) common ≤
      (0 : WithTop ℚ) + comparison := by
    rw [min_comm, ← hnormal']
    simpa only [zero_add, comparison] using hcomparison
  have hreplace := withTop_shifted_min_eq_of_lt_of_domination
    0 shift common comparison current sourceAdjacent (by
      dsimp only [shift]
      exact_mod_cast hshift) hforward hreverse hbound
  calc
    a.representationAlpha b i =
        min common ((shift : WithTop ℚ) + current) := hnormal'
    _ = min ((shift : WithTop ℚ) + current) common := min_comm _ _
    _ = min ((shift : WithTop ℚ) + sourceAdjacent) common := hreplace
    _ = min common ((shift : WithTop ℚ) + sourceAdjacent) := min_comm _ _
    _ = a.representationAlphaReduced b i hi hsmall := hreduced'.symm

/-- Lemma 2.7(i) with the common half-gap/primary cut outside the
previous-prefix secondary candidate. -/
theorem representationAlpha_eq_min_common_secondaryPrevious
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hleft : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩) :
    a.representationAlpha b i =
      min
        (min (a.representationHalfGap b i)
          (a.representationPrimaryDefect b i))
        (a.representationSecondaryPreviousDefect b i hi) := by
  rw [a.representationAlpha_eq_min_halfGap_prime b i,
    a.representationAlphaPrime_eq_min_primary_previous b i hi hleft,
    min_assoc]

/-- In the left-crossing branch, the reduced invariant is the minimum
of the common cut and the shifted target adjacent defect. -/
theorem representationAlphaReduced_eq_min_common_targetAdjacent
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hleft : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩) :
    a.representationAlphaReduced b i hi hsmall =
      min
        (min (a.representationHalfGap b i)
          (a.representationPrimaryDefect b i))
        ((((a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          b.truncatedPrefixDefect b (-1) (i.val - 2) i.val) := by
  let sourceIndex : Fin m := ⟨i.val, by omega⟩
  let targetIndex : Fin n := ⟨i.val - 2, by omega⟩
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      2 * b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let targetGap : ℚ :=
    ((b.order ⟨i.val - 1, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ : Int) : ℚ)
  let primaryShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let common := min (a.representationHalfGap b i)
    (a.representationPrimaryDefect b i)
  let targetAdjacent :=
    b.truncatedPrefixDefect b (-1) (i.val - 2) i.val
  have hsourceSucc : sourceIndex.succ =
      (⟨i.val + 1, hi.2⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hsourceCast : sourceIndex.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetIndex.succ =
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetIndex, Fin.val_succ]
    omega
  have htargetCast : targetIndex.castSucc =
      (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hbeta := by
    letI : Beli2006AlphaLaws.{u, w} K := targetLaws
    exact b.alpha_eq_min_halfGap_add_cappedAdjacent targetIndex
  rw [htargetSucc, htargetCast] at hbeta
  have htargetNext : targetIndex.val + 2 = i.val := by
    dsimp only [targetIndex]
    omega
  rw [htargetNext] at hbeta
  have hshiftEq : targetShift + targetGap = shift := by
    dsimp only [targetShift, targetGap, shift]
    push_cast
    ring
  have htargetForm :
      a.representationSecondaryTargetAlpha b i hi hsmall =
        min
          ((targetShift : WithTop ℚ) +
            b.halfGapCandidate targetIndex)
          ((shift : WithTop ℚ) + targetAdjacent) := by
    unfold representationSecondaryTargetAlpha
    change (targetShift : WithTop ℚ) +
        (b.alphaValue targetIndex : WithTop ℚ) = _
    rw [hbeta, add_min]
    congr 1
    calc
      (targetShift : WithTop ℚ) +
          ((targetGap : WithTop ℚ) + targetAdjacent) =
        ((targetShift + targetGap : ℚ) : WithTop ℚ) +
          targetAdjacent := by norm_num [add_assoc]
      _ = (shift : WithTop ℚ) + targetAdjacent := by rw [hshiftEq]
  have hprimaryCap : a.representationPrimaryDefect b i ≤
      (primaryShift : WithTop ℚ) +
        (a.alphaValue sourceIndex : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b (-1)
      (i.val + 1) (i.val - 1)
    rw [a.prefixAlphaCap_of_internal (by omega) hi.2] at hcap
    have hcap' :
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
          (a.alphaValue sourceIndex : WithTop ℚ) := by
      simpa only [sourceIndex,
        show i.val + 1 - 1 = i.val by omega] using hcap
    unfold representationPrimaryDefect
    simpa only [primaryShift] using add_le_add_right hcap' _
  have hsourceHalf : (a.alphaValue sourceIndex : WithTop ℚ) ≤
      a.halfGapCandidate sourceIndex := by
    rw [← a.coe_halfGapValue sourceIndex]
    exact_mod_cast a.alphaValue_le_halfGapValue sourceIndex
  have hprimarySourceHalf : a.representationPrimaryDefect b i ≤
      (primaryShift : WithTop ℚ) +
        a.halfGapCandidate sourceIndex :=
    hprimaryCap.trans (add_le_add le_rfl hsourceHalf)
  have hhalfStrict :
      (primaryShift : WithTop ℚ) + a.halfGapCandidate sourceIndex <
        (targetShift : WithTop ℚ) +
          b.halfGapCandidate targetIndex := by
    unfold halfGapCandidate
    rw [hsourceSucc, hsourceCast, htargetSucc, htargetCast]
    norm_cast
    simp only [Rat.divInt_eq_div]
    have hshiftQ : (0 : ℚ) < shift := by
      dsimp only [shift]
      exact_mod_cast hshift
    dsimp only [primaryShift, targetShift, shift] at *
    push_cast at *
    linarith
  have hcommonHalf : common ≤
      (targetShift : WithTop ℚ) +
        b.halfGapCandidate targetIndex := by
    exact (min_le_right _ _).trans
      (hprimarySourceHalf.trans hhalfStrict.le)
  rw [a.representationAlphaReduced_eq_min_halfGap_primary_target_of_cross
    b i hi hsmall hleft]
  rw [htargetForm]
  rw [← min_assoc (a.representationHalfGap b i)
    (a.representationPrimaryDefect b i),
    ← min_assoc
      (min (a.representationHalfGap b i)
        (a.representationPrimaryDefect b i))
      ((targetShift : WithTop ℚ) + b.halfGapCandidate targetIndex),
    min_eq_left hcommonHalf]

/-- Lemma 2.9 in the left-crossing branch. -/
theorem representationAlpha_eq_reduced_of_leftCross
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hleft : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hcomparison : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val) :
    a.representationAlpha b i =
      a.representationAlphaReduced b i hi hsmall := by
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let common := min (a.representationHalfGap b i)
    (a.representationPrimaryDefect b i)
  let comparison := a.truncatedPrefixDefect b 1 i.val i.val
  let previous :=
    a.truncatedPrefixDefect b (-1) i.val (i.val - 2)
  let targetAdjacent :=
    b.truncatedPrefixDefect b (-1) (i.val - 2) i.val
  have hnormal := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact a.representationAlpha_eq_min_common_secondaryPrevious b i hi hleft
  have hnormal' : a.representationAlpha b i =
      min common ((shift : WithTop ℚ) + previous) := by
    simpa only [common, shift, previous,
      representationSecondaryPreviousDefect] using hnormal
  have hreduced :=
    a.representationAlphaReduced_eq_min_common_targetAdjacent
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b i hi hsmall hleft hshift
  have hreduced' : a.representationAlphaReduced b i hi hsmall =
      min common ((shift : WithTop ℚ) + targetAdjacent) := by
    simpa only [common, shift, targetAdjacent] using hreduced
  have hforward : min comparison previous ≤ targetAdjacent := by
    have hdom := b.truncatedPrefixDefect_domination a b
      1 (-1) i.val i.val (i.val - 2)
    rw [b.truncatedPrefixDefect_comm a 1 i.val i.val,
      b.truncatedPrefixDefect_comm b (1 * (-1))
        i.val (i.val - 2)] at hdom
    simpa only [comparison, previous, targetAdjacent, one_mul] using hdom
  have hreverse : min comparison targetAdjacent ≤ previous := by
    have hdom := a.truncatedPrefixDefect_domination b b
      1 (-1) i.val i.val (i.val - 2)
    rw [b.truncatedPrefixDefect_comm b (-1)
      i.val (i.val - 2)] at hdom
    simpa only [comparison, previous, targetAdjacent, one_mul] using hdom
  have hbound : min ((shift : WithTop ℚ) + previous) common ≤
      (0 : WithTop ℚ) + comparison := by
    rw [min_comm, ← hnormal']
    simpa only [zero_add, comparison] using hcomparison
  have hreplace := withTop_shifted_min_eq_of_lt_of_domination
    0 shift common comparison previous targetAdjacent (by
      dsimp only [shift]
      exact_mod_cast hshift) hforward hreverse hbound
  calc
    a.representationAlpha b i =
        min common ((shift : WithTop ℚ) + previous) := hnormal'
    _ = min ((shift : WithTop ℚ) + previous) common := min_comm _ _
    _ = min ((shift : WithTop ℚ) + targetAdjacent) common := hreplace
    _ = min common ((shift : WithTop ℚ) + targetAdjacent) := min_comm _ _
    _ = a.representationAlphaReduced b i hi hsmall := hreduced'.symm

/-- Beli (2019), Lemma 2.9 in the form used by Section 4.  A positive
secondary coefficient forces at least one of the two crossing inequalities,
so the two preceding branches cover all cases. -/
theorem representationAlpha_eq_reduced_of_positiveShift
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hcomparison : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val) :
    a.representationAlpha b i =
      a.representationAlphaReduced b i hi hsmall := by
  by_cases hleft :
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
        a.order ⟨i.val, i.lt_large⟩
  · exact a.representationAlpha_eq_reduced_of_leftCross
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b i hi hsmall hleft hshift hcomparison
  · have hright :
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
          a.order ⟨i.val + 1, hi.2⟩ := by
      omega
    exact a.representationAlpha_eq_reduced_of_rightCross
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b i hi hsmall hright hshift hcomparison

end BONG.GoodBONG

end Bong
