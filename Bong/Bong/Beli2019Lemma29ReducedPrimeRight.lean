/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29ReducedEquality

/-!
# Beli (2019), Lemma 2.9: the primed right-crossing branch

This file proves the primed equality required in Section 4.  The proof is
the right-crossing branch of Lemma 2.9 with the primary candidate as its
outer cut.  Remark 1.1 expands the surviving source alpha, and capped
Lemma 1.4(a) replaces the current-prefix defect by the source-adjacent one.
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

/-- In the right-crossing branch, Definition 6's primed invariant is the
minimum of the primary candidate and the shifted source-adjacent defect. -/
theorem representationAlphaPrimeReduced_eq_min_primary_sourceAdjacent
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
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
    a.representationAlphaPrimeReduced b i hi hsmall =
      min (a.representationPrimaryDefect b i)
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
          ((sourceShift : WithTop ℚ) + a.halfGapCandidate sourceIndex)
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
      (primaryShift : WithTop ℚ) + b.halfGapCandidate targetIndex :=
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
  have hprimarySourceHalf : a.representationPrimaryDefect b i ≤
      (sourceShift : WithTop ℚ) + a.halfGapCandidate sourceIndex :=
    hprimaryTargetHalf.trans hhalfStrict.le
  rw [a.representationAlphaPrimeReduced_eq_min_primary_source_of_cross
    b i hi hsmall hright]
  rw [hsourceForm]
  rw [← min_assoc, min_eq_left hprimarySourceHalf]

/-- Lemma 2.9's primed equality in the right-crossing branch. -/
theorem representationAlphaPrime_eq_primeReduced_of_rightCross
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
    (hcomparison : a.representationAlphaPrime b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val) :
    a.representationAlphaPrime b i =
      a.representationAlphaPrimeReduced b i hi hsmall := by
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let primary := a.representationPrimaryDefect b i
  let comparison := a.truncatedPrefixDefect b 1 i.val i.val
  let current := a.truncatedPrefixDefect b (-1) (i.val + 2) i.val
  let sourceAdjacent := a.truncatedPrefixDefect a (-1) i.val (i.val + 2)
  have hnormal :=
    a.representationAlphaPrime_eq_min_primary_current b i hi hright
  have hnormal' : a.representationAlphaPrime b i =
      min primary ((shift : WithTop ℚ) + current) := by
    simpa only [primary, shift, current,
      representationSecondaryCurrentDefect] using hnormal
  have hreduced :=
    a.representationAlphaPrimeReduced_eq_min_primary_sourceAdjacent
      (sourceLaws := sourceLaws) b i hi hsmall hright hshift
  have hreduced' : a.representationAlphaPrimeReduced b i hi hsmall =
      min primary ((shift : WithTop ℚ) + sourceAdjacent) := by
    simpa only [primary, shift, sourceAdjacent] using hreduced
  have hforward : min comparison current ≤ sourceAdjacent := by
    have hdom := a.truncatedPrefixDefect_domination b a
      1 (-1) i.val i.val (i.val + 2)
    rw [b.truncatedPrefixDefect_comm a (-1) i.val (i.val + 2)] at hdom
    simpa only [comparison, current, sourceAdjacent, one_mul] using hdom
  have hreverse : min comparison sourceAdjacent ≤ current := by
    have hdom := b.truncatedPrefixDefect_domination a a
      1 (-1) i.val i.val (i.val + 2)
    rw [b.truncatedPrefixDefect_comm a 1 i.val i.val,
      b.truncatedPrefixDefect_comm a (1 * (-1))
        i.val (i.val + 2)] at hdom
    simpa only [comparison, current, sourceAdjacent, one_mul] using hdom
  have hbound : min ((shift : WithTop ℚ) + current) primary ≤
      (0 : WithTop ℚ) + comparison := by
    rw [min_comm, ← hnormal']
    simpa only [zero_add, comparison] using hcomparison
  have hreplace := withTop_shifted_min_eq_of_lt_of_domination
    0 shift primary comparison current sourceAdjacent (by
      dsimp only [shift]
      exact_mod_cast hshift) hforward hreverse hbound
  calc
    a.representationAlphaPrime b i =
        min primary ((shift : WithTop ℚ) + current) := hnormal'
    _ = min ((shift : WithTop ℚ) + current) primary := min_comm _ _
    _ = min ((shift : WithTop ℚ) + sourceAdjacent) primary := hreplace
    _ = min primary ((shift : WithTop ℚ) + sourceAdjacent) := min_comm _ _
    _ = a.representationAlphaPrimeReduced b i hi hsmall := hreduced'.symm

end BONG.GoodBONG

end Bong
