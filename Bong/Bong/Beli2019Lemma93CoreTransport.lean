/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseTwoSubcaseB

/-!
# Beli (2019), Lemma 9.3: transport of the primary core defects

The low-index argument repeatedly compares the capped defects
`d[-a_(1,i+1)b_(1,i-1)]` before and after deleting equal heads.  This file
isolates that common calculation.  Equality of one such core defect transports
the corresponding primary candidate; the same equality one step to the left
or right transports the two Lemma 2.7 replacement forms of the secondary
candidate.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Deleting equal heads can only increase the primary capped defect at the
corresponding tail boundary. -/
theorem primaryCoreDefect_shift_le_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (i : RepresentationIndex (n + 1) (n + 1)) :
    a.truncatedPrefixDefect b (-1) (i.val + 2) i.val ≤
      a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 1) (i.val - 1) := by
  have hipos := i.pos
  have hilarge := i.lt_large
  have h := a.truncatedPrefixDefect_shift_le_tail_general b hhead (-1)
    (i.val + 1) (i.val - 1) (by omega) (by omega)
  simpa only [show i.val + 1 + 1 = i.val + 2 by omega,
    show i.val - 1 + 1 = i.val by omega] using h

/-- Lemma 9.2's later alpha equalities give exact core-defect transport from
tail value four onward. -/
theorem primaryCoreDefect_shift_eq_tail_of_laterAlphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 2 ≤ k.val →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n, 2 ≤ k.val →
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 4 ≤ i.val) :
    a.truncatedPrefixDefect b (-1) (i.val + 2) i.val =
      a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 1) (i.val - 1) := by
  have hilarge := i.lt_large
  have hcapA := a.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
    halphaA (i.val + 1) (by omega) (by omega)
  have hcapB := b.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
    halphaB (i.val - 1) (by omega) (by omega)
  have h := a.truncatedPrefixDefect_shift_eq_tail_of_caps_eq b hhead (-1)
    (i.val + 1) (i.val - 1) (by omega) (by omega) hcapA hcapB
  simpa only [show i.val + 1 + 1 = i.val + 2 by omega,
    show i.val - 1 + 1 = i.val by omega] using h

/-- Equality of the capped core defect is exactly equality of the primary
comparison candidate, since the order coefficient is unchanged by the tail
shift. -/
theorem representationPrimaryDefect_tail_eq_shift_of_core_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcore : a.truncatedPrefixDefect b (-1) (i.val + 2) i.val =
      a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 1) (i.val - 1)) :
    a.tail.representationPrimaryDefect b.tail i =
      a.representationPrimaryDefect b i.tailShift := by
  have hipos := i.pos
  have hilarge := i.lt_large
  have hshiftLarge := i.tailShift.lt_large
  unfold representationPrimaryDefect
  rw [a.order_goodTail, b.order_goodTail]
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourceIndex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, hsourceIndex]
  convert congrArg (fun d : WithTop ℚ =>
    ((((a.order ⟨i.val + 1, by omega⟩ -
        b.order ⟨i.val, by omega⟩ : Int) : ℚ) : WithTop ℚ) + d))
      hcore.symm using 1 <;>
    congr 2 <;> apply Fin.ext <;>
      simp only [RepresentationIndex.tailShift_val, Fin.val_mk] <;> omega

/-- A strict increase of the core defect gives a strict increase of the
primary comparison candidate. -/
theorem representationPrimaryDefect_shift_lt_tail_of_core_lt
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcore : a.truncatedPrefixDefect b (-1) (i.val + 2) i.val <
      a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 1) (i.val - 1)) :
    a.representationPrimaryDefect b i.tailShift <
      a.tail.representationPrimaryDefect b.tail i := by
  have hipos := i.pos
  have hilarge := i.lt_large
  have hshiftLarge := i.tailShift.lt_large
  unfold representationPrimaryDefect
  rw [a.order_goodTail, b.order_goodTail]
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourceIndex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, hsourceIndex]
  convert WithTop.add_lt_add_left WithTop.coe_ne_top hcore using 1 <;>
    congr 2 <;> apply Fin.ext <;>
      simp only [RepresentationIndex.tailShift_val, Fin.val_mk] <;> omega

/-- The core equality one boundary to the left transports Lemma 2.7(i)'s
previous-form secondary candidate. -/
theorem representationSecondaryPreviousDefect_tail_eq_shift_of_core_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hcore : a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) =
      a.tail.truncatedPrefixDefect b.tail (-1) i.val (i.val - 2)) :
    a.tail.representationSecondaryPreviousDefect b.tail i hi =
      a.representationSecondaryPreviousDefect b i.tailShift
        ⟨by
          simp only [RepresentationIndex.tailShift_val]
          omega,
         by
          simp only [RepresentationIndex.tailShift_val]
          omega⟩ := by
  have hipos := i.pos
  have hilarge := i.lt_large
  unfold representationSecondaryPreviousDefect
  rw [a.order_goodTail, a.order_goodTail,
    b.order_goodTail, b.order_goodTail]
  simp only [RepresentationIndex.tailShift_val]
  have haCurrent : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  have haNext : (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val + 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  have hbPrevious : (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  have hbCurrent : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  rw [haCurrent, haNext, hbPrevious, hbCurrent]
  convert congrArg (fun d : WithTop ℚ =>
    (((a.order ⟨i.val + 1, by omega⟩ +
        a.order ⟨i.val + 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩ -
        b.order ⟨i.val, by omega⟩ : Int) : ℚ) : WithTop ℚ) + d)
      hcore.symm using 1 <;>
    congr 2 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- Monotone form of the preceding transport lemma.  If deleting the common
head raises the preceding core defect, it raises the previous-form secondary
candidate by the same amount. -/
theorem representationSecondaryPreviousDefect_shift_le_tail_of_core_le
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hcore : a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
      a.tail.truncatedPrefixDefect b.tail (-1) i.val (i.val - 2)) :
    a.representationSecondaryPreviousDefect b i.tailShift
        ⟨by
          simp only [RepresentationIndex.tailShift_val]
          omega,
         by
          simp only [RepresentationIndex.tailShift_val]
          omega⟩ ≤
      a.tail.representationSecondaryPreviousDefect b.tail i hi := by
  have hipos := i.pos
  have hilarge := i.lt_large
  unfold representationSecondaryPreviousDefect
  rw [a.order_goodTail, a.order_goodTail,
    b.order_goodTail, b.order_goodTail]
  simp only [RepresentationIndex.tailShift_val]
  have haCurrent : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  have haNext : (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val + 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  have hbPrevious : (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  have hbCurrent : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  rw [haCurrent, haNext, hbPrevious, hbCurrent]
  let coefficient : WithTop ℚ :=
    (((a.order ⟨i.val + 1, by omega⟩ +
        a.order ⟨i.val + 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩ -
        b.order ⟨i.val, by omega⟩ : Int) : ℚ) : WithTop ℚ)
  change coefficient +
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
    coefficient +
      a.tail.truncatedPrefixDefect b.tail (-1) i.val (i.val - 2)
  simpa only [add_comm] using add_le_add_left hcore coefficient

/-- The core equality one boundary to the right transports Lemma 2.7(ii)'s
current-form secondary candidate. -/
theorem representationSecondaryCurrentDefect_tail_eq_shift_of_core_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hcore : a.truncatedPrefixDefect b (-1) (i.val + 3) (i.val + 1) =
      a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 2) i.val) :
    a.tail.representationSecondaryCurrentDefect b.tail i hi =
      a.representationSecondaryCurrentDefect b i.tailShift
        ⟨by
          simp only [RepresentationIndex.tailShift_val]
          omega,
         by
          simp only [RepresentationIndex.tailShift_val]
          omega⟩ := by
  have hipos := i.pos
  have hilarge := i.lt_large
  unfold representationSecondaryCurrentDefect
  rw [a.order_goodTail, a.order_goodTail,
    b.order_goodTail, b.order_goodTail]
  simp only [RepresentationIndex.tailShift_val]
  have haCurrent : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  have haNext : (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val + 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  have hbPrevious : (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  have hbCurrent : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  rw [haCurrent, haNext, hbPrevious, hbCurrent]
  convert congrArg (fun d : WithTop ℚ =>
    (((a.order ⟨i.val + 1, by omega⟩ +
        a.order ⟨i.val + 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩ -
        b.order ⟨i.val, by omega⟩ : Int) : ℚ) : WithTop ℚ) + d)
      hcore.symm using 1 <;>
    congr 2 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- Current essentiality gives the left crossing inequality used in Lemma
2.7(i), at an arbitrary interior comparison boundary. -/
theorem order_previous_lt_current_of_currentEssential
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val) (hinterior : i.val + 1 < n + 1)
    (h : a.IsCurrentEssential b i) :
    b.order ⟨i.val - 2, by omega⟩ <
      a.order ⟨i.val, i.lt_large⟩ := by
  unfold IsCurrentEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at h
  have hcross := h.1 (by
    simp only [currentEssentialIndex]
    omega) (by
    simp only [currentEssentialIndex]
    omega)
  simpa only [orderSequence_at, currentEssentialIndex,
    show i.val - 1 - 1 = i.val - 2 by omega,
    show i.val - 1 + 1 = i.val by omega] using hcross

/-- Next essentiality gives the right crossing inequality used in Lemma
2.7(ii), at an arbitrary interior comparison boundary. -/
theorem order_current_lt_next_of_nextEssential
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val) (hinterior : i.val + 1 < n + 1)
    (h : a.IsNextEssential b i) :
    b.order ⟨i.val - 1, by omega⟩ <
      a.order ⟨i.val + 1, hinterior⟩ := by
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at h
  have hcross := h.1 (by
    simp only [nextEssentialIndex]
    omega) (by
    simp only [nextEssentialIndex]
    omega)
  simpa only [orderSequence_at, nextEssentialIndex] using hcross

set_option maxHeartbeats 800000 in
-- The two essentiality branches use different dependent Lemma 2.7 normal forms.
/-- If the primary core at a boundary and the appropriate adjacent core are
unchanged, then the complete comparison invariant is unchanged at every
important noninitial boundary.  Current essentiality uses the preceding core;
next essentiality uses the following core. -/
theorem representationAlpha_tail_eq_shift_of_core_eq_at_important
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val)
    (himportant : a.tail.IsCurrentEssential b.tail i ∨
      a.tail.IsNextEssential b.tail i)
    (hcore : a.truncatedPrefixDefect b (-1) (i.val + 2) i.val =
      a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 1) (i.val - 1))
    (hprevious : a.tail.IsCurrentEssential b.tail i →
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) =
        a.tail.truncatedPrefixDefect b.tail (-1) i.val (i.val - 2))
    (hnext : a.tail.IsNextEssential b.tail i →
      a.truncatedPrefixDefect b (-1) (i.val + 3) (i.val + 1) =
        a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 2) i.val) :
    a.tail.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift := by
  have hprimary :=
    a.representationPrimaryDefect_tail_eq_shift_of_core_eq b i hcore
  rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i,
    a.representationAlpha_eq_min_halfGap_prime b i.tailShift,
    a.representationHalfGap_tail_eq_shift b i]
  by_cases hinterior : i.val + 1 < n + 1
  · have hiTail : 1 < i.val ∧ i.val + 1 < n + 1 :=
      ⟨hi, hinterior⟩
    have hiOriginal :
        1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rcases himportant with hcurrent | hnextEssential
    · letI : Beli2006AlphaLaws.{u, v} K := alphaV
      have hcrossTail :=
        order_previous_lt_current_of_currentEssential
          a.tail b.tail i hi hinterior hcurrent
      have hcrossOriginal :
          b.order ⟨i.tailShift.val - 2, by omega⟩ ≤
            a.order ⟨i.tailShift.val, i.tailShift.lt_large⟩ := by
        have hcross := hcrossTail.le
        rw [b.order_goodTail, a.order_goodTail] at hcross
        convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp only [RepresentationIndex.tailShift_val, Fin.val_mk,
            Fin.val_succ] <;> omega
      have hpreviousEq :=
        a.representationSecondaryPreviousDefect_tail_eq_shift_of_core_eq
          b i hiTail (hprevious hcurrent)
      rw [a.tail.representationAlphaPrime_eq_min_primary_previous
          b.tail i hiTail hcrossTail.le,
        a.representationAlphaPrime_eq_min_primary_previous
          b i.tailShift hiOriginal hcrossOriginal,
        hprimary, hpreviousEq]
    · letI : Beli2006AlphaLaws.{u, w} K := alphaW
      have hcrossTail :=
        order_current_lt_next_of_nextEssential
          a.tail b.tail i hi hinterior hnextEssential
      have hcrossOriginal :
          b.order ⟨i.tailShift.val - 1, by omega⟩ ≤
            a.order ⟨i.tailShift.val + 1, hiOriginal.2⟩ := by
        have hcross := hcrossTail.le
        rw [b.order_goodTail, a.order_goodTail] at hcross
        convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp only [RepresentationIndex.tailShift_val, Fin.val_mk,
            Fin.val_succ] <;> omega
      have hcurrentEq :=
        a.representationSecondaryCurrentDefect_tail_eq_shift_of_core_eq
          b i hiTail (hnext hnextEssential)
      rw [a.tail.representationAlphaPrime_eq_min_primary_current
          b.tail i hiTail hcrossTail.le,
        a.representationAlphaPrime_eq_min_primary_current
          b i.tailShift hiOriginal hcrossOriginal,
        hprimary, hcurrentEq]
  · have hnotTail : ¬(1 < i.val ∧ i.val + 1 < n + 1) := by
      omega
    have hnotOriginal :
        ¬(1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2) := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rw [a.tail.representationAlphaPrime_eq_primary_of_not_interior
        b.tail i hnotTail,
      a.representationAlphaPrime_eq_primary_of_not_interior
        b i.tailShift hnotOriginal, hprimary]

set_option maxHeartbeats 1200000 in
-- This is the reusable minimum calculation behind the strict-primary branches.
/-- If the shifted original invariant lies strictly below its primary
candidate, increasing that candidate under head deletion does not change the
invariant.  At an important boundary Lemma 2.7 selects an adjacent core that
is assumed to transport exactly. -/
theorem representationAlpha_tail_eq_shift_of_alpha_lt_primary_at_important
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val)
    (hinterior : i.val + 1 < n + 1)
    (himportant : a.tail.IsCurrentEssential b.tail i ∨
      a.tail.IsNextEssential b.tail i)
    (halpha : a.representationAlpha b i.tailShift <
      a.representationPrimaryDefect b i.tailShift)
    (hprevious : a.tail.IsCurrentEssential b.tail i →
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) =
        a.tail.truncatedPrefixDefect b.tail (-1) i.val (i.val - 2))
    (hnext : a.tail.IsNextEssential b.tail i →
      a.truncatedPrefixDefect b (-1) (i.val + 3) (i.val + 1) =
        a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 2) i.val) :
    a.tail.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift := by
  have hiTail : 1 < i.val ∧ i.val + 1 < n + 1 := by
    exact ⟨hi, hinterior⟩
  have hiOriginal :
      1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  have hprimaryLe := a.representationPrimaryDefect_shift_le_tail b hhead i
  have hhalf := a.representationHalfGap_tail_eq_shift b i
  rcases himportant with hcurrent | hnextEssential
  · letI : Beli2006AlphaLaws.{u, v} K := alphaV
    have hcrossTail :=
      order_previous_lt_current_of_currentEssential
        a.tail b.tail i hi hiTail.2 hcurrent
    have hcrossOriginal :
        b.order ⟨i.tailShift.val - 2, by omega⟩ ≤
          a.order ⟨i.tailShift.val, i.tailShift.lt_large⟩ := by
      have hcross := hcrossTail.le
      rw [b.order_goodTail, a.order_goodTail] at hcross
      convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp only [RepresentationIndex.tailShift_val, Fin.val_succ] <;> omega
    have hpreviousEq :=
      a.representationSecondaryPreviousDefect_tail_eq_shift_of_core_eq
        b i hiTail (hprevious hcurrent)
    have htailPrime :=
      a.tail.representationAlphaPrime_eq_min_primary_previous
        b.tail i hiTail hcrossTail.le
    have horiginalPrime :=
      a.representationAlphaPrime_eq_min_primary_previous
        b i.tailShift hiOriginal hcrossOriginal
    have htailNormal : a.tail.representationAlpha b.tail i =
        min (a.tail.representationHalfGap b.tail i)
          (min (a.tail.representationPrimaryDefect b.tail i)
            (a.tail.representationSecondaryPreviousDefect b.tail i hiTail)) := by
      rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i,
        htailPrime]
    have horiginalNormal : a.representationAlpha b i.tailShift =
        min (a.representationHalfGap b i.tailShift)
          (min (a.representationPrimaryDefect b i.tailShift)
            (a.representationSecondaryPreviousDefect b i.tailShift
              hiOriginal)) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b i.tailShift,
        horiginalPrime]
    let half := a.representationHalfGap b i.tailShift
    let previous := a.representationSecondaryPreviousDefect b i.tailShift
      hiOriginal
    let primary := a.representationPrimaryDefect b i.tailShift
    let primaryTail := a.tail.representationPrimaryDefect b.tail i
    have hbelowPrimary : min half (min previous primary) < primary := by
      rw [horiginalNormal] at halpha
      simpa only [half, previous, primary, min_comm primary previous]
        using halpha
    have hbelowTail : min half (min previous primary) < primaryTail :=
      hbelowPrimary.trans_le (by
        simpa only [primary, primaryTail] using hprimaryLe)
    have hnested := min_nested_eq_of_lt_caps half previous primary primaryTail
      hbelowPrimary hbelowTail
    rw [htailNormal, horiginalNormal, hhalf, hpreviousEq]
    change min half (min primaryTail previous) =
      min half (min primary previous)
    rw [min_comm primaryTail previous, min_comm primary previous]
    exact hnested.symm
  · letI : Beli2006AlphaLaws.{u, w} K := alphaW
    have hcrossTail :=
      order_current_lt_next_of_nextEssential
        a.tail b.tail i hi hiTail.2 hnextEssential
    have hcrossOriginal :
        b.order ⟨i.tailShift.val - 1, by omega⟩ ≤
          a.order ⟨i.tailShift.val + 1, hiOriginal.2⟩ := by
      have hcross := hcrossTail.le
      rw [b.order_goodTail, a.order_goodTail] at hcross
      convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp only [RepresentationIndex.tailShift_val, Fin.val_succ] <;> omega
    have hcurrentEq :=
      a.representationSecondaryCurrentDefect_tail_eq_shift_of_core_eq
        b i hiTail (hnext hnextEssential)
    have htailPrime :=
      a.tail.representationAlphaPrime_eq_min_primary_current
        b.tail i hiTail hcrossTail.le
    have horiginalPrime :=
      a.representationAlphaPrime_eq_min_primary_current
        b i.tailShift hiOriginal hcrossOriginal
    have htailNormal : a.tail.representationAlpha b.tail i =
        min (a.tail.representationHalfGap b.tail i)
          (min (a.tail.representationPrimaryDefect b.tail i)
            (a.tail.representationSecondaryCurrentDefect b.tail i hiTail)) := by
      rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i,
        htailPrime]
    have horiginalNormal : a.representationAlpha b i.tailShift =
        min (a.representationHalfGap b i.tailShift)
          (min (a.representationPrimaryDefect b i.tailShift)
            (a.representationSecondaryCurrentDefect b i.tailShift
              hiOriginal)) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b i.tailShift,
        horiginalPrime]
    let half := a.representationHalfGap b i.tailShift
    let current := a.representationSecondaryCurrentDefect b i.tailShift
      hiOriginal
    let primary := a.representationPrimaryDefect b i.tailShift
    let primaryTail := a.tail.representationPrimaryDefect b.tail i
    have hbelowPrimary : min half (min current primary) < primary := by
      rw [horiginalNormal] at halpha
      simpa only [half, current, primary, min_comm primary current]
        using halpha
    have hbelowTail : min half (min current primary) < primaryTail :=
      hbelowPrimary.trans_le (by
        simpa only [primary, primaryTail] using hprimaryLe)
    have hnested := min_nested_eq_of_lt_caps half current primary primaryTail
      hbelowPrimary hbelowTail
    rw [htailNormal, horiginalNormal, hhalf, hcurrentEq]
    change min half (min primaryTail current) =
      min half (min primary current)
    rw [min_comm primaryTail current, min_comm primary current]
    exact hnested.symm

/-- Endpoint version of the preceding lemma.  There is no secondary candidate
at the last comparison boundary, so a strict inequality below the original
primary candidate alone makes a later increase of that candidate irrelevant. -/
theorem representationAlpha_tail_eq_shift_of_alpha_lt_primary_of_not_interior
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val)
    (hnotTail : ¬(1 < i.val ∧ i.val + 1 < n + 1))
    (halpha : a.representationAlpha b i.tailShift <
      a.representationPrimaryDefect b i.tailShift) :
    a.tail.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift := by
  have hnotOriginal :
      ¬(1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2) := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  have hprimaryLe := a.representationPrimaryDefect_shift_le_tail b hhead i
  have hhalf := a.representationHalfGap_tail_eq_shift b i
  have horiginalNormal : a.representationAlpha b i.tailShift =
      min (a.representationHalfGap b i.tailShift)
        (a.representationPrimaryDefect b i.tailShift) := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i.tailShift,
      a.representationAlphaPrime_eq_primary_of_not_interior
        b i.tailShift hnotOriginal]
  rw [horiginalNormal] at halpha
  have hhalfLt : a.representationHalfGap b i.tailShift <
      a.representationPrimaryDefect b i.tailShift :=
    (min_lt_iff.mp halpha).resolve_right (lt_irrefl _)
  rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i,
    a.tail.representationAlphaPrime_eq_primary_of_not_interior
      b.tail i hnotTail,
    horiginalNormal, hhalf,
    min_eq_left (hhalfLt.trans_le hprimaryLe).le,
    min_eq_left hhalfLt.le]

set_option maxHeartbeats 1000000 in
-- The dependent previous-form candidate is the only moving term in this branch.
/-- At a current-essential interior boundary, suppose the primary core is
unchanged while the preceding core can only increase.  If the original
invariant is already strictly below the previous-form secondary candidate,
that increase is unused and the complete invariant transports exactly. -/
theorem representationAlpha_tail_eq_shift_of_alpha_lt_previous_of_currentEssential
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val) (hinterior : i.val + 1 < n + 1)
    (hcurrent : a.tail.IsCurrentEssential b.tail i)
    (hprimaryCore :
      a.truncatedPrefixDefect b (-1) (i.val + 2) i.val =
        a.tail.truncatedPrefixDefect b.tail (-1) (i.val + 1) (i.val - 1))
    (hpreviousCore :
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
        a.tail.truncatedPrefixDefect b.tail (-1) i.val (i.val - 2))
    (halpha : a.representationAlpha b i.tailShift <
      a.representationSecondaryPreviousDefect b i.tailShift
        ⟨by
          simp only [RepresentationIndex.tailShift_val]
          omega,
         by
          simp only [RepresentationIndex.tailShift_val]
          omega⟩) :
    a.tail.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hiTail : 1 < i.val ∧ i.val + 1 < n + 1 :=
    ⟨hi, hinterior⟩
  have hiOriginal :
      1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  have hcrossTail :=
    order_previous_lt_current_of_currentEssential
      a.tail b.tail i hi hinterior hcurrent
  have hcrossOriginal :
      b.order ⟨i.tailShift.val - 2, by omega⟩ ≤
        a.order ⟨i.tailShift.val, i.tailShift.lt_large⟩ := by
    have hcross := hcrossTail.le
    rw [b.order_goodTail, a.order_goodTail] at hcross
    convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;>
      simp only [RepresentationIndex.tailShift_val, Fin.val_succ] <;> omega
  have hprimaryEq :=
    a.representationPrimaryDefect_tail_eq_shift_of_core_eq
      b i hprimaryCore
  have hpreviousLe :=
    a.representationSecondaryPreviousDefect_shift_le_tail_of_core_le
      b i hiTail hpreviousCore
  have hhalf := a.representationHalfGap_tail_eq_shift b i
  have htailPrime :=
    a.tail.representationAlphaPrime_eq_min_primary_previous
      b.tail i hiTail hcrossTail.le
  have horiginalPrime :=
    a.representationAlphaPrime_eq_min_primary_previous
      b i.tailShift hiOriginal hcrossOriginal
  have htailNormal : a.tail.representationAlpha b.tail i =
      min (a.tail.representationHalfGap b.tail i)
        (min (a.tail.representationPrimaryDefect b.tail i)
          (a.tail.representationSecondaryPreviousDefect b.tail i hiTail)) := by
    rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i,
      htailPrime]
  have horiginalNormal : a.representationAlpha b i.tailShift =
      min (a.representationHalfGap b i.tailShift)
        (min (a.representationPrimaryDefect b i.tailShift)
          (a.representationSecondaryPreviousDefect b i.tailShift
            hiOriginal)) := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i.tailShift,
      horiginalPrime]
  let half := a.representationHalfGap b i.tailShift
  let primary := a.representationPrimaryDefect b i.tailShift
  let previous := a.representationSecondaryPreviousDefect b i.tailShift
    hiOriginal
  let previousTail :=
    a.tail.representationSecondaryPreviousDefect b.tail i hiTail
  have hbelowPrevious : min half (min primary previous) < previous := by
    rw [horiginalNormal] at halpha
    simpa only [half, primary, previous] using halpha
  have hbelowTail : min half (min primary previous) < previousTail :=
    hbelowPrevious.trans_le (by
      simpa only [previous, previousTail] using hpreviousLe)
  have hnested := min_nested_eq_of_lt_caps half primary previous previousTail
    hbelowPrevious hbelowTail
  rw [htailNormal, horiginalNormal, hhalf, hprimaryEq]
  change min half (min primary previousTail) =
    min half (min primary previous)
  exact hnested.symm

/-- Current essentiality makes the previous-form Lemma 2.7 candidate an
explicit upper bound for the shifted original comparison invariant. -/
theorem representationAlpha_shift_le_previous_of_currentEssential
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val) (hinterior : i.val + 1 < n + 1)
    (hcurrent : a.tail.IsCurrentEssential b.tail i) :
    a.representationAlpha b i.tailShift ≤
      a.representationSecondaryPreviousDefect b i.tailShift
        ⟨by
          simp only [RepresentationIndex.tailShift_val]
          omega,
         by
          simp only [RepresentationIndex.tailShift_val]
          omega⟩ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hiOriginal :
      1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  have hcrossTail :=
    order_previous_lt_current_of_currentEssential
      a.tail b.tail i hi hinterior hcurrent
  have hcrossOriginal :
      b.order ⟨i.tailShift.val - 2, by omega⟩ ≤
        a.order ⟨i.tailShift.val, i.tailShift.lt_large⟩ := by
    have hcross := hcrossTail.le
    rw [b.order_goodTail, a.order_goodTail] at hcross
    convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;>
      simp only [RepresentationIndex.tailShift_val, Fin.val_succ] <;> omega
  calc
    a.representationAlpha b i.tailShift ≤
        a.representationAlphaPrime b i.tailShift :=
      a.representationAlpha_le_prime b i.tailShift
    _ = min (a.representationPrimaryDefect b i.tailShift)
        (a.representationSecondaryPreviousDefect b i.tailShift
          hiOriginal) :=
      a.representationAlphaPrime_eq_min_primary_previous
        b i.tailShift hiOriginal hcrossOriginal
    _ ≤ a.representationSecondaryPreviousDefect b i.tailShift
        hiOriginal := min_le_right _ _

end BONG.GoodBONG

end Bong
