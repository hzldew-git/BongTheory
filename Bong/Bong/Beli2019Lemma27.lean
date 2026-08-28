/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Lemma 2.7(i)

When `R_(i+1) ≥ S_(i-1)`, the secondary defect in `A_i` and `A'_i` can
be replaced by `d[-a_(1,i) b_(1,i-2)]`.  The proof combines the capped
version of Lemma 1.4(c) with Remark 1.1's adjacent-defect bound.
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

/-- The replacement form of Definition 5's secondary candidate in
Lemma 2.7(i). -/
noncomputable def representationSecondaryPreviousDefect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) : WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    a.truncatedPrefixDefect b (-1) i.val (i.val - 2)

/-- The cut inequality used to invoke Lemma 1.4(c) in Lemma 2.7(i). -/
theorem representationPrimaryDefect_le_secondaryAdjacentCut
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hcross : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩) :
    a.representationPrimaryDefect b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
  let p : Fin m := ⟨i.val, by omega⟩
  let primaryShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let adjacentShift : ℚ :=
    ((a.order ⟨i.val + 1, hi.2⟩ -
      a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ)
  let secondaryShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  have hcap : a.prefixAlphaCap (i.val + 1) =
      (a.alphaValue p : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) hi.2]
    congr 1
  have hprimary : a.representationPrimaryDefect b i ≤
      (primaryShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) := by
    unfold representationPrimaryDefect
    rw [← hcap]
    exact add_le_add_right
      (a.truncatedPrefixDefect_le_leftCap b (-1)
        (i.val + 1) (i.val - 1)) _
  have hadjacent : (a.alphaValue p : WithTop ℚ) ≤
      (adjacentShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
    have h := a.alpha_le_orderGap_add_cappedAdjacent p
    have hsucc : p.succ = (⟨i.val + 1, hi.2⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    have hcast : p.castSucc = (⟨i.val, i.lt_large⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast] at h
    simpa only [adjacentShift] using h
  have hshifts : primaryShift + adjacentShift ≤ secondaryShift := by
    dsimp only [primaryShift, adjacentShift, secondaryShift]
    push_cast
    norm_cast at hcross ⊢
    linarith
  have hshiftsTop : ((primaryShift + adjacentShift : ℚ) : WithTop ℚ) ≤
      (secondaryShift : WithTop ℚ) := by
    exact_mod_cast hshifts
  calc
    a.representationPrimaryDefect b i ≤
        (primaryShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) :=
      hprimary
    _ ≤ (primaryShift : WithTop ℚ) +
        ((adjacentShift : WithTop ℚ) +
          a.truncatedPrefixDefect a (-1) i.val (i.val + 2)) :=
      add_le_add_right hadjacent _
    _ = ((primaryShift + adjacentShift : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
      norm_num [add_assoc]
    _ ≤ (secondaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) :=
      add_le_add_left hshiftsTop _

/-- Lemma 2.7(i), stated as equality of the two candidate minima. -/
theorem representationSecondaryDefect_replace_previous
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hcross : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩) :
    min (a.representationSecondaryDefect b i hi)
        (a.representationPrimaryDefect b i) =
      min (a.representationSecondaryPreviousDefect b i hi)
        (a.representationPrimaryDefect b i) := by
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  have hcut := a.representationPrimaryDefect_le_secondaryAdjacentCut
    b i hi hcross
  have hreplace := a.shiftedTruncatedPrefixDefect_add_two_replace_of_cut_le
    b i.val (i.val - 2) shift (a.representationPrimaryDefect b i)
      (by simpa only [shift] using hcut)
  simpa only [representationSecondaryDefect,
    representationSecondaryPreviousDefect, shift] using hreplace

/-- Lemma 2.7(i), in the exact normal form for Definition 5's `A'_i`. -/
theorem representationAlphaPrime_eq_min_primary_previous
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hcross : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩) :
    a.representationAlphaPrime b i =
      min (a.representationPrimaryDefect b i)
        (a.representationSecondaryPreviousDefect b i hi) := by
  rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
  rw [min_comm (a.representationPrimaryDefect b i),
    a.representationSecondaryDefect_replace_previous b i hi hcross,
    min_comm (a.representationSecondaryPreviousDefect b i hi)]

/-- The replacement form of Definition 5's secondary candidate in
Lemma 2.7(ii). -/
noncomputable def representationSecondaryCurrentDefect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) : WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    a.truncatedPrefixDefect b (-1) (i.val + 2) i.val

/-- The target-side cut inequality used in Lemma 2.7(ii). -/
theorem representationPrimaryDefect_le_secondaryTargetAdjacentCut
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hcross : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationPrimaryDefect b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
  have hone : 1 < i.val := hi.1
  have hsmall : i.val ≤ n + 1 := i.le_small
  have htwo : i.val - 2 + 2 = i.val := by omega
  let p : Fin n := ⟨i.val - 2, by omega⟩
  let primaryShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let adjacentShift : ℚ :=
    ((b.order ⟨i.val - 1, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ : Int) : ℚ)
  let secondaryShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  have hcap : b.prefixAlphaCap (i.val - 1) =
      (b.alphaValue p : WithTop ℚ) := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 1
  have hprimary : a.representationPrimaryDefect b i ≤
      (primaryShift : WithTop ℚ) + (b.alphaValue p : WithTop ℚ) := by
    unfold representationPrimaryDefect
    rw [← hcap]
    exact add_le_add_right
      (a.truncatedPrefixDefect_le_rightCap b (-1)
        (i.val + 1) (i.val - 1)) _
  have hadjacent : (b.alphaValue p : WithTop ℚ) ≤
      (adjacentShift : WithTop ℚ) +
        b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
    have h := b.alpha_le_orderGap_add_cappedAdjacent p
    have hsucc : p.succ =
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, p]
      omega
    have hcast : p.castSucc =
        (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast] at h
    simpa only [p, adjacentShift, htwo] using h
  have hshifts : primaryShift + adjacentShift ≤ secondaryShift := by
    dsimp only [primaryShift, adjacentShift, secondaryShift]
    push_cast
    norm_cast at hcross ⊢
    linarith
  have hshiftsTop : ((primaryShift + adjacentShift : ℚ) : WithTop ℚ) ≤
      (secondaryShift : WithTop ℚ) := by
    exact_mod_cast hshifts
  calc
    a.representationPrimaryDefect b i ≤
        (primaryShift : WithTop ℚ) + (b.alphaValue p : WithTop ℚ) :=
      hprimary
    _ ≤ (primaryShift : WithTop ℚ) +
        ((adjacentShift : WithTop ℚ) +
          b.truncatedPrefixDefect b (-1) (i.val - 2) i.val) :=
      add_le_add_right hadjacent _
    _ = ((primaryShift + adjacentShift : ℚ) : WithTop ℚ) +
        b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
      norm_num [add_assoc]
    _ ≤ (secondaryShift : WithTop ℚ) +
        b.truncatedPrefixDefect b (-1) (i.val - 2) i.val :=
      add_le_add_left hshiftsTop _

/-- Lemma 2.7(ii), stated as equality of the two candidate minima. -/
theorem representationSecondaryDefect_replace_current
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hcross : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    min (a.representationSecondaryDefect b i hi)
        (a.representationPrimaryDefect b i) =
      min (a.representationSecondaryCurrentDefect b i hi)
        (a.representationPrimaryDefect b i) := by
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  have hcut := a.representationPrimaryDefect_le_secondaryTargetAdjacentCut
    b i hi hcross
  have hreplace :=
    a.shiftedTruncatedPrefixDefect_right_add_two_replace_of_cut_le b
      (i.val + 2) (i.val - 2) shift (a.representationPrimaryDefect b i)
      (by simpa only [shift, show i.val - 2 + 2 = i.val by omega] using hcut)
  have hindex : i.val - 2 + 2 = i.val := by omega
  simpa only [representationSecondaryDefect,
    representationSecondaryCurrentDefect, shift, hindex] using hreplace

/-- Lemma 2.7(ii), in the exact normal form for Definition 5's `A'_i`. -/
theorem representationAlphaPrime_eq_min_primary_current
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hcross : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationAlphaPrime b i =
      min (a.representationPrimaryDefect b i)
        (a.representationSecondaryCurrentDefect b i hi) := by
  rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
  rw [min_comm (a.representationPrimaryDefect b i),
    a.representationSecondaryDefect_replace_current b i hi hcross,
    min_comm (a.representationSecondaryCurrentDefect b i hi)]

end BONG.GoodBONG

end Bong
