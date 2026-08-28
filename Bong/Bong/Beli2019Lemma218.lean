/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Bounds
import Bong.Bong.Beli2019Lemma218Arithmetic

/-!
# Beli (2019), Lemma 2.18

This file proves the two arithmetic alternatives used in the proof of Lemma
3.10 from condition 2.1(ii), the local formula for `alpha`, and sharp capped
defect domination.
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

/-- The exceptional and ordinary definitions of `S_i + A_i` are both
bounded by `R_(i+1)` plus the current capped defect. -/
theorem centralAdjustedAlpha_le_currentOrder_add_defect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralAdjustedAlpha b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        a.centralCurrentDefect b i := by
  unfold centralAdjustedAlpha
  split_ifs with hi
  · rw [a.coe_representationAlphaValue b (i.current hi)]
    calc
      (((b.order ⟨i.val - 1, by
          have := i.one_lt
          have := hi
          omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current hi) ≤
        (((b.order ⟨i.val - 1, by
          have := i.one_lt
          have := hi
          omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationPrimaryDefect b (i.current hi) :=
        add_le_add_right
          (a.representationAlpha_le_primary b (i.current hi)) _
      _ = (((a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          a.centralCurrentDefect b i := by
        rw [a.representationPrimaryDefect_current_eq b i hi]
        rw [← add_assoc]
        congr 1
        norm_cast
        ring
  · have hval : i.val = n + 2 := by
      have := i.le_small_succ
      omega
    have hgap : n + 2 < m + 1 := by
      have := i.lt_large
      omega
    calc
      a.terminalAdjustedAlpha b hgap ≤
          a.terminalAdjustedPrimary b hgap :=
        a.terminalAdjustedAlpha_le_primary b hgap
      _ = (((a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          a.centralCurrentDefect b i := by
        unfold terminalAdjustedPrimary centralCurrentDefect
        have hplus : n + 2 + 1 = n + 3 := by omega
        have hminus : n + 2 - 1 = n + 1 := by omega
        simp only [hval, hplus, hminus]

/-- Beli (2019), Lemma 2.18(i), including the exceptional final value of
`S_i + A_i`. -/
theorem beli2019Lemma218_target
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.prefixAlphaCap i.val + a.representationAlpha b i.previous ∨
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.prefixAlphaCap i.val + a.centralCurrentDefect b i := by
  let p : Fin m := ⟨i.val - 1, by
    have := i.one_lt
    have := i.lt_large
    omega⟩
  let gap : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Int) : ℚ)
  let adjacent :=
    a.truncatedPrefixDefect a (-1) (i.val - 1) (i.val + 1)
  have halpha : a.prefixAlphaCap i.val =
      min (((gap / 2 + (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
        ((gap : WithTop ℚ) + adjacent) := by
    rw [a.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large]
    have hlocal := a.alpha_eq_min_halfGap_add_cappedAdjacent p
    have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      have := i.one_lt
      omega
    have hpCast : p.castSucc = ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ := by
      apply Fin.ext
      rfl
    unfold halfGapCandidate at hlocal
    rw [hpSucc, hpCast] at hlocal
    have hstep : i.val - 1 + 2 = i.val + 1 := by
      have := i.one_lt
      omega
    simpa only [p, gap, adjacent,
      hstep] using hlocal
  have hbound := a.centralAdjustedAlpha_le_currentOrder_add_defect b i
  have hfull := htrigger.2.trans_le (add_le_add_right hbound _)
  rw [a.coe_representationAlphaValue b i.previous] at hfull
  have horderEq :
      (((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Int) : ℚ) : WithTop ℚ) + (gap : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) := by
    dsimp only [gap]
    norm_cast
    ring
  have hright :
      (((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (a.representationAlpha b i.previous +
            (gap : WithTop ℚ) + a.centralCurrentDefect b i) =
        a.representationAlpha b i.previous +
          ((((a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
            a.centralCurrentDefect b i) := by
    calc
      _ = a.representationAlpha b i.previous +
          ((((a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ : Int) : ℚ) : WithTop ℚ) + (gap : WithTop ℚ)) +
            a.centralCurrentDefect b i := by ac_rfl
      _ = _ := by rw [horderEq, add_assoc]
  have hfull' :
      ((2 * (ramificationIndex K : ℚ) +
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
        (((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (a.representationAlpha b i.previous +
            (gap : WithTop ℚ) + a.centralCurrentDefect b i) := by
    rw [hright]
    exact hfull
  have hkey := withTop_sub_lt_of_lt_add
    (2 * (ramificationIndex K : ℚ) +
      (a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : ℚ))
    ((a.order ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ : Int) : ℚ)
    (a.representationAlpha b i.previous +
      (gap : WithTop ℚ) + a.centralCurrentDefect b i) hfull'
  have hkey' : ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
      a.representationAlpha b i.previous +
        (gap : WithTop ℚ) + a.centralCurrentDefect b i := by
    convert hkey using 1
    norm_cast
    ring
  have htriangle := b.truncatedPrefixDefect_triangle_alternative a
    (i.val - 1) (i.val + 1) (i.val - 1)
  rw [a.truncatedPrefixDefect_comm a (-1) (i.val + 1) (i.val - 1),
    b.truncatedPrefixDefect_comm a (-1) (i.val - 1) (i.val + 1),
    b.truncatedPrefixDefect_comm a 1 (i.val - 1) (i.val - 1)] at htriangle
  have hA := hdefect i.previous
  rw [a.coe_representationAlphaValue b i.previous] at hA
  have halt : a.centralCurrentDefect b i ≤ adjacent ∨
      a.representationAlpha b i.previous ≤ adjacent := by
    rcases htriangle with hcurrent | hdiagonal
    · exact Or.inl (by
        simpa only [centralCurrentDefect, adjacent] using hcurrent)
    · exact Or.inr (hA.trans (by
        simpa only [CentralRepresentationIndex.previous, adjacent] using
          hdiagonal))
  have hresult := withTop_alpha_sum_alternative
    (ramificationIndex K : ℚ) gap
    (a.representationAlpha b i.previous)
    (a.centralCurrentDefect b i) adjacent
    (a.prefixAlphaCap i.val) hkey' halpha halt
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hresult

/-- Beli (2019), Lemma 2.18(ii). -/
theorem beli2019Lemma218_source
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i)
    (hsource : i.val - 1 < n + 1) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap (i.val - 1) +
          a.representationAlpha b (i.current (by omega)) ∨
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap (i.val - 1) + a.centralPreviousDefect b i := by
  have hi : i.val ≤ n + 1 := by
    have := i.one_lt
    omega
  let p : Fin n := ⟨i.val - 2, by
    have := i.one_lt
    have := hsource
    omega⟩
  let gap : ℚ :=
    ((b.order ⟨i.val - 1, by
        have := i.one_lt
        have := hi
        omega⟩ -
      b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Int) : ℚ)
  let adjacent :=
    b.truncatedPrefixDefect b (-1) (i.val - 2) i.val
  have halpha : b.prefixAlphaCap (i.val - 1) =
      min (((gap / 2 + (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
        ((gap : WithTop ℚ) + adjacent) := by
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) hsource]
    have hlocal := b.alpha_eq_min_halfGap_add_cappedAdjacent p
    have hpSucc : p.succ = ⟨i.val - 1, by
        have := i.one_lt
        have := hi
        omega⟩ := by
      apply Fin.ext
      change i.val - 2 + 1 = i.val - 1
      have := i.one_lt
      omega
    have hpCast : p.castSucc = ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ := by
      apply Fin.ext
      rfl
    unfold halfGapCandidate at hlocal
    rw [hpSucc, hpCast] at hlocal
    have hstep : i.val - 2 + 2 = i.val := by
      have := i.one_lt
      omega
    have hindex : (⟨i.val - 1 - 1, by omega⟩ : Fin n) = p := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    rw [hindex]
    simpa only [p, gap, adjacent, hstep] using hlocal
  have hsum := htrigger.2
  unfold centralAdjustedAlpha at hsum
  rw [dif_pos hi, a.coe_representationAlphaValue b i.previous,
    a.coe_representationAlphaValue b (i.current hi)] at hsum
  have hprevious : a.representationAlpha b i.previous ≤
      (((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ -
        b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.centralPreviousDefect b i := by
    calc
      a.representationAlpha b i.previous ≤
          a.representationPrimaryDefect b i.previous :=
        a.representationAlpha_le_primary b i.previous
      _ = _ := a.representationPrimaryDefect_previous_eq b i
  have hfull := hsum.trans_le (add_le_add_left hprevious _)
  have hbalance :
      (((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Int) : ℚ) : WithTop ℚ) + (gap : WithTop ℚ) =
        (((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ -
          b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (((b.order ⟨i.val - 1, by
            have := i.one_lt
            have := hi
            omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    dsimp only [gap]
    norm_cast
    ring
  have hright :
      (((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (a.representationAlpha b (i.current hi) +
            (gap : WithTop ℚ) + a.centralPreviousDefect b i) =
        ((((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ -
          b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
            a.centralPreviousDefect b i) +
          ((((b.order ⟨i.val - 1, by
            have := i.one_lt
            have := hi
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
            a.representationAlpha b (i.current hi)) := by
    calc
      _ = ((((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : Int) : ℚ) : WithTop ℚ) + (gap : WithTop ℚ)) +
          (a.centralPreviousDefect b i +
            a.representationAlpha b (i.current hi)) := by ac_rfl
      _ = _ := by rw [hbalance]; ac_rfl
  have hfull' :
      ((2 * (ramificationIndex K : ℚ) +
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
        (((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (a.representationAlpha b (i.current hi) +
            (gap : WithTop ℚ) + a.centralPreviousDefect b i) := by
    rw [hright]
    exact hfull
  have hkey := withTop_sub_lt_of_lt_add
    (2 * (ramificationIndex K : ℚ) +
      (a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : ℚ))
    ((a.order ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ : Int) : ℚ)
    (a.representationAlpha b (i.current hi) +
      (gap : WithTop ℚ) + a.centralPreviousDefect b i) hfull'
  have hkey' : ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
      a.representationAlpha b (i.current hi) +
        (gap : WithTop ℚ) + a.centralPreviousDefect b i := by
    convert hkey using 1
    norm_cast
    ring
  have htriangle := a.truncatedPrefixDefect_triangle_alternative b
    i.val (i.val - 2) i.val
  have hA := hdefect (i.current hi)
  rw [a.coe_representationAlphaValue b (i.current hi)] at hA
  have halt : a.centralPreviousDefect b i ≤ adjacent ∨
      a.representationAlpha b (i.current hi) ≤ adjacent := by
    rcases htriangle with hpreviousDefect | hdiagonal
    · exact Or.inl (by
        simpa only [centralPreviousDefect, adjacent] using hpreviousDefect)
    · exact Or.inr (hA.trans (by
        simpa only [CentralRepresentationIndex.current, adjacent] using
          hdiagonal))
  have hresult := withTop_alpha_sum_alternative
    (ramificationIndex K : ℚ) gap
    (a.representationAlpha b (i.current hi))
    (a.centralPreviousDefect b i) adjacent
    (b.prefixAlphaCap (i.val - 1)) hkey' halpha halt
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hresult

end BONG.GoodBONG

end Bong
