/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIBetaValue

/-!
# Beli (2019), Lemma 6.9(ii): type-I source-alpha primary candidate

This is the companion to the odd beta step.  At an even boundary the target
order is two below the source order, while the preceding source alpha is two
above the preceding target alpha.  The two shifts cancel in the primary
candidate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- The proof transports two dependent indices through a defect minimum.
/-- At an even central type-I boundary, the source alpha is no larger than
the primary candidate, provided the preceding target-beta case is known. -/
theorem lemma69_typeI_alpha_le_primary_of_previousBeta
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (heven : Even i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch < i.val - 1)
    (hright : i.val - 1 < C.rightSwitch)
    (hweightPrevious : a.alphaLeftEndpoint ⟨i.val - 2, by
        have hi := i.lt_large
        omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 2, by
        have hi := i.lt_large
        omega⟩)
    (hprevious : a.representationAlpha b
        (⟨i.val - 1, by omega, by
          have hi := i.lt_large
          omega, by
          have hi := i.lt_large
          omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (b.alphaValue ⟨i.val - 2, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ)) :
    (a.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤
      a.representationPrimaryDefect b i := by
  have hiPrevious : i.val - 1 < n + 2 := by
    have hi := i.lt_large
    omega
  have hiAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  have hiPreviousAlpha : i.val - 2 < n + 1 := by
    have hi := i.lt_large
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  let previous : Fin (n + 1) := ⟨i.val - 2, hiPreviousAlpha⟩
  let previousIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val - 1, by omega, hiPrevious, by
      have hi := i.lt_large
      omega⟩
  rcases heven with ⟨d, hd⟩
  have hcurrentOdd : Odd (i.val - 1) := ⟨d - 1, by omega⟩
  have hpreviousEven : Even previous.val :=
    ⟨d - 1, by simp only [previous]; omega⟩
  have hcurrentGap := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (i.val - 1) hcurrentOdd (by omega) hright.le
  have hpreviousGap := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst previous.val hpreviousEven (by
      simp only [previous]
      omega) (by
        simp only [previous]
        omega)
  have hpCast : p.castSucc =
      (⟨i.val - 1, hiPrevious⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have htargetCurrent : b.order p.castSucc =
      a.order p.castSucc - 2 := by
    rw [hpCast]
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    have hgap : b.orderSequence.entryOrZero (i.val - 1) =
        a.orderSequence.entryOrZero (i.val - 1) - 2 := by
      omega
    simpa only using hgap
  have htargetPrevious : b.order previous.castSucc =
      a.order previous.castSucc + 2 := by
    rw [hpreviousCast]
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    simpa only [previous] using hpreviousGap
  have hsourcePrevious : a.alphaValue previous =
      b.alphaValue previous + 2 := by
    apply alpha_eq_add_two_of_leftEndpoint_eq a b previous
      htargetPrevious
    simpa only [previous] using hweightPrevious
  let shift : ℚ :=
    ((a.order p.succ - a.order p.castSucc : Int) : ℚ)
  let shifted : ℚ := shift + 2
  let selfDefect := a.truncatedPrefixDefect a (-1)
    (i.val + 1) (i.val - 1)
  let diagonalDefect := a.truncatedPrefixDefect b 1
    (i.val - 1) (i.val - 1)
  let crossDefect := a.truncatedPrefixDefect b (-1)
    (i.val + 1) (i.val - 1)
  have hlocalRaw := a.alpha_le_orderGap_add_cappedAdjacent p
  have hlocal : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + selfDefect := by
    dsimp only [selfDefect]
    rw [a.truncatedPrefixDefect_comm a (-1)
      (i.val + 1) (i.val - 1)]
    simpa only [shift, selfDefect, p, Fin.val_succ,
      Fin.val_castSucc, show i.val - 1 + 2 = i.val + 1 by omega] using
      hlocalRaw
  have hlocalShifted : (a.alphaValue p : WithTop ℚ) ≤
      (shifted : WithTop ℚ) + selfDefect := by
    have hshiftTop : (shift : WithTop ℚ) ≤ shifted := by
      exact_mod_cast (show shift ≤ shifted by
        dsimp only [shifted]
        linarith)
    apply hlocal.trans
    simpa only [add_comm] using add_le_add_right hshiftTop selfDefect
  have hprevious' : a.representationAlpha b previousIdx =
      (b.alphaValue previous : WithTop ℚ) := by
    simpa only [previousIdx, previous] using hprevious
  have hdiagonal : (b.alphaValue previous : WithTop ℚ) ≤
      diagonalDefect := by
    calc
      (b.alphaValue previous : WithTop ℚ) =
          a.representationAlpha b previousIdx := hprevious'.symm
      _ = (a.representationAlphaValue b previousIdx : WithTop ℚ) :=
        (a.coe_representationAlphaValue b previousIdx).symm
      _ ≤ a.truncatedPrefixDefect b 1 previousIdx.val previousIdx.val :=
        hdefect previousIdx
      _ = diagonalDefect := rfl
  have hendpoint := a.alphaRightEndpoint_antitone
    (show previous ≤ p by
      change previous.val ≤ p.val
      simp only [previous, p]
      omega)
  have hpreviousSucc : previous.succ = p.castSucc := by
    apply Fin.ext
    simp only [previous, p, Fin.val_succ, Fin.val_castSucc]
    omega
  have hpreviousShift : a.alphaValue p ≤
      shifted + b.alphaValue previous := by
    unfold alphaRightEndpoint at hendpoint
    rw [hpreviousSucc, hsourcePrevious] at hendpoint
    dsimp only [shifted, shift]
    push_cast at hendpoint ⊢
    linarith
  have hpreviousBound : (a.alphaValue p : WithTop ℚ) ≤
      (shifted : WithTop ℚ) + diagonalDefect := by
    calc
      (a.alphaValue p : WithTop ℚ) ≤
          (shifted : WithTop ℚ) +
            (b.alphaValue previous : WithTop ℚ) := by
        exact_mod_cast hpreviousShift
      _ ≤ (shifted : WithTop ℚ) + diagonalDefect := by
        simpa only [add_comm] using
          add_le_add_right hdiagonal (shifted : WithTop ℚ)
  have hdomRaw := a.truncatedPrefixDefect_domination a b
    (-1) 1 (i.val + 1) (i.val - 1) (i.val - 1)
  have hdom : min selfDefect diagonalDefect ≤ crossDefect := by
    dsimp only [selfDefect, diagonalDefect, crossDefect]
    simpa only [mul_one] using hdomRaw
  have hminimum : (a.alphaValue p : WithTop ℚ) ≤
      (shifted : WithTop ℚ) + min selfDefect diagonalDefect :=
    withTop_le_shift_add_min _ shifted _ _ hlocalShifted hpreviousBound
  have hcross : (a.alphaValue p : WithTop ℚ) ≤
      (shifted : WithTop ℚ) + crossDefect :=
    hminimum.trans (by
      simpa only [add_comm] using
        add_le_add_right hdom (shifted : WithTop ℚ))
  have hcoefficient :
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) = shifted := by
    rw [← hpSucc, ← hpCast, htargetCurrent]
    dsimp only [shifted, shift]
    push_cast
    ring
  unfold representationPrimaryDefect
  rw [hcoefficient]
  simpa only [crossDefect, p] using hcross

end BONG.GoodBONG

end Bong
