/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIBetaProfile

/-!
# Beli (2019), Lemma 6.9(ii): type-I beta primary candidate

This file isolates the primary-candidate induction step in the central
type-I interval.  The preceding diagonal comparison and the source adjacent
defect dominate the mixed primary defect.
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
-- The proof transports the preceding representation index through a minimum.
/-- At an odd central type-I boundary, the target alpha is no larger than
the primary candidate, provided the preceding source-alpha case is known. -/
theorem lemma69_typeI_beta_le_primary_of_previous
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch)
    (hweight : a.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩)
    (hprevious : a.representationAlpha b
        (⟨i.val - 1, by omega, by
          have hi := i.lt_large
          omega, by
          have hi := i.lt_large
          omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (a.alphaValue ⟨i.val - 2, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ)) :
    (b.alphaValue ⟨i.val - 1, by
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
  rcases hodd with ⟨d, hd⟩
  have hpEven : Even p.val := ⟨d, by simp only [p]; omega⟩
  have hgapEntries := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst p.val hpEven (by simpa only [p] using hleft) (by
      simp only [p]
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
  have htargetCurrent : b.order ⟨i.val - 1, hiPrevious⟩ =
      a.order p.castSucc + 2 := by
    rw [hpCast]
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    simpa only [p] using hgapEntries
  have hsourceNext : a.order ⟨i.val, i.lt_large⟩ =
      a.order p.succ := by
    rw [hpSucc]
  have hbetaSource : b.alphaValue p = a.alphaValue p - 2 := by
    unfold alphaLeftEndpoint at hweight
    change (a.order p.castSucc : ℚ) + a.alphaValue p =
      (b.order p.castSucc : ℚ) + b.alphaValue p at hweight
    have htargetP : b.order p.castSucc = a.order p.castSucc + 2 := by
      rw [hpCast]
      exact htargetCurrent
    rw [htargetP] at hweight
    push_cast at hweight ⊢
    linarith
  let shift : ℚ :=
    ((a.order p.succ - a.order p.castSucc : Int) : ℚ)
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
  have hprevious' : a.representationAlpha b previousIdx =
      (a.alphaValue previous : WithTop ℚ) := by
    simpa only [previousIdx, previous] using hprevious
  have hdiagonal : (a.alphaValue previous : WithTop ℚ) ≤
      diagonalDefect := by
    calc
      (a.alphaValue previous : WithTop ℚ) =
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
      shift + a.alphaValue previous := by
    unfold alphaRightEndpoint at hendpoint
    rw [hpreviousSucc] at hendpoint
    dsimp only [shift]
    push_cast at hendpoint ⊢
    linarith
  have hpreviousBound : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + diagonalDefect := by
    calc
      (a.alphaValue p : WithTop ℚ) ≤
          (shift : WithTop ℚ) +
            (a.alphaValue previous : WithTop ℚ) := by
        exact_mod_cast hpreviousShift
      _ ≤ (shift : WithTop ℚ) + diagonalDefect := by
        simpa only [add_comm] using
          add_le_add_right hdiagonal (shift : WithTop ℚ)
  have hdomRaw := a.truncatedPrefixDefect_domination a b
    (-1) 1 (i.val + 1) (i.val - 1) (i.val - 1)
  have hdom : min selfDefect diagonalDefect ≤ crossDefect := by
    dsimp only [selfDefect, diagonalDefect, crossDefect]
    simpa only [mul_one] using hdomRaw
  have hminimum : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + min selfDefect diagonalDefect :=
    withTop_le_shift_add_min _ shift _ _ hlocal hpreviousBound
  have hcross : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + crossDefect :=
    hminimum.trans (by
      simpa only [add_comm] using
        add_le_add_right hdom (shift : WithTop ℚ))
  have htranslated := add_le_add_right hcross ((-2 : ℚ) : WithTop ℚ)
  have hcoefficient :
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) = shift - 2 := by
    rw [hsourceNext, htargetCurrent]
    dsimp only [shift]
    push_cast
    ring
  unfold representationPrimaryDefect
  rw [hcoefficient]
  have hleftTranslate :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) =
        (b.alphaValue p : WithTop ℚ) := by
    exact_mod_cast (show a.alphaValue p + (-2 : ℚ) =
      b.alphaValue p by linarith [hbetaSource])
  have hrightTranslate :
      (shift : WithTop ℚ) + crossDefect + ((-2 : ℚ) : WithTop ℚ) =
        ((shift - 2 : ℚ) : WithTop ℚ) + crossDefect := by
    rw [sub_eq_add_neg, WithTop.coe_add]
    ac_rfl
  have htranslated' :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) ≤
        ((shift : WithTop ℚ) + crossDefect) +
          ((-2 : ℚ) : WithTop ℚ) := by
    simpa only [add_comm] using htranslated
  rw [hleftTranslate, hrightTranslate] at htranslated'
  simpa only [crossDefect, p] using htranslated'

end BONG.GoodBONG

end Bong
