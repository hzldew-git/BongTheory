/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeIBoundaryLower
import Bong.Bong.Beli2019Remark616
import Bong.Bong.Beli2019Lemma79TypeIRightSourceSecondary

/-!
# Beli (2019), Lemma 7.7: coincident terminal type-I switches

This is the second branch in the proof of Lemma 7.7: `t = t' = u`.
Lemma 7.6 controls the target prefix before the switch, the final adjacent
pair has the same lower bound, and capped domination joins them.  Remark
6.16 transfers the resulting target-prefix estimate to the source prefix;
at full rank the determinant-class invariance of a full prefix gives the
same transfer directly.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- When the two canonical switches coincide with the last unequal order,
the target self-prefix through the first common-suffix coordinate dominates
the final target order drop. -/
theorem beli2019Lemma77_typeI_coincident_terminal_targetCapped
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hleftLast : C.leftSwitch = D.profile.last)
    (hinterior : C.leftSwitch + 1 < n + 2) :
    ((((b.order ⟨C.leftSwitch, by omega⟩ -
        b.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) :
          WithTop ℚ) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ ((C.leftSwitch + 2) / 2)) 0
          (C.leftSwitch + 2)) := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hleftAlphaBound : C.leftSwitch < n + 1 := by omega
  let previous : Fin (n + 1) := ⟨C.leftSwitch - 1, by omega⟩
  let current : Fin (n + 1) := ⟨C.leftSwitch, hleftAlphaBound⟩
  let critical : WithTop ℚ :=
    (((b.order ⟨C.leftSwitch, hleftBound⟩ -
      b.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) :
        WithTop ℚ)
  have hpreviousCurrent : previous ≤ current := by
    change C.leftSwitch - 1 ≤ C.leftSwitch
    omega
  have hrightEndpoint := b.alphaRightEndpoint_antitone hpreviousCurrent
  have hpreviousSucc : previous.succ =
      (⟨C.leftSwitch, hleftBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hcurrentSucc : current.succ =
      (⟨C.leftSwitch + 1, hinterior⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
  have halphaCurrent := (b.alpha_p2 current).1
  have hcriticalBetaQ :
      ((b.order ⟨C.leftSwitch, hleftBound⟩ -
          b.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) ≤
        b.alphaValue previous := by
    unfold alphaRightEndpoint at hrightEndpoint
    rw [hpreviousSucc, hcurrentSucc] at hrightEndpoint
    push_cast at hrightEndpoint ⊢
    linarith
  have hcriticalBeta : critical ≤
      (b.alphaValue previous : WithTop ℚ) := by
    exact WithTop.coe_le_coe.mpr hcriticalBetaQ
  have hgapLower := b.orderGap_ge_neg_two_mul_e current
  have hcriticalTwoEInt :
      b.order ⟨C.leftSwitch, hleftBound⟩ -
          b.order ⟨C.leftSwitch + 1, hinterior⟩ ≤
        2 * (ramificationIndex K : Int) := by
    unfold orderGap at hgapLower
    rw [hcurrentSucc] at hgapLower
    change -(2 * (ramificationIndex K : Int)) ≤
      b.order ⟨C.leftSwitch + 1, hinterior⟩ -
        b.order ⟨C.leftSwitch, hleftBound⟩ at hgapLower
    omega
  have hcriticalTwoEQ :
      ((b.order ⟨C.leftSwitch, hleftBound⟩ -
          b.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
    exact_mod_cast hcriticalTwoEInt
  have hcriticalTwoE : critical ≤
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    exact WithTop.coe_le_coe.mpr hcriticalTwoEQ
  have hprefix := beli2019Lemma76_typeI_boundary_lower
    a b D C hfirst hleftPos critical
      (by simpa only [previous] using hcriticalBeta) hcriticalTwoE
  have hadjacent := b.order_sub_add_alpha_le_cappedAdjacent current
  have hcriticalLocalQ :
      ((b.order current.castSucc - b.order current.succ : Int) : ℚ) ≤
        ((b.order current.castSucc - b.order current.succ : Int) : ℚ) +
          b.alphaValue current := by
    linarith
  have hcriticalLocal : critical ≤
      b.truncatedPrefixDefect b (-1) C.leftSwitch
        (C.leftSwitch + 2) := by
    have hcast : current.castSucc =
        (⟨C.leftSwitch, hleftBound⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hbase := (WithTop.coe_le_coe.mpr hcriticalLocalQ).trans hadjacent
    rw [hcast, hcurrentSucc] at hbase
    simpa only [critical, current] using hbase
  have hrightEven : Even (C.leftSwitch + 2) := by
    rcases C.left_even with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hjoined := alternatingPrefixDefect_concat_lower b
    C.leftSwitch (C.leftSwitch + 2) (by omega) C.left_even hrightEven
      critical hprefix (by
        simpa only [show C.leftSwitch + 2 - C.leftSwitch = 2 by omega,
          show 2 / 2 = 1 by omega, pow_one] using hcriticalLocal)
  simpa only [critical] using hjoined

/-- Lemma 7.7 in the missing `t = t' = u` branch, already in the capped
form needed by the sharp-defect argument in Lemma 7.9(i). -/
theorem beli2019Lemma77_typeI_coincident_terminal_sourceCapped
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefect : a.RepresentationDefectCondition b)
    (hleftLast : C.leftSwitch = D.profile.last)
    (hinterior : C.leftSwitch + 1 < n + 2) :
    (((((a.order
        ⟨C.leftSwitch, C.left_le_anchor.trans_lt D.anchor_bound⟩ -
      a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 2 : ℚ) :
        WithTop ℚ) ≤
      a.truncatedPrefixDefect a
        ((-1) ^ ((C.leftSwitch + 2) / 2)) 0
          (C.leftSwitch + 2)) := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hrightEq : C.rightSwitch = C.leftSwitch := by
    have hleftRight := C.left_le_anchor.trans C.anchor_le_right
    have hrightLast := C.right_le_last
    omega
  have htargetCurrent := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst C.leftSwitch C.left_even le_rfl (by rw [hrightEq])
  have htargetCurrentOrder :
      b.order ⟨C.leftSwitch, hleftBound⟩ =
        a.order ⟨C.leftSwitch, hleftBound⟩ + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact htargetCurrent
  have hnextCommon := D.profile.lastDifference.after
    (C.leftSwitch + 1) (by omega) hinterior
  have hnextOrder :
      b.order ⟨C.leftSwitch + 1, hinterior⟩ =
        a.order ⟨C.leftSwitch + 1, hinterior⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hnextCommon.symm
  have htargetLower :=
    beli2019Lemma77_typeI_coincident_terminal_targetCapped
      a b D C hfirst hleftPos hleftLast hinterior
  let epsilon : Kˣ := (-1) ^ ((C.leftSwitch + 2) / 2)
  have htargetLeSource :
      b.truncatedPrefixDefect b epsilon 0 (C.leftSwitch + 2) ≤
        a.truncatedPrefixDefect a epsilon 0 (C.leftSwitch + 2) := by
    by_cases hfull : C.leftSwitch + 2 = n + 2
    · calc
        b.truncatedPrefixDefect b epsilon 0 (C.leftSwitch + 2) =
            b.truncatedPrefixDefect b epsilon (n + 2) 0 := by
          rw [hfull, b.truncatedPrefixDefect_comm b epsilon 0 (n + 2)]
        _ = b.truncatedPrefixDefect a epsilon (n + 2) 0 :=
          (b.truncatedPrefixDefect_zero_right_eq_self a epsilon (n + 2)).symm
        _ = a.truncatedPrefixDefect a epsilon (n + 2) 0 :=
          truncatedPrefixDefect_fullLeft_change a b a epsilon 0
        _ ≤ a.truncatedPrefixDefect a epsilon 0 (C.leftSwitch + 2) := by
          rw [hfull, a.truncatedPrefixDefect_comm a epsilon (n + 2) 0]
    · have hproper : C.leftSwitch + 2 < n + 2 := by omega
      let idx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨C.leftSwitch + 2, by omega, hproper, hproper.le⟩
      have hAlpha := a.beli2019Lemma63_sameRank_right_value
        b hdefect idx (by
          intro k hk hkn
          exact D.profile.lastDifference.after k (by
            simp only [idx] at hk
            omega) hkn)
      have hformula := beli2019Remark616_rightPrefix
        a b hdefect idx hAlpha epsilon
      calc
        b.truncatedPrefixDefect b epsilon 0 (C.leftSwitch + 2) =
            min (a.truncatedPrefixDefect a epsilon 0
                (C.leftSwitch + 2))
              (b.alphaValue ⟨C.leftSwitch + 1, by omega⟩ :
                WithTop ℚ) := by
          simpa only [idx,
            show C.leftSwitch + 2 - 1 = C.leftSwitch + 1 by omega] using
              hformula
        _ ≤ a.truncatedPrefixDefect a epsilon 0
              (C.leftSwitch + 2) := min_le_left _ _
  have hlower :
      (((((a.order ⟨C.leftSwitch, hleftBound⟩ -
          a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 2 : ℚ) :
        WithTop ℚ) ≤
      a.truncatedPrefixDefect a epsilon 0
        (C.leftSwitch + 2)) := by
    have hcoefficient :
        ((b.order ⟨C.leftSwitch, hleftBound⟩ -
            b.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) =
          ((a.order ⟨C.leftSwitch, hleftBound⟩ -
            a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 2 := by
      exact_mod_cast (show
        b.order ⟨C.leftSwitch, hleftBound⟩ -
            b.order ⟨C.leftSwitch + 1, hinterior⟩ =
          a.order ⟨C.leftSwitch, hleftBound⟩ -
            a.order ⟨C.leftSwitch + 1, hinterior⟩ + 2 by
        omega)
    rw [← hcoefficient]
    have htargetLower' :
        (((b.order ⟨C.leftSwitch, hleftBound⟩ -
            b.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) :
          WithTop ℚ) ≤
        b.truncatedPrefixDefect b epsilon 0
          (C.leftSwitch + 2) := by
      simpa only [epsilon] using htargetLower
    exact htargetLower'.trans htargetLeSource
  simpa only [epsilon] using hlower

end BONG.GoodBONG

end Bong
