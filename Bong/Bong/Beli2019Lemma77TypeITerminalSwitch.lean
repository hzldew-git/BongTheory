/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeICentralEndpointComplete
import Bong.Bong.Beli2019Lemma77TypeIFullTerminal

/-!
# Beli (2019), Lemma 7.7: a terminal right switch

This is the remaining `t' = u` branch.  The boundary prefix from Lemma 7.6,
the endpoint-complete central segment, and the final adjacent pair concatenate
to the required target-prefix estimate.  Remark 6.16 then transports it to
the source prefix, including the full-rank endpoint.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The target self-prefix through the first common-suffix coordinate when
the canonical right switch is terminal. -/
theorem beli2019Lemma77_typeI_terminalSwitch_targetCapped
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hnext : C.rightSwitch + 1 < n + 2) :
    ((((b.order ⟨C.rightSwitch, by omega⟩ -
        b.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ ((C.rightSwitch + 2) / 2)) 0
          (C.rightSwitch + 2)) := by
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hrightAlphaBound : C.rightSwitch < n + 1 := by omega
  let current : Fin (n + 1) := ⟨C.rightSwitch, hrightAlphaBound⟩
  let critical : WithTop ℚ :=
    (((b.order ⟨C.rightSwitch, hrightBound⟩ -
      b.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) : WithTop ℚ)
  have hcurrentSucc : current.succ =
      (⟨C.rightSwitch + 1, hnext⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
  have hcurrentCast : current.castSucc =
      (⟨C.rightSwitch, hrightBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have halphaCurrent := (b.alpha_p2 current).1
  have hadjacent := b.order_sub_add_alpha_le_cappedAdjacent current
  have hcriticalLocalQ :
      ((b.order current.castSucc - b.order current.succ : Int) : ℚ) ≤
        ((b.order current.castSucc - b.order current.succ : Int) : ℚ) +
          b.alphaValue current := by
    linarith
  have hcriticalLocal : critical ≤
      b.truncatedPrefixDefect b (-1) C.rightSwitch
        (C.rightSwitch + 2) := by
    have hbase := (WithTop.coe_le_coe.mpr hcriticalLocalQ).trans hadjacent
    rw [hcurrentCast, hcurrentSucc] at hbase
    simpa only [critical, current] using hbase
  by_cases hleftRight : C.leftSwitch < C.rightSwitch
  · let previous : Fin (n + 1) := ⟨C.rightSwitch - 1, by omega⟩
    have hpreviousCurrent : previous ≤ current := by
      change C.rightSwitch - 1 ≤ C.rightSwitch
      omega
    have hrightEndpoint := b.alphaRightEndpoint_antitone hpreviousCurrent
    have hpreviousSucc : previous.succ =
        (⟨C.rightSwitch, hrightBound⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [previous, Fin.val_succ]
      omega
    have hcriticalPreviousQ :
        ((b.order ⟨C.rightSwitch, hrightBound⟩ -
            b.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) ≤
          b.alphaValue previous := by
      unfold alphaRightEndpoint at hrightEndpoint
      rw [hpreviousSucc, hcurrentSucc] at hrightEndpoint
      push_cast at hrightEndpoint ⊢
      linarith
    have hcriticalPrevious : critical ≤
        (b.alphaValue previous : WithTop ℚ) :=
      WithTop.coe_le_coe.mpr hcriticalPreviousQ
    let i : RepresentationIndex (n + 2) (n + 2) :=
      ⟨C.rightSwitch, by omega, hrightBound, hrightBound.le⟩
    have hsegmentEq :=
      beli2019Lemma76_typeI_central_segment_eq_alpha_endpointComplete
        a b D C hfirst i C.right_even hleftRight le_rfl
    have hsegment : critical ≤ b.truncatedPrefixDefect b
        ((-1) ^ ((C.rightSwitch - C.leftSwitch) / 2))
          C.leftSwitch C.rightSwitch := by
      rw [hsegmentEq]
      simpa only [i, previous] using hcriticalPrevious
    have hprefixRight : critical ≤ b.truncatedPrefixDefect b
        ((-1) ^ (C.rightSwitch / 2)) 0 C.rightSwitch := by
      by_cases hleftZero : C.leftSwitch = 0
      · simpa only [hleftZero, Nat.sub_zero] using hsegment
      · have hleftPos : 0 < C.leftSwitch := Nat.pos_of_ne_zero hleftZero
        let boundary : Fin (n + 1) := ⟨C.leftSwitch - 1, by
          have hbound := C.left_le_anchor.trans_lt D.anchor_bound
          omega⟩
        have hboundaryPrevious : boundary ≤ previous := by
          change C.leftSwitch - 1 ≤ C.rightSwitch - 1
          omega
        have htargetOrders := lemma76_typeI_target_even_order_eq_left
          a b D C hfirst C.rightSwitch hleftRight.le le_rfl C.right_even
        have hboundarySucc : boundary.succ =
            (⟨C.leftSwitch, by
              exact C.left_le_anchor.trans_lt D.anchor_bound⟩ :
                Fin (n + 2)) := by
          apply Fin.ext
          simp only [boundary, Fin.val_succ]
          omega
        have htargetOrder : b.order boundary.succ = b.order previous.succ := by
          rw [← b.orderSequence_entryOrZero_eq_order,
            ← b.orderSequence_entryOrZero_eq_order]
          rw [hboundarySucc, hpreviousSucc]
          exact htargetOrders
        have halphaMono := b.alphaValue_le_of_rightEndpoint_orders_eq
          hboundaryPrevious htargetOrder
        have hcriticalBoundary : critical ≤
            (b.alphaValue boundary : WithTop ℚ) :=
          hcriticalPrevious.trans (WithTop.coe_le_coe.mpr halphaMono)
        have hgapLower := b.orderGap_ge_neg_two_mul_e current
        have hcriticalTwoEInt :
            b.order ⟨C.rightSwitch, hrightBound⟩ -
                b.order ⟨C.rightSwitch + 1, hnext⟩ ≤
              2 * (ramificationIndex K : Int) := by
          unfold orderGap at hgapLower
          rw [hcurrentSucc] at hgapLower
          change -(2 * (ramificationIndex K : Int)) ≤
            b.order ⟨C.rightSwitch + 1, hnext⟩ -
              b.order ⟨C.rightSwitch, hrightBound⟩ at hgapLower
          omega
        have hcriticalTwoEQ :
            ((b.order ⟨C.rightSwitch, hrightBound⟩ -
                b.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) ≤
              2 * (ramificationIndex K : ℚ) := by
          exact_mod_cast hcriticalTwoEInt
        have hcriticalTwoE : critical ≤
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
          WithTop.coe_le_coe.mpr hcriticalTwoEQ
        have hboundary := beli2019Lemma76_typeI_boundary_lower
          a b D C hfirst hleftPos critical (by
            simpa only [boundary] using hcriticalBoundary) hcriticalTwoE
        exact alternatingPrefixDefect_concat_lower b C.leftSwitch
          C.rightSwitch hleftRight.le C.left_even C.right_even critical
            hboundary hsegment
    have hrightTwoEven : Even (C.rightSwitch + 2) := by
      rcases C.right_even with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    exact alternatingPrefixDefect_concat_lower b C.rightSwitch
      (C.rightSwitch + 2) (by omega) C.right_even hrightTwoEven critical
        hprefixRight (by
          simpa only [show C.rightSwitch + 2 - C.rightSwitch = 2 by omega,
            show 2 / 2 = 1 by omega, pow_one] using hcriticalLocal)
  · have hleftEq : C.leftSwitch = C.rightSwitch := by
      have hleftLeRight := C.left_le_anchor.trans C.anchor_le_right
      omega
    by_cases hleftZero : C.leftSwitch = 0
    · have hrightZero : C.rightSwitch = 0 := hleftEq.symm.trans hleftZero
      simpa only [critical, hrightZero, zero_add,
        show 2 / 2 = 1 by omega, pow_one] using hcriticalLocal
    · have hleftLast : C.leftSwitch = D.profile.last :=
        hleftEq.trans hrightLast
      have htarget := beli2019Lemma77_typeI_coincident_terminal_targetCapped
        a b D C hfirst (Nat.pos_of_ne_zero hleftZero) hleftLast (by
          simpa only [hleftEq] using hnext)
      simpa only [critical, hleftEq] using htarget

/-- Lemma 7.7 in the complete terminal-right-switch branch, in the source
capped form needed by Lemma 7.9(i). -/
theorem beli2019Lemma77_typeI_terminalSwitch_sourceCapped
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hnext : C.rightSwitch + 1 < n + 2) :
    (((((a.order ⟨C.rightSwitch, by omega⟩ -
        a.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) + 2 : ℚ) :
          WithTop ℚ) ≤
      a.truncatedPrefixDefect a
        ((-1) ^ ((C.rightSwitch + 2) / 2)) 0
          (C.rightSwitch + 2)) := by
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hleftRight : C.leftSwitch ≤ C.rightSwitch :=
    C.left_le_anchor.trans C.anchor_le_right
  have htargetCurrent := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst C.rightSwitch C.right_even hleftRight le_rfl
  have htargetCurrentOrder :
      b.order ⟨C.rightSwitch, hrightBound⟩ =
        a.order ⟨C.rightSwitch, hrightBound⟩ + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact htargetCurrent
  have hnextCommon := D.profile.lastDifference.after
    (C.rightSwitch + 1) (by omega) hnext
  have hnextOrder :
      b.order ⟨C.rightSwitch + 1, hnext⟩ =
        a.order ⟨C.rightSwitch + 1, hnext⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hnextCommon.symm
  have htargetLower := beli2019Lemma77_typeI_terminalSwitch_targetCapped
    a b D C hfirst hrightLast hnext
  let epsilon : Kˣ := (-1) ^ ((C.rightSwitch + 2) / 2)
  have htargetLeSource :
      b.truncatedPrefixDefect b epsilon 0 (C.rightSwitch + 2) ≤
        a.truncatedPrefixDefect a epsilon 0 (C.rightSwitch + 2) := by
    by_cases hfull : C.rightSwitch + 2 = n + 2
    · calc
        b.truncatedPrefixDefect b epsilon 0 (C.rightSwitch + 2) =
            b.truncatedPrefixDefect b epsilon (n + 2) 0 := by
          rw [hfull, b.truncatedPrefixDefect_comm b epsilon 0 (n + 2)]
        _ = b.truncatedPrefixDefect a epsilon (n + 2) 0 :=
          (b.truncatedPrefixDefect_zero_right_eq_self a epsilon
            (n + 2)).symm
        _ = a.truncatedPrefixDefect a epsilon (n + 2) 0 :=
          truncatedPrefixDefect_fullLeft_change a b a epsilon 0
        _ ≤ a.truncatedPrefixDefect a epsilon 0
              (C.rightSwitch + 2) := by
          rw [hfull, a.truncatedPrefixDefect_comm a epsilon (n + 2) 0]
    · have hproper : C.rightSwitch + 2 < n + 2 := by omega
      let idx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨C.rightSwitch + 2, by omega, hproper, hproper.le⟩
      have hAlpha := a.beli2019Lemma63_sameRank_right_value
        b hdefect idx (by
          intro k hk hkn
          exact D.profile.lastDifference.after k (by
            simp only [idx] at hk
            omega) hkn)
      have hformula := beli2019Remark616_rightPrefix
        a b hdefect idx hAlpha epsilon
      calc
        b.truncatedPrefixDefect b epsilon 0 (C.rightSwitch + 2) =
            min (a.truncatedPrefixDefect a epsilon 0
                (C.rightSwitch + 2))
              (b.alphaValue ⟨C.rightSwitch + 1, by omega⟩ :
                WithTop ℚ) := by
          simpa only [idx,
            show C.rightSwitch + 2 - 1 = C.rightSwitch + 1 by omega] using
              hformula
        _ ≤ a.truncatedPrefixDefect a epsilon 0
              (C.rightSwitch + 2) := min_le_left _ _
  have htargetLower' :
      (((b.order ⟨C.rightSwitch, hrightBound⟩ -
          b.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) : WithTop ℚ) ≤
        b.truncatedPrefixDefect b epsilon 0
          (C.rightSwitch + 2) := by
    simpa only [epsilon] using htargetLower
  have hcoefficient :
      ((b.order ⟨C.rightSwitch, hrightBound⟩ -
          b.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) =
        ((a.order ⟨C.rightSwitch, hrightBound⟩ -
          a.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) + 2 := by
    exact_mod_cast (show
      b.order ⟨C.rightSwitch, hrightBound⟩ -
          b.order ⟨C.rightSwitch + 1, hnext⟩ =
        a.order ⟨C.rightSwitch, hrightBound⟩ -
          a.order ⟨C.rightSwitch + 1, hnext⟩ + 2 by omega)
  have hlower := htargetLower'.trans htargetLeSource
  rw [hcoefficient] at hlower
  simpa only [epsilon] using hlower

end BONG.GoodBONG

end Bong
