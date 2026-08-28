/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftPrimary
import Bong.Bong.Beli2019Lemma79RightTailGapTwoTerminalAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 8: coincident type-I switches

When `u = t = t'`, Lemma 6.9(v) is vacuous.  The paper instead observes
that the target gap at `u - 1` is odd and three larger than the source gap.
Lemma 2.7 and the left-switch source-alpha formula then give the same
identity `beta_(u-1) = alpha_(u-1) + 2` directly.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The direct `u = t` calculation in lines 5888--5889 of the paper. -/
theorem beli2019Lemma79_typeI_caseEight_coincidentPreviousAlpha_eq_add_two
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hleftLast : C.leftSwitch = D.profile.last)
    (hlastPos : 0 < D.profile.last)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hdefect : a.RepresentationDefectCondition b)
    (hgapLe : b.orderGap ⟨D.profile.last - 1, by
      have hbound := D.profile.lastDifference.bound
      omega⟩ ≤ 2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨D.profile.last - 1, by
        have hbound := D.profile.lastDifference.bound
        omega⟩ =
      a.alphaValue ⟨D.profile.last - 1, by
        have hbound := D.profile.lastDifference.bound
        omega⟩ + 2 := by
  have hleftPos : 0 < C.leftSwitch := by omega
  have hleftTwo : 1 < C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hlastBound : D.profile.last < n + 2 :=
    D.profile.lastDifference.bound
  let p : Fin (n + 1) := ⟨D.profile.last - 1, by omega⟩
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨D.profile.last, hlastPos, hlastBound, hlastBound.le⟩
  have hsourceRaw := lemma69_typeI_left_alpha_formula
    a b D C hfirst hdefect idx (by simp only [idx]; omega) (by
      simp only [idx]
      rw [hleftLast]) (by
        simp only [idx]
        rw [← hleftLast]
        exact C.left_even)
  have hpCast : p.castSucc =
      (⟨D.profile.last - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨D.profile.last, hlastBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hsource : a.alphaValue p = (a.orderGap p : Rat) + 1 := by
    unfold orderGap
    rw [hpSucc, hpCast]
    simpa only [idx, p] using hsourceRaw
  have hprevious := lemma69_v_typeI_previous_target_order
    a b D C hfirst hleftPos
  have hprevious' : b.order p.castSucc = a.order p.castSucc - 1 := by
    rw [hpCast]
    simpa only [hleftLast] using hprevious
  have hcurrent : b.order p.succ = a.order p.succ + 2 := by
    rw [hpSucc, ← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hgapTwo
  have hgapShift : b.orderGap p = a.orderGap p + 3 := by
    unfold orderGap
    rw [hprevious', hcurrent]
    ring
  have hodd : Odd (b.orderGap p) := by
    have hraw := lemma76_leftSwitch_gap_odd
      a b D C hfirst hleftPos
    simpa only [p, hleftLast] using hraw
  have hgapLe' : b.orderGap p ≤
      2 * (ramificationIndex K : Int) := by
    simpa only [p] using hgapLe
  have htarget := (b.beli2009Lemma27_iii p hgapLe').2.mpr
    (Or.inr hodd)
  have hgapShiftQ : (b.orderGap p : Rat) =
      (a.orderGap p : Rat) + 3 := by
    exact_mod_cast hgapShift
  rw [htarget, hsource, hgapShiftQ]
  ring

end BONG.GoodBONG

end Bong
