/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78PreviousAlpha
import Bong.Bong.Beli2019Lemma69CappedPropagationRight

/-!
# Beli (2019), Lemma 6.9(ii): normalized type-III left branch

This file proves the source-alpha branch of Lemma 6.9(ii) on the alternating
left profile.  Its reverse-dual form is the `A_i = beta_i` classification
used at the end of Lemma 7.8.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Order identities at an even boundary of the normalized left type-III
profile. -/
theorem lemma78_typeIII_left_boundary_orders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (i : Nat) (hiTwo : 2 ≤ i)
    (hiLeft : i ≤ D.outer.transition.lastZero) (hiEven : Even i) :
    a.orderSequence.entryOrZero i =
        a.orderSequence.entryOrZero (i - 2) ∧
      b.orderSequence.entryOrZero (i - 2) =
        a.orderSequence.entryOrZero (i - 2) + 1 ∧
      b.orderSequence.entryOrZero (i - 1) =
        a.orderSequence.entryOrZero (i - 1) - 1 := by
  let left := D.outer.transition.lastZero
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hprofile := D.outer.leftProfile (by rw [hfirst]; omega)
  have hiPreviousEven : Even (i - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hsourceAt (k : Nat) (hk : k ≤ left) (hkEven : Even k) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero left := by
    have hsame := hprofile.2.2 k (by rw [hfirst]; omega) hk
      (by simpa only [hfirst, Nat.sub_zero] using hkEven)
    have hleftSame := hprofile.2.2 left D.outer.first_le_left
      le_rfl hprofile.1
    exact hsame.trans hleftSame.symm
  have hsourceCurrent := hsourceAt i (by simpa only [left] using hiLeft) hiEven
  have hsourcePrevious := hsourceAt (i - 2) (by omega) hiPreviousEven
  have hsourceEq : a.orderSequence.entryOrZero i =
      a.orderSequence.entryOrZero (i - 2) :=
    hsourceCurrent.trans hsourcePrevious.symm
  have htargetAt (k : Nat) (hk : k ≤ left) (hkEven : Even k) :
      b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero left := by
    have hleftBound : left < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    have hkBound : k < n + 2 := hk.trans_lt hleftBound
    have hleftDistance : Even (left - k) := by
      rcases hleftEven with ⟨d, hd⟩
      rcases hkEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hzeroK := b.orderSequence.entryOrZero_le_of_evenGap
      0 k (Nat.zero_le k) hkBound hkEven
    have hkLeft := b.orderSequence.entryOrZero_le_of_evenGap
      k left hk hleftBound hleftDistance
    have hfirstStrict := hprofile.2.1
    rw [hfirst] at hfirstStrict
    have hfirstUpper := D.no_gap_two 0 (by omega)
    have hsourceLeft := hprofile.2.2 left D.outer.first_le_left
      le_rfl hprofile.1
    rw [hfirst] at hsourceLeft
    have hboundary := D.outer.transition.leftBoundary
    have hleftGap : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using hboundary
    omega
  have htargetPrevious := htargetAt (i - 2) (by omega) hiPreviousEven
  have hboundary := D.outer.transition.leftBoundary
  have hleftGap : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using hboundary
  have htargetPreviousGap : b.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero (i - 2) + 1 := by omega
  have hpair := D.outer.leftPairEq (i - 2) (by omega) (by
    rcases hleftEven with ⟨d, hd⟩
    rcases hiEven with ⟨e, he⟩
    exact ⟨d - e + 1, by omega⟩)
  have htargetCurrent : b.orderSequence.entryOrZero (i - 1) =
      a.orderSequence.entryOrZero (i - 1) - 1 := by
    have hnext : i - 2 + 1 = i - 1 := by omega
    rw [hnext] at hpair
    omega
  exact ⟨hsourceEq, htargetPreviousGap, htargetCurrent⟩

set_option maxHeartbeats 4000000 in
-- Strong induction must normalize all three representation-alpha candidates.
/-- Lemma 6.9(ii) on the normalized left type-III profile: at every even
boundary before the transition, the representation invariant is the source
alpha. -/
theorem beli2019Lemma69_ii_typeIII_sourceLeftValue_of_center
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hcenter : a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hdefect : a.RepresentationDefectCondition b)
    (i : Nat) (hiTwo : 2 ≤ i)
    (hiLeft : i ≤ D.outer.transition.lastZero) (hiEven : Even i) :
    a.representationAlphaValue b
        ⟨i, by omega, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ =
      a.alphaValue ⟨i - 1, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ := by
  let left := D.outer.transition.lastZero
  have hmain : ∀ (t : Nat) (htTwo : 2 ≤ t) (htLeft : t ≤ left)
      (htEven : Even t),
      a.representationAlpha b
          (⟨t, by omega, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            dsimp only [left] at htLeft
            omega, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            dsimp only [left] at htLeft
            omega⟩ : RepresentationIndex (n + 2) (n + 2)) =
        (a.alphaValue ⟨t - 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          dsimp only [left] at htLeft
          omega⟩ : WithTop ℚ) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro htTwo htLeft htEven
        let idx : RepresentationIndex (n + 2) (n + 2) :=
          ⟨t, by omega, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩
        let p : Fin (n + 1) := ⟨t - 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩
        let previous : Fin (n + 1) := ⟨t - 2, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩
        have hleftRank : left < n + 2 := by
          dsimp only [left]
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega
        have hleftAlphaBound : left < n + 1 := by
          dsimp only [left]
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega
        have hpreviousCast : previous.castSucc =
            (⟨t - 2, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          rfl
        have hpreviousSucc : previous.succ =
            (⟨t - 1, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          simp only [previous, Fin.val_succ]
          omega
        have hpCast : p.castSucc =
            (⟨t - 1, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          rfl
        have hpSucc : p.succ =
            (⟨t, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          simp only [p, Fin.val_succ]
          omega
        have horders := lemma78_typeIII_left_boundary_orders
          a b D hfirst t htTwo (by simpa only [left] using htLeft) htEven
        have hsourceEven : a.order ⟨t, by omega⟩ =
            a.order ⟨t - 2, by omega⟩ := by
          rw [← a.orderSequence_entryOrZero_eq_order ⟨t, by omega⟩,
            ← a.orderSequence_entryOrZero_eq_order ⟨t - 2, by omega⟩]
          exact horders.1
        have htargetPrevious : b.order ⟨t - 2, by omega⟩ =
            a.order ⟨t - 2, by omega⟩ + 1 := by
          rw [← b.orderSequence_entryOrZero_eq_order ⟨t - 2, by omega⟩,
            ← a.orderSequence_entryOrZero_eq_order ⟨t - 2, by omega⟩]
          exact horders.2.1
        have htargetCurrent : b.order ⟨t - 1, by omega⟩ =
            a.order ⟨t - 1, by omega⟩ - 1 := by
          rw [← b.orderSequence_entryOrZero_eq_order ⟨t - 1, by omega⟩,
            ← a.orderSequence_entryOrZero_eq_order ⟨t - 1, by omega⟩]
          exact horders.2.2
        have hpreviousOne :=
          a.lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
            b D hfirst hcenter t htTwo
              (by simpa only [left] using htLeft) htEven
        have hpreviousOne' : a.alphaValue previous = 1 := by
          simpa only [previous] using hpreviousOne
        have hadjacentSum : a.adjacentOrderSum previous =
            a.adjacentOrderSum p := by
          unfold adjacentOrderSum
          rw [hpreviousCast, hpreviousSucc, hpCast, hpSucc]
          rw [hsourceEven]
          omega
        have hconstant := a.beli2009Corollary23 previous p (by
          change t - 2 ≤ t - 1
          omega) hadjacentSum
        have hrightEndpoint := hconstant.rightEndpoint_eq p (by
          change t - 2 ≤ t - 1
          omega) le_rfl
        have halphaFormula : a.alphaValue p =
            ((a.order ⟨t, by omega⟩ - a.order ⟨t - 1, by omega⟩ :
              Int) : ℚ) + 1 := by
          unfold alphaRightEndpoint at hrightEndpoint
          rw [hpSucc, hpreviousSucc] at hrightEndpoint
          rw [hpreviousOne'] at hrightEndpoint
          push_cast
          linarith
        have hsourceNext : a.order ⟨idx.val, idx.lt_large⟩ =
            a.order p.succ := by
          apply congrArg a.order
          apply Fin.ext
          simp only [idx, p, Fin.val_succ]
          omega
        have htargetCurrent' :
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
              a.order p.castSucc - 1 := by
          rw [htargetCurrent]
          apply congrArg (fun z : Int ↦ z - 1)
          apply congrArg a.order
          apply Fin.ext
          rfl
        have hupper : a.representationAlpha b idx ≤
            (a.alphaValue p : WithTop ℚ) := by
          calc
            a.representationAlpha b idx =
                (a.representationAlphaValue b idx : WithTop ℚ) :=
              (a.coe_representationAlphaValue b idx).symm
            _ ≤ a.truncatedPrefixDefect b 1 idx.val idx.val := hdefect idx
            _ ≤ a.prefixAlphaCap idx.val :=
              a.truncatedPrefixDefect_le_leftCap b 1 idx.val idx.val
            _ = (a.alphaValue p : WithTop ℚ) := by
              rw [a.prefixAlphaCap_of_internal idx.pos idx.lt_large]
        have hhalfLower : (a.alphaValue p : WithTop ℚ) ≤
            a.representationHalfGap b idx := by
          rw [a.coe_alphaValue p]
          apply (a.alpha_le_halfGapCandidate p).trans
          unfold halfGapCandidate representationHalfGap
          rw [hsourceNext, htargetCurrent']
          exact_mod_cast (show
            ((a.order p.succ - a.order p.castSucc : Int) : ℚ) / 2 +
                (ramificationIndex K : ℚ) ≤
              ((a.order p.succ - (a.order p.castSucc - 1) : Int) : ℚ) / 2 +
                (ramificationIndex K : ℚ) by
            push_cast
            linarith)
        have hcoefficient :
            ((a.order ⟨idx.val, idx.lt_large⟩ -
              b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ :
                Int) : ℚ) = a.alphaValue p := by
          rw [hsourceNext, htargetCurrent']
          have hpSucc : p.succ = (⟨t, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            simp only [p, Fin.val_succ]
            omega
          have hpCast : p.castSucc =
              (⟨t - 1, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            rfl
          rw [hpSucc, hpCast, halphaFormula]
          push_cast
          ring
        have hprimary : (a.alphaValue p : WithTop ℚ) ≤
            a.representationPrimaryDefect b idx := by
          have hnonnegative := a.truncatedPrefixDefect_nonneg
            (alphaV := alpha) (alphaW := alpha) b (-1)
            (idx.val + 1) (idx.val - 1)
          unfold representationPrimaryDefect
          rw [hcoefficient]
          exact le_add_of_nonneg_right hnonnegative
        have hlower : (a.alphaValue p : WithTop ℚ) ≤
            a.representationAlpha b idx := by
          rw [a.representationAlpha_eq_min_halfGap_prime b idx]
          apply le_min hhalfLower
          have hinterior : 1 < idx.val ∧ idx.val + 1 < n + 2 := by
            constructor
            · simp only [idx]
              omega
            · simp only [idx]
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega
          rw [a.representationAlphaPrime_eq_min_primary_secondary
            b idx hinterior]
          apply le_min hprimary
          let previousTwo : Fin (n + 1) := ⟨t - 3, by omega⟩
          let next : Fin (n + 1) := ⟨t, by omega⟩
          let coefficient : ℚ :=
            ((a.order ⟨t, by omega⟩ + a.order ⟨t + 1, by omega⟩ -
              a.order ⟨t - 2, by omega⟩ -
              a.order ⟨t - 1, by omega⟩ : Int) : ℚ)
          let leftDefect := a.truncatedPrefixDefect a (-1) (t - 2) t
          let rightDefect := a.truncatedPrefixDefect a (-1) t (t + 2)
          let diagonalDefect := a.truncatedPrefixDefect b 1 (t - 2) (t - 2)
          let middleDefect := a.truncatedPrefixDefect b (-1) t (t - 2)
          let crossDefect := a.truncatedPrefixDefect b 1 (t + 2) (t - 2)
          have hleftGood := a.good
            (⟨t - 1, by omega⟩ : Fin (n + 2)) (by
              change t - 1 + 2 < n + 2
              omega)
          have hrightGood := a.good
            (⟨t - 2, by omega⟩ : Fin (n + 2)) (by
              change t - 2 + 2 < n + 2
              omega)
          have hleftGood' : a.order ⟨t - 1, by omega⟩ ≤
              a.order ⟨t + 1, by omega⟩ := by
            have hindex :
                (⟨(⟨t - 1, by omega⟩ : Fin (n + 2)).val + 2, by
                  change t - 1 + 2 < n + 2
                  omega⟩ : Fin (n + 2)) = ⟨t + 1, by omega⟩ := by
              apply Fin.ext
              simp only
              omega
            rw [hindex] at hleftGood
            exact hleftGood
          have hrightGood' : a.order ⟨t - 2, by omega⟩ ≤
              a.order ⟨t, by omega⟩ := by
            have hindex :
                (⟨(⟨t - 2, by omega⟩ : Fin (n + 2)).val + 2, by
                  change t - 2 + 2 < n + 2
                  omega⟩ : Fin (n + 2)) = ⟨t, by omega⟩ := by
              apply Fin.ext
              simp only
              omega
            rw [hindex] at hrightGood
            exact hrightGood
          have hleftShift :
              ((a.order p.succ - a.order previous.castSucc : Int) : ℚ) ≤
                coefficient := by
            have hpSucc : p.succ = (⟨t, by omega⟩ : Fin (n + 2)) := by
              apply Fin.ext
              simp only [p, Fin.val_succ]
              omega
            have hpreviousCast : previous.castSucc =
                (⟨t - 2, by omega⟩ : Fin (n + 2)) := by
              apply Fin.ext
              rfl
            rw [hpSucc, hpreviousCast]
            dsimp only [coefficient]
            push_cast
            have hgoodQ : (a.order ⟨t - 1, by omega⟩ : ℚ) ≤
                a.order ⟨t + 1, by omega⟩ := by exact_mod_cast hleftGood'
            linarith
          have hrightShift :
              ((a.order next.succ - a.order p.castSucc : Int) : ℚ) ≤
                coefficient := by
            have hnextSucc : next.succ =
                (⟨t + 1, by omega⟩ : Fin (n + 2)) := by
              apply Fin.ext
              rfl
            have hpCast : p.castSucc =
                (⟨t - 1, by omega⟩ : Fin (n + 2)) := by
              apply Fin.ext
              rfl
            rw [hnextSucc, hpCast]
            dsimp only [coefficient]
            push_cast
            have hgoodQ : (a.order ⟨t - 2, by omega⟩ : ℚ) ≤
                a.order ⟨t, by omega⟩ := by exact_mod_cast hrightGood'
            linarith
          have hleftRaw := a.alpha_le_order_sub_add_cappedAdjacent
            (i := p) (j := previous) (by
              change previous.val ≤ p.val
              simp only [previous, p]
              omega)
          have hleftBound : (a.alphaValue p : WithTop ℚ) ≤
              (coefficient : WithTop ℚ) + leftDefect := by
            have hshiftTop :
                ((((a.order p.succ - a.order previous.castSucc : Int) : ℚ)) :
                  WithTop ℚ) ≤ coefficient := by exact_mod_cast hleftShift
            have hraw : (a.alphaValue p : WithTop ℚ) ≤
                ((((a.order p.succ - a.order previous.castSucc : Int) : ℚ)) :
                    WithTop ℚ) + leftDefect := by
              simpa only [previous, leftDefect,
                show t - 2 + 2 = t by omega] using hleftRaw
            exact hraw.trans (by
              simpa only [add_comm] using add_le_add_right hshiftTop leftDefect)
          have hrightRaw := a.alpha_le_laterOrder_sub_add_cappedAdjacent
            (i := p) (j := next) (by
              change p.val ≤ next.val
              simp only [p, next]
              omega)
          have hrightBound : (a.alphaValue p : WithTop ℚ) ≤
              (coefficient : WithTop ℚ) + rightDefect := by
            have hshiftTop :
                ((((a.order next.succ - a.order p.castSucc : Int) : ℚ)) :
                  WithTop ℚ) ≤ coefficient := by exact_mod_cast hrightShift
            have hraw : (a.alphaValue p : WithTop ℚ) ≤
                ((((a.order next.succ - a.order p.castSucc : Int) : ℚ)) :
                    WithTop ℚ) + rightDefect := by
              simpa only [next, rightDefect] using hrightRaw
            exact hraw.trans (by
              simpa only [add_comm] using add_le_add_right hshiftTop rightDefect)
          have hdiagonalBound : (a.alphaValue p : WithTop ℚ) ≤
              (coefficient : WithTop ℚ) + diagonalDefect := by
            by_cases htBase : t = 2
            · have htop : diagonalDefect = ⊤ := by
                have htSub : t - 2 = 0 := by omega
                dsimp only [diagonalDefect]
                unfold truncatedPrefixDefect
                rw [htSub, a.prefixAlphaCap_zero, b.prefixAlphaCap_zero]
                simp [BONG.GoodBONG.prefixProduct, defectOrder_one]
              rw [htop]
              simp
            · have htFour : 4 ≤ t := by
                rcases htEven with ⟨d, hd⟩
                omega
              let earlierIdx : RepresentationIndex (n + 2) (n + 2) :=
                ⟨t - 2, by omega, by
                  have hbound := D.outer.transition.firstTwo_le_rank
                  rw [D.adjacent] at hbound
                  omega, by
                  have hbound := D.outer.transition.firstTwo_le_rank
                  rw [D.adjacent] at hbound
                  omega⟩
              have hearlier := ih (t - 2) (by omega) (by omega)
                (by simpa only [left] using (show t - 2 ≤ left by omega)) (by
                  rcases htEven with ⟨d, hd⟩
                  exact ⟨d - 1, by omega⟩)
              have hearlierEq : a.representationAlpha b earlierIdx =
                  (a.alphaValue previousTwo : WithTop ℚ) := by
                simpa only [earlierIdx, previousTwo,
                  show t - 2 - 1 = t - 3 by omega] using hearlier
              have hdiag : (a.alphaValue previousTwo : WithTop ℚ) ≤
                  diagonalDefect := by
                calc
                  (a.alphaValue previousTwo : WithTop ℚ) =
                      a.representationAlpha b earlierIdx := hearlierEq.symm
                  _ = (a.representationAlphaValue b earlierIdx : WithTop ℚ) :=
                    (a.coe_representationAlphaValue b earlierIdx).symm
                  _ ≤ a.truncatedPrefixDefect b 1
                      earlierIdx.val earlierIdx.val := hdefect earlierIdx
                  _ = diagonalDefect := rfl
              have hendpoint := a.alphaRightEndpoint_antitone
                (show previousTwo ≤ p by
                  change previousTwo.val ≤ p.val
                  simp only [previousTwo, p]
                  omega)
              have hpreviousTwoSucc : previousTwo.succ =
                  (⟨t - 2, by omega⟩ : Fin (n + 2)) := by
                apply Fin.ext
                simp only [previousTwo, Fin.val_succ]
                omega
              have hshift : a.alphaValue p ≤
                  coefficient + a.alphaValue previousTwo := by
                unfold alphaRightEndpoint at hendpoint
                rw [hpSucc, hpreviousTwoSucc] at hendpoint
                dsimp only [coefficient]
                push_cast at hendpoint ⊢
                have hgoodQ : (a.order ⟨t - 1, by omega⟩ : ℚ) ≤
                    a.order ⟨t + 1, by omega⟩ := by
                  exact_mod_cast hleftGood'
                linarith
              calc
                (a.alphaValue p : WithTop ℚ) ≤
                    (coefficient : WithTop ℚ) +
                      (a.alphaValue previousTwo : WithTop ℚ) := by
                  exact_mod_cast hshift
                _ ≤ (coefficient : WithTop ℚ) + diagonalDefect := by
                  simpa only [add_comm] using
                    add_le_add_right hdiag (coefficient : WithTop ℚ)
          have hfirstDom := a.truncatedPrefixDefect_domination a b
            (-1) 1 t (t - 2) (t - 2)
          have hfirstMin : min leftDefect diagonalDefect ≤ middleDefect := by
            dsimp only [leftDefect, diagonalDefect, middleDefect]
            rw [← a.truncatedPrefixDefect_comm a (-1) t (t - 2)]
            simpa only [mul_one] using hfirstDom
          have hsecondDom := a.truncatedPrefixDefect_domination a b
            (-1) (-1) (t + 2) t (t - 2)
          have hsecondMin : min rightDefect middleDefect ≤ crossDefect := by
            dsimp only [rightDefect, middleDefect, crossDefect]
            rw [← a.truncatedPrefixDefect_comm a (-1) (t + 2) t]
            simpa only [neg_mul, one_mul, neg_neg] using hsecondDom
          have hnested : min rightDefect
              (min leftDefect diagonalDefect) ≤ crossDefect :=
            (min_le_min_left rightDefect hfirstMin).trans hsecondMin
          have hminimum : (a.alphaValue p : WithTop ℚ) ≤
              (coefficient : WithTop ℚ) + min rightDefect
                (min leftDefect diagonalDefect) :=
            withTop_le_shift_add_min _ coefficient _ _ hrightBound
              (withTop_le_shift_add_min _ coefficient _ _
                hleftBound hdiagonalBound)
          have hcrossBound : (a.alphaValue p : WithTop ℚ) ≤
              (coefficient : WithTop ℚ) + crossDefect :=
            hminimum.trans (by
              simpa only [add_comm] using
                add_le_add_right hnested (coefficient : WithTop ℚ))
          unfold representationSecondaryDefect
          rw [htargetPrevious, htargetCurrent]
          have hcoefficientEq :
              a.order ⟨idx.val, idx.lt_large⟩ +
                    a.order ⟨idx.val + 1, hinterior.2⟩ -
                    (a.order ⟨t - 2, by omega⟩ + 1) -
                    (a.order ⟨t - 1, by omega⟩ - 1) =
                a.order ⟨t, by omega⟩ + a.order ⟨t + 1, by omega⟩ -
                  a.order ⟨t - 2, by omega⟩ -
                  a.order ⟨t - 1, by omega⟩ := by
            have hidxCurrent : a.order ⟨idx.val, idx.lt_large⟩ =
                a.order ⟨t, by omega⟩ := by
              apply congrArg a.order
              apply Fin.ext
              rfl
            have hidxNext : a.order ⟨idx.val + 1, hinterior.2⟩ =
                a.order ⟨t + 1, by omega⟩ := by
              apply congrArg a.order
              apply Fin.ext
              rfl
            rw [hidxCurrent, hidxNext]
            ring
          rw [hcoefficientEq]
          simpa only [coefficient, crossDefect, idx] using hcrossBound
        exact le_antisymm hupper hlower
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b]
  simpa only [left] using hmain i hiTwo hiLeft hiEven

/-- Section 7 wrapper for the normalized source-left classification. -/
theorem beli2019Lemma69_ii_typeIII_sourceLeftValue
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : Nat) (hiTwo : 2 ≤ i)
    (hiLeft : i ≤ D.outer.transition.lastZero) (hiEven : Even i) :
    a.representationAlphaValue b
        ⟨i, by omega, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ =
      a.alphaValue ⟨i - 1, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ := by
  have hdata := a.beli2019Lemma78_alphas_and_gap
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
  exact a.beli2019Lemma69_ii_typeIII_sourceLeftValue_of_center
    b D hfirst hdata.1 hdefect i hiTwo hiLeft hiEven

end BONG.GoodBONG

end Bong
