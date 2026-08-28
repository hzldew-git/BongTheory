/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma63
import Bong.Bong.Beli2019FullRankDefect

/-!
# Beli (2019), Lemma 6.3 at the right endpoint

For same-space good BONGs, agreement of the order suffix forces the
representation invariant to equal the target alpha.  This is the concrete
right-end form of the duality argument used in Lemma 6.9.  The reverse
induction starts from the infinite full-rank comparison defect.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 1000000 in
-- Reverse induction again elaborates many proof-dependent `Fin` transports.
/-- Same-space right-end counterpart of Lemma 6.3. -/
theorem beli2019Lemma63_sameRank_right
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (horders : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hmain : ∀ (d t : Nat) (hd : d = n + 2 - t)
      (htPos : 0 < t) (htBound : t < n + 2)
      (hsuffix : ∀ k, t ≤ k → k < n + 2 →
        a.orderSequence.entryOrZero k =
          b.orderSequence.entryOrZero k),
      a.representationAlpha b
          (⟨t, htPos, htBound, by omega⟩ :
            RepresentationIndex (n + 2) (n + 2)) =
        (b.alphaValue ⟨t - 1, by omega⟩ : WithTop ℚ) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro t hd htPos htBound hsuffix
        let idx : RepresentationIndex (n + 2) (n + 2) :=
          ⟨t, htPos, htBound, by omega⟩
        let p : Fin (n + 1) := ⟨t - 1, by omega⟩
        have hidxVal : idx.val = t := rfl
        have hpVal : p.val = t - 1 := rfl
        have hsourceCurrent :
            a.order ⟨idx.val, idx.lt_large⟩ = b.order p.succ := by
          have heq := hsuffix t le_rfl htBound
          let af : Fin (n + 2) := ⟨t, htBound⟩
          let bf : Fin (n + 2) := ⟨t, htBound⟩
          rw [a.orderSequence_entryOrZero_eq_order af,
            b.orderSequence_entryOrZero_eq_order bf] at heq
          have haIndex :
              a.order ⟨idx.val, idx.lt_large⟩ = a.order af := by
            apply congrArg a.order
            apply Fin.ext
            exact hidxVal
          have hbIndex : b.order bf = b.order p.succ := by
            apply congrArg b.order
            apply Fin.ext
            simp only [bf, p, Fin.val_succ]
            omega
          exact haIndex.trans (heq.trans hbIndex)
        have htargetPrevious :
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
              b.order p.castSucc := by
          apply congrArg b.order
          apply Fin.ext
          simp only [p, Fin.val_castSucc]
          exact congrArg (fun x ↦ x - 1) hidxVal
        have hhalf : a.representationHalfGap b idx =
            b.halfGapCandidate p := by
          unfold representationHalfGap halfGapCandidate
          rw [hsourceCurrent, htargetPrevious]
        have hupper : a.representationAlpha b idx ≤
            (b.alphaValue p : WithTop ℚ) := by
          calc
            a.representationAlpha b idx =
                (a.representationAlphaValue b idx : WithTop ℚ) :=
              (a.coe_representationAlphaValue b idx).symm
            _ ≤ a.truncatedPrefixDefect b 1 idx.val idx.val :=
              hdefect idx
            _ ≤ b.prefixAlphaCap idx.val :=
              a.truncatedPrefixDefect_le_rightCap b 1 idx.val idx.val
            _ = (b.alphaValue p : WithTop ℚ) := by
              rw [b.prefixAlphaCap_of_internal idx.pos idx.lt_large]
        have hhalfLower : (b.alphaValue p : WithTop ℚ) ≤
            a.representationHalfGap b idx := by
          rw [hhalf, b.coe_alphaValue p]
          exact b.alpha_le_halfGapCandidate p
        have hprimary : (b.alphaValue p : WithTop ℚ) ≤
            a.representationPrimaryDefect b idx := by
          let shift : ℚ :=
            ((b.order p.succ - b.order p.castSucc : Int) : ℚ)
          have hlocal := b.alpha_le_orderGap_add_cappedAdjacent p
          by_cases hlast : t + 1 = n + 2
          · have hfull := a.truncatedPrefixDefect_full_eq_top b
            have htargetReverse :
                b.truncatedPrefixDefect b (-1) (t + 1) (t - 1) =
                  b.truncatedPrefixDefect b (-1) (t - 1) (t + 1) :=
              b.truncatedPrefixDefect_comm b (-1) (t + 1) (t - 1)
            have hdom := a.truncatedPrefixDefect_domination b b
              1 (-1) (t + 1) (t + 1) (t - 1)
            have hselfLe :
                b.truncatedPrefixDefect b (-1) (t - 1) (t + 1) ≤
                  a.truncatedPrefixDefect b (-1) (t + 1) (t - 1) := by
              have hfull' :
                  a.truncatedPrefixDefect b 1 (t + 1) (t + 1) = ⊤ := by
                simpa only [hlast] using hfull
              rw [hfull', htargetReverse] at hdom
              simpa only [top_inf_eq, one_mul] using hdom
            have hlocal' : (b.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) +
                  b.truncatedPrefixDefect b (-1) (t - 1) (t + 1) := by
              simpa only [shift, p, Fin.val_succ, Fin.val_castSucc,
                show t - 1 + 2 = t + 1 by omega] using hlocal
            have hcrossBound : (b.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) +
                  a.truncatedPrefixDefect b (-1) (t + 1) (t - 1) :=
              hlocal'.trans (by
                simpa only [add_comm] using
                  add_le_add_right hselfLe (shift : WithTop ℚ))
            unfold representationPrimaryDefect
            rw [hsourceCurrent, htargetPrevious, hidxVal]
            simpa only [shift] using hcrossBound
          · have htNextBound : t + 1 < n + 2 := by omega
            let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
              ⟨t + 1, by omega, htNextBound, by omega⟩
            let nextAlpha : Fin (n + 1) := ⟨t, by omega⟩
            have hmeasure : n + 2 - (t + 1) < d := by omega
            have hnext := ih (n + 2 - (t + 1)) hmeasure
              (t + 1) rfl (by omega) htNextBound
              (fun k hk hkn ↦ hsuffix k (by omega) hkn)
            have hnextEq : a.representationAlpha b nextIdx =
                (b.alphaValue nextAlpha : WithTop ℚ) := by
              have halphaIndex :
                  (⟨t + 1 - 1, by omega⟩ : Fin (n + 1)) =
                    nextAlpha := by
                apply Fin.ext
                simp only [nextAlpha]
                omega
              simpa only [nextIdx, halphaIndex] using hnext
            have hdiagonal : (b.alphaValue nextAlpha : WithTop ℚ) ≤
                a.truncatedPrefixDefect b 1 (t + 1) (t + 1) := by
              calc
                (b.alphaValue nextAlpha : WithTop ℚ) =
                    a.representationAlpha b nextIdx := hnextEq.symm
                _ = (a.representationAlphaValue b nextIdx : WithTop ℚ) :=
                  (a.coe_representationAlphaValue b nextIdx).symm
                _ ≤ a.truncatedPrefixDefect b 1
                    nextIdx.val nextIdx.val := hdefect nextIdx
                _ = a.truncatedPrefixDefect b 1 (t + 1) (t + 1) := rfl
            have hendpoint := b.alphaLeftEndpoint_monotone
              (show p ≤ nextAlpha by
                change p.val ≤ nextAlpha.val
                simp only [p, nextAlpha]
                omega)
            have hnextShift : b.alphaValue p ≤
                shift + b.alphaValue nextAlpha := by
              unfold alphaLeftEndpoint at hendpoint
              have hpCast : p.castSucc =
                  (⟨t - 1, by omega⟩ : Fin (n + 2)) := by
                apply Fin.ext
                rfl
              have hnextCast : nextAlpha.castSucc = p.succ := by
                apply Fin.ext
                simp only [nextAlpha, p, Fin.val_castSucc, Fin.val_succ]
                omega
              rw [hnextCast] at hendpoint
              dsimp only [shift]
              push_cast
              linarith
            have hnextBound : (b.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) +
                  a.truncatedPrefixDefect b 1 (t + 1) (t + 1) := by
              calc
                (b.alphaValue p : WithTop ℚ) ≤
                    (shift : WithTop ℚ) +
                      (b.alphaValue nextAlpha : WithTop ℚ) := by
                  exact_mod_cast hnextShift
                _ ≤ (shift : WithTop ℚ) +
                    a.truncatedPrefixDefect b 1 (t + 1) (t + 1) := by
                  simpa only [add_comm] using
                    add_le_add_right hdiagonal (shift : WithTop ℚ)
            have hlocalReverse : (b.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) +
                  b.truncatedPrefixDefect b (-1) (t + 1) (t - 1) := by
              rw [b.truncatedPrefixDefect_comm b (-1) (t + 1) (t - 1)]
              simpa only [shift, p, Fin.val_succ, Fin.val_castSucc,
                show t - 1 + 2 = t + 1 by omega] using hlocal
            have hdom := a.truncatedPrefixDefect_domination b b
              1 (-1) (t + 1) (t + 1) (t - 1)
            have hdom' : min
                (a.truncatedPrefixDefect b 1 (t + 1) (t + 1))
                (b.truncatedPrefixDefect b (-1) (t + 1) (t - 1)) ≤
                  a.truncatedPrefixDefect b (-1) (t + 1) (t - 1) := by
              simpa only [one_mul] using hdom
            have hminimum : (b.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) + min
                  (a.truncatedPrefixDefect b 1 (t + 1) (t + 1))
                  (b.truncatedPrefixDefect b (-1) (t + 1) (t - 1)) :=
              withTop_le_shift_add_min _ shift _ _ hnextBound hlocalReverse
            have hcrossBound : (b.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) +
                  a.truncatedPrefixDefect b (-1) (t + 1) (t - 1) :=
              hminimum.trans (by
                simpa only [add_comm] using
                  add_le_add_right hdom' (shift : WithTop ℚ))
            unfold representationPrimaryDefect
            rw [hsourceCurrent, htargetPrevious, hidxVal]
            simpa only [shift] using hcrossBound
        have hlower : (b.alphaValue p : WithTop ℚ) ≤
            a.representationAlpha b idx := by
          rw [a.representationAlpha_eq_min_halfGap_prime b idx]
          apply le_min hhalfLower
          by_cases hinterior : 1 < idx.val ∧ idx.val + 1 < n + 2
          · rw [a.representationAlphaPrime_eq_min_primary_secondary
              b idx hinterior]
            apply le_min hprimary
            have htInterior : 1 < t ∧ t + 1 < n + 2 := by
              simpa only [idx] using hinterior
            let previous : Fin (n + 1) := ⟨t - 2, by omega⟩
            let next : Fin (n + 1) := ⟨t, by omega⟩
            let coefficient : ℚ :=
              ((b.order ⟨t, by omega⟩ + b.order ⟨t + 1, by omega⟩ -
                b.order ⟨t - 2, by omega⟩ -
                b.order ⟨t - 1, by omega⟩ : Int) : ℚ)
            let leftDefect :=
              b.truncatedPrefixDefect b (-1) (t - 2) t
            let rightDefect :=
              b.truncatedPrefixDefect b (-1) t (t + 2)
            let diagonalDefect :=
              a.truncatedPrefixDefect b 1 (t + 2) (t + 2)
            let middleDefect :=
              a.truncatedPrefixDefect b (-1) (t + 2) t
            let crossDefect :=
              a.truncatedPrefixDefect b 1 (t + 2) (t - 2)
            have htTwoLe : 2 ≤ t := by omega
            have hleftGood := b.good
              (⟨t - 1, by omega⟩ : Fin (n + 2)) (by omega)
            have hrightGap : t - 2 + 2 < n + 2 := by
              rw [Nat.sub_add_cancel htTwoLe]
              exact htBound
            have hrightGood := b.good
              (⟨t - 2, by omega⟩ : Fin (n + 2)) hrightGap
            have hleftGood' :
                b.order ⟨t - 1, by omega⟩ ≤
                  b.order ⟨t + 1, by omega⟩ := by
              have hindex :
                  (⟨(⟨t - 1, by omega⟩ : Fin (n + 2)).val + 2,
                    by omega⟩ : Fin (n + 2)) = ⟨t + 1, by omega⟩ := by
                apply Fin.ext
                simp only
                omega
              rw [hindex] at hleftGood
              exact hleftGood
            have hrightGood' :
                b.order ⟨t - 2, by omega⟩ ≤
                  b.order ⟨t, by omega⟩ := by
              have hindex :
                  (⟨(⟨t - 2, by omega⟩ : Fin (n + 2)).val + 2,
                    by omega⟩ : Fin (n + 2)) = ⟨t, by omega⟩ := by
                apply Fin.ext
                simp only
                omega
              rw [hindex] at hrightGood
              exact hrightGood
            have hleftShift :
                ((b.order p.succ - b.order previous.castSucc : Int) : ℚ) ≤
                  coefficient := by
              have hpSucc : p.succ =
                  (⟨t, by omega⟩ : Fin (n + 2)) := by
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
              have hgoodQ :
                  (b.order ⟨t - 1, by omega⟩ : ℚ) ≤
                    b.order ⟨t + 1, by omega⟩ := by
                exact_mod_cast hleftGood'
              linarith
            have hrightShift :
                ((b.order next.succ - b.order p.castSucc : Int) : ℚ) ≤
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
              have hgoodQ :
                  (b.order ⟨t - 2, by omega⟩ : ℚ) ≤
                    b.order ⟨t, by omega⟩ := by
                exact_mod_cast hrightGood'
              linarith
            have hleftRaw := b.alpha_le_order_sub_add_cappedAdjacent
              (i := p) (j := previous) (by
                change previous.val ≤ p.val
                simp only [previous, p]
                omega)
            have hleftBound : (b.alphaValue p : WithTop ℚ) ≤
                (coefficient : WithTop ℚ) + leftDefect := by
              have hshiftTop :
                  ((((b.order p.succ - b.order previous.castSucc : Int) : ℚ)) :
                      WithTop ℚ) ≤ coefficient := by
                exact_mod_cast hleftShift
              have hleftRaw' : (b.alphaValue p : WithTop ℚ) ≤
                  ((((b.order p.succ - b.order previous.castSucc : Int) : ℚ)) :
                      WithTop ℚ) + leftDefect := by
                simpa only [previous, leftDefect,
                  show t - 2 + 2 = t by omega] using hleftRaw
              exact hleftRaw'.trans (by
                simpa only [add_comm] using
                  add_le_add_right hshiftTop leftDefect)
            have hrightRaw := b.alpha_le_laterOrder_sub_add_cappedAdjacent
              (i := p) (j := next) (by
                change p.val ≤ next.val
                simp only [p, next]
                omega)
            have hrightBound : (b.alphaValue p : WithTop ℚ) ≤
                (coefficient : WithTop ℚ) + rightDefect := by
              have hshiftTop :
                  ((((b.order next.succ - b.order p.castSucc : Int) : ℚ)) :
                      WithTop ℚ) ≤ coefficient := by
                exact_mod_cast hrightShift
              have hrightRaw' : (b.alphaValue p : WithTop ℚ) ≤
                  ((((b.order next.succ - b.order p.castSucc : Int) : ℚ)) :
                      WithTop ℚ) + rightDefect := by
                simpa only [next, rightDefect] using hrightRaw
              exact hrightRaw'.trans (by
                simpa only [add_comm] using
                  add_le_add_right hshiftTop rightDefect)
            have hdiagonalBound : (b.alphaValue p : WithTop ℚ) ≤
                (coefficient : WithTop ℚ) + diagonalDefect := by
              by_cases hfullIndex : t + 2 = n + 2
              · have htop : diagonalDefect = ⊤ := by
                  dsimp only [diagonalDefect]
                  simpa only [hfullIndex] using
                    a.truncatedPrefixDefect_full_eq_top b
                rw [htop]
                simp
              · have htTwoBound : t + 2 < n + 2 := by omega
                let laterIdx : RepresentationIndex (n + 2) (n + 2) :=
                  ⟨t + 2, by omega, htTwoBound, by omega⟩
                let laterAlpha : Fin (n + 1) := ⟨t + 1, by omega⟩
                have hmeasure : n + 2 - (t + 2) < d := by omega
                have hlater := ih (n + 2 - (t + 2)) hmeasure
                  (t + 2) rfl (by omega) htTwoBound
                  (fun k hk hkn ↦ hsuffix k (by omega) hkn)
                have hlaterEq : a.representationAlpha b laterIdx =
                    (b.alphaValue laterAlpha : WithTop ℚ) := by
                  have halphaIndex :
                      (⟨t + 2 - 1, by omega⟩ : Fin (n + 1)) =
                        laterAlpha := by
                    apply Fin.ext
                    simp only [laterAlpha]
                    omega
                  simpa only [laterIdx, halphaIndex] using hlater
                have hdiag : (b.alphaValue laterAlpha : WithTop ℚ) ≤
                    diagonalDefect := by
                  calc
                    (b.alphaValue laterAlpha : WithTop ℚ) =
                        a.representationAlpha b laterIdx := hlaterEq.symm
                    _ = (a.representationAlphaValue b laterIdx :
                        WithTop ℚ) :=
                      (a.coe_representationAlphaValue b laterIdx).symm
                    _ ≤ a.truncatedPrefixDefect b 1
                        laterIdx.val laterIdx.val := hdefect laterIdx
                    _ = diagonalDefect := rfl
                have hendpoint := b.alphaLeftEndpoint_monotone
                  (show p ≤ laterAlpha by
                    change p.val ≤ laterAlpha.val
                    simp only [p, laterAlpha]
                    omega)
                have hshift : b.alphaValue p ≤
                    coefficient + b.alphaValue laterAlpha := by
                  unfold alphaLeftEndpoint at hendpoint
                  have hpCast : p.castSucc =
                      (⟨t - 1, by omega⟩ : Fin (n + 2)) := by
                    apply Fin.ext
                    rfl
                  have hlaterCast : laterAlpha.castSucc =
                      (⟨t + 1, by omega⟩ : Fin (n + 2)) := by
                    apply Fin.ext
                    rfl
                  rw [hpCast, hlaterCast] at hendpoint
                  dsimp only [coefficient]
                  push_cast at hendpoint ⊢
                  have hgoodQ :
                      (b.order ⟨t - 2, by omega⟩ : ℚ) ≤
                        b.order ⟨t, by omega⟩ := by
                    exact_mod_cast hrightGood'
                  linarith
                calc
                  (b.alphaValue p : WithTop ℚ) ≤
                      (coefficient : WithTop ℚ) +
                        (b.alphaValue laterAlpha : WithTop ℚ) := by
                    exact_mod_cast hshift
                  _ ≤ (coefficient : WithTop ℚ) + diagonalDefect := by
                    simpa only [add_comm] using
                      add_le_add_right hdiag (coefficient : WithTop ℚ)
            have hfirstDom := a.truncatedPrefixDefect_domination b b
              1 (-1) (t + 2) (t + 2) t
            have hfirst : min diagonalDefect rightDefect ≤ middleDefect := by
              dsimp only [diagonalDefect, rightDefect, middleDefect]
              rw [← b.truncatedPrefixDefect_comm b (-1) (t + 2) t]
              simpa only [one_mul] using hfirstDom
            have hsecondDom := a.truncatedPrefixDefect_domination b b
              (-1) (-1) (t + 2) t (t - 2)
            have hsecond : min middleDefect leftDefect ≤ crossDefect := by
              dsimp only [middleDefect, leftDefect, crossDefect]
              rw [← b.truncatedPrefixDefect_comm b (-1) t (t - 2)]
              simpa only [neg_mul, one_mul, neg_neg] using hsecondDom
            have hnested : min (min diagonalDefect rightDefect)
                leftDefect ≤ crossDefect :=
              (min_le_min_right leftDefect hfirst).trans hsecond
            have hminimum : (b.alphaValue p : WithTop ℚ) ≤
                (coefficient : WithTop ℚ) +
                  min (min diagonalDefect rightDefect) leftDefect :=
              withTop_le_shift_add_min _ coefficient _ _
                (withTop_le_shift_add_min _ coefficient _ _
                  hdiagonalBound hrightBound) hleftBound
            have hcrossBound : (b.alphaValue p : WithTop ℚ) ≤
                (coefficient : WithTop ℚ) + crossDefect :=
              hminimum.trans (by
                simpa only [add_comm] using
                  add_le_add_right hnested (coefficient : WithTop ℚ))
            unfold representationSecondaryDefect
            have hsourceCurrent' :
                a.order ⟨idx.val, idx.lt_large⟩ =
                  b.order ⟨t, by omega⟩ := by
              exact hsourceCurrent.trans (by
                apply congrArg b.order
                apply Fin.ext
                simp only [p, Fin.val_succ]
                omega)
            have hsourceAfter :
                a.order ⟨idx.val + 1, hinterior.2⟩ =
                  b.order ⟨t + 1, by omega⟩ := by
              have heq := hsuffix (t + 1) (by omega) (by omega)
              let af : Fin (n + 2) := ⟨t + 1, by omega⟩
              let bf : Fin (n + 2) := ⟨t + 1, by omega⟩
              rw [a.orderSequence_entryOrZero_eq_order af,
                b.orderSequence_entryOrZero_eq_order bf] at heq
              have haIndex :
                  a.order ⟨idx.val + 1, hinterior.2⟩ = a.order af := by
                apply congrArg a.order
                apply Fin.ext
                simp only [af, idx]
              exact haIndex.trans heq
            have htargetPrevious' :
                b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ =
                  b.order ⟨t - 2, by omega⟩ := by
              apply congrArg b.order
              apply Fin.ext
              simp only [idx]
            have htargetCurrent' :
                b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
                  b.order ⟨t - 1, by omega⟩ := by
              apply congrArg b.order
              apply Fin.ext
              simp only [idx]
            rw [hsourceCurrent', hsourceAfter, htargetPrevious',
              htargetCurrent']
            simpa only [idx, coefficient, crossDefect] using hcrossBound
          · rw [a.representationAlphaPrime_eq_primary_of_not_interior
              b idx hinterior]
            exact hprimary
        exact le_antisymm hupper hlower
  simpa only using hmain (n + 2 - i.val) i.val rfl i.pos
    i.lt_large horders

/-- Rational-valued right-end statement. -/
theorem beli2019Lemma63_sameRank_right_value
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (horders : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b i]
  exact a.beli2019Lemma63_sameRank_right b hdefect i horders

end BONG.GoodBONG

end Bong
