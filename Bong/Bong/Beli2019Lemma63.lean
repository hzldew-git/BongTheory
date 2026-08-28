/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightSecondary
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm

/-!
# Beli (2019), Lemma 6.3: prefix rigidity of the representation alpha

For two same-rank good BONGs satisfying condition 2.1(ii), agreement of all
orders through a boundary forces the representation invariant at that
boundary to equal the source alpha.  The proof follows Beli's induction:
the diagonal defect at each earlier boundary and the adjacent capped defects
dominate every candidate defining the next representation alpha.
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

set_option maxHeartbeats 1000000 in
-- The strong induction elaborates many proof-dependent `Fin` transports.
/-- Same-rank form of Beli (2019), Lemma 6.3.  The zero-based hypothesis
`k < i.val` is exactly the paper's `R_j = S_j` for `1 ≤ j ≤ i`. -/
theorem beli2019Lemma63_sameRank
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (horders : ∀ k, k < i.val →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hmain : ∀ (t : Nat) (htPos : 0 < t) (htBound : t < n + 2)
      (hagree : ∀ k, k < t → a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k),
      a.representationAlpha b
          (⟨t, htPos, htBound, by omega⟩ :
            RepresentationIndex (n + 2) (n + 2)) =
        (a.alphaValue ⟨t - 1, by omega⟩ : WithTop ℚ) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro htPos htBound hagree
        let idx : RepresentationIndex (n + 2) (n + 2) :=
          ⟨t, htPos, htBound, by omega⟩
        let p : Fin (n + 1) := ⟨t - 1, by omega⟩
        have hidxVal : idx.val = t := rfl
        have hpVal : p.val = t - 1 := rfl
        have hsourceNext :
            a.order ⟨idx.val, idx.lt_large⟩ = a.order p.succ := by
          apply congrArg a.order
          apply Fin.ext
          simp only [idx, p, Fin.val_succ]
          omega
        have htargetCurrent :
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
              a.order p.castSucc := by
          have heq := hagree (t - 1) (by omega)
          let af : Fin (n + 2) := ⟨t - 1, by omega⟩
          let bf : Fin (n + 2) := ⟨t - 1, by omega⟩
          rw [a.orderSequence_entryOrZero_eq_order af,
            b.orderSequence_entryOrZero_eq_order bf] at heq
          have haIndex :
              a.order ⟨t - 1, by omega⟩ = a.order p.castSucc := by
            apply congrArg a.order
            apply Fin.ext
            rfl
          have hbIndex :
              b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
                b.order ⟨t - 1, by omega⟩ := by
            apply congrArg b.order
            apply Fin.ext
            exact congrArg (fun x ↦ x - 1) hidxVal
          exact hbIndex.trans (heq.symm.trans haIndex)
        have hhalf : a.representationHalfGap b idx =
            a.halfGapCandidate p := by
          unfold representationHalfGap halfGapCandidate
          rw [hsourceNext, htargetCurrent]
        have hupper : a.representationAlpha b idx ≤
            (a.alphaValue p : WithTop ℚ) := by
          calc
            a.representationAlpha b idx =
                (a.representationAlphaValue b idx : WithTop ℚ) :=
              (a.coe_representationAlphaValue b idx).symm
            _ ≤ a.truncatedPrefixDefect b 1 idx.val idx.val :=
              hdefect idx
            _ ≤ a.prefixAlphaCap idx.val :=
              a.truncatedPrefixDefect_le_leftCap b 1 idx.val idx.val
            _ = (a.alphaValue p : WithTop ℚ) := by
              rw [a.prefixAlphaCap_of_internal idx.pos idx.lt_large]
        have hhalfLower : (a.alphaValue p : WithTop ℚ) ≤
            a.representationHalfGap b idx := by
          rw [hhalf, a.coe_alphaValue p]
          exact a.alpha_le_halfGapCandidate p
        have hprimary : (a.alphaValue p : WithTop ℚ) ≤
            a.representationPrimaryDefect b idx := by
          by_cases htOne : t = 1
          · have hlocal := a.alpha_le_orderGap_add_cappedAdjacent p
            have hcross :
                a.truncatedPrefixDefect b (-1) (t + 1) (t - 1) =
                  a.truncatedPrefixDefect a (-1) p.val (p.val + 2) := by
              have htSub : t - 1 = 0 := by omega
              have htAdd : t + 1 = 2 := by omega
              have hpZero : p.val = 0 := by
                simp only [p]
                omega
              unfold truncatedPrefixDefect
              rw [htSub, htAdd, hpZero]
              norm_num only [zero_add]
              rw [a.prefixAlphaCap_zero, b.prefixAlphaCap_zero]
              simp [BONG.GoodBONG.prefixProduct]
            unfold representationPrimaryDefect
            rw [hsourceNext, htargetCurrent, hidxVal, hcross]
            simpa only [p, Fin.val_succ, Fin.val_castSucc] using hlocal
          · have htTwo : 2 ≤ t := by omega
            let previousIdx : RepresentationIndex (n + 2) (n + 2) :=
              ⟨t - 1, by omega, by omega, by omega⟩
            let previousAlpha : Fin (n + 1) := ⟨t - 2, by omega⟩
            have hprevious := ih (t - 1) (by omega) (by omega)
              (by omega) (fun k hk ↦ hagree k (by omega))
            have hpreviousEq :
                a.representationAlpha b previousIdx =
                  (a.alphaValue previousAlpha : WithTop ℚ) := by
              have halphaIndex :
                  (⟨t - 1 - 1, by omega⟩ : Fin (n + 1)) =
                    previousAlpha := by
                apply Fin.ext
                simp only [previousAlpha]
                omega
              simpa only [previousIdx, halphaIndex] using hprevious
            have hdiagonal : (a.alphaValue previousAlpha : WithTop ℚ) ≤
                a.truncatedPrefixDefect b 1 (t - 1) (t - 1) := by
              calc
                (a.alphaValue previousAlpha : WithTop ℚ) =
                    a.representationAlpha b previousIdx := hpreviousEq.symm
                _ = (a.representationAlphaValue b previousIdx : WithTop ℚ) :=
                  (a.coe_representationAlphaValue b previousIdx).symm
                _ ≤ a.truncatedPrefixDefect b 1
                    previousIdx.val previousIdx.val := hdefect previousIdx
                _ = a.truncatedPrefixDefect b 1 (t - 1) (t - 1) := rfl
            let shift : ℚ :=
              ((a.order p.succ - a.order p.castSucc : Int) : ℚ)
            have hendpoint := a.alphaRightEndpoint_antitone
              (show previousAlpha ≤ p by
                change previousAlpha.val ≤ p.val
                simp only [previousAlpha, p]
                omega)
            have hpreviousShift : a.alphaValue p ≤
                shift + a.alphaValue previousAlpha := by
              unfold alphaRightEndpoint at hendpoint
              have hprevSucc : previousAlpha.succ = p.castSucc := by
                apply Fin.ext
                simp only [previousAlpha, p, Fin.val_succ, Fin.val_castSucc]
                omega
              rw [hprevSucc] at hendpoint
              dsimp only [shift]
              push_cast
              linarith
            have hpreviousBound : (a.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) +
                  a.truncatedPrefixDefect b 1 (t - 1) (t - 1) := by
              calc
                (a.alphaValue p : WithTop ℚ) ≤
                    (shift : WithTop ℚ) +
                      (a.alphaValue previousAlpha : WithTop ℚ) := by
                  exact_mod_cast hpreviousShift
                _ ≤ (shift : WithTop ℚ) +
                    a.truncatedPrefixDefect b 1 (t - 1) (t - 1) := by
                  simpa only [add_comm] using
                    add_le_add_right hdiagonal (shift : WithTop ℚ)
            have hlocal := a.alpha_le_orderGap_add_cappedAdjacent p
            have hlocal' : (a.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) +
                  a.truncatedPrefixDefect a (-1) (t + 1) (t - 1) := by
              rw [a.truncatedPrefixDefect_comm a (-1) (t + 1) (t - 1)]
              simpa only [shift, p, Fin.val_succ, Fin.val_castSucc,
                show t - 1 + 2 = t + 1 by omega] using hlocal
            have hdom := a.truncatedPrefixDefect_domination a b
              (-1) 1 (t + 1) (t - 1) (t - 1)
            have hdom' : min
                (a.truncatedPrefixDefect a (-1) (t + 1) (t - 1))
                (a.truncatedPrefixDefect b 1 (t - 1) (t - 1)) ≤
                  a.truncatedPrefixDefect b (-1) (t + 1) (t - 1) := by
              simpa only [mul_one] using hdom
            have hminimum : (a.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) + min
                  (a.truncatedPrefixDefect a (-1) (t + 1) (t - 1))
                  (a.truncatedPrefixDefect b 1 (t - 1) (t - 1)) :=
              withTop_le_shift_add_min _ shift _ _ hlocal' hpreviousBound
            have hcrossBound : (a.alphaValue p : WithTop ℚ) ≤
                (shift : WithTop ℚ) +
                  a.truncatedPrefixDefect b (-1) (t + 1) (t - 1) :=
              hminimum.trans (by
                simpa only [add_comm] using
                  add_le_add_right hdom' (shift : WithTop ℚ))
            unfold representationPrimaryDefect
            rw [hsourceNext, htargetCurrent, hidxVal]
            simpa only [shift] using hcrossBound
        have hlower : (a.alphaValue p : WithTop ℚ) ≤
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
              ((a.order ⟨t, by omega⟩ + a.order ⟨t + 1, by omega⟩ -
                a.order ⟨t - 2, by omega⟩ -
                a.order ⟨t - 1, by omega⟩ : Int) : ℚ)
            let leftDefect :=
              a.truncatedPrefixDefect a (-1) (t - 2) t
            let rightDefect :=
              a.truncatedPrefixDefect a (-1) t (t + 2)
            let diagonalDefect :=
              a.truncatedPrefixDefect b 1 (t - 2) (t - 2)
            let middleDefect :=
              a.truncatedPrefixDefect b (-1) t (t - 2)
            let crossDefect :=
              a.truncatedPrefixDefect b 1 (t + 2) (t - 2)
            have htTwoLe : 2 ≤ t := by omega
            have hleftGood := a.good
              (⟨t - 1, by omega⟩ : Fin (n + 2)) (by omega)
            have hrightGap : t - 2 + 2 < n + 2 := by
              rw [Nat.sub_add_cancel htTwoLe]
              exact htBound
            have hrightGood := a.good
              (⟨t - 2, by omega⟩ : Fin (n + 2)) hrightGap
            have hleftGood' :
                a.order ⟨t - 1, by omega⟩ ≤
                  a.order ⟨t + 1, by omega⟩ := by
              have hindex :
                  (⟨(⟨t - 1, by omega⟩ : Fin (n + 2)).val + 2,
                    by omega⟩ : Fin (n + 2)) = ⟨t + 1, by omega⟩ := by
                apply Fin.ext
                simp only
                omega
              rw [hindex] at hleftGood
              exact hleftGood
            have hrightGood' :
                a.order ⟨t - 2, by omega⟩ ≤
                  a.order ⟨t, by omega⟩ := by
              have hindex :
                  (⟨(⟨t - 2, by omega⟩ : Fin (n + 2)).val + 2,
                    by omega⟩ : Fin (n + 2)) = ⟨t, by omega⟩ := by
                apply Fin.ext
                simp only
                omega
              rw [hindex] at hrightGood
              exact hrightGood
            have hleftShift :
                ((a.order p.succ - a.order previous.castSucc : Int) : ℚ) ≤
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
                  (a.order ⟨t - 1, by omega⟩ : ℚ) ≤
                    a.order ⟨t + 1, by omega⟩ := by
                exact_mod_cast hleftGood'
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
              have hgoodQ :
                  (a.order ⟨t - 2, by omega⟩ : ℚ) ≤
                    a.order ⟨t, by omega⟩ := by
                exact_mod_cast hrightGood'
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
                      WithTop ℚ) ≤ coefficient := by
                exact_mod_cast hleftShift
              have hleftRaw' : (a.alphaValue p : WithTop ℚ) ≤
                  ((((a.order p.succ - a.order previous.castSucc : Int) : ℚ)) :
                      WithTop ℚ) + leftDefect := by
                simpa only [previous, leftDefect,
                  show t - 2 + 2 = t by omega] using hleftRaw
              exact hleftRaw'.trans (by
                simpa only [add_comm] using
                  add_le_add_right hshiftTop leftDefect)
            have hrightRaw := a.alpha_le_laterOrder_sub_add_cappedAdjacent
              (i := p) (j := next) (by
                change p.val ≤ next.val
                simp only [p, next]
                omega)
            have hrightBound : (a.alphaValue p : WithTop ℚ) ≤
                (coefficient : WithTop ℚ) + rightDefect := by
              have hshiftTop :
                  ((((a.order next.succ - a.order p.castSucc : Int) : ℚ)) :
                      WithTop ℚ) ≤ coefficient := by
                exact_mod_cast hrightShift
              have hrightRaw' : (a.alphaValue p : WithTop ℚ) ≤
                  ((((a.order next.succ - a.order p.castSucc : Int) : ℚ)) :
                      WithTop ℚ) + rightDefect := by
                simpa only [next, rightDefect] using hrightRaw
              exact hrightRaw'.trans (by
                simpa only [add_comm] using
                  add_le_add_right hshiftTop rightDefect)
            have hdiagonalBound : (a.alphaValue p : WithTop ℚ) ≤
                (coefficient : WithTop ℚ) + diagonalDefect := by
              by_cases htTwo : t = 2
              · have htop : diagonalDefect = ⊤ := by
                  have htSub : t - 2 = 0 := by omega
                  dsimp only [diagonalDefect]
                  unfold truncatedPrefixDefect
                  rw [htSub, a.prefixAlphaCap_zero, b.prefixAlphaCap_zero]
                  simp [BONG.GoodBONG.prefixProduct, defectOrder_one]
                rw [htop]
                simp
              · let previousTwo : Fin (n + 1) := ⟨t - 3, by omega⟩
                let earlierIdx : RepresentationIndex (n + 2) (n + 2) :=
                  ⟨t - 2, by omega, by omega, by omega⟩
                have hearlier := ih (t - 2) (by omega) (by omega)
                  (by omega) (fun k hk ↦ hagree k (by omega))
                have hearlierEq :
                    a.representationAlpha b earlierIdx =
                      (a.alphaValue previousTwo : WithTop ℚ) := by
                  have halphaIndex :
                      (⟨t - 2 - 1, by omega⟩ : Fin (n + 1)) =
                        previousTwo := by
                    apply Fin.ext
                    simp only [previousTwo]
                    omega
                  simpa only [earlierIdx, halphaIndex] using hearlier
                have hdiag : (a.alphaValue previousTwo : WithTop ℚ) ≤
                    diagonalDefect := by
                  calc
                    (a.alphaValue previousTwo : WithTop ℚ) =
                        a.representationAlpha b earlierIdx := hearlierEq.symm
                    _ = (a.representationAlphaValue b earlierIdx :
                        WithTop ℚ) :=
                      (a.coe_representationAlphaValue b earlierIdx).symm
                    _ ≤ a.truncatedPrefixDefect b 1
                        earlierIdx.val earlierIdx.val := hdefect earlierIdx
                    _ = diagonalDefect := rfl
                have hendpoint := a.alphaRightEndpoint_antitone
                  (show previousTwo ≤ p by
                    change previousTwo.val ≤ p.val
                    simp only [previousTwo, p]
                    omega)
                have hshift : a.alphaValue p ≤
                    coefficient + a.alphaValue previousTwo := by
                  unfold alphaRightEndpoint at hendpoint
                  have hpSucc : p.succ =
                      (⟨t, by omega⟩ : Fin (n + 2)) := by
                    apply Fin.ext
                    simp only [p, Fin.val_succ]
                    omega
                  have hpreviousSucc : previousTwo.succ =
                      (⟨t - 2, by omega⟩ : Fin (n + 2)) := by
                    apply Fin.ext
                    simp only [previousTwo, Fin.val_succ]
                    omega
                  rw [hpSucc, hpreviousSucc] at hendpoint
                  dsimp only [coefficient]
                  push_cast at hendpoint ⊢
                  have hgoodQ :
                      (a.order ⟨t - 1, by omega⟩ : ℚ) ≤
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
            have hfirst : min leftDefect diagonalDefect ≤ middleDefect := by
              dsimp only [leftDefect, diagonalDefect, middleDefect]
              rw [← a.truncatedPrefixDefect_comm a (-1) t (t - 2)]
              simpa only [mul_one] using hfirstDom
            have hsecondDom := a.truncatedPrefixDefect_domination a b
              (-1) (-1) (t + 2) t (t - 2)
            have hsecond : min rightDefect middleDefect ≤ crossDefect := by
              dsimp only [rightDefect, middleDefect, crossDefect]
              rw [← a.truncatedPrefixDefect_comm a (-1) (t + 2) t]
              simpa only [neg_mul, one_mul, neg_neg] using hsecondDom
            have hnested : min rightDefect
                (min leftDefect diagonalDefect) ≤ crossDefect :=
              (min_le_min_left rightDefect hfirst).trans hsecond
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
            have htargetPrevious :
                b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ =
                  a.order ⟨t - 2, by omega⟩ := by
              have heq := hagree (t - 2) (by omega)
              let af : Fin (n + 2) := ⟨t - 2, by omega⟩
              let bf : Fin (n + 2) := ⟨t - 2, by omega⟩
              rw [a.orderSequence_entryOrZero_eq_order af,
                b.orderSequence_entryOrZero_eq_order bf] at heq
              have hbIndex :
                  b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ =
                    b.order bf := by
                apply congrArg b.order
                apply Fin.ext
                simp only [bf, idx]
              exact hbIndex.trans heq.symm
            have hsourceCurrent :
                a.order ⟨idx.val, idx.lt_large⟩ =
                  a.order ⟨t, by omega⟩ := by
              apply congrArg a.order
              apply Fin.ext
              exact hidxVal
            have hsourceAfter :
                a.order ⟨idx.val + 1, hinterior.2⟩ =
                  a.order ⟨t + 1, by omega⟩ := by
              apply congrArg a.order
              apply Fin.ext
              exact congrArg (fun x ↦ x + 1) hidxVal
            have htargetCurrent' :
                b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
                  a.order ⟨t - 1, by omega⟩ := by
              exact htargetCurrent.trans (by
                apply congrArg a.order
                apply Fin.ext
                simp only [p, Fin.val_castSucc])
            rw [hsourceCurrent, hsourceAfter, htargetPrevious,
              htargetCurrent']
            simpa only [idx, coefficient, crossDefect] using hcrossBound
          · rw [a.representationAlphaPrime_eq_primary_of_not_interior
              b idx hinterior]
            exact hprimary
        exact le_antisymm hupper hlower
  simpa only using hmain i.val i.pos i.lt_large horders

/-- Rational-valued statement of Lemma 6.3. -/
theorem beli2019Lemma63_sameRank_value
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (horders : ∀ k, k < i.val →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    a.representationAlphaValue b i =
      a.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b i]
  exact a.beli2019Lemma63_sameRank b hdefect i horders

end BONG.GoodBONG

end Bong
