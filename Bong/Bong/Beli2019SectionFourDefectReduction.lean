/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma213Nonessential

/-!
# Beli (2019), Section 4: closing the defect-reduction branches

This file combines Lemmas 2.11 and 2.13 with condition 2.1(i).  It proves the
order comparisons used in the two fallback cases of the proof of condition
2.1(ii), rather than retaining them as fields of a local-law parameter.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- The reduction object in the proof of Section 4, condition 2.1(ii).
The nonessential case is Lemma 2.13.  In each essential fallback, the two
source order conditions turn the failed strict branch of Lemma 4.2 into the
two order hypotheses of Lemma 2.11. -/
theorem sectionFourDefectReduction
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl) :
    SectionFourDefectReduction a b c where
  nonessential j hcurrent hnext :=
    a.representationDefectAt_of_not_essential
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      c j hcurrent hnext
  currentFallback j hprev hcurrent hdirect := by
    have hfailureRaw := hdirect
    unfold KeyLemmaRightDirectTrigger at hfailureRaw
    push Not at hfailureRaw
    rcases hfailureRaw with ⟨hiPos, hiTwo, hfailureRaw⟩
    have hiNext : j.val + 1 < n + 1 := by
      have hindex := currentEssentialIndex_val j
      omega
    have hsourceCurrent :
        (⟨(currentEssentialIndex j).val + 1, by omega⟩ : Fin (n + 1)) =
          ⟨j.val, j.lt_large⟩ := by
      apply Fin.ext
      simp only [currentEssentialIndex]
      omega
    have hsourceNext :
        (⟨(currentEssentialIndex j).val + 2, by omega⟩ : Fin (n + 1)) =
          ⟨j.val + 1, by omega⟩ := by
      apply Fin.ext
      simp only [currentEssentialIndex]
      omega
    have hmiddleCurrent :
        (⟨(currentEssentialIndex j).val, by omega⟩ : Fin (n + 1)) =
          ⟨j.val - 1, by omega⟩ := by
      apply Fin.ext
      rfl
    have htargetPrevious :
        (⟨(currentEssentialIndex j).val - 1, by omega⟩ : Fin (n + 1)) =
          ⟨j.val - 2, by omega⟩ := by
      apply Fin.ext
      simp only [currentEssentialIndex]
      omega
    rw [hsourceCurrent, hsourceNext, hmiddleCurrent,
      htargetPrevious] at hfailureRaw
    have hfailure :
        a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hiNext⟩ ≤
          b.order ⟨j.val - 1, by omega⟩ +
            c.order ⟨j.val - 2, by omega⟩ := hfailureRaw
    unfold IsCurrentEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hcurrent
    have hessentialRaw := hcurrent.1 (by
      simp only [currentEssentialIndex]
      omega) (by
      simp only [currentEssentialIndex]
      omega)
    simp only [orderSequence_at] at hessentialRaw
    rw [htargetPrevious, hsourceCurrent] at hessentialRaw
    have hessential : c.order ⟨j.val - 2, by omega⟩ <
        a.order ⟨j.val, j.lt_large⟩ := hessentialRaw
    have hpair :
        a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hiNext⟩ ≤
          c.order ⟨j.val - 2, by omega⟩ +
            c.order ⟨j.val - 1, by omega⟩ := by
      by_contra hnot
      have htargetLt :
          c.order ⟨j.val - 2, by omega⟩ +
              c.order ⟨j.val - 1, by omega⟩ <
            a.order ⟨j.val, j.lt_large⟩ +
              a.order ⟨j.val + 1, hiNext⟩ := lt_of_not_ge hnot
      have hmiddleGt : c.order ⟨j.val - 1, by omega⟩ <
          b.order ⟨j.val - 1, by omega⟩ := by
        omega
      rcases hbc ⟨j.val - 1, by omega⟩ with hcurrentBC |
          ⟨_, _, hpairBCRaw⟩
      · exact (not_lt_of_ge hcurrentBC hmiddleGt).elim
      · have hpairBC :
            b.order ⟨j.val - 1, by omega⟩ +
                b.order ⟨j.val, j.lt_large⟩ ≤
              c.order ⟨j.val - 2, by omega⟩ +
                c.order ⟨j.val - 1, by omega⟩ := by
            simpa only [Nat.sub_sub,
              Nat.sub_add_cancel (show 1 ≤ j.val by omega)] using hpairBCRaw
        have hmiddlePairLt :
            b.order ⟨j.val - 1, by omega⟩ +
                b.order ⟨j.val, j.lt_large⟩ <
              a.order ⟨j.val, j.lt_large⟩ +
                a.order ⟨j.val + 1, hiNext⟩ :=
          hpairBC.trans_lt htargetLt
        have hnextGt : b.order ⟨j.val - 1, by omega⟩ <
            a.order ⟨j.val + 1, hiNext⟩ := by
          rcases hab ⟨j.val, j.lt_large⟩ with hcurrentAB |
              ⟨_, _, hpairABRaw⟩
          · have hcurrentAB' : a.order ⟨j.val, j.lt_large⟩ ≤
                b.order ⟨j.val, j.lt_large⟩ := by
              simpa using hcurrentAB
            omega
          · have hpairAB :
                a.order ⟨j.val, j.lt_large⟩ +
                    a.order ⟨j.val + 1, hiNext⟩ ≤
                  b.order ⟨j.val - 1, by omega⟩ +
                    b.order ⟨j.val, j.lt_large⟩ := by
              simpa using hpairABRaw
            exact (not_lt_of_ge hpairAB hmiddlePairLt).elim
        omega
    have hright : a.order ⟨j.val + 1, hiNext⟩ ≤
        c.order ⟨j.val - 1, by omega⟩ := by
      omega
    constructor
    · exact a.le_currentFallbackAlphaBound_of_representationDefectAt
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        c j hprev hiNext hpair hright
    · exact a.representationDefectAt_of_le_currentFallbackAlphaBound
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        c j hprev hiNext hpair hright
  nextFallback j hnext hessential hdirect := by
    have hfailureRaw := hdirect
    unfold KeyLemmaLeftDirectTrigger at hfailureRaw
    push Not at hfailureRaw
    rcases hfailureRaw with ⟨hiTwo, _, hfailureRaw⟩
    have hfailure :
        a.order ⟨j.val + 1, hnext⟩ + b.order ⟨j.val, j.lt_large⟩ ≤
          c.order ⟨j.val - 2, by omega⟩ +
            c.order ⟨j.val - 1, by omega⟩ := by
      simpa only [nextEssentialIndex] using hfailureRaw
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    have hessentialRaw := hessential.1 j.pos hnext
    have hcross : c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hnext⟩ := by
      simpa only [orderSequence_at, nextEssentialIndex] using hessentialRaw
    have hpair :
        a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hnext⟩ ≤
          c.order ⟨j.val - 2, by omega⟩ +
            c.order ⟨j.val - 1, by omega⟩ := by
      by_contra hnot
      have htargetLt :
          c.order ⟨j.val - 2, by omega⟩ +
              c.order ⟨j.val - 1, by omega⟩ <
            a.order ⟨j.val, j.lt_large⟩ +
              a.order ⟨j.val + 1, hnext⟩ := lt_of_not_ge hnot
      have hmiddleLt : b.order ⟨j.val, j.lt_large⟩ <
          a.order ⟨j.val, j.lt_large⟩ := by
        omega
      rcases hab ⟨j.val, j.lt_large⟩ with hcurrentAB |
          ⟨_, _, hpairABRaw⟩
      · have hcurrentAB' : a.order ⟨j.val, j.lt_large⟩ ≤
            b.order ⟨j.val, j.lt_large⟩ := by
          simpa using hcurrentAB
        exact (not_lt_of_ge hcurrentAB' hmiddleLt).elim
      · have hpairAB :
            a.order ⟨j.val, j.lt_large⟩ +
                a.order ⟨j.val + 1, hnext⟩ ≤
              b.order ⟨j.val - 1, by omega⟩ +
                b.order ⟨j.val, j.lt_large⟩ := by
          simpa using hpairABRaw
        have hmiddlePairLt :
            c.order ⟨j.val - 2, by omega⟩ +
                c.order ⟨j.val - 1, by omega⟩ <
              b.order ⟨j.val - 1, by omega⟩ +
                b.order ⟨j.val, j.lt_large⟩ :=
          htargetLt.trans_le hpairAB
        have hpreviousLt : c.order ⟨j.val - 2, by omega⟩ <
            b.order ⟨j.val, j.lt_large⟩ := by
          rcases hbc ⟨j.val - 1, by omega⟩ with hcurrentBC |
              ⟨_, _, hpairBCRaw⟩
          · have hcurrentBC' : b.order ⟨j.val - 1, by omega⟩ ≤
                c.order ⟨j.val - 1, by omega⟩ := by
              simpa using hcurrentBC
            omega
          · have hpairBC :
                b.order ⟨j.val - 1, by omega⟩ +
                    b.order ⟨j.val, j.lt_large⟩ ≤
                  c.order ⟨j.val - 2, by omega⟩ +
                    c.order ⟨j.val - 1, by omega⟩ := by
                have hmiddleNext :
                    (⟨j.val - 1 + 1, by omega⟩ : Fin (n + 1)) =
                      ⟨j.val, j.lt_large⟩ := by
                  apply Fin.ext
                  change j.val - 1 + 1 = j.val
                  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr j.pos)
                have htargetPrev :
                    (⟨j.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
                      ⟨j.val - 2, by omega⟩ := by
                  apply Fin.ext
                  change j.val - 1 - 1 = j.val - 2
                  exact Nat.sub_sub j.val 1 1
                rw [hmiddleNext, htargetPrev] at hpairBCRaw
                exact hpairBCRaw
            exact (not_lt_of_ge hpairBC hmiddlePairLt).elim
        omega
    have hleft : a.order ⟨j.val, j.lt_large⟩ ≤
        c.order ⟨j.val - 2, by omega⟩ := by
      omega
    constructor
    · exact a.le_nextFallbackAlphaBound_of_representationDefectAt
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        c j hiTwo hnext hpair hleft
    · exact a.representationDefectAt_of_le_nextFallbackAlphaBound
        (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        c j hiTwo hnext hpair hleft

end BONG.GoodBONG

end Bong
