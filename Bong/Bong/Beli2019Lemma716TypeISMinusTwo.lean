/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeISMinusTwoGeometry
import Bong.Bong.Beli2019Lemma79TypeICaseOneAssembly
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha

/-!
# Beli (2019), Lemma 7.16(ii): the type-I boundary `i = s - 2`

This is the last boundary in condition 2.1(ii).  If the preceding even
comparison order is high, both adjacent essential indices fail and Lemma
2.13 applies.  Otherwise that order is `R + 1`.  A nonexceptional final
gap is handled by Lemma 7.4(i) and the zero source alpha in the primary
candidate.  The exceptional gap `-2e` is reduced by Corollary 2.10 to the
prefix square-class statement proved by the endpoint-tower geometry module.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- Condition 2.1(ii) at the type-I boundary with paper index `s - 2`. -/
theorem lemma716_typeI_sMinusTwo_representationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hsFour : 4 ≤ s) :
    b.RepresentationDefectAt c
      { val := s - 2
        pos := by omega
        lt_large := by have := D.le_rank; omega
        le_small := by have := D.le_rank; omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s - 2
      pos := by omega
      lt_large := by have := D.le_rank; omega
      le_small := by have := D.le_rank; omega }
  let high : Fin (n + 3) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  let low : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  let sourceCurrent : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  let sourceNext : Fin (n + 3) := ⟨s - 1, by
    have := D.le_rank
    omega⟩
  have hhighEven : Even high.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by dsimp only [high]; omega⟩
  have hhighLower : R + 1 ≤ c.order high :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm high hhighEven
  have hsourceCurrent : b.order sourceCurrent = R + 2 := by
    simpa only [sourceCurrent] using
      a.lemma716_typeI_leftBoundary_order_eq b R s D hfirst hvalues
  have hsourceNext : b.order sourceNext =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    simpa only [sourceNext] using
      a.lemma716_typeI_rightBoundary_order_eq b R s D hsecond hvalues
  let gap : Fin (n + 2) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  have hgapDef : c.orderGap gap = c.order low - c.order high := by
    unfold orderGap
    have hsucc : gap.succ = low := by
      apply Fin.ext
      simp only [gap, low, Fin.val_succ]
      omega
    have hcast : gap.castSucc = high := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  have hgapLower := c.orderGap_ge_neg_two_mul_e gap
  rw [hgapDef] at hgapLower
  by_cases hhigh : R + 2 ≤ c.order high
  · have hlowLower :
        R - 2 * (ramificationIndex K : Int) + 2 ≤ c.order low := by
      omega
    have hcurrentNot : ¬b.IsCurrentEssential c i := by
      have hcurrentPos : 0 < (currentEssentialIndex i).val := by
        simp only [currentEssentialIndex]
        dsimp only [i]
        omega
      have hcurrentNext :
          (currentEssentialIndex i).val + 1 < n + 3 := by
        simp only [currentEssentialIndex]
        dsimp only [i]
        have := D.le_rank
        omega
      apply b.not_isEssentialFor_of_next_le_previous c
        (currentEssentialIndex i) hcurrentPos hcurrentNext
      have hnextIndex :
          (⟨(currentEssentialIndex i).val + 1, hcurrentNext⟩ :
            Fin (n + 3)) = sourceCurrent := by
        apply Fin.ext
        simp only [currentEssentialIndex]
        dsimp only [i, sourceCurrent]
        omega
      have hpreviousIndex :
          (⟨(currentEssentialIndex i).val - 1, by
            have := hcurrentNext
            omega⟩ : Fin (n + 3)) = high := by
        apply Fin.ext
        simp only [currentEssentialIndex]
        dsimp only [i, high]
        omega
      rw [hnextIndex, hpreviousIndex, hsourceCurrent]
      exact hhigh
    have hnextNot : ¬b.IsNextEssential c i := by
      have hnextPos : 0 < (nextEssentialIndex i).val := by
        simp only [nextEssentialIndex]
        dsimp only [i]
        omega
      have hnextNext : (nextEssentialIndex i).val + 1 < n + 3 := by
        simp only [nextEssentialIndex]
        dsimp only [i]
        have := D.le_rank
        omega
      apply b.not_isEssentialFor_of_next_le_previous c
        (nextEssentialIndex i) hnextPos hnextNext
      have hnextIndex :
          (⟨(nextEssentialIndex i).val + 1, hnextNext⟩ :
            Fin (n + 3)) = sourceNext := by
        apply Fin.ext
        simp only [nextEssentialIndex]
        dsimp only [i, sourceNext]
        omega
      have hpreviousIndex :
          (⟨(nextEssentialIndex i).val - 1, by
            have := hnextNext
            omega⟩ : Fin (n + 3)) = low := by
        apply Fin.ext
        simp only [nextEssentialIndex]
        dsimp only [i, low]
        omega
      rw [hnextIndex, hpreviousIndex, hsourceNext]
      exact hlowLower
    simpa only [i] using
      b.representationDefectAt_of_not_essential c i hcurrentNot hnextNot
  · have hhighEq : c.order high = R + 1 := by omega
    let zero : Fin (n + 3) := 0
    have hzeroLower : R + 1 ≤ c.order zero := by
      simpa only [zero] using
        a.lemma716_comparison_order_zero_ge c R hfirst hnorm
    have hzeroHigh : c.order zero ≤ c.order high := by
      apply lemma716_order_le_of_evenGap c zero high
      · exact Fin.zero_le high
      · simpa only [zero, Fin.val_zero, Nat.sub_zero] using hhighEven
    have hzeroEq : c.order zero = R + 1 := by omega
    by_cases hnormal :
        2 - 2 * (ramificationIndex K : Int) ≤
          c.order low - c.order high
    · have hlowStrong :
          R - 2 * (ramificationIndex K : Int) + 3 ≤ c.order low := by
        rw [hhighEq] at hnormal
        omega
      have Psource := a.lemma716_typeI_sMinusTwo_sourceProfile
        b R s D hthird hvalues hsFour
      have hsMinusTwoEven : Even (s - 2) := by
        rcases D.even with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩
      have hsourceSelf :=
        b.lemma716_typeII_comparisonPrefixDefect_ge_twoE R (s - 2)
          (by omega) (by have := D.le_rank; omega) hsMinusTwoEven Psource
      have halphaNe : c.alphaValue gap ≠ 0 := by
        intro halphaZero
        have hgapZero := (c.alpha_p2 gap).2.mp halphaZero
        rw [hgapDef] at hgapZero
        omega
      have halphaOne : 1 ≤ c.alphaValue gap :=
        c.one_le_alphaValue_of_ne_zero gap halphaNe
      let first : Fin (n + 2) := ⟨0, by omega⟩
      let last : Fin (n + 2) := ⟨s - 4, by
        have := D.le_rank
        omega⟩
      have hfirstLast : first ≤ last := Fin.zero_le last
      have hsegmentEven : Even (last.val - first.val) := by
        rcases D.even with ⟨d, hd⟩
        exact ⟨d - 2, by dsimp only [last, first]; omega⟩
      have hfirstOrder : c.order first.castSucc = R + 1 := by
        have hindex : first.castSucc = zero := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hzeroEq
      have hlastOrder : c.order last.castSucc = R + 1 := by
        have hindex : last.castSucc = high := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hhighEq
      have hcomparisonRaw := c.beli2019Lemma74_i first last
        hfirstLast hsegmentEven (hfirstOrder.trans hlastOrder.symm)
      have hlastGap : last = gap := by
        apply Fin.ext
        rfl
      have hcomparisonSelf :
          (((((R + 2 - c.order low : Int) : ℚ)) : WithTop ℚ)) ≤
            c.truncatedPrefixDefect c
              ((-1) ^ ((s - 2) / 2)) 0 (s - 2) := by
        have hlowerQ :
            ((R + 2 - c.order low : Int) : ℚ) ≤
              ((c.order high - c.order low : Int) : ℚ) +
                c.alphaValue gap := by
          rw [hhighEq]
          push_cast
          linarith
        have hlowerTop :
            (((((R + 2 - c.order low : Int) : ℚ)) : WithTop ℚ)) ≤
              (((((c.order high - c.order low : Int) : ℚ) +
                c.alphaValue gap : ℚ)) : WithTop ℚ) :=
          WithTop.coe_le_coe.mpr hlowerQ
        apply hlowerTop.trans
        have hlength : last.val + 2 = s - 2 := by
          dsimp only [last]
          omega
        have hexponent :
            (last.val - first.val + 2) / 2 = (s - 2) / 2 := by
          dsimp only [last, first]
          omega
        have hgapCast : gap.castSucc = high := by
          apply Fin.ext
          rfl
        have hgapSucc : gap.succ = low := by
          apply Fin.ext
          dsimp only [gap, low]
          simp only [Fin.val_succ]
          omega
        rw [hlastGap] at hlength hexponent
        rw [hlastGap, hgapCast, hgapSucc, hhighEq] at hcomparisonRaw
        simpa only [hhighEq, hlength, hexponent, first, Fin.val_mk]
          using hcomparisonRaw
      have hboundTwoE :
          (((((R + 2 - c.order low : Int) : ℚ)) : WithTop ℚ)) ≤
            (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) := by
        apply WithTop.coe_le_coe.mpr
        have hlowQ :
            ((R - 2 * (ramificationIndex K : Int) + 3 : Int) : ℚ) ≤
              (c.order low : ℚ) := by
          exact_mod_cast hlowStrong
        push_cast at hlowQ ⊢
        linarith
      have hsourceBound :
          (((((R + 2 - c.order low : Int) : ℚ)) : WithTop ℚ)) ≤
            b.truncatedPrefixDefect b
              ((-1) ^ ((s - 2) / 2)) 0 (s - 2) :=
        hboundTwoE.trans hsourceSelf
      let theta : Kˣ := (-1) ^ ((s - 2) / 2)
      have htheta : theta * theta = 1 := by
        dsimp only [theta]
        rw [← mul_pow]
        simp
      have hmixed :
          (((((R + 2 - c.order low : Int) : ℚ)) : WithTop ℚ)) ≤
            b.truncatedPrefixDefect c 1 (s - 2) (s - 2) := by
        exact mixedPrefixDefect_ge_of_selfPrefixDefects b c
          (((((R + 2 - c.order low : Int) : ℚ)) : WithTop ℚ))
          theta theta 1 (s - 2) (s - 2)
          (by simpa only [theta] using hsourceBound)
          (by simpa only [theta] using hcomparisonSelf) htheta
      let alphaIndex : Fin (n + 2) := ⟨s - 2, by
        have := D.le_rank
        omega⟩
      have hsourceAlphaZero : b.alphaValue alphaIndex = 0 := by
        apply (b.alpha_p2 alphaIndex).2.mpr
        unfold orderGap
        have hcast : alphaIndex.castSucc = sourceCurrent := by
          apply Fin.ext
          rfl
        have hsucc : alphaIndex.succ = sourceNext := by
          apply Fin.ext
          dsimp only [alphaIndex, sourceNext]
          simp only [Fin.val_succ]
          omega
        rw [hcast, hsucc, hsourceCurrent, hsourceNext]
        omega
      have hAlphaBound : b.representationAlpha c i ≤
          (((((R + 2 - c.order low : Int) : ℚ)) : WithTop ℚ)) := by
        calc
          b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
            b.representationAlpha_le_primary c i
          _ ≤ (((((b.order sourceCurrent - c.order low : Int) : ℚ)) :
                WithTop ℚ) + (b.alphaValue alphaIndex : WithTop ℚ)) := by
            unfold representationPrimaryDefect
            have hcap := b.truncatedPrefixDefect_le_leftCap c (-1)
              (i.val + 1) (i.val - 1)
            have hcapPos : 0 < i.val + 1 := by omega
            have hcapLt : i.val + 1 < n + 3 := by
              dsimp only [i]
              have := D.le_rank
              omega
            rw [b.prefixAlphaCap_of_internal hcapPos hcapLt] at hcap
            have hcurrentIndex :
                (⟨i.val, i.lt_large⟩ : Fin (n + 3)) = sourceCurrent := by
              apply Fin.ext
              rfl
            have hlowIndex :
                (⟨i.val - 1, by omega⟩ : Fin (n + 3)) = low := by
              apply Fin.ext
              dsimp only [i, low]
              omega
            have halphaIndex :
                (⟨i.val + 1 - 1, by omega⟩ : Fin (n + 2)) =
                  alphaIndex := by
              apply Fin.ext
              dsimp only [i, alphaIndex]
              omega
            simpa only [hcurrentIndex, hlowIndex, halphaIndex] using
              add_le_add_right hcap
                (((b.order sourceCurrent - c.order low : Int) : ℚ) :
                  WithTop ℚ)
          _ = (((((R + 2 - c.order low : Int) : ℚ)) : WithTop ℚ)) := by
            rw [hsourceCurrent, hsourceAlphaZero]
            simp
      unfold RepresentationDefectAt
      change b.representationAlpha c i ≤
        b.truncatedPrefixDefect c 1 i.val i.val
      exact hAlphaBound.trans (by simpa only [i] using hmixed)
    · have hgapNegative : c.orderGap gap < 0 := by
        rw [hgapDef]
        have he := ramificationIndex_pos (K := K)
        omega
      have hgapEven := c.orderGap_even_of_negative gap hgapNegative
      rw [hgapDef] at hgapEven
      rcases hgapEven with ⟨z, hz⟩
      have hgapEq : c.order low - c.order high =
          -(2 * (ramificationIndex K : Int)) := by
        omega
      have hlowEq : c.order low =
          R - 2 * (ramificationIndex K : Int) + 1 := by
        rw [hhighEq] at hgapEq
        omega
      have Pcomparison :
          Beli2019Lemma716TypeIIFailureProfile c R (s - 2)
            (by omega) (by have := D.le_rank; omega) := by
        refine {
          first := by simpa only [zero] using hzeroEq
          high := ?_
          low := ?_ }
        · have hindex :
              (⟨(s - 2) - 2, by
                have := D.le_rank
                omega⟩ : Fin (n + 3)) = high := by
            apply Fin.ext
            change (s - 2) - 2 = s - 4
            omega
          simpa only [hindex] using hhighEq
        · have hindex :
              (⟨(s - 2) - 1, by
                have := D.le_rank
                omega⟩ : Fin (n + 3)) = low := by
            apply Fin.ext
            change (s - 2) - 1 = s - 3
            omega
          simpa only [hindex] using hlowEq
      have hsquare :=
        a.lemma716_typeI_sMinusTwo_exceptional_prefixProduct_isSquare
          b c R s D hfirst hsecond hthird hvalues hac hI hdiscriminant
            hsFour Pcomparison
      have hsourcePrevious : b.order low =
          R - 2 * (ramificationIndex K : Int) + 1 := by
        have hlowOdd : Odd low.val := by
          rcases D.even with ⟨d, hd⟩
          exact ⟨d - 2, by dsimp only [low]; omega⟩
        exact a.lemma716_typeI_prefix_order_eq_low b R s D hthird hvalues
          low (by dsimp only [low]; omega) hlowOdd
      have hsourceGap : b.orderGap ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ = 2 * (ramificationIndex K : Int) + 1 := by
        unfold orderGap
        have hcast :
            (⟨i.val - 1, by
              have := i.lt_large
              omega⟩ : Fin (n + 2)).castSucc = low := by
          apply Fin.ext
          change i.val - 1 = s - 3
          dsimp only [i]
          omega
        have hsucc :
            (⟨i.val - 1, by
              have := i.lt_large
              omega⟩ : Fin (n + 2)).succ =
              sourceCurrent := by
          apply Fin.ext
          change i.val - 1 + 1 = s - 2
          dsimp only [i]
          omega
        rw [hcast, hsucc, hsourcePrevious, hsourceCurrent]
        omega
      have hprevious : c.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ = b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ := by
        have hindex :
            (⟨i.val - 1, by
              have := i.lt_large
              omega⟩ : Fin (n + 3)) = low := by
          apply Fin.ext
          dsimp only [i, low]
          omega
        rw [hindex, hlowEq, hsourcePrevious]
      unfold RepresentationDefectAt
      have hcase :=
        beli2019Lemma79_ii_typeI_caseOne_of_prefixProduct_isSquare
          b c horderBC i hsourceGap hprevious hsquare
      rw [b.coe_representationAlphaValue c i] at hcase
      simpa only [i] using hcase

end BONG.GoodBONG

end Bong
