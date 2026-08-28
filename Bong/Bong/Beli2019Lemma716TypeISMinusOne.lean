/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeIISMinusTwo

/-!
# Beli (2019), Lemma 7.16(ii): the type-I boundary `i = s - 1`

If the preceding comparison order is at least `R + 2`, the half-gap
candidate is nonpositive.  In the remaining case it is `R + 1`.  The order
condition and parity of a negative good-BONG gap then put the preceding odd
comparison order at least at `R - 2e + 3`.  Its alpha is at most `2e - 1`,
so the primary candidate is nonpositive as well.
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

/-- In the low comparison branch at `i = s - 1`, the comparison alpha
immediately before `T_(s-1)` is at most `2e - 1`. -/
theorem lemma716_typeI_sMinusOne_comparisonAlpha_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hcomparison : c.order ⟨s - 2, by
      have := D.le_rank
      omega⟩ = R + 1) :
    c.alphaValue ⟨s - 3, by
      have := D.le_rank
      omega⟩ ≤ 2 * (ramificationIndex K : ℚ) - 1 := by
  have hsNotTwo : s ≠ 2 := by
    intro hsTwo
    have hsource := a.lemma716_typeI_leftBoundary_order_eq b R s D
      hfirst hvalues
    have O := (b.representationOrderCondition_iff c le_rfl).mp horderBC
    rcases O.compare 0 (by omega) with hzero | ⟨hpos, _, _⟩
    · change b.order (0 : Fin (n + 3)) ≤ c.order (0 : Fin (n + 3)) at hzero
      have hleftIndex : (⟨s - 2, by
          have := D.le_rank
          omega⟩ : Fin (n + 3)) = 0 := by
        apply Fin.ext
        simp only [hsTwo, Fin.val_zero]
      rw [hleftIndex] at hsource hcomparison
      omega
    · omega
  have hsFour : 4 ≤ s := by
    rcases D.even with ⟨d, hd⟩
    have := D.two_le
    omega
  let high : Fin (n + 3) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  let low : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  let previous : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  have hhighEven : Even high.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by dsimp only [high]; omega⟩
  have hhighLower : R + 1 ≤ c.order high :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm high hhighEven
  have hhighPreviousEven : Even (previous.val - high.val) := by
    exact ⟨1, by dsimp only [previous, high]; omega⟩
  have hhighPrevious : c.order high ≤ c.order previous :=
    lemma716_order_le_of_evenGap c high previous (by
      dsimp only [high, previous]
      omega) hhighPreviousEven
  have hcomparisonPrevious : c.order previous = R + 1 := by
    simpa only [previous] using hcomparison
  have hhighEq : c.order high = R + 1 := by omega
  have hlowOdd : Odd low.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by dsimp only [low]; omega⟩
  have hsourceLow : b.order low =
      R - 2 * (ramificationIndex K : Int) + 1 :=
    a.lemma716_typeI_prefix_order_eq_low b R s D hthird hvalues low
      (by dsimp only [low]; omega) hlowOdd
  have hsourcePrevious : b.order previous = R + 2 := by
    simpa only [previous] using
      a.lemma716_typeI_leftBoundary_order_eq b R s D hfirst hvalues
  have O := (b.representationOrderCondition_iff c le_rfl).mp horderBC
  have hpairRaw := O.pairSum_le low.val (by
    dsimp only [low]
    have := D.le_rank
    omega)
  have hpair : b.order low + b.order previous ≤
      c.order low + c.order previous := by
    have hnext : low.val + 1 = previous.val := by
      dsimp only [low, previous]
      omega
    simpa only [orderSequence_at, hnext] using hpairRaw
  have hlowLower : R - 2 * (ramificationIndex K : Int) + 2 ≤
      c.order low := by
    rw [hsourceLow, hsourcePrevious, hcomparisonPrevious] at hpair
    omega
  let gap : Fin (n + 2) := ⟨high.val, by
    dsimp only [high]
    have := D.le_rank
    omega⟩
  have hgapDef : c.orderGap gap = c.order low - c.order high := by
    unfold orderGap
    have hsucc : gap.succ = low := by
      apply Fin.ext
      simp only [gap, low, high, Fin.val_succ]
      omega
    have hcast : gap.castSucc = high := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  have hlowStrong : R - 2 * (ramificationIndex K : Int) + 3 ≤
      c.order low := by
    by_cases hnegative : c.orderGap gap < 0
    · have heven := c.orderGap_even_of_negative gap hnegative
      rw [hgapDef, hhighEq] at heven hnegative
      rcases heven with ⟨z, hz⟩
      omega
    · rw [hgapDef, hhighEq] at hnegative
      have he := ramificationIndex_pos (K := K)
      omega
  let alphaIndex : Fin (n + 2) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  have hhalf := c.alphaValue_le_halfGapValue alphaIndex
  have hgapAlpha : c.orderGap alphaIndex =
      c.order previous - c.order low := by
    unfold orderGap
    have hsucc : alphaIndex.succ = previous := by
      apply Fin.ext
      simp only [alphaIndex, previous, Fin.val_succ]
      omega
    have hcast : alphaIndex.castSucc = low := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  unfold halfGapValue at hhalf
  rw [hgapAlpha, hcomparisonPrevious] at hhalf
  have hlowStrongQ :
      ((R - 2 * (ramificationIndex K : Int) + 3 : Int) : ℚ) ≤
        (c.order low : ℚ) := by exact_mod_cast hlowStrong
  have hresult : c.alphaValue alphaIndex ≤
      2 * (ramificationIndex K : ℚ) - 1 := by
    push_cast at hlowStrongQ hhalf ⊢
    linarith
  simpa only [alphaIndex] using hresult

/-- Condition 2.1(ii) at the type-I boundary with paper index `s - 1`. -/
theorem lemma716_typeI_sMinusOne_representationDefectAt
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
    (horderBC : b.RepresentationOrderCondition c le_rfl) :
    b.RepresentationDefectAt c
      { val := s - 1
        pos := by have := D.two_le; omega
        lt_large := by have := D.le_rank; omega
        le_small := by have := D.le_rank; omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s - 1
      pos := by have := D.two_le; omega
      lt_large := by have := D.le_rank; omega
      le_small := by have := D.le_rank; omega }
  let previous : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  let current : Fin (n + 3) := ⟨s - 1, by
    have := D.le_rank
    omega⟩
  have hpreviousEven : Even previous.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 1, by dsimp only [previous]; omega⟩
  have hcomparisonPrevious : R + 1 ≤ c.order previous :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm previous
      hpreviousEven
  have hsourceCurrent : b.order current =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    simpa only [current] using
      a.lemma716_typeI_rightBoundary_order_eq b R s D hsecond hvalues
  by_cases hhigh : R + 2 ≤ c.order previous
  · apply b.representationDefectAt_of_add_twoE_le c i
    change b.order current + 2 * (ramificationIndex K : Int) ≤
      c.order previous
    rw [hsourceCurrent]
    omega
  · have hcomparisonEq : c.order previous = R + 1 := by omega
    have hsNotTwo : s ≠ 2 := by
      intro hsTwo
      have hsourceLeft := a.lemma716_typeI_leftBoundary_order_eq b R s D
        hfirst hvalues
      have O := (b.representationOrderCondition_iff c le_rfl).mp horderBC
      rcases O.compare 0 (by omega) with hzero | ⟨hpos, _, _⟩
      · change b.order (0 : Fin (n + 3)) ≤ c.order (0 : Fin (n + 3)) at hzero
        have hidx : previous = (0 : Fin (n + 3)) := by
          apply Fin.ext
          simp only [previous, hsTwo, Fin.val_zero]
        have hsourceLeft' : b.order previous = R + 2 := by
          simpa only [previous] using hsourceLeft
        rw [hidx] at hsourceLeft' hcomparisonEq
        omega
      · omega
    have halpha := a.lemma716_typeI_sMinusOne_comparisonAlpha_le
      b c R s D hfirst hthird hnorm hvalues horderBC (by
        simpa only [previous] using hcomparisonEq)
    let alphaIndex : Fin (n + 2) := ⟨s - 3, by
      have := D.le_rank
      omega⟩
    have halpha' : c.alphaValue alphaIndex ≤
        2 * (ramificationIndex K : ℚ) - 1 := by
      simpa only [alphaIndex] using halpha
    unfold RepresentationDefectAt
    change b.representationAlpha c i ≤
      b.truncatedPrefixDefect c 1 i.val i.val
    calc
      b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
        b.representationAlpha_le_primary c i
      _ ≤ ((((b.order current - c.order previous : Int) : ℚ) :
            WithTop ℚ) + (c.alphaValue alphaIndex : WithTop ℚ)) := by
        unfold representationPrimaryDefect
        have hcap := b.truncatedPrefixDefect_le_rightCap c (-1)
          (i.val + 1) (i.val - 1)
        have hcapPos : 0 < i.val - 1 := by
          dsimp only [i]
          rcases D.even with ⟨d, hd⟩
          have := D.two_le
          omega
        have hcapLt : i.val - 1 < n + 3 := by
          dsimp only [i]
          have := D.le_rank
          omega
        rw [c.prefixAlphaCap_of_internal hcapPos hcapLt] at hcap
        have hcurrentIndex : (⟨i.val, i.lt_large⟩ : Fin (n + 3)) =
            current := by
          apply Fin.ext
          rfl
        have hpreviousIndex :
            (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 3)) =
              previous := by
          apply Fin.ext
          dsimp only [i, previous]
          omega
        have halphaIndex : (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 2)) =
            alphaIndex := by
          apply Fin.ext
          dsimp only [i, alphaIndex]
          omega
        simpa only [hcurrentIndex, hpreviousIndex, halphaIndex] using
          add_le_add_right hcap
            ((((b.order current - c.order previous : Int) : ℚ) :
              WithTop ℚ))
      _ ≤ ((0 : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_le_coe.mpr
        have hsourceQ : (b.order current : ℚ) =
            (R : ℚ) - 2 * (ramificationIndex K : ℚ) + 2 := by
          rw [hsourceCurrent]
          push_cast
          ring
        have hcomparisonQ : (c.order previous : ℚ) = (R : ℚ) + 1 := by
          rw [hcomparisonEq]
          push_cast
          ring
        push_cast
        rw [hsourceQ, hcomparisonQ]
        linarith
      _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
        b.truncatedPrefixDefect_nonneg c 1 i.val i.val

end BONG.GoodBONG

end Bong
