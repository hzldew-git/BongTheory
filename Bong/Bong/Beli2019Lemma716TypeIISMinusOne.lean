/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716BoundaryAlpha
import Bong.Bong.Beli2019Lemma79DefectOdd

/-!
# Beli (2019), Lemma 7.16(ii): the type-II boundary `i = s - 1`

At the middle coefficient of the exceptional ternary block, the preceding
comparison order is either at least `R + 2`, in which case the primary
candidate is nonpositive, or it is exactly `R + 1`.  In the equality case,
Lemma 6.6(i) supplies the prefix-sum parity needed by the defect-one branch
of Lemma 7.9(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [DyadicDiscriminantClassLaws K]
variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [PerfectResidueFieldLaws K]

/-- Condition 2.1(ii) at the type-II boundary with paper index `s - 1`. -/
theorem lemma716_typeII_sMinusOne_representationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (horderBC : b.RepresentationOrderCondition c le_rfl) :
    b.RepresentationDefectAt c
      { val := s - 1
        pos := by
          have := D.two_le
          omega
        lt_large := by
          have hs : s < n + 3 := Classical.choose hII
          omega
        le_small := by
          have hs : s < n + 3 := Classical.choose hII
          omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s - 1
      pos := by
        have := D.two_le
        omega
      lt_large := by
        have hs : s < n + 3 := Classical.choose hII
        omega
      le_small := by
        have hs : s < n + 3 := Classical.choose hII
        omega }
  let previous : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  let current : Fin (n + 3) := ⟨s - 1, by
    have hs : s < n + 3 := Classical.choose hII
    omega⟩
  let betaIndex : Fin (n + 2) := ⟨s - 1, by
    have hs : s < n + 3 := Classical.choose hII
    omega⟩
  have hpreviousEven : Even previous.val := by
    rcases D.even with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    simp only [previous, Fin.val_mk]
    omega
  have hsourcePrevious : b.order previous = R + 1 := by
    simpa only [previous] using
      a.lemma716_typeII_leftBoundary_order_eq b R s D hII epsilon eta
        hepsilonUnit hetaUnit hvalues
  have hsourceCurrent : b.order current =
      R - 2 * (ramificationIndex K : Int) + 3 := by
    simpa only [current] using
      a.lemma716_typeII_rightBoundary_order_eq b R s D hII epsilon eta
        hepsilonUnit hetaUnit hvalues
  have hbeta : b.alphaValue betaIndex =
      2 * (ramificationIndex K : ℚ) - 1 := by
    simpa only [betaIndex] using
      a.lemma716_typeII_rightBoundary_alphaValue_eq_twoE_sub_one
        b R s D hII epsilon eta hepsilonUnit hetaUnit hvalues
  have hcomparisonPrevious : R + 1 ≤ c.order previous :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm previous
      hpreviousEven
  by_cases hhigh : R + 2 ≤ c.order previous
  · unfold RepresentationDefectAt
    have harith :
        (((b.order current - c.order previous : Int) : ℚ) +
          b.alphaValue betaIndex) ≤ 0 := by
      rw [hsourceCurrent, hbeta]
      have hhighQ : ((R + 2 : Int) : ℚ) ≤ (c.order previous : ℚ) := by
        exact_mod_cast hhigh
      push_cast at hhighQ ⊢
      linarith
    calc
      b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
        b.representationAlpha_le_primary c i
      _ ≤ ((((b.order current - c.order previous : Int) : ℚ) :
            WithTop ℚ) + (b.alphaValue betaIndex : WithTop ℚ)) := by
        unfold representationPrimaryDefect
        have hcap := b.truncatedPrefixDefect_le_leftCap c (-1)
          (i.val + 1) (i.val - 1)
        have hiCapPos : 0 < i.val + 1 := by omega
        have hiCapLt : i.val + 1 < n + 3 := by
          have hs : s < n + 3 := Classical.choose hII
          simp only [i, Fin.val_mk]
          omega
        rw [b.prefixAlphaCap_of_internal hiCapPos hiCapLt] at hcap
        have hcurrentIndex : (⟨i.val, i.lt_large⟩ : Fin (n + 3)) =
            current := by
          apply Fin.ext
          simp only [i, current, Fin.val_mk]
        have hpreviousIndex :
            (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 3)) =
              previous := by
          apply Fin.ext
          simp only [i, previous, Fin.val_mk]
          omega
        have hcapBetaIndex :
            (⟨i.val + 1 - 1, by omega⟩ : Fin (n + 2)) =
            betaIndex := by
          apply Fin.ext
          simp only [i, betaIndex, Fin.val_mk]
          omega
        simpa only [hcurrentIndex, hpreviousIndex, hcapBetaIndex] using
          add_le_add_right hcap
            ((((b.order current - c.order previous : Int) : ℚ) :
              WithTop ℚ))
      _ ≤ ((0 : ℚ) : WithTop ℚ) := by exact_mod_cast harith
      _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
        b.truncatedPrefixDefect_nonneg c 1 i.val i.val
  · have hcomparisonEq : c.order previous = R + 1 := by omega
    unfold RepresentationDefectAt
    change b.representationAlpha c i ≤
      b.truncatedPrefixDefect c 1 i.val i.val
    rw [← b.coe_representationAlphaValue c i]
    have hiNext : i.val + 1 < n + 3 := by
      have hs : s < n + 3 := Classical.choose hII
      dsimp only [i]
      omega
    have hnextAlpha : b.alphaValue ⟨i.val, by omega⟩ ≤
        ((b.orderSequence.entryOrZero (i.val - 1) -
          b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ) := by
      have hpreviousEntry :
          b.orderSequence.entryOrZero (i.val - 1) = b.order previous := by
        have hindex : i.val - 1 = previous.val := by
          dsimp only [i, previous]
          omega
        rw [hindex]
        exact b.orderSequence_entryOrZero_eq_order previous
      have hcurrentEntry :
          b.orderSequence.entryOrZero i.val = b.order current := by
        have hindex : i.val = current.val := by
          rfl
        rw [hindex]
        exact b.orderSequence_entryOrZero_eq_order current
      have hbetaIndex : (⟨i.val, by omega⟩ : Fin (n + 2)) =
          betaIndex := by
        apply Fin.ext
        rfl
      rw [hbetaIndex, hbeta, hpreviousEntry, hcurrentEntry,
        hsourcePrevious, hsourceCurrent]
      push_cast
      ring_nf
      exact le_rfl
    have hcurrentLe : b.orderSequence.entryOrZero (i.val - 1) ≤
        c.orderSequence.entryOrZero (i.val - 1) := by
      have hsourceEntry :
          b.orderSequence.entryOrZero (i.val - 1) = b.order previous := by
        have hindex : i.val - 1 = previous.val := by
          dsimp only [i, previous]
          omega
        rw [hindex]
        exact b.orderSequence_entryOrZero_eq_order previous
      have hcomparisonEntry :
          c.orderSequence.entryOrZero (i.val - 1) = c.order previous := by
        have hindex : i.val - 1 = previous.val := by
          dsimp only [i, previous]
          omega
        rw [hindex]
        exact c.orderSequence_entryOrZero_eq_order previous
      rw [hsourceEntry, hcomparisonEntry, hsourcePrevious, hcomparisonEq]
    have hparity : b.orderSequence.entryOrZero (i.val - 1) =
        c.orderSequence.entryOrZero (i.val - 1) →
        Int.ModEq 2 (b.orderSequence.prefixSum i.val)
          (c.orderSequence.prefixSum i.val) := by
      intro _
      let zero : Fin (n + 3) := 0
      have hsourceZero : b.order zero = R + 1 := by
        by_cases hsTwo : s = 2
        · have hzeroPrevious : zero = previous := by
            apply Fin.ext
            simp only [zero, previous, Fin.val_zero, Fin.val_mk]
            omega
          rw [hzeroPrevious, hsourcePrevious]
        · have hsGtTwo : 2 < s := by
            have := D.two_le
            omega
          have hzeroPrefix : zero.val < s - 2 := by
            simp only [zero, Fin.val_zero]
            omega
          have hzeroEven : Even zero.val := by
            simp only [zero, Fin.val_zero]
            exact ⟨0, by omega⟩
          exact a.lemma716_typeII_prefix_order_eq_high b R s D hthird hII
            epsilon eta hvalues zero hzeroPrefix hzeroEven
      have hcomparisonZeroLower : R + 1 ≤ c.order zero := by
        simpa only [zero] using
          a.lemma716_comparison_order_zero_ge c R hfirst hnorm
      have hzeroPreviousEven : Even (previous.val - zero.val) := by
        simpa only [zero, Fin.val_zero, Nat.sub_zero] using hpreviousEven
      have hcomparisonZeroUpper : c.order zero ≤ c.order previous :=
        lemma716_order_le_of_evenGap c zero previous (by
          simp only [zero, Fin.val_zero]
          exact Nat.zero_le _) hzeroPreviousEven
      have hcomparisonZero : c.order zero = R + 1 := by omega
      have hsourceEndpoints : b.order zero = b.order previous := by
        rw [hsourceZero, hsourcePrevious]
      have hcomparisonEndpoints : c.order zero = c.order previous := by
        rw [hcomparisonZero, hcomparisonEq]
      have hzeroPrevious : zero.val ≤ previous.val := by
        simp only [zero, Fin.val_zero]
        exact Nat.zero_le _
      have hb66 := b.beli2019Lemma66_i zero previous hzeroPrevious
        hzeroPreviousEven hsourceEndpoints
      have hc66 := c.beli2019Lemma66_i zero previous hzeroPrevious
        hzeroPreviousEven hcomparisonEndpoints
      have hprefixLength : previous.val + 1 = i.val := by
        dsimp only [previous, i]
        have := D.two_le
        omega
      have hbPrefix : Int.ModEq 2
          (b.orderSequence.prefixSum i.val) (R + 1) := by
        have hsum := hb66.closedSum_modEq
        simpa only [zero, Fin.val_zero,
          BeliOrderSequence.closedSegmentSum,
          BeliOrderSequence.prefixSum, Nat.Ico_zero_eq_range,
          hprefixLength, hsourceZero] using hsum
      have hcPrefix : Int.ModEq 2
          (c.orderSequence.prefixSum i.val) (R + 1) := by
        have hsum := hc66.closedSum_modEq
        simpa only [zero, Fin.val_zero,
          BeliOrderSequence.closedSegmentSum,
          BeliOrderSequence.prefixSum, Nat.Ico_zero_eq_range,
          hprefixLength, hcomparisonZero] using hsum
      exact hbPrefix.trans hcPrefix.symm
    exact b.lemma79_ii_of_odd_coordinate_of_order c i hiNext horderBC
      hnextAlpha hcurrentLe hparity

end BONG.GoodBONG

end Bong
