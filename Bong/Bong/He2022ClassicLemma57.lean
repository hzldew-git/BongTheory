/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma56

/-!
# He (2024), Lemma 5.7

For the odd paper rank `n = 2 * k + 3`, this file proves the equivalence
between the publisher's condition (iii) for every classic integral target,
the two literal first-column tests displayed in Lemma 5.7(ii), and the
numerical condition `J2_O(n)`.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- The two literal targets in He, Lemma 5.7(ii).  The implication keeps
the printed qualification `R_(n+1)=1` or `R_(n+2)>1` inside the test
predicate. -/
noncomputable def HeClassicLemma57PublishedTests {m : Nat}
    (a : GoodBONG q L (m + 5)) (k : Nat)
    (_hSource : 2 * k + 6 <= m + 5) : Prop :=
  (a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) →
    ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
      a.CentralRepresentationConditionsPrime
          (he2022ClassicLemma56Target (K := K) (heHuLemma59C a k) k) ∧
        a.CentralRepresentationConditionsPrime
          (he2022ClassicLemma56Target (K := K)
            (heHuLemma59C a k *
              heHuSharp (heHuLemma59CTilde a k) hc) k)

/-- Every literal `C₁^(2k+3)(x)` used in Lemma 5.7 is classic integral. -/
theorem he2022ClassicLemma56Target_isClassicIntegral (x : Kˣ) (k : Nat) :
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1 (K := K) k
          (heHuLemma59NormalizedParameter (K := K) x)))
      (heHuExactRealization
        (heClassicOddC1 (K := K) k
          (heHuLemma59NormalizedParameter (K := K) x))
        (heClassicOddC1_adjacentAdmissible k
          (heHuLemma59NormalizedParameter (K := K) x) (by
            rw [heHuLemma59NormalizedParameter_order]
            exact heHuLemma59Parity_nonneg x))
        (heClassicOddC1_weakTwoStep k
          (heHuLemma59NormalizedParameter (K := K) x) (by
            rw [heHuLemma59NormalizedParameter_order]
            exact heHuLemma59Parity_nonneg x))).lattice := by
  exact heClassicOddC1_isClassicIntegral (K := K) k
    (heHuLemma59NormalizedParameter (K := K) x) (by
      rw [heHuLemma59NormalizedParameter_order]
      exact heHuLemma59Parity_nonneg x)

/-- The initial zero-order block supplied by `J1'_E(n-1)`. -/
theorem he2022ClassicLemma57_initialOrders_zero {m k : Nat}
    (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega)) :
    ∀ i : Fin (m + 5), i.val < 2 * k + 3 → a.order i = 0 := by
  intro i hi
  let small : Fin (2 * k + 3) := ⟨i.val, hi⟩
  have h := hJ1.1 small
  have hindex : (⟨small.val, by omega⟩ : Fin (m + 5)) = i := Fin.ext rfl
  rw [hindex] at h
  exact h

/-- The signed-prefix equality extracted from `J2_E(n-1)`. -/
theorem he2022ClassicLemma57_sourceEquality {m k : Nat}
    (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega)) :
    a.truncatedPrefixDefect a ((-1) ^ (k + 2)) 0 (2 * k + 4) =
      ((((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ)) := by
  have hSum :
      (((a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (k + 2)) 0
            (2 * k + 4) = 1 := by
    have hNext : 2 * k + 2 + 1 = 2 * k + 3 := by omega
    have hLength : 2 * k + 2 + 2 = 2 * k + 4 := by omega
    have hExponent : (2 * k + 2 + 2) / 2 = k + 2 := by omega
    simpa only [hNext, hLength, hExponent] using hJ2.2.1
  apply WithTop.add_left_cancel WithTop.coe_ne_top
  calc
    (((a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a ((-1) ^ (k + 2)) 0 (2 * k + 4) = 1 := hSum
    _ = (((a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        ((((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
      norm_cast
      ring

/-- Lemma 5.7, implication `(i) -> (ii)`: the universal condition (iii)
specializes to the two displayed classic targets. -/
theorem he2022ClassicLemma57_all_to_tests
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hAll : HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
      (n := 2 * k + 2) a) :
    a.HeClassicLemma57PublishedTests k hSource := by
  intro hTrigger
  rcases a.he2022ClassicLemma55 (m := m + 2) (k := k) (by omega)
      hClassic hJ1 hJ2 hTrigger with ⟨hc, _hraw, _hunit, _hsharp⟩
  refine ⟨hc, ?_, ?_⟩
  · exact hAll _
      (he2022ClassicLemma56Target_isClassicIntegral
        (K := K) (heHuLemma59C a k) k)
  · exact hAll _
      (he2022ClassicLemma56Target_isClassicIntegral (K := K)
        (heHuLemma59C a k *
          heHuSharp (heHuLemma59CTilde a k) hc) k)

/-- Lemma 5.7, implication `(ii) -> (iii)`: Lemma 5.6 rules out a
simultaneous failure of the `J2_O` alpha bound. -/
theorem he2022ClassicLemma57_tests_to_j2O
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hTests : a.HeClassicLemma57PublishedTests k hSource) :
    a.HeClassicJ2O (2 * k + 3) (by omega) (by omega) := by
  intro hTrigger
  by_contra hnot
  have hAlphaNext :
      (a.heClassicOddThreshold (2 * k + 3) (by omega) : ℚ) <
        a.alphaValue ⟨2 * k + 4, by omega⟩ := lt_of_not_ge hnot
  rcases a.he2022ClassicLemma56 (m := m + 2) (k := k) (by omega)
      hClassic hJ1 hJ2 hAlphaNext hTrigger with
    ⟨hcObstruction, _hFirstTrigger, _hSecondTrigger, _hNotBoth,
      hFailure⟩
  rcases hTests hTrigger with ⟨hcTests, hFirst, hSecond⟩
  have hhc : hcTests = hcObstruction := Subsingleton.elim _ _
  subst hcTests
  rcases hFailure with hFirstFailure | hSecondFailure
  · exact hFirstFailure
      ((a.heClassicPublishedCentralConditions_iff_forall_at _).1 hFirst
        (heHuLemma59CentralIndex k (by omega)))
  · exact hSecondFailure
      ((a.heClassicPublishedCentralConditions_iff_forall_at _).1 hSecond
        (heHuLemma59CentralIndex k (by omega)))

/-- The terminal defect trigger is impossible under `J2_O(n)`.  This is
the numerical core of Lemma 5.7, implication `(iii) -> (i)`: Lemma 3.7
bounds the previous defect, equation (5.1) forces the last source gap to be
odd, and the resulting zero current defect contradicts Lemma 5.3. -/
theorem he2022ClassicLemma57_terminalTrigger_false
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hSource : 2 * k + 6 <= m + 5)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hOdd : a.HeClassicJ2O (2 * k + 3) (by omega) (by omega))
    (hAlternative : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩)
    (i : CentralRepresentationIndex (m + 5) (2 * k + 3))
    (hi : i.val = 2 * k + 4)
    (htrigger : a.centralDefectTrigger b i) : False := by
  have hRBefore : a.order ⟨2 * k + 1, by omega⟩ = 0 := by
    exact hJ1.1 ⟨2 * k + 1, by omega⟩
  have hRAt : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
    exact hJ1.1 ⟨2 * k + 2, by omega⟩
  have hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 := hJ2.1
  have hSourceEquality :=
    a.he2022ClassicLemma57_sourceEquality hSource hJ2
  have hGapUpper :
      a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩ <=
        2 * (ramificationIndex K : Int) - 1 :=
    (a.he2022ClassicLemma53 (m := m + 3) (n := 2 * k + 3)
      (by omega) ⟨k + 1, by omega⟩ (by omega) hAClassic hRAt
      hAlpha hOdd).1
  have hBounds := a.he2022ClassicLemma37BoundsLongSource
    (m := m + 2) k b (by omega) hAClassic hBClassic hRBefore hRAt
      hAlpha hSourceEquality
  have hCommonCap :
      a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) <=
        (1 : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b 1
      (2 * k + 3) (2 * k + 3)
    rw [a.prefixAlphaCap_of_internal (i := 2 * k + 3)
      (by omega) (by omega)] at hcap
    have hindex :
        (⟨2 * k + 3 - 1, by omega⟩ : Fin (m + 4)) =
          (⟨2 * k + 2, by omega⟩ : Fin (m + 4)) := by
      apply Fin.ext
      change 2 * k + 3 - 1 = 2 * k + 2
      omega
    rw [hindex, hAlpha] at hcap
    exact hcap
  let targetLast : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  have hTargetLastEven : Even targetLast.val := ⟨k + 1, by
    simp only [targetLast]
    omega⟩
  have hTargetLastNonnegative : 0 <= b.order targetLast :=
    ((b.he2022ClassicProposition24 hBClassic).oddIndexed
      targetLast targetLast le_rfl hTargetLastEven hTargetLastEven).1
  have hTargetIndex :
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin (2 * k + 3)) = targetLast := by
    apply Fin.ext
    simp only [targetLast]
    omega
  have hSourceIndex :
      (⟨i.val, by
        have := i.lt_large
        omega⟩ : Fin (m + 5)) =
          ⟨2 * k + 4, by omega⟩ := Fin.ext hi
  have hOrderTrigger : b.order targetLast <
      a.order ⟨2 * k + 4, by omega⟩ := by
    have h := htrigger.1
    rw [hTargetIndex, hSourceIndex] at h
    exact h
  have hDefectTrigger :
      (((2 * (ramificationIndex K : ℚ) +
          (b.order targetLast : ℚ) -
          (a.order ⟨2 * k + 4, by omega⟩ : ℚ) : ℚ) :
            WithTop ℚ)) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
    have h := htrigger.2
    rw [hTargetIndex, hSourceIndex] at h
    exact h
  have hDefectTriggerInt :
      ((((2 * (ramificationIndex K : Int) +
          b.order targetLast -
          a.order ⟨2 * k + 4, by omega⟩ : Int) : ℚ) :
            WithTop ℚ)) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
    convert hDefectTrigger using 1; norm_cast
  have hPreviousUpper :
      a.centralPreviousDefect b i <=
        (((b.order targetLast -
            a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) := by
    unfold centralPreviousDefect
    rw [hi]
    dsimp only [targetLast]
    convert hBounds.1 using 1; congr 1
  have hCommonNe :
      a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hCommonCap
  have hPreviousNe : a.centralPreviousDefect b i ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      ((WithTop.add_ne_top).2 ⟨WithTop.coe_ne_top, hCommonNe⟩)
    exact hPreviousUpper
  have h37Central :
      (((a.order ⟨2 * k + 3, by omega⟩ -
          b.order targetLast : Int) : ℚ) : WithTop ℚ) +
        a.centralPreviousDefect b i <=
          a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) := by
    rw [← WithTop.coe_untop (a.centralPreviousDefect b i) hPreviousNe,
      ← WithTop.coe_untop
        (a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3))
        hCommonNe] at hPreviousUpper ⊢
    norm_cast at hPreviousUpper ⊢
    push_cast at hPreviousUpper ⊢
    linarith
  have hCurrentCap : a.centralCurrentDefect b i <=
      (a.alphaValue ⟨2 * k + 4, by omega⟩ : WithTop ℚ) := by
    have hcap := a.centralCurrentDefect_le_leftCap b i
    rw [hi] at hcap
    rw [a.prefixAlphaCap_of_internal (i := 2 * k + 5)
      (by omega) (by omega)] at hcap
    have hindex :
        (⟨2 * k + 5 - 1, by omega⟩ : Fin (m + 4)) =
          (⟨2 * k + 4, by omega⟩ : Fin (m + 4)) := by
      apply Fin.ext
      change 2 * k + 5 - 1 = 2 * k + 4
      omega
    rw [hindex] at hcap
    exact hcap
  have hCurrentThreshold : a.centralCurrentDefect b i <=
      (((a.heClassicOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
        WithTop ℚ) :=
    hCurrentCap.trans (by exact_mod_cast hOdd hAlternative)
  have hThreshold :
      (((2 * (ramificationIndex K : Int) -
          a.order ⟨2 * k + 4, by omega⟩ +
          a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) <
        a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
          (((a.heClassicOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
            WithTop ℚ) := by
    calc
      (((2 * (ramificationIndex K : Int) -
          a.order ⟨2 * k + 4, by omega⟩ +
          a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) =
          ((((a.order ⟨2 * k + 3, by omega⟩ -
              b.order targetLast : Int) : ℚ) : WithTop ℚ) +
            (((2 * (ramificationIndex K : Int) +
              b.order targetLast -
              a.order ⟨2 * k + 4, by omega⟩ : Int) : ℚ) :
                WithTop ℚ)) := by
                  norm_cast
                  ring
      _ < ((((a.order ⟨2 * k + 3, by omega⟩ -
              b.order targetLast : Int) : ℚ) : WithTop ℚ) +
            (a.centralPreviousDefect b i +
              a.centralCurrentDefect b i)) :=
        WithTop.add_lt_add_left (by simp) hDefectTriggerInt
      _ = (((((a.order ⟨2 * k + 3, by omega⟩ -
              b.order targetLast : Int) : ℚ) : WithTop ℚ) +
            a.centralPreviousDefect b i) +
              a.centralCurrentDefect b i) := by ac_rfl
      _ <= a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
            a.centralCurrentDefect b i := by
        gcongr
      _ <= a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
            (((a.heClassicOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
              WithTop ℚ) := by
        gcongr
  let sourceGap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  have hGapNotEven : ¬ Even sourceGap := by
    intro hEven
    have hThresholdFormula :
        a.heClassicOddThreshold (2 * k + 3) (by omega) =
          2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
            a.order ⟨2 * k + 3, by omega⟩ - 1 := by
      simp only [heClassicOddThreshold, heHuOddThreshold, sourceGap,
        hEven, if_pos]
    have hCommonShift :
        a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
            (((a.heClassicOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
              WithTop ℚ) <=
          (1 : WithTop ℚ) +
            (((a.heClassicOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
              WithTop ℚ) := by
      gcongr
    have hcontr := hThreshold.trans_le hCommonShift
    rw [hThresholdFormula] at hcontr
    have heq :
        (1 : WithTop ℚ) +
            ((((2 * (ramificationIndex K : Int) -
              a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
                WithTop ℚ)) =
          (((2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
            a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) := by
      norm_cast
      ring
    rw [heq] at hcontr
    exact lt_irrefl _ hcontr
  have hGapOdd : Odd sourceGap :=
    (Int.even_or_odd sourceGap).resolve_left hGapNotEven
  have hThresholdFormula :
      a.heClassicOddThreshold (2 * k + 3) (by omega) =
        2 * (ramificationIndex K : Int) -
          a.order ⟨2 * k + 4, by omega⟩ +
          a.order ⟨2 * k + 3, by omega⟩ := by
    simp [heClassicOddThreshold, heHuOddThreshold, sourceGap, hGapNotEven]
  have hCommonNonnegative : (0 : WithTop ℚ) <=
      a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) :=
    a.truncatedPrefixDefect_nonneg
      (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
      b 1 (2 * k + 3) (2 * k + 3)
  have hCommonPositive : (0 : WithTop ℚ) <
      a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) := by
    by_contra hnot
    have hzero : a.truncatedPrefixDefect b 1 (2 * k + 3)
        (2 * k + 3) = 0 :=
      le_antisymm (le_of_not_gt hnot) hCommonNonnegative
    rw [hzero, zero_add, hThresholdFormula] at hThreshold
    exact lt_irrefl _ hThreshold
  have hCommonOrderEven : Even (ordUnit K
      (a.prefixProduct (2 * k + 3) *
        b.prefixProduct (2 * k + 3))) := by
    rcases Int.even_or_odd (ordUnit K
      (a.prefixProduct (2 * k + 3) *
        b.prefixProduct (2 * k + 3))) with hEven | hOddOrder
    · exact hEven
    · have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
          (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
          b 1 (2 * k + 3) (2 * k + 3) (by
            simpa only [one_mul] using hOddOrder)
      rw [hzero] at hCommonPositive
      exact (lt_irrefl 0 hCommonPositive).elim
  have hCommonSumEven : Even
      (a.orderSequence.prefixSum (2 * k + 3) +
        b.orderSequence.prefixSum (2 * k + 3)) := by
    rw [ordUnit_mul,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 3) (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 3) le_rfl] at hCommonOrderEven
    exact hCommonOrderEven
  have hSourcePairOdd : Odd
      (a.order ⟨2 * k + 3, by omega⟩ +
        a.order ⟨2 * k + 4, by omega⟩) := by
    rcases hGapOdd with ⟨z, hz⟩
    refine ⟨z + a.order ⟨2 * k + 3, by omega⟩, ?_⟩
    simp only [sourceGap] at hz
    omega
  have hSourceExtended :
      a.orderSequence.prefixSum (2 * k + 5) =
        a.orderSequence.prefixSum (2 * k + 3) +
          a.order ⟨2 * k + 3, by omega⟩ +
          a.order ⟨2 * k + 4, by omega⟩ := by
    rw [a.orderSequence.prefixSum_succ,
      a.orderSequence.prefixSum_succ,
      a.orderSequence_entryOrZero_eq_order
        (⟨2 * k + 3, by omega⟩ : Fin (m + 5)),
      a.orderSequence_entryOrZero_eq_order
        (⟨2 * k + 4, by omega⟩ : Fin (m + 5))]
  have hMixedOdd : Odd (ordUnit K
      ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
        b.prefixProduct (2 * k + 3))) := by
    have hNegOne : ordUnit K (-1 : Kˣ) = 0 := by
      rw [ordUnit_neg]
      simp [ordUnit]
    rw [ordUnit_mul, ordUnit_mul, hNegOne,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 5) (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 3) le_rfl, hSourceExtended]
    have hOddSum := hCommonSumEven.add_odd hSourcePairOdd
    convert Even.zero.add_odd hOddSum using 1; ring
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
    (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
    b (-1) (2 * k + 5) (2 * k + 3) hMixedOdd
  have hCurrentZero : a.centralCurrentDefect b i = 0 := by
    unfold centralCurrentDefect
    rw [hi]
    convert hzero using 1; congr 1
  have hLarge :
      ((((2 * (ramificationIndex K : Int) +
          b.order ⟨2 * k + 2, by omega⟩ -
          a.order ⟨2 * k + 4, by omega⟩ : Int) : ℚ) : WithTop ℚ)) <
        a.truncatedPrefixDefect b (-1) (2 * k + 4) (2 * k + 2) +
          a.truncatedPrefixDefect b (-1) (2 * k + 5) (2 * k + 3) := by
    unfold centralPreviousDefect centralCurrentDefect at hDefectTriggerInt
    rw [hi] at hDefectTriggerInt
    dsimp only [targetLast] at hDefectTriggerInt
    convert hDefectTriggerInt using 1; congr 1
  have hGapLower := a.he2022ClassicLemma37GapLongSource
    (m := m + 1) k b (by omega) hAClassic hBClassic hRBefore hRAt
      hAlpha hSourceEquality hzero hLarge
  exact (not_lt_of_ge hGapUpper) hGapLower

/-- Lemma 5.7, implication `(iii) -> (i)`: `J2_O(n)` supplies condition
(iii) for every classic integral target.  Corollary 3.12(iii) handles all
nonterminal indices and Lemma 3.9(ii) handles the small boundary case; the
remaining terminal trigger is excluded by the preceding theorem. -/
theorem he2022ClassicLemma57_all_of_j2O
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hOdd : a.HeClassicJ2O (2 * k + 3) (by omega) (by omega)) :
    HeClassicAllCentralRepresentationConditionsPrime.{u, v, w}
      (n := 2 * k + 2) a := by
  intro W _ _ r M b hBClassic
  apply (a.heClassicPublishedCentralConditions_iff_forall_at b).2
  intro i
  have hzero := a.he2022ClassicLemma57_initialOrders_zero hSource hJ1
  have hRAt : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
    let idx : Fin (m + 5) := ⟨2 * k + 2, by omega⟩
    have hz := hzero idx (by simp only [idx]; omega)
    simpa only [idx] using hz
  have hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 := hJ2.1
  have hSourceEquality :=
    a.he2022ClassicLemma57_sourceEquality hSource hJ2
  by_cases hiInitial : i.val <= 2 * k + 3
  · exact a.he2022ClassicCorollary312iiiInitial (m := m + 1) k b
      (by omega) hAClassic hBClassic hzero hAlpha hSourceEquality i
      hiInitial
  · have hiTerminal : i.val = 2 * k + 4 := by
      have := i.le_small_succ
      omega
    have hRn1 := a.heClassicBoundaryOrder_zeroOrOne_of_alphaOne
      (m := m + 3) (n := 2 * k + 3) (by omega) (by omega)
      hAClassic hRAt hAlpha
    rcases hRn1 with hRn1Zero | hRn1One
    · let sourceNext : Fin (m + 5) := ⟨2 * k + 4, by omega⟩
      have hNextEven : Even sourceNext.val := ⟨k + 2, by
        simp only [sourceNext]
        omega⟩
      have hNextNonnegative : 0 <= a.order sourceNext :=
        ((a.he2022ClassicProposition24 hAClassic).oddIndexed
          sourceNext sourceNext le_rfl hNextEven hNextEven).1
      by_cases hNextZero : a.order sourceNext = 0
      · exact a.he2022ClassicCorollary312iii (m := m) k b (by omega)
          hAClassic hBClassic hzero hAlpha hSourceEquality hRn1Zero
          (Or.inl (by simpa only [sourceNext] using hNextZero)) i
      · by_cases hNextOne : a.order sourceNext = 1
        · exact a.he2022ClassicCorollary312iii (m := m) k b (by omega)
            hAClassic hBClassic hzero hAlpha hSourceEquality hRn1Zero
            (Or.inr (by simpa only [sourceNext] using hNextOne)) i
        · have hAlternative :
              a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
                1 < a.order ⟨2 * k + 4, by omega⟩ := by
            right
            have hgt : 1 < a.order sourceNext := by omega
            simpa only [sourceNext] using hgt
          intro htrigger
          exact (a.he2022ClassicLemma57_terminalTrigger_false b hSource
            hAClassic hBClassic hJ1 hJ2 hOdd hAlternative i hiTerminal
            htrigger).elim
    · have hAlternative :
          a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
            1 < a.order ⟨2 * k + 4, by omega⟩ := Or.inl hRn1One
      intro htrigger
      exact (a.he2022ClassicLemma57_terminalTrigger_false b hSource
        hAClassic hBClassic hJ1 hJ2 hOdd hAlternative i hiTerminal
        htrigger).elim

/-- He (2024), Lemma 5.7, in the publisher's full three-condition form.
The ambient `n`-universality and `J3_E(n-1)` assumptions are retained
verbatim, although the central-condition equivalence uses only the displayed
classic-integrality, `J1'_E`, and `J2_E` hypotheses. -/
theorem he2022ClassicLemma57
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (_hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3))
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (_hJ3 : a.HeClassicJ3E (2 * k + 2) (by omega)) :
    (HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
        (n := 2 * k + 2) a ↔
      a.HeClassicLemma57PublishedTests k hSource) ∧
      (a.HeClassicLemma57PublishedTests k hSource ↔
        a.HeClassicJ2O (2 * k + 3) (by omega) (by omega)) := by
  constructor
  · constructor
    · exact a.he2022ClassicLemma57_all_to_tests hSource hAClassic hJ1 hJ2
    · intro hTests
      exact a.he2022ClassicLemma57_all_of_j2O hSource hAClassic hJ1 hJ2
        (a.he2022ClassicLemma57_tests_to_j2O hSource hAClassic hJ1 hJ2
          hTests)
  · constructor
    · exact a.he2022ClassicLemma57_tests_to_j2O hSource hAClassic hJ1 hJ2
    · intro hOdd
      exact a.he2022ClassicLemma57_all_to_tests hSource hAClassic hJ1 hJ2
        (a.he2022ClassicLemma57_all_of_j2O hSource hAClassic hJ1 hJ2 hOdd)

end BONG.GoodBONG

end Bong
