/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicCorollary310
import Bong.Bong.He2022ClassicLemma32

/-!
# He (2024), Corollary 3.11

This file assembles the four ranges in Corollary 3.11 from Lemmas 3.2--3.4
and 3.6.  Range hypotheses use addition rather than truncated subtraction,
so the small-rank boundary cases are literal and vacuous where appropriate.
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

/-- Corollary 3.11(i), even target rank: condition (ii) holds through
paper index `n-3`. -/
theorem he2022ClassicCorollary311iEven {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 2))
    (_hSourceRank : 2 * t + 2 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 3), k.val < 2 * t + 2 ->
      a.order k = 0)
    (halpha : forall k : Fin (m + 2), k.val < 2 * t + 2 ->
      a.alphaValue k = 1)
    (i : RepresentationIndex (m + 3) (2 * t + 2))
    (hiRange : i.val + 3 <= 2 * t + 2) :
    a.HeClassicDefectConditionAt b i := by
  by_cases hiOne : i.val = 1
  · have hfirst : a.order (0 : Fin (m + 3)) = 0 :=
      hzero (0 : Fin (m + 3)) (by simp)
    have hsecond : a.order (1 : Fin (m + 3)) = 0 :=
      hzero (1 : Fin (m + 3)) (by simp)
    have halphaTwo : a.alphaValue (1 : Fin (m + 2)) = 1 :=
      halpha (1 : Fin (m + 2)) (by simp)
    exact a.he2022ClassicLemma33 b hAClassic hBClassic
      hfirst hsecond halphaTwo i hiOne
  · have hzeroToJ :
        forall k : Fin (m + 3), k.val <= 2 * t -> a.order k = 0 := by
      intro k hk
      exact hzero k (by omega)
    have hiTwo : 2 <= i.val := by
      have hiPositive := i.pos
      omega
    have hiJ : i.val < 2 * t := by omega
    exact a.he2022ClassicLemma32 b hBClassic (2 * t)
      (by omega) (by exact ⟨t, by omega⟩) (by omega)
      hzeroToJ i hiTwo hiJ

/-- Corollary 3.11(i), odd target rank: condition (ii) holds through
paper index `n-2`. -/
theorem he2022ClassicCorollary311iOdd {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 3))
    (hSourceRank : 2 * t + 3 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 3), k.val < 2 * t + 3 ->
      a.order k = 0)
    (halpha : forall k : Fin (m + 2), k.val < 2 * t + 3 ->
      a.alphaValue k = 1)
    (i : RepresentationIndex (m + 3) (2 * t + 3))
    (hiRange : i.val + 2 <= 2 * t + 3) :
    a.HeClassicDefectConditionAt b i := by
  by_cases hiOne : i.val = 1
  · have hfirst : a.order (0 : Fin (m + 3)) = 0 :=
      hzero (0 : Fin (m + 3)) (by simp)
    have hsecond : a.order (1 : Fin (m + 3)) = 0 :=
      hzero (1 : Fin (m + 3)) (by simp)
    have halphaTwo : a.alphaValue (1 : Fin (m + 2)) = 1 :=
      halpha (1 : Fin (m + 2)) (by simp)
    exact a.he2022ClassicLemma33 b hAClassic hBClassic
      hfirst hsecond halphaTwo i hiOne
  · have hzeroToJ :
        forall k : Fin (m + 3), k.val <= 2 * t + 2 -> a.order k = 0 := by
      intro k hk
      exact hzero k (by omega)
    have hiTwo : 2 <= i.val := by
      have hiPositive := i.pos
      omega
    have hiJ : i.val < 2 * t + 2 := by omega
    exact a.he2022ClassicLemma32 b hBClassic (2 * t + 2)
      (by omega) (by exact ⟨t + 1, by omega⟩) (by omega)
      hzeroToJ i hiTwo hiJ

/-- Corollary 3.11(ii), first assertion: for even `n` and `R_(n+1)=0`,
condition (ii) holds through `n-1`. -/
theorem he2022ClassicCorollary311iiInitial {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 2))
    (_hSourceRank : 2 * t + 2 <= m + 3)
    (hNextBound : 2 * t + 2 < m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 3), k.val < 2 * t + 2 ->
      a.order k = 0)
    (halpha : forall k : Fin (m + 2), k.val < 2 * t + 2 ->
      a.alphaValue k = 1)
    (hnext : a.order ⟨2 * t + 2, hNextBound⟩ = 0)
    (i : RepresentationIndex (m + 3) (2 * t + 2))
    (hiRange : i.val < 2 * t + 2) :
    a.HeClassicDefectConditionAt b i := by
  by_cases hiOne : i.val = 1
  · have hfirst : a.order (0 : Fin (m + 3)) = 0 :=
      hzero (0 : Fin (m + 3)) (by simp)
    have hsecond : a.order (1 : Fin (m + 3)) = 0 :=
      hzero (1 : Fin (m + 3)) (by simp)
    have halphaTwo : a.alphaValue (1 : Fin (m + 2)) = 1 :=
      halpha (1 : Fin (m + 2)) (by simp)
    exact a.he2022ClassicLemma33 b hAClassic hBClassic
      hfirst hsecond halphaTwo i hiOne
  · have hzeroToJ :
        forall k : Fin (m + 3), k.val <= 2 * t + 2 -> a.order k = 0 := by
      intro k hk
      by_cases hlt : k.val < 2 * t + 2
      · exact hzero k hlt
      · have heq : k.val = 2 * t + 2 := by omega
        have hindex : k = ⟨2 * t + 2, hNextBound⟩ := by
          apply Fin.ext
          exact heq
        simpa only [hindex] using hnext
    have hiTwo : 2 <= i.val := by
      have hiPositive := i.pos
      omega
    exact a.he2022ClassicLemma32 b hBClassic (2 * t + 2)
      (by omega) (by exact ⟨t + 1, by omega⟩) (by omega)
      hzeroToJ i hiTwo hiRange

/-- An additive `J2'_E` bound is the weak signed-prefix inequality used
by Lemma 3.4. -/
theorem truncatedPrefixDefect_le_one_sub_order_of_add_le
    (R : Int) (D : WithTop ℚ)
    (hadd : ((((R : Int) : ℚ) : WithTop ℚ)) + D <= 1) :
    D <= ((((1 - R : Int) : ℚ) : WithTop ℚ)) := by
  have hDne : D ≠ ⊤ := by
    intro htop
    rw [htop] at hadd
    simp at hadd
  rw [← WithTop.coe_untop D hDne] at hadd ⊢
  norm_cast at hadd ⊢
  push_cast at hadd ⊢
  linarith

/-- The precise consequence of Corollary 3.11(ii) used in Lemma 4.2.
Only `alpha_n = 1` and the weak signed-prefix inequality are needed by
Lemma 3.4 at the final index.  Its additive hypothesis is exactly the
form printed as `J2'_E(n)` in Section 4. -/
theorem he2022ClassicCorollary311ii_of_previousAlpha {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 2))
    (hNextTwoBound : 2 * t + 3 < m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 3), k.val < 2 * t + 2 ->
      a.order k = 0)
    (halpha : forall k : Fin (m + 2), k.val < 2 * t + 2 ->
      a.alphaValue k = 1)
    (hnext : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hfield : ramificationIndex K = 1 ∨
      (1 < ramificationIndex K ∧
        ((((a.order ⟨2 * t + 3, hNextTwoBound⟩ : Int) : ℚ) :
              WithTop ℚ)) +
            a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
              (2 * t + 4) <= 1))
    (i : RepresentationIndex (m + 3) (2 * t + 2)) :
    a.HeClassicDefectConditionAt b i := by
  by_cases hiBefore : i.val < 2 * t + 2
  · exact a.he2022ClassicCorollary311iiInitial t b (by omega) (by omega)
      hAClassic hBClassic hzero halpha hnext i hiBefore
  · have hiLast : i.val = 2 * t + 2 := by
      have := i.le_small
      omega
    have hiEven : Even i.val := by
      exact ⟨t + 1, by omega⟩
    have hprevious :
        a.order (⟨i.val - 1, by omega⟩ : Fin (m + 3)) = 0 := by
      apply hzero
      change i.val - 1 < 2 * t + 2
      omega
    have halphaPrevious :
        a.alphaValue (⟨i.val - 1, by omega⟩ : Fin (m + 2)) = 1 := by
      apply halpha
      change i.val - 1 < 2 * t + 2
      omega
    apply a.he2022ClassicLemma34 b hAClassic hBClassic i hiEven
      (by omega)
      hprevious
      (by
        have hindex : (⟨i.val, i.lt_large⟩ : Fin (m + 3)) =
            ⟨2 * t + 2, by omega⟩ := by
          apply Fin.ext
          exact hiLast
        rw [hindex]
        exact hnext)
      halphaPrevious
    rcases hfield with heOne | ⟨heLarge, hdefect⟩
    · exact Or.inl heOne
    · right
      refine ⟨heLarge, ?_⟩
      have hiFormula : (i.val + 2) / 2 = t + 2 := by omega
      have hLength : i.val + 2 = 2 * t + 4 := by omega
      rw [hiFormula, hLength]
      have hOrderIndex :
          (⟨i.val + 1, by omega⟩ : Fin (m + 3)) =
            ⟨2 * t + 3, hNextTwoBound⟩ := by
        apply Fin.ext
        change i.val + 1 = 2 * t + 3
        omega
      rw [hOrderIndex]
      exact truncatedPrefixDefect_le_one_sub_order_of_add_le
        (a.order ⟨2 * t + 3, hNextTwoBound⟩) _ hdefect

/-- Corollary 3.11(ii), literal full assertion through paper index `n`.
The publisher explicitly assumes `alpha_(n+1)=1` and a signed-prefix
equality.  Both imply the weaker endpoint data isolated above. -/
theorem he2022ClassicCorollary311ii {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 2))
    (hNextTwoBound : 2 * t + 3 < m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 3), k.val < 2 * t + 2 ->
      a.order k = 0)
    (halpha : forall k : Fin (m + 2), k.val < 2 * t + 2 ->
      a.alphaValue k = 1)
    (hnext : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (_halphaNext : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hfield : ramificationIndex K = 1 ∨
      (1 < ramificationIndex K ∧
        a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) =
          ((((1 - a.order ⟨2 * t + 3, hNextTwoBound⟩ : Int) : ℚ) :
            WithTop ℚ))))
    (i : RepresentationIndex (m + 3) (2 * t + 2)) :
    a.HeClassicDefectConditionAt b i := by
  apply a.he2022ClassicCorollary311ii_of_previousAlpha t b
    hNextTwoBound hAClassic hBClassic hzero halpha hnext
  · rcases hfield with heOne | ⟨heLarge, hdefect⟩
    · exact Or.inl heOne
    · refine Or.inr ⟨heLarge, ?_⟩
      rw [hdefect]
      norm_cast
      linarith

/-- Corollary 3.11(iii): for odd `n`, the signed-prefix equality extends
condition (ii) over all paper indices `1 <= i <= n`. -/
theorem he2022ClassicCorollary311iii {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 3))
    (hSourceBound : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 3), k.val < 2 * t + 3 ->
      a.order k = 0)
    (halpha : forall k : Fin (m + 2), k.val < 2 * t + 3 ->
      a.alphaValue k = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)))
    (i : RepresentationIndex (m + 3) (2 * t + 3)) :
    a.HeClassicDefectConditionAt b i := by
  by_cases hiInitial : i.val + 2 <= 2 * t + 3
  · exact a.he2022ClassicCorollary311iOdd t b (by omega)
      hAClassic hBClassic
      hzero halpha i hiInitial
  · by_cases hiPenultimate : i.val = 2 * t + 2
    · have hiEven : Even i.val := ⟨t + 1, by omega⟩
      have hprevious :
          a.order (⟨i.val - 1, by omega⟩ : Fin (m + 3)) = 0 := by
        apply hzero
        change i.val - 1 < 2 * t + 3
        omega
      have hcurrent :
          a.order (⟨i.val, i.lt_large⟩ : Fin (m + 3)) = 0 := by
        apply hzero
        change i.val < 2 * t + 3
        omega
      have halphaPrevious :
          a.alphaValue (⟨i.val - 1, by omega⟩ : Fin (m + 2)) = 1 := by
        apply halpha
        change i.val - 1 < 2 * t + 3
        omega
      apply a.he2022ClassicLemma34 b hAClassic hBClassic i hiEven
        (by omega)
        hprevious hcurrent halphaPrevious
      have hePos := ramificationIndex_pos (K := K)
      rcases eq_or_lt_of_le (Nat.succ_le_iff.mpr hePos) with heOne | heLarge
      · exact Or.inl heOne.symm
      · right
        refine ⟨heLarge, ?_⟩
        have hiFormula : (i.val + 2) / 2 = t + 2 := by omega
        have hLength : i.val + 2 = 2 * t + 4 := by omega
        rw [hiFormula, hLength]
        have hOrderIndex :
            (⟨i.val + 1, by omega⟩ : Fin (m + 3)) =
              ⟨2 * t + 3, by omega⟩ := by
          apply Fin.ext
          change i.val + 1 = 2 * t + 3
          omega
        rw [hOrderIndex]
        exact le_of_eq hSourceEquality
    · have hiLast : i.val = 2 * t + 3 := by
        have := i.le_small
        omega
      have hterminal := a.he2022ClassicLemma36DefectConditionLongSource t b
        hSourceBound hAClassic hBClassic
        (hzero ⟨2 * t + 1, by omega⟩ (by
          change 2 * t + 1 < 2 * t + 3
          omega))
        (hzero ⟨2 * t + 2, by omega⟩ (by
          change 2 * t + 2 < 2 * t + 3
          omega))
        (halpha ⟨2 * t + 2, by omega⟩ (by
          change 2 * t + 2 < 2 * t + 3
          omega))
        hSourceEquality
      let terminalIndex : RepresentationIndex (m + 3) (2 * t + 3) :=
        { val := 2 * t + 3
          pos := by omega
          lt_large := by omega
          le_small := by omega }
      have hiEq : i = terminalIndex := by
        apply RepresentationIndex.ext
        exact hiLast
      rw [hiEq]
      exact hterminal

end BONG.GoodBONG

end Bong
