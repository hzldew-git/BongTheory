/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicSectionFour
import Bong.Bong.He2022ClassicCorollary311
import Bong.Bong.He2022ClassicPublishedTestingSet
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm

/-!
# He (2024), Lemma 4.2

The two published tests are used literally: `C₁ⁿ(ω)` forces the first
source order to vanish, while `H_eⁿ(1)` forces the terminal adjacent
source pair to vanish.  Proposition 2.4(v) then gives the whole zero
prefix occurring in `J1'_E(n)`.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The first `pairs` hyperbolic blocks of the published row `H_e^n(c)`
have signed determinant `(-1)^pairs`.  This is the exact prefix-product
calculation used in assertion (c) of Lemma 4.2. -/
theorem heClassicEvenH_prefixProduct_even
    (pairs : Nat) (hOneOrder : ordUnit K (1 : Kˣ) = 0)
    (j : Nat) (hj : j <= pairs) :
    let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
    b.prefixProduct (2 * j) = (-1 : Kˣ) ^ j := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
  induction j with
  | zero =>
      simpa only [Nat.mul_zero, pow_zero, GoodBONG.prefixProduct] using
        (heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl)
          hOneOrder).toBONG.prefixProduct_zero
  | succ j ih =>
      have hjlt : j < pairs := by omega
      have hevenBound : 2 * j < 2 * pairs + 2 := by omega
      have hoddBound : 2 * j + 1 < 2 * pairs + 2 := by omega
      have hevenBefore : 2 * j < 2 * pairs + 1 := by omega
      have hoddBefore : 2 * j + 1 < 2 * pairs + 1 := by omega
      unfold GoodBONG.prefixProduct at ih ⊢
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega,
        b.toBONG.prefixProduct_succ (2 * j + 1) hoddBound,
        b.toBONG.prefixProduct_succ (2 * j) hevenBound,
        ih (by omega)]
      have hevenValue : b.toBONG.valueUnit
          (⟨2 * j, hevenBound⟩ : Fin (2 * pairs + 2)) =
          uniformizerPowerUnit K (ramificationIndex K : Int) := by
        change b.valueUnit _ = _
        simp only [b, heClassicEvenHGoodBONG,
          heHuExactGoodBONG_valueUnit]
        rw [heClassicEvenH_beforeLast pairs 1 _ hevenBefore]
        exact heClassicScaledHyperbolicTower_even
          (⟨j, by omega⟩ : Fin (pairs + 1))
      have hoddValue : b.toBONG.valueUnit
          (⟨2 * j + 1, hoddBound⟩ : Fin (2 * pairs + 2)) =
          -(uniformizerPowerUnit K (-(ramificationIndex K : Int))) := by
        change b.valueUnit _ = _
        simp only [b, heClassicEvenHGoodBONG,
          heHuExactGoodBONG_valueUnit]
        rw [heClassicEvenH_beforeLast pairs 1 _ hoddBefore]
        exact heClassicScaledHyperbolicTower_odd
          (⟨j, by omega⟩ : Fin (pairs + 1))
      rw [hevenValue, hoddValue, pow_succ]
      unfold uniformizerPowerUnit
      rw [mul_neg, mul_assoc, ← zpow_add]
      simp

/-- In `H_e^n(1)`, the alpha invariant immediately before the final
hyperbolic block is `2e`; equivalently this is the target cap occurring in
the secondary candidate of `A_n`. -/
theorem heClassicEvenH_alpha_beforeFinalBlock
    (pairs : Nat) (hpairs : 0 < pairs)
    (hOneOrder : ordUnit K (1 : Kˣ) = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
    b.alphaValue (⟨2 * pairs - 1, by omega⟩ : Fin (2 * pairs + 1)) =
      2 * (ramificationIndex K : ℚ) := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
  let gap : Fin (2 * pairs + 1) := ⟨2 * pairs - 1, by omega⟩
  have hgap : b.orderGap gap = 2 * (ramificationIndex K : Int) := by
    unfold orderGap
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenH_order pairs 1 hOneOrder,
      heClassicEvenH_order pairs 1 hOneOrder]
    have hodd : ¬ Even gap.val := by
      apply Nat.not_even_iff_odd.mpr
      refine ⟨pairs - 1, ?_⟩
      dsimp only [gap]
      omega
    have heven : Even (gap.val + 1) := by
      refine ⟨pairs, ?_⟩
      dsimp only [gap]
      omega
    have hoddCast : ¬ Even gap.castSucc.val := by
      simpa only [Fin.val_castSucc] using hodd
    have hevenSucc : Even gap.succ.val := by
      simpa only [Fin.val_succ] using heven
    rw [if_pos hevenSucc, if_neg hoddCast]
    ring
  exact ((b.he2022ClassicProposition22).compareTwoE gap).2.1.mpr hgap

/-- The target-side cap in the secondary `A_n` candidate for `H_e^n(1)`.
The binary case has an empty target prefix and hence cap `top`. -/
theorem heClassicEvenH_secondaryPrefixCap
    (pairs : Nat) (hOneOrder : ordUnit K (1 : Kˣ) = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
    b.prefixAlphaCap (2 * pairs) =
      if pairs = 0 then ⊤
      else ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
  by_cases hpairs : pairs = 0
  · subst pairs
    simp
  · have hpairsPos : 0 < pairs := Nat.pos_of_ne_zero hpairs
    rw [if_neg hpairs]
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
    have hindex :
        (⟨2 * pairs - 1, by omega⟩ : Fin (2 * pairs + 1)) =
          ⟨2 * pairs - 1, by omega⟩ := Fin.ext rfl
    rw [hindex, heClassicEvenH_alpha_beforeFinalBlock pairs hpairsPos hOneOrder]

/-- The mixed capped defect in the secondary candidate for `A_n` is the
source signed-prefix defect, with the additional target cap `2e`; at rank
two the target prefix is empty and that extra cap is absent. -/
theorem heClassicEvenH_secondaryPrefixDefect
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hOneOrder : ordUnit K (1 : Kˣ) = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
    a.truncatedPrefixDefect b 1 (2 * pairs + 4) (2 * pairs) =
      if pairs = 0 then
        a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0 (2 * pairs + 4)
      else
        min (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
            (2 * pairs + 4))
          (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
  have hbProduct : b.prefixProduct (2 * pairs) = (-1 : Kˣ) ^ pairs := by
    simpa only [b] using
      (heClassicEvenH_prefixProduct_even (K := K) pairs hOneOrder pairs le_rfl)
  have hbCap : b.prefixAlphaCap (2 * pairs) =
      if pairs = 0 then ⊤
      else ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    simpa only [b] using
      (heClassicEvenH_secondaryPrefixCap (K := K) pairs hOneOrder)
  have hsign : (-1 : Kˣ) ^ (pairs + 2) = (-1 : Kˣ) ^ pairs := by
    rw [pow_add]
    norm_num
  unfold truncatedPrefixDefect
  rw [hbProduct, hbCap, a.prefixAlphaCap_zero,
    show a.prefixProduct 0 = 1 from a.toBONG.prefixProduct_zero]
  simp only [GoodBONG.prefixProduct, one_mul]
  rw [hsign]
  by_cases hpairs : pairs = 0
  · simp [hpairs, mul_comm]
  · simp [hpairs, min_comm, min_left_comm, mul_comm]

/-- The final alpha invariant of `H_e^n(1)` is zero, because its last order
gap is `-2e`. -/
theorem heClassicEvenH_finalAlpha
    (pairs : Nat) (hOneOrder : ordUnit K (1 : Kˣ) = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
    b.alphaValue (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) = 0 := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
  let gap : Fin (2 * pairs + 1) := ⟨2 * pairs, by omega⟩
  apply ((b.he2022ClassicProposition23 gap).alphaZero).2
  unfold orderGap
  simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenH_order pairs 1 hOneOrder,
    heClassicEvenH_order pairs 1 hOneOrder]
  have heven : Even gap.castSucc.val := by
    change Even (2 * pairs)
    exact even_two_mul pairs
  have hodd : ¬ Even gap.succ.val := by
    change ¬ Even (2 * pairs + 1)
    exact Nat.not_even_two_mul_add_one pairs
  rw [if_neg hodd, if_pos heven]
  ring

/-- Consequently the prefix of length `n-1` in `H_e^n(1)` has zero cap. -/
theorem heClassicEvenH_primaryPrefixCap
    (pairs : Nat) (hOneOrder : ordUnit K (1 : Kˣ) = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
    b.prefixAlphaCap (2 * pairs + 1) = 0 := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
  rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
  have hindex :
      (⟨2 * pairs + 1 - 1, by omega⟩ : Fin (2 * pairs + 1)) =
        ⟨2 * pairs, by omega⟩ := by
    apply Fin.ext
    change 2 * pairs + 1 - 1 = 2 * pairs
    omega
  rw [hindex, heClassicEvenH_finalAlpha pairs hOneOrder]
  norm_num

/-- The displayed three-candidate formula for
`A_n(M,H_e^n(1))` in the proof of Lemma 4.2.  The third candidate carries
the `2e` cap only when `n > 2`. -/
theorem he2022Classic_evenH_lastRepresentationAlpha
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hzero : forall j : Fin (m + 3), j.val <= 2 * pairs + 2 ->
      a.order j = 0)
    (hOneOrder : ordUnit K (1 : Kˣ) = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
    let last : RepresentationIndex (m + 3) (2 * pairs + 2) :=
      { val := 2 * pairs + 2
        pos := by omega
        lt_large := by omega
        le_small := by omega }
    a.representationAlpha b last =
      min
        (((((ramificationIndex K : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ))) : WithTop ℚ)
        (min
          (((ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
          (((((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            if pairs = 0 then
              a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
                (2 * pairs + 4)
            else
              min (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
                  (2 * pairs + 4))
                (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))))) := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) hOneOrder
  let last : RepresentationIndex (m + 3) (2 * pairs + 2) :=
    { val := 2 * pairs + 2
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hbLast : b.order (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      -(ramificationIndex K : Int) := by
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenH_order pairs 1 hOneOrder]
    have hodd : ¬ Even (2 * pairs + 1) :=
      Nat.not_even_two_mul_add_one pairs
    rw [if_neg hodd]
  have hbPrevious : b.order (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
      (ramificationIndex K : Int) := by
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenH_order pairs 1 hOneOrder]
    rw [if_pos (even_two_mul pairs)]
  have hprimaryDefect :
      a.truncatedPrefixDefect b (-1) (2 * pairs + 3) (2 * pairs + 1) = 0 := by
    apply le_antisymm
    · calc
        a.truncatedPrefixDefect b (-1) (2 * pairs + 3) (2 * pairs + 1) <=
            b.prefixAlphaCap (2 * pairs + 1) :=
          a.truncatedPrefixDefect_le_rightCap b (-1)
            (2 * pairs + 3) (2 * pairs + 1)
        _ = 0 := heClassicEvenH_primaryPrefixCap pairs hOneOrder
    · exact a.truncatedPrefixDefect_nonneg b (-1)
        (2 * pairs + 3) (2 * pairs + 1)
  have hsecondaryDefect :
      a.truncatedPrefixDefect b 1 (2 * pairs + 4) (2 * pairs) =
        if pairs = 0 then
          a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
            (2 * pairs + 4)
        else
          min (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
              (2 * pairs + 4))
            (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) := by
    simpa only [b] using
      (heClassicEvenH_secondaryPrefixDefect (K := K) pairs a hOneOrder)
  rw [a.representationAlpha_eq_min_halfGap_prime b last,
    a.representationAlphaPrime_eq_min_primary_secondary b last (by
      dsimp only [last]
      omega)]
  unfold representationHalfGap representationPrimaryDefect
    representationSecondaryDefect
  dsimp only [last]
  have hsubOne : 2 * pairs + 2 - 1 = 2 * pairs + 1 := by omega
  have hsubTwo : 2 * pairs + 2 - 2 = 2 * pairs := by omega
  have haddOne : 2 * pairs + 2 + 1 = 2 * pairs + 3 := by omega
  have haddTwo : 2 * pairs + 2 + 2 = 2 * pairs + 4 := by omega
  have hsourceCurrent :
      a.order (⟨2 * pairs + 2, by omega⟩ : Fin (m + 3)) = 0 :=
    hzero (⟨2 * pairs + 2, by omega⟩ : Fin (m + 3)) (by
      change 2 * pairs + 2 <= 2 * pairs + 2
      exact le_rfl)
  simp only [hsubOne, hsubTwo, haddOne, haddTwo, hsourceCurrent,
    hbLast, hbPrevious, hprimaryDefect,
    hsecondaryDefect]
  norm_num

set_option maxHeartbeats 800000 in
-- The explicit published test rows unfold through exact diagonal realizations.

/-- The literal two-test middle statement in Lemma 4.2: conditions (i)--(ii)
hold for `C₁ⁿ(ω)` and `H_eⁿ(1)`.  Keeping this predicate separate from
the universal quantification makes the advertised testing reduction directly
auditable. -/
noncomputable def HeClassicLemma42PublishedTests
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hRank : 2 * t + 1 <= m + 2) : Prop :=
  let omegaUnit : Kˣ := heClassicOmega (K := K)
  let bC1 := heClassicEvenC1GoodBONG (K := K) t omegaUnit
    (by rw [heClassicOmega_order (K := K)])
  let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let bH := heClassicEvenHGoodBONG (K := K) t 1 (Or.inl rfl) oneOrder
  (a.RepresentationOrderCondition bC1 hRank ∧
      a.RepresentationDefectCondition bC1) ∧
    (a.RepresentationOrderCondition bH hRank ∧
      a.RepresentationDefectCondition bH)

/-- Assertion (a) in the necessity proof of Lemma 4.2, using only the
two printed tests. -/
theorem he2022ClassicLemma42_orders_of_publishedTests
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hTests : a.HeClassicLemma42PublishedTests t (by omega)) :
    forall i : Fin (2 * t + 3),
      a.order ⟨i.val, by omega⟩ = 0 := by
  unfold HeClassicLemma42PublishedTests at hTests
  dsimp only at hTests
  let omegaUnit : Kˣ := heClassicOmega (K := K)
  have homegaOrder : ordUnit K omegaUnit = 0 :=
    heClassicOmega_order (K := K)
  let bC1 := heClassicEvenC1GoodBONG (K := K) t omegaUnit
    (by rw [homegaOrder])
  have hC1 := hTests.1
  have hfirstLe := hC1.1 (0 : Fin (2 * t + 2))
  have hfirstLe' : a.order (0 : Fin (m + 3)) <= 0 := by
    rcases hfirstLe with hleft | hright
    · have htarget : bC1.order (0 : Fin (2 * t + 2)) = 0 := by
        simp only [bC1, heClassicEvenC1GoodBONG,
          heHuExactGoodBONG_order]
        rw [heClassicEvenC1_order]
        change (if (0 : Nat) = 2 * t + 1 then ordUnit K omegaUnit else 0) = 0
        simp
      change a.order (0 : Fin (m + 3)) <=
        bC1.order (0 : Fin (2 * t + 2)) at hleft
      simpa only [htarget] using hleft
    · rcases hright with ⟨hpositive, _⟩
      exact (Nat.not_lt_zero _ hpositive).elim
  have hfirstNonnegative : 0 <= a.order (0 : Fin (m + 3)) :=
    ((a.he2022ClassicProposition24 hAClassic).oddIndexed
      0 0 le_rfl Even.zero Even.zero).1
  have hfirst : a.order (0 : Fin (m + 3)) = 0 := by omega
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let bH := heClassicEvenHGoodBONG (K := K) t 1 (Or.inl rfl)
    honeOrder
  have hH := hTests.2
  let last : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
  have hlastCondition := hH.1 last
  have hnonnegative :=
    (a.he2022ClassicProposition24 hAClassic).nonnegativeOfFirstZero hfirst
  have hpair :
      a.order (⟨2 * t + 1, by omega⟩ : Fin (m + 3)) +
        a.order (⟨2 * t + 2, by omega⟩ : Fin (m + 3)) <= 0 := by
    rcases hlastCondition with hleft | hright
    · have hsourceNonnegative :=
        hnonnegative (⟨last.val, by omega⟩ : Fin (m + 3))
      have htarget : bH.order last = -(ramificationIndex K : Int) := by
        simp only [bH, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
        rw [heClassicEvenH_order t 1 honeOrder]
        have hlastOdd : Odd last.val := by
          refine ⟨t, ?_⟩
          dsimp only [last]
        have hodd : ¬ Even last.val :=
          Nat.not_even_iff_odd.mpr hlastOdd
        rw [if_neg hodd]
      rw [htarget] at hleft
      have hePos := ramificationIndex_pos (K := K)
      omega
    · rcases hright with ⟨_hpositive, _hbound, hsum⟩
      have hprevious : bH.order
          (⟨last.val - 1, by omega⟩ : Fin (2 * t + 2)) =
            (ramificationIndex K : Int) := by
        simp only [bH, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
        rw [heClassicEvenH_order t 1 honeOrder]
        have heven : Even (last.val - 1) := by
          refine ⟨t, ?_⟩
          dsimp only [last]
          omega
        rw [if_pos heven]
      have hcurrent : bH.order last = -(ramificationIndex K : Int) := by
        simp only [bH, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
        rw [heClassicEvenH_order t 1 honeOrder]
        have hlastOdd : Odd last.val := by
          refine ⟨t, ?_⟩
          dsimp only [last]
        have hodd : ¬ Even last.val :=
          Nat.not_even_iff_odd.mpr hlastOdd
        rw [if_neg hodd]
      have hsourceCurrent :
          (⟨last.val, by omega⟩ : Fin (m + 3)) =
            ⟨2 * t + 1, by omega⟩ := Fin.ext (by simp [last])
      have hsourceNext :
          (⟨last.val + 1, by omega⟩ : Fin (m + 3)) =
            ⟨2 * t + 2, by omega⟩ := Fin.ext (by simp [last])
      have htargetPrevious :
          (⟨last.val - 1, by omega⟩ : Fin (2 * t + 2)) =
            ⟨2 * t, by omega⟩ := Fin.ext (by simp [last])
      have hpreviousExplicit :
          bH.order (⟨2 * t, by omega⟩ : Fin (2 * t + 2)) =
            (ramificationIndex K : Int) := by
        rw [← htargetPrevious]
        exact hprevious
      change a.order ⟨last.val, by omega⟩ +
          a.order ⟨last.val + 1, by omega⟩ <=
        bH.order ⟨last.val - 1, by omega⟩ + bH.order last at hsum
      rw [hsourceCurrent, hsourceNext, htargetPrevious,
        hpreviousExplicit, hcurrent] at hsum
      have htargetSum : (ramificationIndex K : Int) +
          -(ramificationIndex K : Int) = 0 := by ring
      rw [htargetSum] at hsum
      exact hsum
  have hleftNonnegative :=
    hnonnegative (⟨2 * t + 1, by omega⟩ : Fin (m + 3))
  have hrightNonnegative :=
    hnonnegative (⟨2 * t + 2, by omega⟩ : Fin (m + 3))
  have hleftZero :
      a.order (⟨2 * t + 1, by omega⟩ : Fin (m + 3)) = 0 := by omega
  have hrightZero :
      a.order (⟨2 * t + 2, by omega⟩ : Fin (m + 3)) = 0 := by omega
  let boundary : Fin (m + 2) := ⟨2 * t + 1, by omega⟩
  have hprefix :=
    (a.he2022ClassicProposition24 hAClassic).zeroPairForcesPrefixZero
      boundary
      (by
        have hindex : boundary.castSucc =
            (⟨2 * t + 1, by omega⟩ : Fin (m + 3)) := Fin.ext rfl
        rw [hindex]
        exact hleftZero)
      (by
        have hindex : boundary.succ =
            (⟨2 * t + 2, by omega⟩ : Fin (m + 3)) := Fin.ext rfl
        rw [hindex]
        exact hrightZero)
  intro i
  have hi : (⟨i.val, by omega⟩ : Fin (m + 3)) <= boundary.succ := by
    apply Fin.mk_le_mk.mpr
    change i.val <= 2 * t + 2
    omega
  exact hprefix _ hi

/-- The lower estimate hidden in the displayed identity
`A_1=min{e,d[-a_1,2]}` in the proof of Lemma 4.2.  It is proved directly
from the three candidates defining `A_1`. -/
theorem he2022Classic_alphaOne_le_firstRepresentationAlpha
    {m n : Nat} (a : GoodBONG q L (m + 3))
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (n + 2))
    (hzero : forall j : Fin (m + 3), j.val <= 2 -> a.order j = 0)
    (htarget : b.order (0 : Fin (n + 2)) = 0)
    (i : RepresentationIndex (m + 3) (n + 2)) (hi : i.val = 1) :
    (a.alphaValue (0 : Fin (m + 2)) : WithTop ℚ) <=
      a.representationAlpha b i := by
  rw [a.representationAlpha_eq_min_halfGap_prime b i,
    a.representationAlphaPrime_eq_primary_of_not_interior b i (by omega)]
  apply le_min
  · have hhalf := a.alphaValue_le_halfGapValue (0 : Fin (m + 2))
    unfold halfGapValue orderGap at hhalf
    unfold representationHalfGap
    have hsourceIndex :
        (⟨i.val, i.lt_large⟩ : Fin (m + 3)) = 1 := Fin.ext hi
    have htargetIndex :
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) = 0 := by
      apply Fin.ext
      simp [hi]
    rw [hzero _ (by simp), hzero _ (by simp)] at hhalf
    rw [hsourceIndex, htargetIndex, hzero 1 (by simp), htarget]
    norm_num at hhalf ⊢
    rw [← a.coe_alphaValue]
    exact_mod_cast hhalf
  · unfold representationPrimaryDefect
    have hsourceIndex :
        (⟨i.val, i.lt_large⟩ : Fin (m + 3)) = 1 := Fin.ext hi
    have htargetIndex :
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) = 0 := by
      apply Fin.ext
      simp [hi]
    rw [hsourceIndex, htargetIndex, hzero 1 (by simp), htarget]
    norm_num
    simp [hi]
    unfold truncatedPrefixDefect
    apply le_min
    · have hraw := a.alpha_le_rightDefectCandidate
          (i := (0 : Fin (m + 2))) (j := (0 : Fin (m + 2))) le_rfl
      unfold rightDefectCandidate at hraw
      change a.alpha (0 : Fin (m + 2)) <=
          (((a.order (1 : Fin (m + 3)) -
            a.order (0 : Fin (m + 3)) : Int) : ℚ) : WithTop ℚ) +
            a.adjacentDefect (0 : Fin (m + 2)) at hraw
      rw [hzero 0 (by simp), hzero 1 (by simp)] at hraw
      norm_num at hraw
      have hproduct :
          (-1 : Kˣ) * a.prefixProduct 2 * b.prefixProduct 0 =
            a.adjacentProduct (0 : Fin (m + 2)) := by
        unfold GoodBONG.prefixProduct adjacentProduct
        rw [BONG.prefixProduct_zero,
          a.toBONG.prefixProduct_succ 1 (by omega),
          a.toBONG.prefixProduct_succ 0 (by omega),
          BONG.prefixProduct_zero]
        have hcast : (0 : Fin (m + 2)).castSucc =
            (0 : Fin (m + 3)) := Fin.ext rfl
        have hsucc : (0 : Fin (m + 2)).succ =
            (1 : Fin (m + 3)) := Fin.ext rfl
        rw [hcast, hsucc]
        unfold GoodBONG.valueUnit
        simp
      rw [hproduct]
      simpa only [adjacentDefect] using hraw
    · apply le_min
      · rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
        have hmono :=
          (a.he2022ClassicProposition22).endpointMonotonicity
            (0 : Fin (m + 2)) (1 : Fin (m + 2)) (by simp)
        unfold alphaLeftEndpoint at hmono
        have hmonoLeft := hmono.1
        change (a.order (0 : Fin (m + 3)) : ℚ) +
            a.alphaValue (0 : Fin (m + 2)) <=
          (a.order (1 : Fin (m + 3)) : ℚ) +
            a.alphaValue (1 : Fin (m + 2)) at hmonoLeft
        rw [hzero 0 (by simp), hzero 1 (by simp)] at hmonoLeft
        norm_num at hmonoLeft
        have hindex : (⟨2 - 1, by omega⟩ : Fin (m + 2)) = 1 := Fin.ext rfl
        rw [hindex]
        rw [← a.coe_alphaValue]
        exact_mod_cast hmonoLeft
      · rw [b.prefixAlphaCap_zero]
        exact le_top

/-- Assertions (a)--(b) in the necessity proof: the two printed tests
force `J1'_E(n)`. -/
theorem he2022ClassicLemma42_j1Prime_of_publishedTests
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hTests : a.HeClassicLemma42PublishedTests t (by omega)) :
    a.HeClassicJ1EPrime (2 * t + 2) (by omega) := by
  have horders := a.he2022ClassicLemma42_orders_of_publishedTests t
    hSource hAClassic hTests
  have hTests' := hTests
  unfold HeClassicLemma42PublishedTests at hTests'
  dsimp only at hTests'
  let omegaUnit : Kˣ := heClassicOmega (K := K)
  have homegaOrder : ordUnit K omegaUnit = 0 :=
    heClassicOmega_order (K := K)
  let bC1 := heClassicEvenC1GoodBONG (K := K) t omegaUnit
    (by rw [homegaOrder])
  have hC1 := hTests'.1
  let first : RepresentationIndex (m + 3) (2 * t + 2) :=
    { val := 1
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have htargetOrder : bC1.order (0 : Fin (2 * t + 2)) = 0 := by
    simp only [bC1, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    change (if (0 : Nat) = 2 * t + 1 then ordUnit K omegaUnit else 0) = 0
    simp
  have hsourceLower := a.he2022Classic_alphaOne_le_firstRepresentationAlpha
    bC1 (fun j hj => horders ⟨j.val, by omega⟩) htargetOrder first rfl
  have hdefect := hC1.2 first
  have htargetCap := a.truncatedPrefixDefect_le_rightCap
    bC1 1 first.val first.val
  rw [bC1.prefixAlphaCap_of_internal (by simp [first]) (by
      dsimp only [first]
      omega)] at htargetCap
  have hcapIndex :
      (⟨first.val - 1, by dsimp only [first]; omega⟩ : Fin (2 * t + 1)) = 0 := by
    apply Fin.ext
    dsimp only [first]
    norm_num
  rw [hcapIndex] at htargetCap
  have hbeta : bC1.alphaValue (0 : Fin (2 * t + 1)) = 1 := by
    have hall := heClassicEvenC1_alpha_eq_one (K := K) t omegaUnit 1
      (by rw [homegaOrder]) (Or.inr rfl)
      (by rw [homegaOrder]; norm_num)
      (by
        rw [heClassicOmega_defect (K := K)]
        norm_num)
    exact hall 0
  rw [hbeta] at htargetCap
  have halphaUpperTop :
      (a.alphaValue (0 : Fin (m + 2)) : WithTop ℚ) <= 1 := by
    calc
      (a.alphaValue (0 : Fin (m + 2)) : WithTop ℚ) <=
          a.representationAlpha bC1 first := hsourceLower
      _ = (a.representationAlphaValue bC1 first : WithTop ℚ) :=
        (a.coe_representationAlphaValue bC1 first).symm
      _ <= a.truncatedPrefixDefect bC1 1 first.val first.val := hdefect
      _ <= (1 : WithTop ℚ) := htargetCap
  have halphaUpper : a.alphaValue (0 : Fin (m + 2)) <= 1 := by
    exact_mod_cast halphaUpperTop
  let terminal : Fin (m + 2) := ⟨2 * t + 2, by omega⟩
  have hzeroPrefix : forall j : Fin (m + 3),
      j <= terminal.castSucc -> a.order j = 0 := by
    intro j hj
    have hjBound : j.val < 2 * t + 3 := by
      have hjVal : j.val <= 2 * t + 2 := by
        have hjVal' := Fin.mk_le_mk.mp hj
        change j.val <= 2 * t + 2 at hjVal'
        exact hjVal'
      omega
    have hjZero := horders ⟨j.val, hjBound⟩
    have hsourceIndex :
        (⟨j.val, by omega⟩ : Fin (m + 3)) = j := Fin.ext rfl
    rw [hsourceIndex] at hjZero
    exact hjZero
  have halphas :=
    (a.he2022ClassicProposition24 hAClassic).alphaOneOnZeroPrefix
      terminal hzeroPrefix (0 : Fin (m + 2)) (Fin.zero_le terminal)
        halphaUpper
  constructor
  · intro i
    exact horders i
  · intro i
    let sourceGap : Fin (m + 2) := ⟨i.val, by omega⟩
    have hlt : sourceGap < terminal := by
      apply Fin.mk_lt_mk.mpr
      exact i.isLt
    exact halphas sourceGap hlt

set_option maxHeartbeats 800000 in
/-- Assertion (c) in the necessity proof: the printed tests, specifically
`H_e^n(1)`, force `J2'_E(n)` whenever `e > 1`. -/
theorem he2022ClassicLemma42_j2Prime_of_publishedTests
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hTests : a.HeClassicLemma42PublishedTests t (by omega)) :
    a.HeClassicJ2EPrime (2 * t + 2) (by omega) := by
  unfold HeClassicJ2EPrime
  intro heLarge
  have hJ1 := a.he2022ClassicLemma42_j1Prime_of_publishedTests t
    hSource hAClassic hTests
  have hTests' := hTests
  unfold HeClassicLemma42PublishedTests at hTests'
  dsimp only at hTests'
  have hzero : forall j : Fin (m + 3), j.val <= 2 * t + 2 ->
      a.order j = 0 := by
    intro j hj
    let small : Fin (2 * t + 3) := ⟨j.val, by omega⟩
    have hz := hJ1.1 small
    have hindex :
        (⟨small.val, by omega⟩ : Fin (m + 3)) = j := Fin.ext rfl
    rw [hindex] at hz
    exact hz
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let bH := heClassicEvenHGoodBONG (K := K) t 1 (Or.inl rfl)
    honeOrder
  have hH := hTests'.2
  let last : RepresentationIndex (m + 3) (2 * t + 2) :=
    { val := 2 * t + 2
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hcondition := hH.2 last
  have hleftCap := a.truncatedPrefixDefect_le_leftCap
    bH 1 last.val last.val
  rw [a.prefixAlphaCap_of_internal (by dsimp only [last]; omega)
      (by dsimp only [last]; omega)] at hleftCap
  have hcapIndex :
      (⟨last.val - 1, by dsimp only [last]; omega⟩ : Fin (m + 2)) =
        ⟨2 * t + 1, by omega⟩ := by
    apply Fin.ext
    dsimp only [last]
    omega
  have halphaN :
      a.alphaValue (⟨2 * t + 1, by omega⟩ : Fin (m + 2)) = 1 := by
    let small : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
    have h := hJ1.2 small
    simpa only [small] using h
  rw [hcapIndex, halphaN] at hleftCap
  have hAlphaUpper : a.representationAlpha bH last <= (1 : WithTop ℚ) := by
    calc
      a.representationAlpha bH last =
          (a.representationAlphaValue bH last : WithTop ℚ) :=
        (a.coe_representationAlphaValue bH last).symm
      _ <= a.truncatedPrefixDefect bH 1 last.val last.val := hcondition
      _ <= (1 : WithTop ℚ) := hleftCap
  have hformula := a.he2022Classic_evenH_lastRepresentationAlpha
    t hSource hzero honeOrder
  have hlastFormula : a.representationAlpha bH last =
      min
        (((((ramificationIndex K : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ))) : WithTop ℚ)
        (min
          (((ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
          (((((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            if t = 0 then
              a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
                (2 * t + 4)
            else
              min (a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
                  (2 * t + 4))
                (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))))) := by
    simpa only [bH, last] using hformula
  rw [hlastFormula, min_le_iff, min_le_iff] at hAlphaUpper
  have heQ : (1 : ℚ) < (ramificationIndex K : ℚ) := by
    exact_mod_cast heLarge
  have hhalfQ : (1 : ℚ) <
      (ramificationIndex K : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by linarith
  have heTop : (1 : WithTop ℚ) <
      (((ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    exact_mod_cast heQ
  have hhalfTop : (1 : WithTop ℚ) <
      (((ramificationIndex K : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hhalfQ
  let D : WithTop ℚ :=
    a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4)
  let R : WithTop ℚ :=
    ((((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ))
  let E : WithTop ℚ :=
    ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
  have hthird : R + (if t = 0 then D else min D E) <= 1 := by
    rcases hAlphaUpper with hhalf | heCandidate | hthird
    · exact (not_le_of_gt hhalfTop hhalf).elim
    · exact (not_le_of_gt heTop heCandidate).elim
    · simpa only [R, D, E] using hthird
  have hfirstZero : a.order (0 : Fin (m + 3)) = 0 := hzero 0 (by simp)
  have hRnonnegativeInt :
      0 <= a.order (⟨2 * t + 3, by omega⟩ : Fin (m + 3)) :=
    (a.he2022ClassicProposition24 hAClassic).nonnegativeOfFirstZero
      hfirstZero _
  have hRnonnegative : (0 : WithTop ℚ) <=
      ((((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ)) := by
    exact_mod_cast hRnonnegativeInt
  have hresult : R + D <= 1 := by
    by_cases ht : t = 0
    · simpa only [R, D, if_pos ht] using hthird
    · have htruncated : R + min D E <= 1 := by
        simpa only [if_neg ht] using hthird
      rcases le_total D E with hD | htwoE
      · rw [min_eq_left hD] at htruncated
        exact htruncated
      · rw [min_eq_right htwoE] at htruncated
        have htwoEQ : (1 : ℚ) < 2 * (ramificationIndex K : ℚ) := by
          linarith
        have htwoETop : (1 : WithTop ℚ) < E := by
          dsimp only [E]
          exact_mod_cast htwoEQ
        have htwoELeSum : E <= R + E := by
          simpa only [zero_add] using
            (add_le_add_left hRnonnegative E)
        exact (not_le_of_gt htwoETop (htwoELeSum.trans htruncated)).elim
  have hhalfIndex : (2 * t + 4) / 2 = t + 2 := by omega
  have horderIndex : 2 * t + 2 + 1 = 2 * t + 3 := by omega
  have hlength : 2 * t + 2 + 2 = 2 * t + 4 := by omega
  simpa only [R, D, horderIndex, hlength, hhalfIndex] using hresult

/-- Universal validity of conditions (i)--(ii) implies validity on the two
specific rows printed in Lemma 4.2. -/
theorem he2022ClassicLemma42_publishedTests_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAll : HeClassicAllOrderAndDefectConditions.{u, v, u}
      (n := 2 * t + 1) a (by omega)) :
    a.HeClassicLemma42PublishedTests t (by omega) := by
  unfold HeClassicLemma42PublishedTests
  dsimp only
  constructor
  · exact hAll _ (heClassicEvenC1_isClassicIntegral
      (K := K) t (heClassicOmega (K := K)) (by
        rw [heClassicOmega_order (K := K)]))
  · have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    exact hAll _ (heClassicEvenH_isClassicIntegral (K := K) t 1
      (Or.inl rfl) honeOrder)

/-- Backwards-compatible order-prefix endpoint derived from universal
validity by restricting to the two published rows. -/
theorem he2022ClassicLemma42_orders
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hAll : HeClassicAllOrderAndDefectConditions.{u, v, u}
      (n := 2 * t + 1) a (by omega)) :
    forall i : Fin (2 * t + 3),
      a.order ⟨i.val, by omega⟩ = 0 := by
  exact a.he2022ClassicLemma42_orders_of_publishedTests t hSource hAClassic
    (a.he2022ClassicLemma42_publishedTests_of_all t hSource hAll)

/-- The universal formulation implies `J1'_E(n)` through the literal
published tests. -/
theorem he2022ClassicLemma42_j1Prime
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hAll : HeClassicAllOrderAndDefectConditions.{u, v, u}
      (n := 2 * t + 1) a (by omega)) :
    a.HeClassicJ1EPrime (2 * t + 2) (by omega) := by
  exact a.he2022ClassicLemma42_j1Prime_of_publishedTests t hSource hAClassic
    (a.he2022ClassicLemma42_publishedTests_of_all t hSource hAll)

/-- The universal formulation implies `J2'_E(n)` through the literal
published tests. -/
theorem he2022ClassicLemma42_j2Prime
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hAll : HeClassicAllOrderAndDefectConditions.{u, v, u}
      (n := 2 * t + 1) a (by omega)) :
    a.HeClassicJ2EPrime (2 * t + 2) (by omega) := by
  exact a.he2022ClassicLemma42_j2Prime_of_publishedTests t hSource hAClassic
    (a.he2022ClassicLemma42_publishedTests_of_all t hSource hAll)

/-- Sufficiency in Lemma 4.2: `J1'_E(n)` supplies the zero-order and
unit-alpha prefix used by Corollaries 3.10(i) and 3.11(ii), while
`J2'_E(n)` is exactly the remaining ramified-field endpoint inequality. -/
theorem he2022ClassicLemma42_sufficiency
    [QuadraticDefectLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2EPrime (2 * t + 2) (by omega)) :
    HeClassicAllOrderAndDefectConditions.{u, v, u}
      (n := 2 * t + 1) a (by omega) := by
  intro W _ _ r M b hBClassic
  have hzero : forall k : Fin (m + 3), k.val < 2 * t + 2 ->
      a.order k = 0 := by
    intro k hk
    let small : Fin (2 * t + 3) := ⟨k.val, by omega⟩
    have hz := hJ1.1 small
    have hindex : (⟨small.val, by omega⟩ : Fin (m + 3)) = k :=
      Fin.ext rfl
    simpa only [hindex] using hz
  have halpha : forall k : Fin (m + 2), k.val < 2 * t + 2 ->
      a.alphaValue k = 1 := by
    intro k hk
    let small : Fin (2 * t + 2) := ⟨k.val, hk⟩
    have ha := hJ1.2 small
    have hindex : (⟨small.val, by omega⟩ : Fin (m + 2)) = k :=
      Fin.ext rfl
    simpa only [hindex] using ha
  have hnext : a.order ⟨2 * t + 2, by omega⟩ = 0 := by
    let small : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
    simpa only [small] using hJ1.1 small
  constructor
  · exact a.he2022ClassicCorollary310i_of_nextOrderZero t b
      (by omega) (by omega) hBClassic hzero hnext
  · intro i
    apply a.he2022ClassicCorollary311ii_of_previousAlpha t b
      (by omega) hAClassic hBClassic hzero halpha hnext
    · by_cases heOne : ramificationIndex K = 1
      · exact Or.inl heOne
      · right
        have hePos := ramificationIndex_pos (K := K)
        have heLarge : 1 < ramificationIndex K := by omega
        refine ⟨heLarge, ?_⟩
        have hbound := hJ2 heLarge
        have hhalfIndex : (2 * t + 2 + 2) / 2 = t + 2 := by omega
        have horderIndex : 2 * t + 2 + 1 = 2 * t + 3 := by omega
        have hlength : 2 * t + 2 + 2 = 2 * t + 4 := by omega
        simpa only [hhalfIndex, horderIndex, hlength] using hbound

/-- Necessity in Lemma 4.2, with the two printed tests realized over the
base field itself. -/
theorem he2022ClassicLemma42_necessity
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hAll : HeClassicAllOrderAndDefectConditions.{u, v, u}
      (n := 2 * t + 1) a (by omega)) :
    a.HeClassicJ1EPrime (2 * t + 2) (by omega) ∧
      a.HeClassicJ2EPrime (2 * t + 2) (by omega) := by
  exact ⟨a.he2022ClassicLemma42_j1Prime t hSource hAClassic hAll,
    a.he2022ClassicLemma42_j2Prime t hSource hAClassic hAll⟩

/-- Lemma 4.2, invariant form: conditions (i)--(ii) hold for every
classic integral even-rank target if and only if `J1'_E(n)` and
`J2'_E(n)` hold. -/
theorem he2022ClassicLemma42
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L) :
    HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * t + 1) a (by omega) ↔
      a.HeClassicJ1EPrime (2 * t + 2) (by omega) ∧
        a.HeClassicJ2EPrime (2 * t + 2) (by omega) := by
  constructor
  · exact a.he2022ClassicLemma42_necessity t hSource hAClassic
  · rintro ⟨hJ1, hJ2⟩
    exact a.he2022ClassicLemma42_sufficiency t hSource hAClassic hJ1 hJ2

/-- The literal two rows in the proof are equivalent to the printed
`J1'_E(n)`--`J2'_E(n)` package. -/
theorem he2022ClassicLemma42_publishedTests_iff_invariants
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L) :
    a.HeClassicLemma42PublishedTests t (by omega) ↔
      a.HeClassicJ1EPrime (2 * t + 2) (by omega) ∧
        a.HeClassicJ2EPrime (2 * t + 2) (by omega) := by
  constructor
  · intro hTests
    exact ⟨a.he2022ClassicLemma42_j1Prime_of_publishedTests t
        hSource hAClassic hTests,
      a.he2022ClassicLemma42_j2Prime_of_publishedTests t
        hSource hAClassic hTests⟩
  · rintro ⟨hJ1, hJ2⟩
    have hAll : HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * t + 1) a (by omega) :=
      a.he2022ClassicLemma42_sufficiency t hSource hAClassic hJ1 hJ2
    exact a.he2022ClassicLemma42_publishedTests_of_all t hSource hAll

/-- Lemma 4.2 in its advertised testing-set form: conditions (i)--(ii)
hold for every classic integral target exactly when they hold for
`C₁ⁿ(ω)` and `H_eⁿ(1)`. -/
theorem he2022ClassicLemma42_all_iff_publishedTests
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L) :
    HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * t + 1) a (by omega) ↔
      a.HeClassicLemma42PublishedTests t (by omega) := by
  constructor
  · exact a.he2022ClassicLemma42_publishedTests_of_all t hSource
  · intro hTests
    have hInv :=
      (a.he2022ClassicLemma42_publishedTests_iff_invariants t
        hSource hAClassic).1 hTests
    exact (a.he2022ClassicLemma42_sufficiency t hSource hAClassic
      hInv.1 hInv.2 : HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * t + 1) a (by omega))

end BONG.GoodBONG

end Bong
