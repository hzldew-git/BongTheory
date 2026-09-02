/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma42
import Bong.Bong.HeHu2022Proposition37
import Bong.Bong.Beli2019Lemma216Complete

/-!
# He--Hu 2022, Lemma 4.3

This file isolates the exceptional second-column test used in the
necessity proof of Lemma 4.4.  The target is the literal Table 2 lattice
`N_2^n(Delta)`, represented by the exact good BONG constructed in
Lemma 3.11.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The exact `N_2^(2k+2)(Delta)` test used in Lemmas 4.3 and 4.4. -/
noncomputable def heHuLemma43Target
    [DyadicDiscriminantClassLaws K] (k : Nat) :=
  (heHuLemma311EvenSecondDeltaBONG (K := K) k).castLength
    (show 1 + 1 + 2 * k = 2 * k + 2 by omega)

/-- The last two orders of `N_2^(2k+2)(Delta)` are
`1, 1-2e`, as in Lemma 3.11(i). -/
theorem heHuLemma43Target_lastOrders
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    (heHuLemma43Target (K := K) k).order ⟨2 * k, by omega⟩ = 1 ∧
      (heHuLemma43Target (K := K) k).order ⟨2 * k + 1, by omega⟩ =
        1 - 2 * (ramificationIndex K : Int) := by
  unfold heHuLemma43Target
  simpa only [order_castLength] using
    (heHu2022Lemma311iSecondDelta (K := K) k).2

/-- The initial `k` pairs of `N_2^(2k+2)(Delta)` are the literal
`1,-pi^(-2e)` hyperbolic pairs constructed in Lemma 3.10. -/
theorem heHuLemma43Target_hyperbolicValues
    [DyadicDiscriminantClassLaws K] (k : Nat) (t : Fin k) :
    (heHuLemma43Target (K := K) k).valueUnit
        ⟨2 * t.val, by omega⟩ = 1 ∧
      (heHuLemma43Target (K := K) k).valueUnit
        ⟨2 * t.val + 1, by omega⟩ =
          -(uniformizerPowerUnit K
            (-(2 * (ramificationIndex K : Int)))) := by
  unfold heHuLemma43Target heHuLemma311EvenSecondDeltaBONG
  simpa only [valueUnit_castLength_heHu] using
    (Bong.heHu2022Lemma310HyperbolicValues
      (heHuDiscriminantEndpointGoodBONG (K := K) 1)
      (heHuIntegral_of_firstOrder_nonneg
        (heHuDiscriminantEndpointGoodBONG (K := K) 1) (by
          rw [heHuDiscriminantEndpointGoodBONG_order]
          norm_num)) k t)

/-- The signed determinant of the hyperbolic prefix is a square. -/
theorem heHuLemma43Target_signedHyperbolicPrefix_isSquare
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    IsSquare
      ((heHuLemma43Target (K := K) k).toBONG
        |>.signedEvenPrefixProduct k) := by
  let b := heHuLemma43Target (K := K) k
  have hprefix : ∀ t : Nat, t ≤ k →
      IsSquare (b.toBONG.signedEvenPrefixProduct t) := by
    intro t ht
    induction t with
    | zero =>
        refine ⟨1, ?_⟩
        simp [BONG.signedEvenPrefixProduct, BONG.prefixProduct]
    | succ t ih =>
        have hrec := b.toBONG.signedEvenPrefixProduct_succ t (by omega)
        rw [hrec]
        apply (ih (by omega)).mul
        have hvalues := heHuLemma43Target_hyperbolicValues
          (K := K) k ⟨t, by omega⟩
        change IsSquare
          (-(b.valueUnit ⟨2 * t, by omega⟩ *
            b.valueUnit ⟨2 * t + 1, by omega⟩))
        rw [hvalues.1, hvalues.2]
        refine ⟨uniformizerPowerUnit K
          (-(ramificationIndex K : Int)), ?_⟩
        unfold uniformizerPowerUnit
        rw [← zpow_add]
        simp only [one_mul, neg_neg]
        congr 1
        ring
  exact hprefix k le_rfl

/-- The terminal discriminant pair is literally
`pi,-Delta*pi^(1-2e)`. -/
theorem heHuLemma43Target_lastValues
    [laws : DyadicDiscriminantClassLaws K] (k : Nat) :
    (heHuLemma43Target (K := K) k).valueUnit
        ⟨2 * k, by omega⟩ = uniformizerPowerUnit K 1 ∧
      (heHuLemma43Target (K := K) k).valueUnit
        ⟨2 * k + 1, by omega⟩ =
          -(laws.discriminantUnit *
            uniformizerPowerUnit K
              (1 - 2 * (ramificationIndex K : Int))) := by
  let tail := heHuDiscriminantEndpointGoodBONG (K := K) 1
  let hIntegral := heHuIntegral_of_firstOrder_nonneg tail (by
    rw [heHuDiscriminantEndpointGoodBONG_order]
    norm_num)
  have hzero := Bong.heHu2022Lemma310TailValues tail hIntegral k (0 : Fin 2)
  have hone := Bong.heHu2022Lemma310TailValues tail hIntegral k (1 : Fin 2)
  constructor
  · unfold heHuLemma43Target heHuLemma311EvenSecondDeltaBONG
    rw [valueUnit_castLength_heHu]
    change (Bong.heHu2022Lemma310BONG tail hIntegral k).valueUnit
      ⟨2 * k + (0 : Fin 2).val, by omega⟩ = _
    rw [hzero, heHuDiscriminantEndpointGoodBONG_valueUnit,
      heHuDiscriminantEndpointValues_zero]
  · unfold heHuLemma43Target heHuLemma311EvenSecondDeltaBONG
    rw [valueUnit_castLength_heHu]
    change (Bong.heHu2022Lemma310BONG tail hIntegral k).valueUnit
      ⟨2 * k + (1 : Fin 2).val, by omega⟩ = _
    rw [hone, heHuDiscriminantEndpointGoodBONG_valueUnit,
      heHuDiscriminantEndpointValues_one]

/-- The full signed determinant of the exceptional target has square class
`Delta`.  The witness keeps the exact uniformizer normalization visible. -/
theorem heHuLemma43Target_signedFullProduct_eq_discriminant_mul_square
    [laws : DyadicDiscriminantClassLaws K] (k : Nat) :
    ∃ s : Kˣ,
      (heHuLemma43Target (K := K) k).toBONG.signedEvenPrefixProduct
          (k + 1) =
        laws.discriminantUnit * s ^ 2 := by
  let b := heHuLemma43Target (K := K) k
  rcases heHuLemma43Target_signedHyperbolicPrefix_isSquare
      (K := K) k with ⟨h, hh⟩
  let tailSquare := uniformizerPowerUnit K
    (1 - (ramificationIndex K : Int))
  refine ⟨h * tailSquare, ?_⟩
  rw [b.toBONG.signedEvenPrefixProduct_succ k (by omega)]
  have hlast := heHuLemma43Target_lastValues (K := K) k
  change b.toBONG.signedEvenPrefixProduct k *
      (-(b.valueUnit ⟨2 * k, by omega⟩ *
        b.valueUnit ⟨2 * k + 1, by omega⟩)) = _
  rw [hh, hlast.1, hlast.2]
  have htail :
      -(uniformizerPowerUnit K 1 *
          -(laws.discriminantUnit *
            uniformizerPowerUnit K
              (1 - 2 * (ramificationIndex K : Int)))) =
        laws.discriminantUnit *
          (uniformizerPowerUnit K 1 *
            uniformizerPowerUnit K
              (1 - 2 * (ramificationIndex K : Int))) := by
    simp only [mul_neg, neg_neg]
    ac_rfl
  rw [htail]
  have hpowers :
      uniformizerPowerUnit K 1 *
          uniformizerPowerUnit K
            (1 - 2 * (ramificationIndex K : Int)) =
        tailSquare ^ 2 := by
    dsimp only [tailSquare]
    rw [pow_two]
    unfold uniformizerPowerUnit
    rw [← zpow_add, ← zpow_add]
    congr 1
    ring
  rw [hpowers]
  simp only [pow_two]
  ac_rfl

/-- Consequently the full target prefix has the discriminant defect `2e`,
as used in the second domination step of Lemma 4.3. -/
theorem heHuLemma43Target_fullSignedDefect
    [laws : DyadicDiscriminantClassLaws K] (k : Nat) :
    defectOrder (K := K)
        ((heHuLemma43Target (K := K) k).toBONG.signedEvenPrefixProduct
          (k + 1)) =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  rcases
      heHuLemma43Target_signedFullProduct_eq_discriminant_mul_square
        (K := K) k with ⟨s, hs⟩
  rw [hs, defectOrder_mul_square]
  unfold defectOrder
  rw [laws.discriminant_defect]
  rfl

/-- At full target rank both alpha caps are omitted, so the capped defect is
the raw discriminant defect. -/
theorem heHuLemma43Target_fullTruncatedDefect
    [laws : DyadicDiscriminantClassLaws K] (k : Nat) :
    (heHuLemma43Target (K := K) k).truncatedPrefixDefect
        (heHuLemma43Target (K := K) k) ((-1) ^ (k + 1))
          0 (2 * k + 2) =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  let b := heHuLemma43Target (K := K) k
  change b.truncatedPrefixDefect b ((-1) ^ (k + 1))
    0 (2 * k + 2) = _
  unfold truncatedPrefixDefect
  rw [b.prefixAlphaCap_zero, b.prefixAlphaCap_last]
  simp only [min_eq_left (le_top), BONG.GoodBONG.prefixProduct,
    BONG.prefixProduct_zero, mul_one]
  change defectOrder (K := K)
      (b.toBONG.signedEvenPrefixProduct (k + 1)) = _
  exact heHuLemma43Target_fullSignedDefect (K := K) k

/-- The unique terminal central index `i=n+1` of Lemma 4.3, translated to
zero-based prefix lengths. -/
def heHuLemma43CentralIndex {m : Nat} (k : Nat) (hm : 2 * k + 2 ≤ m) :
    CentralRepresentationIndex (m + 2) (2 * k + 2) where
  val := 2 * k + 3
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- Proposition 2.7(iii) and the adjacent hypothesis propagate to the
signed source prefix of length `n+2`. -/
theorem heHuLemma43_sourceFullDefect_gt
    [_sourceLaws : Beli2006AlphaLaws.{u, v} K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (hm : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent :
      ((((1 : ℚ) -
        (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) <
        a.heHuAdjacentCappedDefect ⟨2 * k + 2, by omega⟩) :
    ((((1 : ℚ) -
      (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect a ((-1) ^ (k + 2)) (2 * k + 4) 0 := by
  let threshold : WithTop ℚ :=
    (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ)
  let j : Fin (m + 2) := ⟨2 * k + 1, by omega⟩
  have hjOdd : Odd j.val := ⟨k, by simp only [j]⟩
  have hjOrder : a.order j =
      -(2 * (ramificationIndex K : Int)) := by
    have h := hI1.evenOrder ⟨2 * k + 1, by omega⟩
      (⟨k + 1, by omega⟩ : Even (2 * k + 1 + 1))
    simpa only [j] using h
  have hprefix :=
    (a.heHu2022Proposition27iiiiv hAIntegral j hjOdd hjOrder)
      |>.alternatingPrefixDefect
  have hthresholdTwoE : threshold <
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
    apply WithTop.coe_lt_coe.mpr
    have hRQ :
        (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
          (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
      exact_mod_cast hR
    linarith
  have hfirst : threshold <
      a.truncatedPrefixDefect a ((-1) ^ (k + 1)) 0 (2 * k + 2) := by
    apply hthresholdTwoE.trans_le
    simp only [j] at hprefix
    have hlength : 2 * k + 1 - 1 + 2 = 2 * k + 2 := by omega
    rw [hlength] at hprefix
    have hhalf : (2 * k + 2) / 2 = k + 1 := by omega
    rw [hhalf] at hprefix
    exact hprefix
  have hsecond : threshold <
      a.truncatedPrefixDefect a (-1) (2 * k + 2) (2 * k + 4) := by
    simpa only [threshold, heHuAdjacentCappedDefect] using hAdjacent
  have hdom := a.truncatedPrefixDefect_domination a a
    ((-1) ^ (k + 1)) (-1) 0 (2 * k + 2) (2 * k + 4)
  have hout : threshold <
      a.truncatedPrefixDefect a
        (((-1) ^ (k + 1)) * (-1)) 0 (2 * k + 4) :=
    (lt_min hfirst hsecond).trans_le hdom
  rw [a.truncatedPrefixDefect_comm a
    (((-1) ^ (k + 1)) * (-1)) 0 (2 * k + 4)] at hout
  simpa only [threshold, pow_succ] using hout

/-- The second capped defect in the terminal trigger is strictly above the
paper's threshold `1-R_(n+2)`. -/
theorem heHuLemma43_centralCurrentDefect_gt
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (hm : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent :
      ((((1 : ℚ) -
        (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) <
        a.heHuAdjacentCappedDefect ⟨2 * k + 2, by omega⟩) :
    ((((1 : ℚ) -
      (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) <
      a.centralCurrentDefect (heHuLemma43Target (K := K) k)
        (heHuLemma43CentralIndex k hm) := by
  let b := heHuLemma43Target (K := K) k
  let i := heHuLemma43CentralIndex k hm
  let threshold : WithTop ℚ :=
    (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ)
  have hsource : threshold <
      a.truncatedPrefixDefect a ((-1) ^ (k + 2)) (2 * k + 4) 0 := by
    exact a.heHuLemma43_sourceFullDefect_gt k hm hAIntegral hI1 hR hAdjacent
  have hthresholdTwoE : threshold <
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
    apply WithTop.coe_lt_coe.mpr
    have hRQ :
        (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
          (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
      exact_mod_cast hR
    linarith
  have htargetSelf : threshold <
      b.truncatedPrefixDefect b ((-1) ^ (k + 1)) 0 (2 * k + 2) := by
    rw [heHuLemma43Target_fullTruncatedDefect (K := K) k]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hthresholdTwoE
  have htarget : threshold <
      a.truncatedPrefixDefect b ((-1) ^ (k + 1)) 0 (2 * k + 2) := by
    rw [a.truncatedPrefixDefect_zero_left_eq_self b]
    exact htargetSelf
  have hdom := a.truncatedPrefixDefect_domination a b
    ((-1) ^ (k + 2)) ((-1) ^ (k + 1))
      (2 * k + 4) 0 (2 * k + 2)
  have hout : threshold <
      a.truncatedPrefixDefect b
        (((-1) ^ (k + 2)) * ((-1) ^ (k + 1)))
          (2 * k + 4) (2 * k + 2) :=
    (lt_min hsource htarget).trans_le hdom
  have hsign : ((-1 : Kˣ) ^ (k + 2)) * ((-1) ^ (k + 1)) = -1 := by
    rw [← pow_add]
    exact (show Odd (k + 2 + (k + 1)) from ⟨k + 1, by omega⟩).neg_one_pow
  rw [hsign] at hout
  unfold centralCurrentDefect
  change threshold < a.truncatedPrefixDefect b (-1)
    (i.val + 1) (i.val - 1)
  dsimp only [i, heHuLemma43CentralIndex]
  have hplus : 2 * k + 3 + 1 = 2 * k + 4 := by omega
  have hminus : 2 * k + 3 - 1 = 2 * k + 2 := by omega
  rw [hplus, hminus]
  exact hout

/-- The final target alpha invariant is zero because its last order gap is
`-2e`. -/
theorem heHuLemma43Target_lastAlpha_eq_zero
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    (heHuLemma43Target (K := K) k).alphaValue
        ⟨2 * k, by omega⟩ = 0 := by
  let b := heHuLemma43Target (K := K) k
  have hgap : b.orderGap ⟨2 * k, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    unfold orderGap
    change b.order ⟨2 * k + 1, by omega⟩ -
        b.order ⟨2 * k, by omega⟩ = _
    rw [(heHuLemma43Target_lastOrders (K := K) k).2,
      (heHuLemma43Target_lastOrders (K := K) k).1]
    omega
  exact ((b.heHu2022Proposition26 ⟨2 * k, by omega⟩).alphaZero).2 hgap

/-- The first capped defect in the Lemma 4.3 terminal trigger equals the
target invariant `beta_(n-1)=0`. -/
theorem heHuLemma43_centralPreviousDefect_eq_zero
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (_hm : 2 * k + 2 ≤ m) :
    a.truncatedPrefixDefect (heHuLemma43Target (K := K) k) (-1)
        (2 * k + 3) (2 * k + 1) = 0 := by
  let b := heHuLemma43Target (K := K) k
  have hnonnegative : (0 : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) (2 * k + 3) (2 * k + 1) :=
    a.truncatedPrefixDefect_nonneg
      (alphaV := sourceLaws)
      (alphaW := beliUniversalAlphaLaws)
      b (-1) (2 * k + 3) (2 * k + 1)
  have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
    (2 * k + 3) (2 * k + 1)
  have hcapZero : b.prefixAlphaCap (2 * k + 1) = 0 := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
    have halpha : b.alphaValue ⟨2 * k + 1 - 1, by omega⟩ = 0 := by
      have hindex : (⟨2 * k + 1 - 1, by omega⟩ : Fin (2 * k + 1)) =
          ⟨2 * k, by omega⟩ := by
        apply Fin.ext
        simp
      rw [hindex]
      exact heHuLemma43Target_lastAlpha_eq_zero (K := K) k
    rw [halpha]
    rfl
  rw [hcapZero] at hcap
  exact le_antisymm hcap hnonnegative

/-- The two numerical conclusions of Lemma 4.3 are exactly the revised
condition-(iii') trigger at `i=n+1`. -/
theorem heHu2022Lemma43_defectTrigger
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (hm : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent :
      ((((1 : ℚ) -
        (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) <
        a.heHuAdjacentCappedDefect ⟨2 * k + 2, by omega⟩) :
    a.centralDefectTrigger (heHuLemma43Target (K := K) k)
      (heHuLemma43CentralIndex k hm) := by
  let b := heHuLemma43Target (K := K) k
  let i := heHuLemma43CentralIndex k hm
  unfold centralDefectTrigger
  constructor
  · change b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ <
      a.order ⟨i.val, i.lt_large⟩
    have hlast := (heHuLemma43Target_lastOrders (K := K) k).2
    dsimp only [i, heHuLemma43CentralIndex]
    have hindex :
        (⟨2 * k + 3 - 2, by omega⟩ : Fin (2 * k + 2)) =
          ⟨2 * k + 1, by omega⟩ := by
      apply Fin.ext
      change 2 * k + 3 - 2 = 2 * k + 1
      omega
    rw [hindex, hlast]
    omega
  · have hprevious : a.centralPreviousDefect b i = 0 := by
      unfold centralPreviousDefect
      dsimp only [i, heHuLemma43CentralIndex]
      have hminus : 2 * k + 3 - 2 = 2 * k + 1 := by omega
      rw [hminus]
      exact a.heHuLemma43_centralPreviousDefect_eq_zero k hm
    have hcurrent :
        ((((1 : ℚ) -
          (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) <
          a.centralCurrentDefect b i :=
      a.heHuLemma43_centralCurrentDefect_gt k hm hAIntegral hI1 hR hAdjacent
    rw [hprevious, zero_add]
    have hlast := (heHuLemma43Target_lastOrders (K := K) k).2
    change
      ((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : ℚ) -
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) <
        a.centralCurrentDefect b i
    dsimp only [i, heHuLemma43CentralIndex]
    have hindex :
        (⟨2 * k + 3 - 2, by omega⟩ : Fin (2 * k + 2)) =
          ⟨2 * k + 1, by omega⟩ := by
      apply Fin.ext
      change 2 * k + 3 - 2 = 2 * k + 1
      omega
    rw [hindex, hlast]
    have hidentity :
        2 * (ramificationIndex K : ℚ) +
            ((1 - 2 * (ramificationIndex K : Int) : Int) : ℚ) -
              (a.order ⟨2 * k + 3, by omega⟩ : ℚ) =
          1 - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
      push_cast
      ring
    rw [hidentity]
    exact hcurrent

/-- The Table 1 second-column model is defined for the discriminant
square class in every even rank. -/
theorem heHuLemma43_evenSecondDefined
    (k : Nat) :
    HeHuEvenSecondDefined k
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit := by
  cases k with
  | zero =>
      right
      exact
        AlternatingEndpointNormalization.discriminantUnit_not_isSquare
          (K := K)
  | succ k =>
      left
      omega

/-- For the discriminant square class, the defined second-column model is
exactly a standard hyperbolic tower followed by `[pi,-Delta*pi]`. -/
theorem heHuLemma43_evenSecond_eq_model
    (k : Nat) :
    heHuEvenSecond k
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) k) =
      Fin.append
        (AlternatingEndpointTower.standardHyperbolicEndpointTower
          (K := K) k)
        (heHuDiscriminantBinary (K := K)
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminantUnit) := by
  cases k with
  | zero =>
      rw [heHuEvenSecond_zero_of_discriminant]
      · funext i
        have hi : i = Fin.natAdd 0 i := by
          apply Fin.ext
          simp
        rw [hi, Fin.append_right]
        congr 1
        apply Fin.ext
        simp
      · refine ⟨1, ?_⟩
        calc
          (Dyadic.dyadicDiscriminantClassLawsProved
              (K := K)).discriminantUnit /
              (Dyadic.dyadicDiscriminantClassLawsProved
                (K := K)).discriminantUnit = 1 :=
            div_self'
              (Dyadic.dyadicDiscriminantClassLawsProved
                (K := K)).discriminantUnit
          _ = 1 * 1 := by simp only [one_mul]
  | succ k =>
      rw [heHuEvenSecond_succ_of_discriminant]
      · simpa only [heHuEvenDiscriminantTail] using
          heHuFinFamilyCast_tower_hyperbolic_tail
            (K := K) k
            (heHuDiscriminantBinary (K := K)
              (Dyadic.dyadicDiscriminantClassLawsProved
                (K := K)).discriminantUnit)
      · exact
          AlternatingEndpointNormalization.discriminantUnit_not_isSquare
            (K := K)
      · refine ⟨1, ?_⟩
        calc
          (Dyadic.dyadicDiscriminantClassLawsProved
              (K := K)).discriminantUnit /
              (Dyadic.dyadicDiscriminantClassLawsProved
                (K := K)).discriminantUnit = 1 :=
            div_self'
              (Dyadic.dyadicDiscriminantClassLawsProved
                (K := K)).discriminantUnit
          _ = 1 * 1 := by simp only [one_mul]

/-- The coordinatewise square factor converting the literal good-BONG
coefficients of `N_2^(2k+2)(Delta)` to the Table 1 space model. -/
noncomputable def heHuLemma43SquareFactor (k : Nat)
    (i : Fin (2 * k + 2)) : Kˣ :=
  if Odd i.val then
    uniformizerPowerUnit K (-(ramificationIndex K : Int))
  else 1

/-- The literal target BONG and the Table 1 discriminant model differ only
by the displayed coordinatewise nonzero squares. -/
theorem heHuLemma43Target_eq_model_mul_square
    (k : Nat) (i : Fin (2 * k + 2)) :
    (heHuLemma43Target (K := K) k).valueUnit i =
      (Fin.append
        (AlternatingEndpointTower.standardHyperbolicEndpointTower
          (K := K) k)
        (heHuDiscriminantBinary (K := K)
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminantUnit)) i *
        heHuLemma43SquareFactor (K := K) k i ^ 2 := by
  by_cases hprefix : i.val < 2 * k
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · rcases hiEven with ⟨t, ht⟩
      have htlt : t < k := by omega
      have hiEq : i = (⟨2 * t, by omega⟩ : Fin (2 * k + 2)) := by
        apply Fin.ext
        change i.val = 2 * t
        omega
      have hvalue := heHuLemma43Target_hyperbolicValues
        (K := K) k ⟨t, htlt⟩
      rw [hiEq, hvalue.1]
      have happend :
          (Fin.append
            (AlternatingEndpointTower.standardHyperbolicEndpointTower
              (K := K) k)
            (heHuDiscriminantBinary (K := K)
              (Dyadic.dyadicDiscriminantClassLawsProved
                (K := K)).discriminantUnit))
              (⟨2 * t, by omega⟩ : Fin (2 * k + 2)) =
            AlternatingEndpointTower.standardHyperbolicEndpointTower
              (K := K) k (⟨2 * t, by omega⟩ : Fin (2 * k)) := by
        have hindex : (⟨2 * t, by omega⟩ : Fin (2 * k + 2)) =
            Fin.castAdd 2 (⟨2 * t, by omega⟩ : Fin (2 * k)) := by
          apply Fin.ext
          rfl
        rw [hindex, Fin.append_left]
      rw [happend]
      have hstandard :
          AlternatingEndpointTower.standardHyperbolicEndpointTower
              (K := K) k (⟨2 * t, by omega⟩ : Fin (2 * k)) = 1 :=
        AlternatingEndpointTower.standardHyperbolicEndpointTower_even
          (K := K) (⟨t, htlt⟩ : Fin k)
      rw [hstandard]
      have hnotOdd : ¬ Odd (2 * t) :=
        Nat.not_odd_iff_even.mpr ⟨t, by omega⟩
      simp [heHuLemma43SquareFactor, hnotOdd]
    · rcases hiOdd with ⟨t, ht⟩
      have htlt : t < k := by omega
      have hiEq : i =
          (⟨2 * t + 1, by omega⟩ : Fin (2 * k + 2)) := by
        apply Fin.ext
        change i.val = 2 * t + 1
        omega
      have hvalue := heHuLemma43Target_hyperbolicValues
        (K := K) k ⟨t, htlt⟩
      rw [hiEq, hvalue.2]
      have happend :
          (Fin.append
            (AlternatingEndpointTower.standardHyperbolicEndpointTower
              (K := K) k)
            (heHuDiscriminantBinary (K := K)
              (Dyadic.dyadicDiscriminantClassLawsProved
                (K := K)).discriminantUnit))
              (⟨2 * t + 1, by omega⟩ : Fin (2 * k + 2)) =
            AlternatingEndpointTower.standardHyperbolicEndpointTower
              (K := K) k (⟨2 * t + 1, by omega⟩ : Fin (2 * k)) := by
        have hindex :
            (⟨2 * t + 1, by omega⟩ : Fin (2 * k + 2)) =
              Fin.castAdd 2
                (⟨2 * t + 1, by omega⟩ : Fin (2 * k)) := by
          apply Fin.ext
          rfl
        rw [hindex, Fin.append_left]
      rw [happend]
      have hstandard :
          AlternatingEndpointTower.standardHyperbolicEndpointTower
              (K := K) k (⟨2 * t + 1, by omega⟩ : Fin (2 * k)) = -1 :=
        AlternatingEndpointTower.standardHyperbolicEndpointTower_odd
          (K := K) (⟨t, htlt⟩ : Fin k)
      rw [hstandard]
      have hodd : Odd (2 * t + 1) := ⟨t, by omega⟩
      rw [heHuLemma43SquareFactor, if_pos hodd]
      simp only [neg_mul, one_mul]
      unfold uniformizerPowerUnit
      rw [pow_two, ← zpow_add]
      congr 2
      ring
  · have hlast : i.val = 2 * k ∨ i.val = 2 * k + 1 := by
      omega
    rcases hlast with hzero | hone
    · have hiEq : i = Fin.natAdd (2 * k) (0 : Fin 2) := by
        apply Fin.ext
        exact hzero
      rw [hiEq, Fin.append_right]
      change
        (heHuLemma43Target (K := K) k).valueUnit
            ⟨2 * k, by omega⟩ =
          uniformizerPowerUnit K 1 *
            heHuLemma43SquareFactor (K := K) k
              ⟨2 * k, by omega⟩ ^ 2
      rw [(heHuLemma43Target_lastValues (K := K) k).1]
      have hnotOdd : ¬ Odd (2 * k) :=
        Nat.not_odd_iff_even.mpr ⟨k, by omega⟩
      simp [heHuLemma43SquareFactor, hnotOdd]
    · have hiEq : i = Fin.natAdd (2 * k) (1 : Fin 2) := by
        apply Fin.ext
        exact hone
      rw [hiEq, Fin.append_right]
      let delta :=
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit
      change
        (heHuLemma43Target (K := K) k).valueUnit
            ⟨2 * k + 1, by omega⟩ =
          -(uniformizerPowerUnit K 1 * delta) *
            heHuLemma43SquareFactor (K := K) k
              ⟨2 * k + 1, by omega⟩ ^ 2
      rw [(heHuLemma43Target_lastValues (K := K) k).2]
      have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
      rw [heHuLemma43SquareFactor, if_pos hodd]
      have hpowers :
          uniformizerPowerUnit K
              (1 - 2 * (ramificationIndex K : Int)) =
            uniformizerPowerUnit K 1 *
              (uniformizerPowerUnit K
                (-(ramificationIndex K : Int)) *
               uniformizerPowerUnit K
                (-(ramificationIndex K : Int))) := by
        unfold uniformizerPowerUnit
        rw [← zpow_add, ← zpow_add]
        congr 1
        ring
      rw [hpowers, pow_two]
      dsimp only [delta]
      simp only [neg_mul]
      ac_rfl

/-- The odd normal form supplied by Proposition 2.7(v) is the first-column
Table 1 model in the matching odd rank. -/
theorem heHuLemma43_snoc_standard_eq_oddFirst
    (k : Nat) (epsilon : Kˣ) :
    Fin.snoc
        (AlternatingEndpointTower.standardHyperbolicEndpointTower
          (K := K) (k + 1)) epsilon =
      heHuOddFirst (K := K) k epsilon := by
  rw [Fin.snoc_eq_append]
  let line : Fin 1 → Kˣ := Fin.cons epsilon Fin.elim0
  have htail :
      Fin.append (heHuHyperbolicPair (K := K)) line =
        heHuOddFirstTail (K := K) epsilon := by
    funext i
    fin_cases i <;> rfl
  have htower := heHuFinFamilyCast_tower_hyperbolic_tail
    (K := K) k line
  rw [htail] at htower
  simpa only [heHuOddFirst, heHuFinFamilyCast_self] using htower.symm

/-- The literal Lemma 4.3 target is isometric to the defined second-column
space `W_2^(2k+2)(Delta)`. -/
theorem heHuLemma43Target_represents_evenSecond (k : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma43Target (K := K) k).valueUnit)
      (diagonalUnitCoefficients
        (heHuEvenSecond k
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) k))) := by
  rw [heHuLemma43_evenSecond_eq_model (K := K) k]
  exact
    Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
      (heHuLemma43Target (K := K) k).valueUnit
      (Fin.append
        (AlternatingEndpointTower.standardHyperbolicEndpointTower
          (K := K) k)
        (heHuDiscriminantBinary (K := K)
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminantUnit))
      (heHuLemma43SquareFactor (K := K) k)
      (heHuLemma43Target_eq_model_mul_square (K := K) k)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- Reindex a diagonal representation across arithmetic equalities of the
two displayed ranks. -/
theorem heHuLemma43_diagonalRepresents_castLengths
    {s t s' t' : Nat} (hs : s = s') (ht : t = t')
    {source : Fin s → K} {target : Fin t → K}
    (hrep : DiagonalRepresents source target) :
    DiagonalRepresents
      (fun i : Fin s' => source (Fin.cast hs.symm i))
      (fun i : Fin t' => target (Fin.cast ht.symm i)) := by
  subst s'
  subst t'
  convert hrep using 1 <;> funext i <;> congr 1

/-- Under `I1^E(n)`, Proposition 2.7(v) puts the relevant odd source
prefix into the first-column space `W_1^(2k+3)(epsilon)`. -/
theorem heHuLemma43_sourcePrefix_represents_oddFirst
    {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (hm : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega)) :
    ∃ epsilon : Kˣ,
      IsValuationUnit K (epsilon : K) ∧
        DiagonalRepresents
          (a.prefixValues (2 * k + 3) (by omega))
          (diagonalUnitCoefficients
            (heHuOddFirst (K := K) k epsilon)) := by
  let j : Fin (m + 2) := ⟨2 * k + 1, by omega⟩
  have hjOdd : Odd j.val := ⟨k, by simp only [j]⟩
  have hjOrder : a.order j =
      -(2 * (ramificationIndex K : Int)) := by
    have h := hI1.evenOrder ⟨2 * k + 1, by omega⟩
      (⟨k + 1, by omega⟩ : Even (2 * k + 1 + 1))
    simpa only [j] using h
  have hnext : j.val + 1 < m + 2 := by
    simp only [j]
    omega
  have hnextOrder :
      a.order ⟨j.val + 1, hnext⟩ = 0 := by
    have h := hI1.oddOrder ⟨2 * k + 2, by omega⟩
      (⟨k + 1, by omega⟩ : Odd (2 * k + 2 + 1))
    simpa only [j] using h
  have hnextEven : Even (a.order ⟨j.val + 1, hnext⟩) := by
    rw [hnextOrder]
    exact Even.zero
  rcases a.heHu2022Proposition27v hAIntegral j hjOdd hjOrder
      hnext hnextEven with ⟨w⟩
  rcases w with
    ⟨pairs, hpairCount, hextended, epsilon, squareFactor,
      hepsilonUnit, hepsilonClass, hnormal⟩
  have hpairs : pairs = k + 1 := by
    simp only [j] at hpairCount
    omega
  subst pairs
  rcases hnormal with ⟨f⟩
  refine ⟨epsilon, hepsilonUnit, ?_⟩
  have hdiagRaw : DiagonalRepresents
      (a.prefixValues (2 * (k + 1) + 1) hextended)
      (diagonalUnitCoefficients
        (Fin.snoc
          (AlternatingEndpointTower.standardHyperbolicEndpointTower
            (K := K) (k + 1)) epsilon)) := by
    refine ⟨f.toLinearEquiv.toLinearMap,
      f.toLinearEquiv.injective, ?_⟩
    intro x
    have hq := f.map_quadratic x
    have hq' :
        diagonalQuadratic
            (diagonalUnitCoefficients
              (Fin.snoc
                (AlternatingEndpointTower.standardHyperbolicEndpointTower
                  (K := K) (k + 1)) epsilon))
            (f.toLinearEquiv x) =
          diagonalQuadratic
            (a.prefixValues (2 * (k + 1) + 1) hextended) x := by
      simpa only [BONG.GoodBONG.prefixDiagonalSpace,
        AlternatingEndpointTower.hyperbolicEndpointTowerWithLineSpace,
        QuadraticSpace.finiteDiagonal_quadratic_apply,
        diagonalUnitCoefficients] using hq
    exact hq'
  rw [heHuLemma43_snoc_standard_eq_oddFirst (K := K) k epsilon]
    at hdiagRaw
  let hdim : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  have hcast := heHuLemma43_diagonalRepresents_castLengths
    hdim hdim hdiagRaw
  have hsourceEq :
      (fun i : Fin (2 * k + 3) =>
        a.prefixValues (2 * (k + 1) + 1) hextended
          (Fin.cast hdim.symm i)) =
        a.prefixValues (2 * k + 3) (by omega) := by
    funext i
    unfold BONG.GoodBONG.prefixValues
    congr 1
  have htargetEq :
      (fun i : Fin (2 * k + 3) =>
        diagonalUnitCoefficients (heHuOddFirst (K := K) k epsilon)
          (Fin.cast hdim.symm i)) =
        diagonalUnitCoefficients (heHuOddFirst (K := K) k epsilon) := by
    funext i
    unfold diagonalUnitCoefficients
    congr 1
  rw [hsourceEq, htargetEq] at hcast
  exact hcast

/-- The exceptional target of Lemma 4.3 is not represented by the source
prefix of rank `n+1`.  This is exactly the negative assertion supplied by
Lemma 3.14(i) after the two explicit normal-form identifications above. -/
theorem heHu2022Lemma43_not_represents
    {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (hm : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega)) :
    ¬ DiagonalRepresents
      ((heHuLemma43Target (K := K) k).prefixValues
        (2 * k + 2) le_rfl)
      (a.prefixValues (2 * k + 3) (by omega)) := by
  intro hrep
  let b := heHuLemma43Target (K := K) k
  have hbPrefix :
      b.prefixValues (2 * k + 2) le_rfl =
        diagonalUnitCoefficients b.valueUnit := by
    funext i
    rfl
  rw [hbPrefix] at hrep
  rcases a.heHuLemma43_sourcePrefix_represents_oddFirst
      k hm hAIntegral hI1 with ⟨epsilon, hepsilonUnit, hsource⟩
  have htarget := heHuLemma43Target_represents_evenSecond
    (K := K) k
  have hforbidden : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuEvenSecond k
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) k)))
      (diagonalUnitCoefficients
        (heHuOddFirst (K := K) k epsilon)) :=
    htarget.symm_of_sameRank.trans (hrep.trans hsource)
  exact (heHu2022Lemma314i (K := K) k
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit epsilon
    (Or.inr rfl) hepsilonUnit
    (heHuLemma43_evenSecondDefined (K := K) k)).2 hforbidden

/-- He--Hu, Lemma 4.3, in zero-based prefix notation.

For `n=2k+2`, `centralDefectTrigger` unfolds to the two strict numerical
conclusions in the paper: `R_(n+2)>S_n` and the displayed sum of two
capped defects exceeding `2e+S_n-R_(n+2)`.  The second conjunct is the
paper's assertion that `[b_1,...,b_n]` is not represented by
`[a_1,...,a_(n+1)]`. -/
theorem heHu2022Lemma43
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (hm : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hR : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨2 * k + 3, by omega⟩)
    (hAdjacent :
      ((((1 : ℚ) -
        (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) <
        a.heHuAdjacentCappedDefect ⟨2 * k + 2, by omega⟩) :
    a.centralDefectTrigger (heHuLemma43Target (K := K) k)
        (heHuLemma43CentralIndex k hm) ∧
      ¬ DiagonalRepresents
        ((heHuLemma43Target (K := K) k).prefixValues
          (2 * k + 2) le_rfl)
        (a.prefixValues (2 * k + 3) (by omega)) := by
  exact ⟨a.heHu2022Lemma43_defectTrigger k hm hAIntegral hI1 hR hAdjacent,
    a.heHu2022Lemma43_not_represents k hm hAIntegral hI1⟩

end BONG.GoodBONG

end Bong
