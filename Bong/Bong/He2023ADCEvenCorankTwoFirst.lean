/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankTwoTests
import Bong.Bong.He2023ADCSignedDeterminant
import Bong.Bong.He2023ADCEvenCentralAlpha

/-!
# He (2025), Lemma 6.8(i)--(ii)

The actual maximal tests force the alternating endpoint profile. A raised
terminal order would give a full signed defect below 2e, contradicting the
ambient determinant. The square first-column argument also covers n=2.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The three actual tests and endpoint full defect force a fully alternating order profile. -/
theorem heADCEvenCorankTwo_endpoint_orders (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hIntegral : Lattice.IsIntegral q L)
    (hOne : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))
      L (heADCN1Even k (1 : Kˣ)).lattice)
    (hDelta : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
      L (heADCN1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice)
    (μ : Kˣ) (hdefined : HeHuEvenSecondDefined k μ)
    (hμ : μ = 1 ∨ μ = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hTwo : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k μ hdefined))
      L (heADCN2Even k μ hdefined).lattice)
    (hfull : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2))) :
    ∀ i, a.order i = if Even i.val then 0 else -(2 * (ramificationIndex K : Int)) := by
  obtain ⟨_, hhead, hnext⟩ := a.heADC2025Lemma64ii k hIntegral hOne hDelta
  let current : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  have hheadLast : a.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    have hodd : ¬ Even (2 * k + 1) := by rintro ⟨z, hz⟩; omega
    simpa only [if_neg hodd] using hhead ⟨2 * k + 1, by omega⟩
  have hsmall : a.order ⟨2 * k + 3, by omega⟩ <
      2 - 2 * (ramificationIndex K : Int) := by
    by_contra hnot
    have hR := le_of_not_gt hnot
    have hcase : Even (a.order ⟨2 * k + 2, by omega⟩) := by rw [hnext]; exact Even.zero
    have H := a.heADC2025Lemma67_endpoint k hIntegral hhead hR μ hdefined hμ
      (Or.inl hcase) hTwo
    rcases H with hzero | ⟨_, hraw, hcap⟩
    · have hgap := (a.heADC2025Proposition34 current).alphaZero.mp hzero
      change a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩ = _ at hgap
      rw [hnext] at hgap
      omega
    · have hrawEq := hraw.trans hcap
      have hpairLt : a.adjacentDefect current <
          ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
        rw [hrawEq]
        apply WithTop.coe_lt_coe.mpr
        have hRQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
            (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by exact_mod_cast hR
        linarith
      have hprefix := a.heADCEvenEndpoint_signedPrefix_defect k (by omega)
        hIntegral hheadLast
      have hfullEq : defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) =
          a.adjacentDefect current := by
        rw [show k + 2 = (k + 1) + 1 by omega,
          a.toBONG.signedEvenPrefixProduct_succ (k + 1) (by omega)]
        exact defectOrder_mul_eq_right_of_lt_left (hpairLt.trans_le hprefix)
      exact (not_lt_of_ge hfull) (hfullEq.trans_lt hpairLt)
  have hlast : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    have hgap := a.orderGap_ge_neg_two_mul_e current
    change -(2 * (ramificationIndex K : Int)) ≤
      a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩ at hgap
    rw [hnext] at hgap
    by_contra hnot
    have hlastValue : a.order ⟨2 * k + 3, by omega⟩ =
        1 - 2 * (ramificationIndex K : Int) := by omega
    have hodd : Odd (a.orderGap current) := by
      change Odd (a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩)
      rw [hlastValue, hnext]
      exact ⟨-(ramificationIndex K : Int), by ring⟩
    have hpositive := a.heADC2025Corollary32i current hodd
    change 0 < a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩ at hpositive
    have he := ramificationIndex_pos (K := K)
    omega
  intro i
  by_cases hi : i.val < 2 * k + 2
  · exact hhead ⟨i.val, hi⟩
  · have hcases : i.val = 2 * k + 2 ∨ i.val = 2 * k + 3 := by omega
    rcases hcases with hprevious | hterminal
    · have hiEq : i = ⟨2 * k + 2, by omega⟩ := Fin.ext hprevious
      rw [hiEq]
      simpa only [if_pos (show Even (2 * k + 2) from ⟨k + 1, by omega⟩)] using hnext
    · have hiEq : i = ⟨2 * k + 3, by omega⟩ := Fin.ext hterminal
      rw [hiEq]
      have hodd : ¬ Even (2 * k + 3) := by rintro ⟨z, hz⟩; omega
      simpa only [if_neg hodd] using hlast

/-- Lemma 6.8(i) on a supplied good BONG, with the full n=2 case included. -/
theorem heADC2025Lemma68i_of_goodBONG (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) (1 : Kˣ)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) (1 : Kˣ)))
      L (heADCN1Even (k + 1) (1 : Kˣ)).lattice := by
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hnot : ¬ IsSquare ((1 : Kˣ) * δ) := by
    simpa only [one_mul] using
      AlternatingEndpointNormalization.discriminantUnit_not_isSquare (K := K)
  have hOne := Lattice.heADCEvenCorankTwoFirst_same k 1 hADC ambient
  have hDelta := Lattice.heADCEvenCorankTwoFirst_of_not_square k 1 δ hADC ambient hnot
  have hTwo := Lattice.heADCEvenCorankTwoSecond_of_not_square k 1 δ
    (heHuLemma43_evenSecondDefined k) hADC ambient hnot
  have hfull : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) := by
    rw [a.heADC_signedFullDefectOrder_of_ambient _ (by omega) (k + 2) (by omega) 1
      ambient (by simpa only [Nat.add_assoc] using
        heADCEvenFirst_determinantClass (K := K) (k + 1) 1), defectOrder_one]
    exact le_top
  have horders := a.heADCEvenCorankTwo_endpoint_orders k hADC.isIntegral hOne hDelta δ
    (heHuLemma43_evenSecondDefined k) (Or.inr rfl) hTwo hfull
  apply (heADC2025Lemma411iOnePublished (k + 1) (a.castLength (by omega))
    hADC.isIntegral ambient).mpr
  intro i
  rw [heADCMaximalOrderProfile_endpoint]
  simpa only [order_castLength] using horders ⟨i.val, by omega⟩

/-- Lemma 6.8(ii) on a supplied good BONG, retaining the published n>=4 restriction. -/
theorem heADC2025Lemma68ii_of_goodBONG (k : Nat) (hk : 0 < k)
    (a : GoodBONG q L (2 * k + 4)) (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1)
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1)
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
      L (heADCN1Even (k + 1)
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice := by
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hnot : ¬ IsSquare (δ * (1 : Kˣ)) := by
    simpa only [mul_one] using
      AlternatingEndpointNormalization.discriminantUnit_not_isSquare (K := K)
  have hOne := Lattice.heADCEvenCorankTwoFirst_of_not_square k δ 1 hADC ambient hnot
  have hDelta := Lattice.heADCEvenCorankTwoFirst_same k δ hADC ambient
  have hTwo := Lattice.heADCEvenCorankTwoSecond_of_not_square k δ 1 (Or.inl hk)
    hADC ambient hnot
  have hfull : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) := by
    rw [a.heADC_signedFullDefectOrder_of_ambient _ (by omega) (k + 2) (by omega) δ
      ambient (by simpa only [Nat.add_assoc] using heADCEvenFirst_determinantClass (k + 1) δ)]
    have hδ : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤ quadraticDefect K δ := by
      rw [(Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (natCast_le_defectOrder_iff δ (2 * ramificationIndex K)).mpr hδ
  have horders := a.heADCEvenCorankTwo_endpoint_orders k hADC.isIntegral hOne hDelta 1
    (Or.inl hk) (Or.inl rfl) hTwo hfull
  apply (heADC2025Lemma411iDeltaPublished (k + 1) (a.castLength (by omega))
    hADC.isIntegral ambient).mpr
  intro i
  rw [heADCMaximalOrderProfile_endpoint]
  simpa only [order_castLength] using horders ⟨i.val, by omega⟩

end BONG.GoodBONG

namespace Lattice

/-- He (2025), Lemma 6.8(i): an n-ADC lattice in the split corank-two space is maximal. -/
theorem heADC2025Lemma68i (k : Nat) (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) (1 : Kˣ)))) :
    IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) (1 : Kˣ)))
      L (heADCN1Even (k + 1) (1 : Kˣ)).lattice := by
  have hrank := (Classical.choice ambient).toLinearEquiv.finrank_eq
  rw [finrank_fin_fun] at hrank
  let a := (BONG.GoodBONG.ofLattice q L).castLength (by omega : finrank K V = 2 * k + 4)
  exact a.heADC2025Lemma68i_of_goodBONG k hADC ambient

/-- He (2025), Lemma 6.8(ii): the first discriminant row is maximal for even n>=4. -/
theorem heADC2025Lemma68ii (k : Nat) (hk : 0 < k)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1)
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))) :
    IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1)
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
      L (heADCN1Even (k + 1)
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice := by
  have hrank := (Classical.choice ambient).toLinearEquiv.finrank_eq
  rw [finrank_fin_fun] at hrank
  let a := (BONG.GoodBONG.ofLattice q L).castLength (by omega : finrank K V = 2 * k + 4)
  exact a.heADC2025Lemma68ii_of_goodBONG k hk hADC ambient

end Lattice

end Bong
