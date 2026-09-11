/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenSecondEndpointTests

/-!
# He (2025), Lemma 6.8(iii), and the n>=4 part of (iv)

The complementary endpoint and kappa tests are derived from the actual
ambient space and n-ADC property. The resulting full profile identifies
the source with the named maximal lattice by the proved Lemma 4.11(ii).
The discriminant ambient case at n=2 is not asserted in this file.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Lemma 6.8(iii), with all required profiles derived on the actual source good BONG. -/
theorem heADC2025Lemma68iii_of_goodBONG (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))))
      L (heADCN2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))).lattice := by
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hnot : ¬ IsSquare (δ * (1 : Kˣ)) := by
    simpa only [mul_one] using
      AlternatingEndpointNormalization.discriminantUnit_not_isSquare (K := K)
  obtain ⟨hhead, hnext, hlast⟩ := a.heADCSecondEndpoint_orders k 1 δ (Or.inl rfl)
    (Or.inr rfl) (heHuLemma43_evenSecondDefined k) hnot hADC ambient
  have horders := a.heADCSecondEndpoint_full_profile k hhead hnext hlast
  apply (heADC2025Lemma411iiOnePublished k (a.castLength (by omega))
    hADC.isIntegral ambient).mpr
  intro i
  rw [heADCMaximalOrderProfile_raisedFour]
  simpa only [order_castLength] using horders ⟨i.val, by omega⟩

/-- The n>=4 part of Lemma 6.8(iv); the smaller square second test requires this restriction. -/
theorem heADC2025Lemma68iv_of_goodBONG_of_pos (k : Nat) (hk : 0 < k)
    (a : GoodBONG q L (2 * k + 4)) (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1)
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) (k + 1))))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1)
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) (k + 1))))
      L (heADCN2Even (k + 1) (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) (k + 1))).lattice := by
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hnot : ¬ IsSquare ((1 : Kˣ) * δ) := by
    simpa only [one_mul] using
      AlternatingEndpointNormalization.discriminantUnit_not_isSquare (K := K)
  obtain ⟨hhead, hnext, hlast⟩ := a.heADCSecondEndpoint_orders k δ 1 (Or.inr rfl)
    (Or.inl rfl) (Or.inl hk) hnot hADC ambient
  have horders := a.heADCSecondEndpoint_full_profile k hhead hnext hlast
  apply (heADC2025Lemma411iiDeltaPublished (k + 1) (a.castLength (by omega))
    hADC.isIntegral ambient).mpr
  intro i
  simpa only [order_castLength] using horders ⟨i.val, by omega⟩

end BONG.GoodBONG

namespace Lattice

open BONG.GoodBONG

/-- He (2025), Lemma 6.8(iii), for every even n>=2 and arbitrary actual n-ADC lattice. -/
theorem heADC2025Lemma68iii (k : Nat) (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))))) :
    IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))))
      L (heADCN2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))).lattice := by
  have hrank := (Classical.choice ambient).toLinearEquiv.finrank_eq
  rw [finrank_fin_fun] at hrank
  let a := (BONG.GoodBONG.ofLattice q L).castLength (by omega : finrank K V = 2 * k + 4)
  exact a.heADC2025Lemma68iii_of_goodBONG k hADC ambient

/-- Lemma 6.8(iv) for even n>=4, without claiming its remaining n=2 boundary. -/
theorem heADC2025Lemma68iv_of_pos (k : Nat) (hk : 0 < k)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1)
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) (k + 1))))) :
    IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1)
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) (k + 1))))
      L (heADCN2Even (k + 1) (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) (k + 1))).lattice := by
  have hrank := (Classical.choice ambient).toLinearEquiv.finrank_eq
  rw [finrank_fin_fun] at hrank
  let a := (BONG.GoodBONG.ofLattice q L).castLength (by omega : finrank K V = 2 * k + 4)
  exact a.heADC2025Lemma68iv_of_goodBONG_of_pos k hk hADC ambient

end Lattice

end Bong
