/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankTwoGenericOrders

/-!
# Actual tests for both nonexceptional columns in He (2025), Lemma 6.8

The signed determinant class gives the three required ambient embeddings.
The n-ADC property supplies integral representations and hence the full
generic order profile. The two ambient columns use the same argument.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The nonexceptional class domain excludes the product with the discriminant class. -/
theorem heADCSharp_mul_discriminant_not_square (c : Kˣ) (hs : HeHuSharpDomain c) :
    ¬ IsSquare (c * (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit) := by
  intro h
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have H := h.div (show IsSquare (δ ^ 2) from ⟨δ, pow_two δ⟩)
  apply hs.notDiscriminantSquare
  simpa [δ, pow_two, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using H

namespace Lattice

/-- Internal proof data for three actual maximal tests, not a new paper definition. -/
structure HeADCEvenCorankTwoThreeTests (k : Nat)
    (q : QuadraticSpace K V) (L : Lattice K V) : Prop where
  one : Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))
    L (heADCN1Even k (1 : Kˣ)).lattice
  delta : Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
    L (heADCN1Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice
  secondDelta : Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) k))) L (heADCN2Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) k)).lattice

/-- A nonexceptional ambient determinant supplies all three actual maximal tests. -/
theorem heADCEvenCorankTwo_tests_of_sharp_ambient (k : Nat) (c : Kˣ)
    (hs : HeHuSharpDomain c) {m : Nat} (w : Fin m → Kˣ) (hm : m = (2 * k + 2) + 2)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace w))
    (hclass : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ (k + 2) * c))) :
    HeADCEvenCorankTwoThreeTests k q L := by
  have lift (source : Fin (2 * k + 2) → Kˣ) (d : Kˣ)
      (hsource : IsSquare (diagonalUnitDeterminant source * ((-1 : Kˣ) ^ (k + 1) * d)))
      (hd : ¬ IsSquare (d * c)) :
      Represents q (BONG.coefficientDiagonalSpace source) L (heHuOMaximalLattice source) :=
    heADCMaximal_represents_of_ambient_model hADC source w ambient
      (heADCEvenCodimensionTwo_represents_of_parameter_not_square k hm source w d c
        hsource hclass hd)
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hδ : ¬ IsSquare (δ * c) := by
    simpa only [mul_comm] using heADCSharp_mul_discriminant_not_square c hs
  refine ⟨?_, ?_, ?_⟩
  · exact lift _ 1 (heADCEvenFirst_determinantClass k 1) (by simpa using hs.notSquare)
  · exact lift _ δ (heADCEvenFirst_determinantClass k δ) hδ
  · exact lift _ δ (heADCEvenSecond_determinantClass k δ (heHuLemma43_evenSecondDefined k)) hδ

end Lattice

namespace BONG.GoodBONG

/-- The generic profile is derived from n-ADC and the actual nonexceptional ambient model. -/
theorem heADCEvenCorankTwo_sharp_orders (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (c : Kˣ) (hs : HeHuSharpDomain c) {m : Nat} (w : Fin m → Kˣ)
    (hm : 2 * k + 4 = m) (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace w))
    (hclass : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ (k + 2) * c))) :
    ∀ i, a.order i = heADCMaximalOrderProfile (K := K) (k + 1)
      ![0, 1 - ((quadraticDefect K c).toNat : Int)] ⟨i.val, by omega⟩ := by
  have tests := Lattice.heADCEvenCorankTwo_tests_of_sharp_ambient k c hs w
    (by omega) hADC ambient hclass
  obtain ⟨hd, hdefect⟩ := heADCSharpDefectData c hs
  apply a.heADCEvenCorankTwo_orders_of_finite_full_defect k hADC.isIntegral
    tests.one tests.delta tests.secondDelta _ hd
  exact (a.heADC_signedFullDefectOrder_of_ambient w hm (k + 2) (by omega) c
    ambient hclass).trans hdefect

end BONG.GoodBONG

end Bong
