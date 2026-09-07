/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCDefinition716
import Bong.Bong.He2023ADCPublishedProfiles

/-!
# He (2025), Lemma 7.20(i)--(ii): the maximal endpoints

The symbol `M_{nu,r}^{n+2}(c)` was introduced in Definition 7.16 as an
isometry class.  Here the named maximal lattices from Definition 4.1 are
proved to realize the endpoint classes in Lemma 7.20.  The first column has
index `r=e` for both allowed parameter orders.  In the second column the
order-one parameter again has index `e`, while the order-zero parameter has
the exceptional index `e-1`.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The first-column named maximal lattice has penultimate order `-2e`
for a unit parameter. -/
theorem heADC2025Lemma720iFirstUnitOrder (k : Nat) (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) :
    (heADCMaximalGoodBONG (heADCW1Odd (k + 1) c)).order
        ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
  let a := heADCMaximalGoodBONG (heADCW1Odd (K := K) (k + 1) c)
  have hM := heHuOMaximalLattice_isOMaximal
    (heADCW1Odd (K := K) (k + 1) c)
  have hprofile := (heADC2025Lemma412iPublished c hc (k + 1)
    (a.castLength (by omega)) hM.isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp
      (Lattice.isIsometric_refl _ _)
  have h := hprofile ⟨2 * k + 3, by omega⟩
  have hodd : ¬ Even (2 * k + 3) := by
    rintro ⟨z, hz⟩
    omega
  simpa [a, order_castLength, heADCMaximalOrderProfile,
    show 2 * k + 3 < 2 * (k + 2) by omega, hodd] using h

/-- The first-column named maximal lattice has penultimate order `-2e`
for an order-one parameter. -/
theorem heADC2025Lemma720iFirstUniformizerOrder (k : Nat) (delta : Kˣ)
    (hdelta : IsValuationUnit K (delta : K)) :
    (heADCMaximalGoodBONG
      (heADCW1Odd (k + 1) (delta * uniformizerPowerUnit K 1))).order
        ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
  let c := delta * uniformizerPowerUnit K 1
  let a := heADCMaximalGoodBONG (heADCW1Odd (K := K) (k + 1) c)
  have hM := heHuOMaximalLattice_isOMaximal
    (heADCW1Odd (K := K) (k + 1) c)
  have hprofile := (heADC2025Lemma412iiiFirstPublished delta hdelta (k + 1)
    (a.castLength (by omega)) hM.isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp
      (Lattice.isIsometric_refl _ _)
  have h := hprofile ⟨2 * k + 3, by omega⟩
  have hodd : ¬ Even (2 * k + 3) := by
    rintro ⟨z, hz⟩
    omega
  simpa [a, c, order_castLength, heADCMaximalOrderProfile,
    show 2 * k + 3 < 2 * (k + 2) by omega, hodd] using h

/-- The second-column order-one named maximal lattice has penultimate
order `-2e`. -/
theorem heADC2025Lemma720iSecondUniformizerOrder (k : Nat) (delta : Kˣ)
    (hdelta : IsValuationUnit K (delta : K)) :
    (heADCMaximalGoodBONG
      (heADCW2Odd (k + 1) (delta * uniformizerPowerUnit K 1))).order
        ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
  let c := delta * uniformizerPowerUnit K 1
  let a := heADCMaximalGoodBONG (heADCW2Odd (K := K) (k + 1) c)
  have hM := heHuOMaximalLattice_isOMaximal
    (heADCW2Odd (K := K) (k + 1) c)
  have hprofile := (heADC2025Lemma412iiiSecondPublished delta hdelta (k + 1)
    (a.castLength (by omega)) hM.isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp
      (Lattice.isIsometric_refl _ _)
  have h := hprofile ⟨2 * k + 3, by omega⟩
  simpa [a, c, order_castLength, heADCMaximalOrderProfile,
    show ¬ 2 * k + 3 < 2 * (k + 1) by omega,
    show 2 * k + 3 - 2 * (k + 1) = 1 by omega] using h

/-- The second-column unit named maximal lattice has the exceptional
penultimate order `2-2e = -2(e-1)`. -/
theorem heADC2025Lemma720iiSecondUnitOrder (k : Nat) (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) :
    (heADCMaximalGoodBONG (heADCW2Odd (k + 1) c)).order
        ⟨2 * k + 3, by omega⟩ =
      -(2 * ((ramificationIndex K - 1 : Nat) : Int)) := by
  let a := heADCMaximalGoodBONG (heADCW2Odd (K := K) (k + 1) c)
  have hM := heHuOMaximalLattice_isOMaximal
    (heADCW2Odd (K := K) (k + 1) c)
  have hprofile := (heADC2025Lemma412iiPublished c hc (k + 1)
    (a.castLength (by omega)) hM.isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp
      (Lattice.isIsometric_refl _ _)
  have h := hprofile ⟨2 * k + 3, by omega⟩
  have hvalue :
      (heADCMaximalGoodBONG (heADCW2Odd (K := K) (k + 1) c)).order
          ⟨2 * k + 3, by omega⟩ =
        2 - 2 * (ramificationIndex K : Int) := by
    simpa [a, order_castLength, heADCMaximalOrderProfile,
      show ¬ 2 * k + 3 < 2 * (k + 1) by omega,
      show 2 * k + 3 - 2 * (k + 1) = 1 by omega] using h
  rw [hvalue]
  have he : 0 < ramificationIndex K := ramificationIndex_pos K
  omega

/-- Lemma 7.20(i), first column: the named maximal lattice realizes the
class `M_{1,e}^{n+2}(c)` for either allowed parameter order. -/
theorem heADC2025Lemma720iFirst (k : Nat) (c : Kˣ)
    (hc : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    HeADC2025Definition716 k (ramificationIndex K) HeADC716Column.one c
      (heADCMaximalGoodBONG (heADCW1Odd (k + 1) c)) := by
  let a := heADCMaximalGoodBONG (heADCW1Odd (K := K) (k + 1) c)
  have hM := heHuOMaximalLattice_isOMaximal
    (heADCW1Odd (K := K) (k + 1) c)
  refine
    { indexBound := le_rfl
      parameterOrder := hc
      nADC := hM.isNADC (2 * k + 3)
      ambient := QuadraticSpace.isIsometric_refl _
      penultimate := ?_ }
  rcases hc with hc | hc
  · exact heADC2025Lemma720iFirstUnitOrder k c
      ((isValuationUnit_iff_ordUnit_eq_zero K c).2 hc)
  · let delta := normalizedUnitPart K c
    have hdelta : IsValuationUnit K (delta : K) :=
      normalizedUnitPart_isValuationUnit K c
    have hnormalize : c = delta * uniformizerPowerUnit K 1 := by
      simpa only [delta, hc, mul_comm] using
        (uniformizerPower_mul_normalizedUnitPart K c).symm
    rw [hnormalize]
    exact heADC2025Lemma720iFirstUniformizerOrder k delta hdelta

/-- Lemma 7.20(i), second column: outside the excluded unit endpoint, the
named maximal lattice realizes `M_{2,e}^{n+2}(c)`. -/
theorem heADC2025Lemma720iSecond (k : Nat) (c : Kˣ)
    (hc : ordUnit K c = 1) :
    HeADC2025Definition716 k (ramificationIndex K) HeADC716Column.two c
      (heADCMaximalGoodBONG (heADCW2Odd (k + 1) c)) := by
  let a := heADCMaximalGoodBONG (heADCW2Odd (K := K) (k + 1) c)
  have hM := heHuOMaximalLattice_isOMaximal
    (heADCW2Odd (K := K) (k + 1) c)
  refine
    { indexBound := le_rfl
      parameterOrder := Or.inr hc
      nADC := hM.isNADC (2 * k + 3)
      ambient := QuadraticSpace.isIsometric_refl _
      penultimate := ?_ }
  let delta := normalizedUnitPart K c
  have hdelta : IsValuationUnit K (delta : K) :=
    normalizedUnitPart_isValuationUnit K c
  have hnormalize : c = delta * uniformizerPowerUnit K 1 := by
    simpa only [delta, hc, mul_comm] using
      (uniformizerPower_mul_normalizedUnitPart K c).symm
  rw [hnormalize]
  exact heADC2025Lemma720iSecondUniformizerOrder k delta hdelta

/-- Lemma 7.20(ii): the excluded maximal endpoint reappears one row lower,
as `M_{2,e-1}^{n+2}(c)` for a unit parameter. -/
theorem heADC2025Lemma720ii (k : Nat) (c : Kˣ)
    (hc : ordUnit K c = 0) :
    HeADC2025Definition716 k (ramificationIndex K - 1)
      HeADC716Column.two c
      (heADCMaximalGoodBONG (heADCW2Odd (k + 1) c)) := by
  let a := heADCMaximalGoodBONG (heADCW2Odd (K := K) (k + 1) c)
  have hM := heHuOMaximalLattice_isOMaximal
    (heADCW2Odd (K := K) (k + 1) c)
  refine
    { indexBound := Nat.sub_le _ _
      parameterOrder := Or.inl hc
      nADC := hM.isNADC (2 * k + 3)
      ambient := QuadraticSpace.isIsometric_refl _
      penultimate := ?_ }
  exact heADC2025Lemma720iiSecondUnitOrder k c
    ((isValuationUnit_iff_ordUnit_eq_zero K c).2 hc)

/-- Any realization of the first-column endpoint class is isometric to the
named maximal lattice, which is the isometry assertion in Lemma 7.20(i). -/
theorem heADC2025Lemma720iFirst_isometricNamed
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (k : Nat) (c : Kˣ) (a : GoodBONG q L (2 * k + 5))
    (A : HeADC2025Definition716 k (ramificationIndex K)
      HeADC716Column.one c a) :
    Lattice.IsIsometric q
      (BONG.coefficientDiagonalSpace (heADCW1Odd (k + 1) c)) L
      (heADCN1Odd (k + 1) c).lattice := by
  exact heADC2025Remark717_unique k (ramificationIndex K)
    HeADC716Column.one c a
    (heADCMaximalGoodBONG (heADCW1Odd (k + 1) c)) A
    (heADC2025Lemma720iFirst k c A.parameterOrder)

/-- Any realization of the nonexceptional second-column endpoint class is
isometric to the named maximal lattice. -/
theorem heADC2025Lemma720iSecond_isometricNamed
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (k : Nat) (c : Kˣ) (a : GoodBONG q L (2 * k + 5))
    (hc : ordUnit K c = 1)
    (A : HeADC2025Definition716 k (ramificationIndex K)
      HeADC716Column.two c a) :
    Lattice.IsIsometric q
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) c)) L
      (heADCN2Odd (k + 1) c).lattice := by
  exact heADC2025Remark717_unique k (ramificationIndex K)
    HeADC716Column.two c a
    (heADCMaximalGoodBONG (heADCW2Odd (k + 1) c)) A
    (heADC2025Lemma720iSecond k c hc)

/-- Any realization of the exceptional second-column row is isometric to
the named maximal lattice, which is Lemma 7.20(ii). -/
theorem heADC2025Lemma720ii_isometricNamed
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (k : Nat) (c : Kˣ) (a : GoodBONG q L (2 * k + 5))
    (hc : ordUnit K c = 0)
    (A : HeADC2025Definition716 k (ramificationIndex K - 1)
      HeADC716Column.two c a) :
    Lattice.IsIsometric q
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) c)) L
      (heADCN2Odd (k + 1) c).lattice := by
  exact heADC2025Remark717_unique k (ramificationIndex K - 1)
    HeADC716Column.two c a
    (heADCMaximalGoodBONG (heADCW2Odd (k + 1) c)) A
    (heADC2025Lemma720ii k c hc)

end BONG.GoodBONG

end Bong
