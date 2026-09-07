/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryEndpoint

/-!
# Named nonexceptional binary tests for the quaternary boundary candidate

The source-side hypotheses are supplied by the actual candidate. Target
orders come from the proved maximal-lattice table and the full defect is
transported from its determinant class. No ADC premise is used.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A maximal binary model with the displayed sharp profile is represented whenever relevant. -/
theorem heADCQuaternaryBoundaryCandidate_represents_profiledMaximal
    (w : Fin 2 → Kˣ) (c : Kˣ) (hs : HeHuSharpDomain c)
    (hclass : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) * c)))
    (hprofile : ∀ i, (heADCMaximalGoodBONG w).order i =
      (![0, 1 - ((quadraticDefect K c).toNat : Int)] : Fin 2 → Int) i)
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace w)) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace w) (heADCQuaternaryBoundaryLattice (K := K))
      (heHuOMaximalLattice w) := by
  let b := heADCMaximalGoodBONG w
  let d := (quadraticDefect K c).toNat
  have hd : d < 2 * ramificationIndex K := by
    have h := (heHuSharpData c hs).sourceDefect_lt_twoE
    change (d : ℚ) < 2 * (ramificationIndex K : ℚ) at h
    exact_mod_cast h
  have hdefect : defectOrder (K := K) c = ((d : ℚ) : WithTop ℚ) :=
    (heHuSharpData c hs).source_defectOrder
  have hbRaw := b.heADC_signedFullDefectOrder_of_ambient w rfl 1 rfl c
    (QuadraticSpace.isIsometric_refl _) (by simpa only [pow_one] using hclass)
  have hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ) := by
    simpa only [BONG.signedEvenPrefixProduct, pow_one, GoodBONG.prefixProduct] using
      hbRaw.trans hdefect
  exact heADCQuaternaryBoundaryCandidate_represents_finite b d hd
    (hprofile 0) (hprofile 1) hb ambient

/-- All nonexceptional unit tests in the first column are actually represented when relevant. -/
theorem heADCQuaternaryBoundaryCandidate_represents_unitFirst (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) (hs : HeHuSharpDomain c)
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 c))) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 c))
      (heADCQuaternaryBoundaryLattice (K := K)) (heADCN1Even 0 c).lattice := by
  let b := heADCMaximalGoodBONG (heADCW1Even 0 c)
  have hprofile := (heADC2025Lemma411iiiUnitFirstPublished c hc hs 0 b
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  apply heADCQuaternaryBoundaryCandidate_represents_profiledMaximal _ c hs
    (by simpa only [Nat.zero_add, pow_one] using heADCEvenFirst_determinantClass 0 c) _ ambient
  intro i
  simpa [heADCMaximalOrderProfile, b] using hprofile i

/-- All nonexceptional unit tests in the second column are actually represented when relevant. -/
theorem heADCQuaternaryBoundaryCandidate_represents_unitSecond (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) (hs : HeHuSharpDomain c)
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW2Even 0 c (Or.inr hs.notSquare)))) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW2Even 0 c (Or.inr hs.notSquare)))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heADCN2Even 0 c (Or.inr hs.notSquare)).lattice := by
  let b := heADCMaximalGoodBONG (heADCW2Even 0 c (Or.inr hs.notSquare))
  have hprofile := (heADC2025Lemma411iiiUnitSecondPublished c hc hs 0 b
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  apply heADCQuaternaryBoundaryCandidate_represents_profiledMaximal _ c hs
    (by simpa only [Nat.zero_add, pow_one] using
      heADCEvenSecond_determinantClass 0 c (Or.inr hs.notSquare)) _ ambient
  intro i
  simpa [heADCMaximalOrderProfile, b] using hprofile i

/-- A unit times the uniformizer has odd valuation and hence quadratic defect zero. -/
theorem heADCBoundary_unitUniformizer_defect_zero (δ : Kˣ)
    (hδ : IsValuationUnit K (δ : K)) :
    quadraticDefect K (δ * uniformizerPowerUnit K 1) = 0 := by
  apply quadraticDefect_eq_zero_of_odd_ordUnit
  rw [ordUnit_mul, (isValuationUnit_iff_ordUnit_eq_zero K δ).mp hδ,
    ordUnit_uniformizerPowerUnit, zero_add]
  exact odd_one

/-- Every first-column unit-uniformizer binary test is represented when its space is relevant. -/
theorem heADCQuaternaryBoundaryCandidate_represents_uniformizerFirst (δ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 (δ * uniformizerPowerUnit K 1)))) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 (δ * uniformizerPowerUnit K 1)))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heADCN1Even 0 (δ * uniformizerPowerUnit K 1)).lattice := by
  let c := δ * uniformizerPowerUnit K 1
  let b := heADCMaximalGoodBONG (heADCW1Even 0 c)
  have hs := heADCUnitUniformizerSharpDomain δ hδ
  have hprofile := (heADC2025Lemma411iiiUniformizerFirstPublished δ hδ 0 b
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  apply heADCQuaternaryBoundaryCandidate_represents_profiledMaximal _ c hs
    (by simpa only [Nat.zero_add, pow_one] using heADCEvenFirst_determinantClass 0 c) _ ambient
  intro i
  simpa [heADCMaximalOrderProfile, b, c, heADCBoundary_unitUniformizer_defect_zero δ hδ]
    using hprofile i

/-- Every second-column unit-uniformizer binary test is represented when relevant. -/
theorem heADCQuaternaryBoundaryCandidate_represents_uniformizerSecond (δ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW2Even 0 (δ * uniformizerPowerUnit K 1)
        (Or.inr (heADCUnitUniformizerSharpDomain δ hδ).notSquare)))) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW2Even 0 (δ * uniformizerPowerUnit K 1)
        (Or.inr (heADCUnitUniformizerSharpDomain δ hδ).notSquare)))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heADCN2Even 0 (δ * uniformizerPowerUnit K 1)
        (Or.inr (heADCUnitUniformizerSharpDomain δ hδ).notSquare)).lattice := by
  let c := δ * uniformizerPowerUnit K 1
  let hs := heADCUnitUniformizerSharpDomain δ hδ
  let b := heADCMaximalGoodBONG (heADCW2Even 0 c (Or.inr hs.notSquare))
  have hprofile := (heADC2025Lemma411iiiUniformizerSecondPublished δ hδ 0 b
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  apply heADCQuaternaryBoundaryCandidate_represents_profiledMaximal _ c hs
    (by simpa only [Nat.zero_add, pow_one] using
      heADCEvenSecond_determinantClass 0 c (Or.inr hs.notSquare)) _ ambient
  intro i
  simpa [heADCMaximalOrderProfile, b, c, heADCBoundary_unitUniformizer_defect_zero δ hδ]
    using hprofile i

end BONG.GoodBONG

end Bong
