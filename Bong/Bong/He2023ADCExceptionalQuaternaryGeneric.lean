/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCExceptionalQuaternaryTests

/-!
# Named nonexceptional tests for the exceptional quaternary lattice

The target orders are supplied by the proved maximal-lattice catalogue, and
the target defect is transported from its determinant square class.  The
extra parity input required by the exceptional source profile is derived from
the same unit and unit-uniformizer alternatives used in He (2025), Lemma 6.12.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A maximal binary model with the displayed finite-defect profile is
represented whenever it is ambiently relevant. -/
theorem heADCExceptionalQuaternaryCandidate_represents_profiledMaximal
    (w : Fin 2 → Kˣ) (c : Kˣ) (hs : HeHuSharpDomain c)
    (hparity : (quadraticDefect K c).toNat = 0 ∨
      Odd (quadraticDefect K c).toNat)
    (hclass : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) * c)))
    (hprofile : ∀ i, (heADCMaximalGoodBONG w).order i =
      (![0, 1 - ((quadraticDefect K c).toNat : Int)] : Fin 2 → Int) i)
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace w)) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace w) (heADCExceptionalQuaternaryLattice (K := K))
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
  exact heADCExceptionalQuaternaryCandidate_represents_finite b d hd hparity
    (hprofile 0) (hprofile 1) hb ambient

/-- The natural quadratic-defect index of a nonexceptional unit is odd. -/
theorem heADCExceptional_unitSharpDefect_odd (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) (hs : HeHuSharpDomain c) :
    Odd (quadraticDefect K c).toNat := by
  obtain ⟨hodd, _, _, _⟩ := heADCUnitSharpDefectData c hc hs
  exact_mod_cast hodd

/-- All nonexceptional unit tests in the first column are represented when relevant. -/
theorem heADCExceptionalQuaternaryCandidate_represents_unitFirst (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) (hs : HeHuSharpDomain c)
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 c))) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 c))
      (heADCExceptionalQuaternaryLattice (K := K)) (heADCN1Even 0 c).lattice := by
  let b := heADCMaximalGoodBONG (heADCW1Even 0 c)
  have hprofile := (heADC2025Lemma411iiiUnitFirstPublished c hc hs 0 b
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  apply heADCExceptionalQuaternaryCandidate_represents_profiledMaximal _ c hs
    (Or.inr (heADCExceptional_unitSharpDefect_odd c hc hs))
    (by simpa only [Nat.zero_add, pow_one] using heADCEvenFirst_determinantClass 0 c)
    _ ambient
  intro i
  simpa [heADCMaximalOrderProfile, b] using hprofile i

/-- All nonexceptional unit tests in the second column are represented when relevant. -/
theorem heADCExceptionalQuaternaryCandidate_represents_unitSecond (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) (hs : HeHuSharpDomain c)
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW2Even 0 c (Or.inr hs.notSquare)))) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW2Even 0 c (Or.inr hs.notSquare)))
      (heADCExceptionalQuaternaryLattice (K := K))
      (heADCN2Even 0 c (Or.inr hs.notSquare)).lattice := by
  let b := heADCMaximalGoodBONG (heADCW2Even 0 c (Or.inr hs.notSquare))
  have hprofile := (heADC2025Lemma411iiiUnitSecondPublished c hc hs 0 b
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  apply heADCExceptionalQuaternaryCandidate_represents_profiledMaximal _ c hs
    (Or.inr (heADCExceptional_unitSharpDefect_odd c hc hs))
    (by simpa only [Nat.zero_add, pow_one] using
      heADCEvenSecond_determinantClass 0 c (Or.inr hs.notSquare)) _ ambient
  intro i
  simpa [heADCMaximalOrderProfile, b] using hprofile i

/-- A unit times one uniformizer has quadratic defect zero. -/
theorem heADCExceptional_unitUniformizer_defect_zero (delta : Kˣ)
    (hdelta : IsValuationUnit K (delta : K)) :
    quadraticDefect K (delta * uniformizerPowerUnit K 1) = 0 := by
  apply quadraticDefect_eq_zero_of_odd_ordUnit
  rw [ordUnit_mul, (isValuationUnit_iff_ordUnit_eq_zero K delta).mp hdelta,
    ordUnit_uniformizerPowerUnit, zero_add]
  exact odd_one

/-- Every first-column unit-uniformizer test is represented when relevant. -/
theorem heADCExceptionalQuaternaryCandidate_represents_uniformizerFirst (delta : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace
        (heADCW1Even 0 (delta * uniformizerPowerUnit K 1)))) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace
        (heADCW1Even 0 (delta * uniformizerPowerUnit K 1)))
      (heADCExceptionalQuaternaryLattice (K := K))
      (heADCN1Even 0 (delta * uniformizerPowerUnit K 1)).lattice := by
  let c := delta * uniformizerPowerUnit K 1
  let b := heADCMaximalGoodBONG (heADCW1Even 0 c)
  have hs := heADCUnitUniformizerSharpDomain delta hdelta
  have hzero := heADCExceptional_unitUniformizer_defect_zero delta hdelta
  have hprofile := (heADC2025Lemma411iiiUniformizerFirstPublished delta hdelta 0 b
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  apply heADCExceptionalQuaternaryCandidate_represents_profiledMaximal _ c hs
    (by left; simp [c, hzero])
    (by simpa only [Nat.zero_add, pow_one] using heADCEvenFirst_determinantClass 0 c)
    _ ambient
  intro i
  simpa [heADCMaximalOrderProfile, b, c, hzero] using hprofile i

/-- Every second-column unit-uniformizer test is represented when relevant. -/
theorem heADCExceptionalQuaternaryCandidate_represents_uniformizerSecond (delta : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW2Even 0
        (delta * uniformizerPowerUnit K 1)
        (Or.inr (heADCUnitUniformizerSharpDomain delta hdelta).notSquare)))) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW2Even 0
        (delta * uniformizerPowerUnit K 1)
        (Or.inr (heADCUnitUniformizerSharpDomain delta hdelta).notSquare)))
      (heADCExceptionalQuaternaryLattice (K := K))
      (heADCN2Even 0 (delta * uniformizerPowerUnit K 1)
        (Or.inr (heADCUnitUniformizerSharpDomain delta hdelta).notSquare)).lattice := by
  let c := delta * uniformizerPowerUnit K 1
  let hs := heADCUnitUniformizerSharpDomain delta hdelta
  let b := heADCMaximalGoodBONG (heADCW2Even 0 c (Or.inr hs.notSquare))
  have hzero := heADCExceptional_unitUniformizer_defect_zero delta hdelta
  have hprofile := (heADC2025Lemma411iiiUniformizerSecondPublished delta hdelta 0 b
    (heHuOMaximalLattice_isOMaximal _).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  apply heADCExceptionalQuaternaryCandidate_represents_profiledMaximal _ c hs
    (by left; simp [c, hzero])
    (by simpa only [Nat.zero_add, pow_one] using
      heADCEvenSecond_determinantClass 0 c (Or.inr hs.notSquare)) _ ambient
  intro i
  simpa [heADCMaximalOrderProfile, b, c, hzero] using hprofile i

end BONG.GoodBONG

end Bong
