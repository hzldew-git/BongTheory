/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma97
import Bong.Bong.BinaryDiagonalExactBONG
import Bong.Bong.BinaryDiagonalHyperbolic
import Bong.Bong.Beli2019Lemma95NormalForm
import Bong.Bong.BeliLemma313

/-!
# Beli (2019), Lemma 9.8: the odd binary branch

Lemma 9.5 writes the ternary lattice as a unary line orthogonal to a binary
block.  When both first alpha invariants are odd, the two displayed orders in
the binary blocks differ by even integers.  The exact model BONG constructed
in `BinaryDiagonalExactBONG` therefore lets Lemma 9.7(i) apply literally.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Lemma 9.7(i) specialized to the exact BONGs of two explicit binary
diagonal models. -/
theorem binaryDiagonalModel_represents_of_exactComparison
    [BONGStructuralLaws.{u, u} K]
    (targetFirst targetSecond sourceFirst sourceSecond : Kˣ)
    (targetAdmissible :
      IsBinaryParameterAdmissible (targetSecond / targetFirst))
    (sourceAdmissible :
      IsBinaryParameterAdmissible (sourceSecond / sourceFirst))
    (horders : ∀ i : Fin 2,
      ![ordUnit K targetFirst, ordUnit K targetSecond] i ≤
        ![ordUnit K sourceFirst, ordUnit K sourceSecond] i)
    (hparity : ∀ i : Fin 2, Int.ModEq 2
      (![ordUnit K sourceFirst, ordUnit K sourceSecond] i)
      (![ordUnit K targetFirst, ordUnit K targetSecond] i))
    (hnormalized : ∀ i : Fin 2,
      normalizedUnitPart K (![targetFirst, targetSecond] i) =
        normalizedUnitPart K (![sourceFirst, sourceSecond] i)) :
    Lattice.Represents
      (binaryDiagonalModelSpace targetFirst targetSecond targetAdmissible)
      (binaryDiagonalModelSpace sourceFirst sourceSecond sourceAdmissible)
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) := by
  let target := binaryDiagonalExactGoodBONG
    targetFirst targetSecond targetAdmissible
  let source := binaryDiagonalExactGoodBONG
    sourceFirst sourceSecond sourceAdmissible
  apply BONG.GoodBONG.beli2019Lemma97_i target source
  · intro i
    simpa only [target, source,
      binaryDiagonalExactGoodBONG_order] using horders i
  · intro i
    simpa only [target, source,
      binaryDiagonalExactGoodBONG_order] using hparity i
  · intro i
    simpa only [target, source,
      binaryDiagonalExactGoodBONG_normalizedValue] using hnormalized i

/-- The binary comparison used in the odd--odd branch of Lemma 9.8.  The
two parity hypotheses are the relations between the two alphas supplied by
Remark 8.7. -/
theorem beli2019Lemma98_binary_odd
    [BONGStructuralLaws.{u, u} K]
    (R A₁ A₂ B₁ B₂ : Int) (twist : Kˣ)
    (htwist : IsValuationUnit K (twist : K))
    (targetAdmissible : IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K (R - A₂) * twist) /
        uniformizerPowerUnit K (R + A₁)))
    (sourceAdmissible : IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K (R - B₂) * twist) /
        uniformizerPowerUnit K (R + B₁)))
    (hfirst : A₁ ≤ B₁) (hsecond : B₂ ≤ A₂)
    (hA₁Odd : Odd A₁) (hB₁Odd : Odd B₁)
    (hAParity : Even (A₁ - A₂))
    (hBParity : Even (B₁ - B₂)) :
    Lattice.Represents
      (binaryDiagonalModelSpace
        (uniformizerPowerUnit K (R + A₁))
        (-(uniformizerPowerUnit K (R - A₂) * twist))
        targetAdmissible)
      (binaryDiagonalModelSpace
        (uniformizerPowerUnit K (R + B₁))
        (-(uniformizerPowerUnit K (R - B₂) * twist))
        sourceAdmissible)
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) := by
  have htwistOrder : ordUnit K twist = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K twist).1 htwist
  have hnegTwist : IsValuationUnit K ((-twist : Kˣ) : K) := by
    change ord K (-((twist : K))) = 0
    rw [ord_neg]
    exact htwist
  have hA₂Odd : Odd A₂ := by
    rcases hA₁Odd with ⟨a, ha⟩
    rcases hAParity with ⟨k, hk⟩
    exact ⟨a - k, by omega⟩
  have hB₂Odd : Odd B₂ := by
    rcases hB₁Odd with ⟨b, hb⟩
    rcases hBParity with ⟨k, hk⟩
    exact ⟨b - k, by omega⟩
  apply binaryDiagonalModel_represents_of_exactComparison
  · intro i
    fin_cases i
    · change ordUnit K (uniformizerPowerUnit K (R + A₁)) ≤
        ordUnit K (uniformizerPowerUnit K (R + B₁))
      rw [ordUnit_uniformizerPowerUnit,
        ordUnit_uniformizerPowerUnit]
      omega
    · change ordUnit K (-(uniformizerPowerUnit K (R - A₂) * twist)) ≤
        ordUnit K (-(uniformizerPowerUnit K (R - B₂) * twist))
      rw [ordUnit_neg, ordUnit_mul, ordUnit_uniformizerPowerUnit,
        htwistOrder, ordUnit_neg, ordUnit_mul,
        ordUnit_uniformizerPowerUnit, htwistOrder]
      omega
  · intro i
    fin_cases i
    · change Int.ModEq 2
        (ordUnit K (uniformizerPowerUnit K (R + B₁)))
        (ordUnit K (uniformizerPowerUnit K (R + A₁)))
      rw [ordUnit_uniformizerPowerUnit,
        ordUnit_uniformizerPowerUnit, Int.modEq_iff_dvd]
      rcases hA₁Odd with ⟨a, ha⟩
      rcases hB₁Odd with ⟨b, hb⟩
      exact ⟨a - b, by omega⟩
    · change Int.ModEq 2
        (ordUnit K (-(uniformizerPowerUnit K (R - B₂) * twist)))
        (ordUnit K (-(uniformizerPowerUnit K (R - A₂) * twist)))
      rw [ordUnit_neg, ordUnit_mul, ordUnit_uniformizerPowerUnit,
        htwistOrder, ordUnit_neg, ordUnit_mul,
        ordUnit_uniformizerPowerUnit, htwistOrder,
        Int.modEq_iff_dvd]
      rcases hA₂Odd with ⟨a, ha⟩
      rcases hB₂Odd with ⟨b, hb⟩
      exact ⟨b - a, by omega⟩
  · intro i
    fin_cases i
    · change normalizedUnitPart K
          (uniformizerPowerUnit K (R + A₁)) =
        normalizedUnitPart K
          (uniformizerPowerUnit K (R + B₁))
      simpa using
        (normalizedUnitPart_uniformizerPower_mul_valuationUnit
          (K := K) (R + A₁) (1 : Kˣ)
          (by simp [IsValuationUnit])) |>.trans
            (normalizedUnitPart_uniformizerPower_mul_valuationUnit
              (K := K) (R + B₁) (1 : Kˣ)
              (by simp [IsValuationUnit])).symm
    · change normalizedUnitPart K
          (-(uniformizerPowerUnit K (R - A₂) * twist)) =
        normalizedUnitPart K
          (-(uniformizerPowerUnit K (R - B₂) * twist))
      have htarget :
          normalizedUnitPart K
              (-(uniformizerPowerUnit K (R - A₂) * twist)) =
            -twist := by
        rw [show -(uniformizerPowerUnit K (R - A₂) * twist) =
            uniformizerPowerUnit K (R - A₂) * (-twist) by
          simp]
        exact normalizedUnitPart_uniformizerPower_mul_valuationUnit
          (K := K) (R - A₂) (-twist) hnegTwist
      have hsource :
          normalizedUnitPart K
              (-(uniformizerPowerUnit K (R - B₂) * twist)) =
            -twist := by
        rw [show -(uniformizerPowerUnit K (R - B₂) * twist) =
            uniformizerPowerUnit K (R - B₂) * (-twist) by
          simp]
        exact normalizedUnitPart_uniformizerPower_mul_valuationUnit
          (K := K) (R - B₂) (-twist) hnegTwist
      exact htarget.trans hsource.symm

/-- The binary comparison used in either even branch of Lemma 9.8.  The
displayed binary spaces are both hyperbolic, while Lemma 9.5(iii) supplies
the stronger integral scaled-hyperbolic hypothesis for whichever first
alpha is even. -/
theorem beli2019Lemma98_binary_even
    [BONGStructuralLaws.{u, u} K]
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
    (R A₁ A₂ B₁ B₂ : Int)
    (targetAdmissible : IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K (R - A₂)) /
        uniformizerPowerUnit K (R + A₁)))
    (sourceAdmissible : IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K (R - B₂)) /
        uniformizerPowerUnit K (R + B₁)))
    (hfirst : A₁ ≤ B₁) (hsecond : B₂ ≤ A₂)
    (hAParity : Even (A₁ - A₂))
    (hBParity : Even (B₁ - B₂))
    (hhyperbolic :
      Lattice.IsScaledHyperbolicLattice
          (binaryDiagonalModelSpace
            (uniformizerPowerUnit K (R + A₁))
            (-(uniformizerPowerUnit K (R - A₂)))
            targetAdmissible)
          (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) ∨
        Lattice.IsScaledHyperbolicLattice
          (binaryDiagonalModelSpace
            (uniformizerPowerUnit K (R + B₁))
            (-(uniformizerPowerUnit K (R - B₂)))
            sourceAdmissible)
          (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))) :
    Lattice.Represents
      (binaryDiagonalModelSpace
        (uniformizerPowerUnit K (R + A₁))
        (-(uniformizerPowerUnit K (R - A₂)))
        targetAdmissible)
      (binaryDiagonalModelSpace
        (uniformizerPowerUnit K (R + B₁))
        (-(uniformizerPowerUnit K (R - B₂)))
        sourceAdmissible)
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) := by
  have htargetRatio :
      -(uniformizerPowerUnit K (R + A₁) /
          (-(uniformizerPowerUnit K (R - A₂)))) =
        uniformizerPowerUnit K (A₁ + A₂) := by
    calc
      -(uniformizerPowerUnit K (R + A₁) /
          (-(uniformizerPowerUnit K (R - A₂)))) =
          uniformizerPowerUnit K (R + A₁) /
            uniformizerPowerUnit K (R - A₂) := by
        apply Units.ext
        simp only [Units.val_neg, Units.val_div_eq_div_val]
        rw [← neg_div, neg_div_neg_eq]
      _ = uniformizerPowerUnit K (A₁ + A₂) := by
        unfold uniformizerPowerUnit
        rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
        congr 1
        omega
  have hsourceRatio :
      -(uniformizerPowerUnit K (R + B₁) /
          (-(uniformizerPowerUnit K (R - B₂)))) =
        uniformizerPowerUnit K (B₁ + B₂) := by
    calc
      -(uniformizerPowerUnit K (R + B₁) /
          (-(uniformizerPowerUnit K (R - B₂)))) =
          uniformizerPowerUnit K (R + B₁) /
            uniformizerPowerUnit K (R - B₂) := by
        apply Units.ext
        simp only [Units.val_neg, Units.val_div_eq_div_val]
        rw [← neg_div, neg_div_neg_eq]
      _ = uniformizerPowerUnit K (B₁ + B₂) := by
        unfold uniformizerPowerUnit
        rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
        congr 1
        omega
  have htargetSquare : IsSquare
      (-(uniformizerPowerUnit K (R + A₁) /
        (-(uniformizerPowerUnit K (R - A₂))))) := by
    rw [htargetRatio]
    have hASumEven : Even (A₁ + A₂) := by
      rcases hAParity with ⟨k, hk⟩
      exact ⟨A₂ + k, by omega⟩
    exact GoodBONG.isSquare_uniformizerPowerUnit_of_even
      (K := K) (A₁ + A₂) hASumEven
  have hsourceSquare : IsSquare
      (-(uniformizerPowerUnit K (R + B₁) /
        (-(uniformizerPowerUnit K (R - B₂))))) := by
    rw [hsourceRatio]
    have hBSumEven : Even (B₁ + B₂) := by
      rcases hBParity with ⟨k, hk⟩
      exact ⟨B₂ + k, by omega⟩
    exact GoodBONG.isSquare_uniformizerPowerUnit_of_even
      (K := K) (B₁ + B₂) hBSumEven
  let target := binaryDiagonalExactGoodBONG
    (uniformizerPowerUnit K (R + A₁))
    (-(uniformizerPowerUnit K (R - A₂))) targetAdmissible
  let source := binaryDiagonalExactGoodBONG
    (uniformizerPowerUnit K (R + B₁))
    (-(uniformizerPowerUnit K (R - B₂))) sourceAdmissible
  apply BONG.GoodBONG.beli2019Lemma97_ii target source
  · intro i
    fin_cases i
    · simp [target, source, binaryDiagonalExactGoodBONG_order,
        ordUnit_uniformizerPowerUnit]
      omega
    · simp [target, source, binaryDiagonalExactGoodBONG_order,
        ordUnit_neg, ordUnit_uniformizerPowerUnit]
      omega
  · exact binaryDiagonalModel_isIsometric_of_signedRatioSquares
      (uniformizerPowerUnit K (R + A₁))
      (-(uniformizerPowerUnit K (R - A₂)))
      (uniformizerPowerUnit K (R + B₁))
      (-(uniformizerPowerUnit K (R - B₂)))
      targetAdmissible sourceAdmissible htargetSquare hsourceSquare
  · exact hhyperbolic

/-- The complete isotropic binary comparison in Lemma 9.8.  The two
functions expose exactly the scaled-hyperbolic conclusion supplied by
Lemma 9.5(iii) when the corresponding first alpha is even. -/
theorem beli2019Lemma98_binary_isotropic
    [BONGStructuralLaws.{u, u} K]
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
    (R A₁ A₂ B₁ B₂ : Int)
    (targetAdmissible : IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K (R - A₂)) /
        uniformizerPowerUnit K (R + A₁)))
    (sourceAdmissible : IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K (R - B₂)) /
        uniformizerPowerUnit K (R + B₁)))
    (hfirst : A₁ ≤ B₁) (hsecond : B₂ ≤ A₂)
    (hAParity : Even (A₁ - A₂))
    (hBParity : Even (B₁ - B₂))
    (hhyperA : Even A₁ →
      Lattice.IsScaledHyperbolicLattice
        (binaryDiagonalModelSpace
          (uniformizerPowerUnit K (R + A₁))
          (-(uniformizerPowerUnit K (R - A₂))) targetAdmissible)
        (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)))
    (hhyperB : Even B₁ →
      Lattice.IsScaledHyperbolicLattice
        (binaryDiagonalModelSpace
          (uniformizerPowerUnit K (R + B₁))
          (-(uniformizerPowerUnit K (R - B₂))) sourceAdmissible)
        (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))) :
    Lattice.Represents
      (binaryDiagonalModelSpace
        (uniformizerPowerUnit K (R + A₁))
        (-(uniformizerPowerUnit K (R - A₂))) targetAdmissible)
      (binaryDiagonalModelSpace
        (uniformizerPowerUnit K (R + B₁))
        (-(uniformizerPowerUnit K (R - B₂))) sourceAdmissible)
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) := by
  rcases Int.even_or_odd A₁ with hA₁Even | hA₁Odd
  · exact beli2019Lemma98_binary_even R A₁ A₂ B₁ B₂
      targetAdmissible sourceAdmissible hfirst hsecond hAParity hBParity
      (Or.inl (hhyperA hA₁Even))
  · rcases Int.even_or_odd B₁ with hB₁Even | hB₁Odd
    · exact beli2019Lemma98_binary_even R A₁ A₂ B₁ B₂
        targetAdmissible sourceAdmissible hfirst hsecond hAParity hBParity
        (Or.inr (hhyperB hB₁Even))
    · simpa only [mul_one] using
        beli2019Lemma98_binary_odd (K := K) R A₁ A₂ B₁ B₂ 1
          (by simp [IsValuationUnit])
          (by simpa only [mul_one] using targetAdmissible)
          (by simpa only [mul_one] using sourceAdmissible)
          hfirst hsecond hA₁Odd hB₁Odd hAParity hBParity

end BONG

end Bong
