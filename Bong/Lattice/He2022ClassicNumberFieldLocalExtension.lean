/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Number-field coefficient extension for He (2024), Lemma 8.1

This file proves the order-scaling and ramification-tower statements for a
nonzero coefficient in a number field and two height-one primes in a finite
extension.  It is the dense global-coefficient specialization of Lemma 8.1(i),
not yet the statement for every element of the completed local field.

The final adapter derives the three arithmetic fields of
`HeClassic2024LocalExtensionData.Lemma81Laws`.  Quadratic-defect scaling and
good-BONG scalar extension remain explicit inputs.
-/

open scoped NumberField

namespace Bong.HeClassic2024NumberFieldLocalExtension

/-- The additive order of a nonzero number-field element at a height-one
prime, obtained from mathlib's multiplicative adic valuation. -/
noncomputable def adicOrder {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) : Int :=
  -(p.valuation K (x : K)).log

/-- The order-scaling part of He (2024), Lemma 8.1(i), for a nonzero
coefficient in the underlying number field. -/
theorem adicOrder_liesOver
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] (x : Kˣ) :
    adicOrder P (Units.map (algebraMap K L) x) =
      adicOrder p x *
        (P.asIdeal.ramificationIdx (𝓞 K) : Int) := by
  have hrel :
      p.asIdeal.ramificationIdx' P.asIdeal =
        P.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx
      p.asIdeal P.asIdeal p.ne_bot
  unfold adicOrder
  change
    -((P.valuation L) ((algebraMap K L) (x : K))).log =
      -(p.valuation K (x : K)).log *
        (P.asIdeal.ramificationIdx (𝓞 K) : Int)
  rw [← p.valuation_liesOver L P (x : K), WithZero.log_pow, hrel]
  simp only [nsmul_eq_mul]
  ring

/-- Positivity of the relative ramification index at a prime lying over the
chosen base prime. -/
theorem relativeRamificationIndex_pos
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] :
    0 < P.asIdeal.ramificationIdx (𝓞 K) := by
  exact Ideal.ramificationIdx_pos P.asIdeal (𝓞 K)

/-- The absolute ramification indices satisfy
`e(P / 2) = e(p / 2) * e(P / p)`. -/
theorem absoluteRamificationIndex_tower
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] :
    P.asIdeal.ramificationIdx ℤ =
      p.asIdeal.ramificationIdx ℤ *
        P.asIdeal.ramificationIdx (𝓞 K) := by
  exact Ideal.ramificationIdx_tower p.asIdeal P.asIdeal

/-- The still-unformalized parts of Lemma 8.1 after specializing its
coefficients to `Kˣ` and deriving order and ramification from prime ideals. -/
structure RemainingCoefficientInputs
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) where
  baseDefect : Kˣ → WithTop ℚ
  extensionDefect : Kˣ → WithTop ℚ
  BaseGoodBONG : {m : Nat} → (Fin m → Kˣ) → Prop
  ExtensionGoodBONG : {m : Nat} → (Fin m → Kˣ) → Prop
  defect_scale (x : Kˣ) :
    (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : ℚ) : WithTop ℚ) *
        baseDefect x ≤ extensionDefect x
  goodBONG_transfer {m : Nat} (a : Fin m → Kˣ) :
    BaseGoodBONG a → ExtensionGoodBONG a

/-- Interpret the number-field coefficient specialization in the abstract
local-extension interface used by Section 8. -/
noncomputable def RemainingCoefficientInputs.toLocalExtensionData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal]
    (D : RemainingCoefficientInputs p P) :
    HeClassic2024LocalExtensionData where
  Element := Kˣ
  baseOrder := adicOrder p
  extensionOrder x := adicOrder P (Units.map (algebraMap K L) x)
  baseDefect := D.baseDefect
  extensionDefect := D.extensionDefect
  baseRamificationIndex := p.asIdeal.ramificationIdx ℤ
  extensionRamificationIndex := P.asIdeal.ramificationIdx ℤ
  relativeRamificationIndex := P.asIdeal.ramificationIdx (𝓞 K)
  BaseGoodBONG := D.BaseGoodBONG
  ExtensionGoodBONG := D.ExtensionGoodBONG

/-- Derive the order, positivity, and ramification-tower fields of Lemma 8.1;
only defect scaling and good-BONG transfer are supplied by the caller. -/
theorem RemainingCoefficientInputs.lemma81Laws
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal]
    (D : RemainingCoefficientInputs p P) :
    D.toLocalExtensionData.Lemma81Laws where
  relativeRamificationIndex_pos := relativeRamificationIndex_pos p P
  ramificationIndex_tower := absoluteRamificationIndex_tower p P
  order_scale := adicOrder_liesOver p P
  defect_scale := D.defect_scale
  goodBONG_transfer := D.goodBONG_transfer

end Bong.HeClassic2024NumberFieldLocalExtension
