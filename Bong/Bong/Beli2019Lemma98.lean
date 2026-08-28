/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma98Binary
import Bong.Bong.Beli2019Lemma95
import Bong.Bong.UnaryBinaryModelRepresentation
import Bong.Bong.Beli2019NecessityComplete
import Bong.Bong.Beli2019Lemma94

/-!
# Beli (2019), Lemma 9.8

This file assembles the explicit ternary normal forms from Lemma 9.5, the
binary comparisons from Lemmas 9.7--9.8, and the unary--binary product
isometries.  In particular, the sufficiency proof does not invoke Theorem 2.1.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- Under the equal-outer-order hypothesis, both ternary alpha invariants
are rational integers.  Remark 8.7 bounds their sum by `2e`, excluding the
half-integral branch of Corollary 2.8(iii). -/
theorem beli2019Lemma95_alphas_isRationalInteger
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3)) :
    IsRationalInteger (a.alphaValue (0 : Fin 2)) ∧
      IsRationalInteger (a.alphaValue (1 : Fin 2)) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hsum : a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    simpa [remark87PreviousAlpha, remark87CurrentAlpha] using
      hremark.alphaSum_le_twoE
  have hzeroNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have honeNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  constructor
  · rcases a.beli2009Corollary28_iii (0 : Fin 2) with hsmall | hlarge
    · exact hsmall.2.2
    · exfalso
      linarith [hlarge.1]
  · rcases a.beli2009Corollary28_iii (1 : Fin 2) with hsmall | hlarge
    · exact hsmall.2.2
    · exfalso
      linarith [hlarge.1]

/-- An even integer witness for an alpha invariant forces the half-gap
equality.  This is the contrapositive of Lemma 2.7(iv). -/
theorem attainsHalfGap_of_alphaInteger_even
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3) (i : Fin 2) (A : Int)
    (hA : a.alphaValue i = (A : ℚ)) (hEven : Even A) :
    a.AttainsHalfGap i := by
  unfold AttainsHalfGap
  by_contra hne
  rcases a.beli2009Lemma27_iv i hne with ⟨z, hzOdd, hz⟩
  have hAz : A = z := by
    exact_mod_cast hA.symm.trans hz
  subst z
  exact (Int.not_odd_iff_even.mpr hEven) hzOdd

/-- The isotropic/anisotropic branch of Lemma 9.5 depends only on the
ambient ternary quadratic space, not on the chosen lattice or BONG. -/
theorem lemma95_firstThreeIsotropic_iff_sameSpace
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG q M 3) :
    a.Lemma814FirstThreeIsotropic ↔
      b.Lemma814FirstThreeIsotropic := by
  rw [a.lemma814FirstThreeIsotropic_iff_diagonalValueUnits,
    b.lemma814FirstThreeIsotropic_iff_diagonalValueUnits]
  constructor
  · intro ha
    have hrep := a.toBONG.diagonalRepresents_values b.toBONG
    apply hrep.isotropic_of
    have hcoeff : diagonalUnitCoefficients a.valueUnit =
        a.toBONG.value := by
      funext i
      exact a.toBONG.coe_valueUnit i
    rw [← hcoeff]
    exact ha
  · intro hb
    have hrep := b.toBONG.diagonalRepresents_values a.toBONG
    apply hrep.isotropic_of
    have hcoeff : diagonalUnitCoefficients b.valueUnit =
        b.toBONG.value := by
      funext i
      exact b.toBONG.coe_valueUnit i
    rw [← hcoeff]
    exact hb

/-- Normalizing an equality up to a square keeps the square relation and
replaces its multiplier by a valuation unit. -/
theorem normalizedUnitPart_eq_mul_square_of_eq_mul_square
    (a b p : Kˣ) (h : b = a * p ^ 2) :
    normalizedUnitPart K b =
      normalizedUnitPart K a * (normalizedUnitPart K p) ^ 2 := by
  have hord := congrArg (ordUnit K) h
  rw [ordUnit_mul, ordUnit_pow] at hord
  have hpower :
      uniformizerPowerUnit K (-ordUnit K b) =
        uniformizerPowerUnit K (-ordUnit K a) *
          (uniformizerPowerUnit K (-ordUnit K p)) ^ 2 := by
    rw [hord]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
    omega
  unfold normalizedUnitPart
  rw [hpower, h]
  simp only [pow_two]
  ac_rfl

/-- The two determinant-unit factors attached to BONGs in the same ternary
space differ by the square of a valuation unit. -/
theorem exists_ternaryDeterminantUnitPart_eq_mul_unit_square
    (a : GoodBONG q L 3) (b : GoodBONG q M 3) :
    ∃ scale : Kˣ, IsValuationUnit K (scale : K) ∧
      b.ternaryDeterminantUnitPart =
        a.ternaryDeterminantUnitPart * scale ^ 2 := by
  rcases BONG.exists_valueProduct_eq_mul_square a.toBONG b.toBONG with
    ⟨p, hp⟩
  refine ⟨normalizedUnitPart K p,
    normalizedUnitPart_isValuationUnit K p, ?_⟩
  exact normalizedUnitPart_eq_mul_square_of_eq_mul_square
    a.toBONG.valueProduct b.toBONG.valueProduct p hp

/-- Transport a representation between two explicit models back across
lattice isometries from the original target and source lattices. -/
theorem represents_of_isometric_models
    {X : Type w} [AddCommGroup X] [Module K X]
    {Y : Type z} [AddCommGroup Y] [Module K Y]
    {qx : QuadraticSpace K X} {qy : QuadraticSpace K Y}
    {LX : Lattice K X} {LY : Lattice K Y}
    (htarget : Lattice.IsIsometric q qx L LX)
    (hsource : Lattice.IsIsometric q qy M LY)
    (hmodels : Lattice.Represents qx qy LX LY) :
    Lattice.Represents q q L M := by
  rcases htarget with ⟨ftarget⟩
  rcases hsource with ⟨fsource⟩
  have htargetBack : Lattice.Represents q qx L LX :=
    ⟨ftarget.symm.toRepresentation⟩
  have hsourceForward : Lattice.Represents qy q LY M :=
    ⟨fsource.toRepresentation⟩
  exact (htargetBack.trans hmodels).trans hsourceForward

/-- Reassemble a represented binary block with an isometric unary head and
transport the resulting unary--binary representation back to the original
ternary lattices. -/
theorem represents_of_unaryBinary_models
    (targetHead sourceHead scale : Kˣ)
    (hscale : IsValuationUnit K (scale : K))
    (hsourceHead : sourceHead = targetHead * scale ^ 2)
    (targetFirst targetSecond sourceFirst sourceSecond : Kˣ)
    (targetAdmissible :
      IsBinaryParameterAdmissible (targetSecond / targetFirst))
    (sourceAdmissible :
      IsBinaryParameterAdmissible (sourceSecond / sourceFirst))
    (htarget : Lattice.IsIsometric q
      (unaryBinaryModelSpace targetHead targetFirst targetSecond
        targetAdmissible)
      L (unaryBinaryModelLattice (K := K)))
    (hsource : Lattice.IsIsometric q
      (unaryBinaryModelSpace sourceHead sourceFirst sourceSecond
        sourceAdmissible)
      M (unaryBinaryModelLattice (K := K)))
    (hbinary : Lattice.Represents
      (binaryDiagonalModelSpace targetFirst targetSecond targetAdmissible)
      (binaryDiagonalModelSpace sourceFirst sourceSecond sourceAdmissible)
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))) :
    Lattice.Represents q q L M := by
  apply represents_of_isometric_models htarget hsource
  exact BONG.unaryBinaryModel_represents_of_valuationUnitSquare
    targetHead sourceHead scale hscale hsourceHead
    targetFirst targetSecond sourceFirst sourceSecond
    targetAdmissible sourceAdmissible hbinary

/-- Sufficiency in Lemma 9.8 with explicit integer witnesses for the four
alpha invariants. -/
theorem beli2019Lemma98_sufficiency_integer
    [QuadraticDefectLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaSource : Beli2006AlphaLaws.{u, v} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    (a : GoodBONG q L 3) (b : GoodBONG q M 3)
    (houterA : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (houterB : b.order (0 : Fin 3) = b.order (2 : Fin 3))
    (hfirstOrder : a.order (0 : Fin 3) = b.order (0 : Fin 3))
    (A₁ A₂ B₁ B₂ : Int)
    (hA₁ : a.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hA₂ : a.alphaValue (1 : Fin 2) = (A₂ : ℚ))
    (hB₁ : b.alphaValue (0 : Fin 2) = (B₁ : ℚ))
    (hB₂ : b.alphaValue (1 : Fin 2) = (B₂ : ℚ))
    (hfirst : A₁ ≤ B₁) (hsecond : B₂ ≤ A₂) :
    Lattice.Represents q q L M := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaSource
  have hAParity : Even (A₁ - A₂) :=
    a.beli2019Lemma95_alphaInteger_sameParity
      houterA A₁ A₂ hA₁ hA₂
  have hBParity : Even (B₁ - B₂) :=
    b.beli2019Lemma95_alphaInteger_sameParity
      houterB B₁ B₂ hB₁ hB₂
  have hisotropyIff := a.lemma95_firstThreeIsotropic_iff_sameSpace b
  rcases a.exists_ternaryDeterminantUnitPart_eq_mul_unit_square b with
    ⟨scale, hscale, hdet⟩
  have hhead (twist : Kˣ) :
      b.beli2019Lemma95NormalFormValues B₁ B₂ twist 0 =
        a.beli2019Lemma95NormalFormValues A₁ A₂ twist 0 *
          scale ^ 2 := by
    rw [beli2019Lemma95NormalFormValues_zero,
      beli2019Lemma95NormalFormValues_zero, ← hfirstOrder, hdet]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  by_cases hisotropicA : a.Lemma814FirstThreeIsotropic
  · have hisotropicB : b.Lemma814FirstThreeIsotropic :=
      hisotropyIff.mp hisotropicA
    let targetAdmissible : IsBinaryParameterAdmissible
        (-(uniformizerPowerUnit K (a.order 0 - A₂)) /
          uniformizerPowerUnit K (a.order 0 + A₁)) := by
      simpa only [beli2019Lemma95NormalFormValues_one,
        beli2019Lemma95NormalFormValues_two, mul_one] using
          a.beli2019Lemma95NormalForm_binaryAdmissible_one
            houterA A₁ A₂ hA₁ hA₂
    let sourceAdmissible : IsBinaryParameterAdmissible
        (-(uniformizerPowerUnit K (a.order 0 - B₂)) /
          uniformizerPowerUnit K (a.order 0 + B₁)) := by
      have h := b.beli2019Lemma95NormalForm_binaryAdmissible_one
        houterB B₁ B₂ hB₁ hB₂
      simpa only [beli2019Lemma95NormalFormValues_one,
        beli2019Lemma95NormalFormValues_two, mul_one, ← hfirstOrder] using h
    have hhyperA (hA₁Even : Even A₁) :
        Lattice.IsScaledHyperbolicLattice
          (binaryDiagonalModelSpace
            (uniformizerPowerUnit K (a.order 0 + A₁))
            (-(uniformizerPowerUnit K (a.order 0 - A₂)))
            targetAdmissible)
          (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) := by
      have hhalfA := a.attainsHalfGap_of_alphaInteger_even
        (0 : Fin 2) A₁ hA₁ hA₁Even
      let targetBONG := BONG.binaryDiagonalExactBONG
        (uniformizerPowerUnit K (a.order 0 + A₁))
        (-(uniformizerPowerUnit K (a.order 0 - A₂))) targetAdmissible
      have htargetZero : targetBONG.valueUnit (0 : Fin 2) =
          uniformizerPowerUnit K (a.order 0 + A₁) := by
        apply Units.ext
        change targetBONG.value (0 : Fin 2) =
          (uniformizerPowerUnit K (a.order 0 + A₁) : K)
        simpa only [targetBONG] using BONG.binaryDiagonalExactBONG_value_zero
          (uniformizerPowerUnit K (a.order 0 + A₁))
          (-(uniformizerPowerUnit K (a.order 0 - A₂))) targetAdmissible
      have htargetOne : targetBONG.valueUnit (1 : Fin 2) =
          -(uniformizerPowerUnit K (a.order 0 - A₂)) := by
        apply Units.ext
        change targetBONG.value (1 : Fin 2) =
          ((-(uniformizerPowerUnit K (a.order 0 - A₂)) : Kˣ) : K)
        simpa only [targetBONG] using BONG.binaryDiagonalExactBONG_value_one
          (uniformizerPowerUnit K (a.order 0 + A₁))
          (-(uniformizerPowerUnit K (a.order 0 - A₂))) targetAdmissible
      refine ⟨(a.order 0 + a.order 1) / 2, ?_⟩
      exact a.beli2019Lemma95_iii targetBONG houterA A₁ A₂ hA₁ hA₂
        hhalfA htargetZero htargetOne
    have hhyperB (hB₁Even : Even B₁) :
        Lattice.IsScaledHyperbolicLattice
          (binaryDiagonalModelSpace
            (uniformizerPowerUnit K (a.order 0 + B₁))
            (-(uniformizerPowerUnit K (a.order 0 - B₂)))
            sourceAdmissible)
          (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) := by
      have hhalfB := b.attainsHalfGap_of_alphaInteger_even
        (0 : Fin 2) B₁ hB₁ hB₁Even
      let sourceBONG := BONG.binaryDiagonalExactBONG
        (uniformizerPowerUnit K (a.order 0 + B₁))
        (-(uniformizerPowerUnit K (a.order 0 - B₂))) sourceAdmissible
      have hsourceZero : sourceBONG.valueUnit (0 : Fin 2) =
          uniformizerPowerUnit K (b.order 0 + B₁) := by
        rw [← hfirstOrder]
        apply Units.ext
        change sourceBONG.value (0 : Fin 2) =
          (uniformizerPowerUnit K (a.order 0 + B₁) : K)
        simpa only [sourceBONG] using BONG.binaryDiagonalExactBONG_value_zero
          (uniformizerPowerUnit K (a.order 0 + B₁))
          (-(uniformizerPowerUnit K (a.order 0 - B₂))) sourceAdmissible
      have hsourceOne : sourceBONG.valueUnit (1 : Fin 2) =
          -(uniformizerPowerUnit K (b.order 0 - B₂)) := by
        rw [← hfirstOrder]
        apply Units.ext
        change sourceBONG.value (1 : Fin 2) =
          ((-(uniformizerPowerUnit K (a.order 0 - B₂)) : Kˣ) : K)
        simpa only [sourceBONG] using BONG.binaryDiagonalExactBONG_value_one
          (uniformizerPowerUnit K (a.order 0 + B₁))
          (-(uniformizerPowerUnit K (a.order 0 - B₂))) sourceAdmissible
      refine ⟨(b.order 0 + b.order 1) / 2, ?_⟩
      exact b.beli2019Lemma95_iii sourceBONG houterB B₁ B₂ hB₁ hB₂
        hhalfB hsourceZero hsourceOne
    have hbinary := BONG.beli2019Lemma98_binary_isotropic
      (a.order 0) A₁ A₂ B₁ B₂ targetAdmissible sourceAdmissible
      hfirst hsecond hAParity hBParity hhyperA hhyperB
    have hbinaryRaw : Lattice.Represents
        (binaryDiagonalModelSpace
          (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 1)
          (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 2)
          (a.beli2019Lemma95NormalForm_binaryAdmissible_one
            houterA A₁ A₂ hA₁ hA₂))
        (binaryDiagonalModelSpace
          (b.beli2019Lemma95NormalFormValues B₁ B₂ 1 1)
          (b.beli2019Lemma95NormalFormValues B₁ B₂ 1 2)
          (b.beli2019Lemma95NormalForm_binaryAdmissible_one
            houterB B₁ B₂ hB₁ hB₂))
        (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))
        (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) := by
      simpa only [beli2019Lemma95NormalFormValues_one,
        beli2019Lemma95NormalFormValues_two, mul_one, ← hfirstOrder] using
          hbinary
    exact represents_of_unaryBinary_models
      (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 0)
      (b.beli2019Lemma95NormalFormValues B₁ B₂ 1 0)
      scale hscale (hhead 1)
      (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 1)
      (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 2)
      (b.beli2019Lemma95NormalFormValues B₁ B₂ 1 1)
      (b.beli2019Lemma95NormalFormValues B₁ B₂ 1 2)
      (a.beli2019Lemma95NormalForm_binaryAdmissible_one
        houterA A₁ A₂ hA₁ hA₂)
      (b.beli2019Lemma95NormalForm_binaryAdmissible_one
        houterB B₁ B₂ hB₁ hB₂)
      (a.beli2019Lemma95_ii_isotropic
        (alphaSource := alphaSource) (alphaModel := alphaModel)
        houterA A₁ A₂ hA₁ hA₂ hisotropicA)
      (b.beli2019Lemma95_ii_isotropic
        (alphaSource := alphaSource) (alphaModel := alphaModel)
        houterB B₁ B₂ hB₁ hB₂ hisotropicB)
      hbinaryRaw
  · have hnotIsotropicB : ¬b.Lemma814FirstThreeIsotropic := by
      intro hB
      exact hisotropicA (hisotropyIff.mpr hB)
    have hanisotropicA : a.Lemma814FirstThreeAnisotropic :=
      (a.not_firstThreeIsotropic_iff_anisotropic).mp hisotropicA
    have hanisotropicB : b.Lemma814FirstThreeAnisotropic :=
      (b.not_firstThreeIsotropic_iff_anisotropic).mp hnotIsotropicB
    rcases a.beli2019Lemma95_i houterA hanisotropicA with
      ⟨A, hAOdd, hA⟩
    rcases b.beli2019Lemma95_i houterB hanisotropicB with
      ⟨B, hBOdd, hB⟩
    have hAeq : A₁ = A := by
      exact_mod_cast hA₁.symm.trans hA
    have hBeq : B₁ = B := by
      exact_mod_cast hB₁.symm.trans hB
    have hA₁Odd : Odd A₁ := by simpa [hAeq] using hAOdd
    have hB₁Odd : Odd B₁ := by simpa [hBeq] using hBOdd
    let targetAdmissible : IsBinaryParameterAdmissible
        (-(uniformizerPowerUnit K (a.order 0 - A₂) *
            disc.discriminantUnit) /
          uniformizerPowerUnit K (a.order 0 + A₁)) := by
      simpa only [beli2019Lemma95NormalFormValues_one,
        beli2019Lemma95NormalFormValues_two] using
          a.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
            houterA A₁ A₂ hA₁ hA₂
    let sourceAdmissible : IsBinaryParameterAdmissible
        (-(uniformizerPowerUnit K (a.order 0 - B₂) *
            disc.discriminantUnit) /
          uniformizerPowerUnit K (a.order 0 + B₁)) := by
      have h := b.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
        houterB B₁ B₂ hB₁ hB₂
      simpa only [beli2019Lemma95NormalFormValues_one,
        beli2019Lemma95NormalFormValues_two, ← hfirstOrder] using h
    have hbinary := BONG.beli2019Lemma98_binary_odd
      (a.order 0) A₁ A₂ B₁ B₂ disc.discriminantUnit
      disc.discriminant_isValuationUnit targetAdmissible sourceAdmissible
      hfirst hsecond hA₁Odd hB₁Odd hAParity hBParity
    have hbinaryRaw : Lattice.Represents
        (binaryDiagonalModelSpace
          (a.beli2019Lemma95NormalFormValues A₁ A₂
            disc.discriminantUnit 1)
          (a.beli2019Lemma95NormalFormValues A₁ A₂
            disc.discriminantUnit 2)
          (a.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
            houterA A₁ A₂ hA₁ hA₂))
        (binaryDiagonalModelSpace
          (b.beli2019Lemma95NormalFormValues B₁ B₂
            disc.discriminantUnit 1)
          (b.beli2019Lemma95NormalFormValues B₁ B₂
            disc.discriminantUnit 2)
          (b.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
            houterB B₁ B₂ hB₁ hB₂))
        (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))
        (binaryDiagonalModelLattice : Lattice K (Fin 2 → K)) := by
      simpa only [beli2019Lemma95NormalFormValues_one,
        beli2019Lemma95NormalFormValues_two, ← hfirstOrder] using hbinary
    exact represents_of_unaryBinary_models
      (a.beli2019Lemma95NormalFormValues A₁ A₂
        disc.discriminantUnit 0)
      (b.beli2019Lemma95NormalFormValues B₁ B₂
        disc.discriminantUnit 0)
      scale hscale (hhead disc.discriminantUnit)
      (a.beli2019Lemma95NormalFormValues A₁ A₂
        disc.discriminantUnit 1)
      (a.beli2019Lemma95NormalFormValues A₁ A₂
        disc.discriminantUnit 2)
      (b.beli2019Lemma95NormalFormValues B₁ B₂
        disc.discriminantUnit 1)
      (b.beli2019Lemma95NormalFormValues B₁ B₂
        disc.discriminantUnit 2)
      (a.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
        houterA A₁ A₂ hA₁ hA₂)
      (b.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
        houterB B₁ B₂ hB₁ hB₂)
      (a.beli2019Lemma95_ii_anisotropic
        (alphaSource := alphaSource) (alphaModel := alphaModel)
        houterA A₁ A₂ hA₁ hA₂ hanisotropicA)
      (b.beli2019Lemma95_ii_anisotropic
        (alphaSource := alphaSource) (alphaModel := alphaModel)
        houterB B₁ B₂ hB₁ hB₂ hanisotropicB)
      hbinaryRaw

/-- Sufficiency in Beli (2019), Lemma 9.8, stated only in terms of the
paper's alpha inequalities.  Integrality of the four alpha values follows
from the equal-outer-order hypotheses. -/
theorem beli2019Lemma98_sufficiency
    [QuadraticDefectLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaSource : Beli2006AlphaLaws.{u, v} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    (a : GoodBONG q L 3) (b : GoodBONG q M 3)
    (houterA : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (houterB : b.order (0 : Fin 3) = b.order (2 : Fin 3))
    (hfirstOrder : a.order (0 : Fin 3) = b.order (0 : Fin 3))
    (hfirst : a.alphaValue (0 : Fin 2) ≤ b.alphaValue (0 : Fin 2))
    (hsecond : b.alphaValue (1 : Fin 2) ≤ a.alphaValue (1 : Fin 2)) :
    Lattice.Represents q q L M := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaSource
  rcases a.beli2019Lemma95_alphas_isRationalInteger houterA with
    ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩⟩
  rcases b.beli2019Lemma95_alphas_isRationalInteger houterB with
    ⟨⟨B₁, hB₁⟩, ⟨B₂, hB₂⟩⟩
  have hfirstInt : A₁ ≤ B₁ := by
    rw [hA₁, hB₁] at hfirst
    exact_mod_cast hfirst
  have hsecondInt : B₂ ≤ A₂ := by
    rw [hB₂, hA₂] at hsecond
    exact_mod_cast hsecond
  exact a.beli2019Lemma98_sufficiency_integer
    (alphaSource := alphaSource) (alphaModel := alphaModel)
    b houterA houterB hfirstOrder A₁ A₂ B₁ B₂
    hA₁ hA₂ hB₁ hB₂ hfirstInt hsecondInt

/-- Beli (2019), Lemma 9.8.  For ternary lattices in the same quadratic
space with `R₁ = R₃ = S₁ = S₃`, representation is equivalent to the two
alpha inequalities appearing in the paper. -/
theorem beli2019Lemma98
    [QuadraticDefectLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [structuralSource : BONGStructuralLaws.{u, v} K]
    [BONGGoodExistenceLaws.{u, u} K]
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaSource : Beli2006AlphaLaws.{u, v} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [classificationSource : GoodBONGClassificationLaws.{u, v, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    [GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG q M 3)
    (houterA : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (houterB : b.order (0 : Fin 3) = b.order (2 : Fin 3))
    (hfirstOrder : a.order (0 : Fin 3) = b.order (0 : Fin 3)) :
    Lattice.Represents q q L M ↔
      a.alphaValue (0 : Fin 2) ≤ b.alphaValue (0 : Fin 2) ∧
        b.alphaValue (1 : Fin 2) ≤ a.alphaValue (1 : Fin 2) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaSource
  constructor
  · intro hrepresentation
    letI : BONGStructuralLaws.{u, v} K := structuralSource
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationSource
    have hconditions := beli2019_necessity
      (sourceLaws := alphaSource) (targetLaws := alphaSource)
      a b (Nat.le_refl 2) hrepresentation
    exact (a.beli2019Lemma94 b houterA houterB hfirstOrder).mp hconditions
  · rintro ⟨hfirst, hsecond⟩
    letI : BONGStructuralLaws.{u, u} K := structuralModel
    letI : GoodBONGClassificationLaws.{u, v, u} K := classificationModel
    exact a.beli2019Lemma98_sufficiency
      (alphaSource := alphaSource) (alphaModel := alphaModel)
      b houterA houterB hfirstOrder hfirst hsecond

end BONG.GoodBONG

end Bong
