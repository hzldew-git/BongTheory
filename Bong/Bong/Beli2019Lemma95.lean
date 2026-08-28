/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814Sufficiency
import Bong.Bong.BinaryHyperbolicEndpoint
import Bong.Bong.Beli2019Lemma95Jordan

/-!
# Beli (2019), Lemma 9.5

This file begins the formalization of the ternary equal-outer-order normal
form used in Section 9.  Part (i) is a direct consequence of the parity
argument already needed in the proof of Lemma 8.14, together with the
even order difference supplied by Remark 8.7.

The paper uses one-based indices: its `α₁` is `alphaValue 0` below.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Beli (2019), Lemma 9.5(i): if a ternary quadratic space with
`R₁ = R₃` is anisotropic, then the first alpha invariant is an odd
rational integer.

The anisotropy predicate is stated on the diagonal coefficients of the
good BONG, hence is exactly the coordinate form of the paper's assumption
that the ambient ternary space is not isotropic. -/
theorem beli2019Lemma95_i
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    IsOddRationalInteger (a.alphaValue (0 : Fin 2)) := by
  have hsecondOdd : IsOddRationalInteger
      (a.alphaValue (1 : Fin 2)) :=
    a.secondAlpha_isOddRationalInteger_of_equalOuter_anisotropic
      houter hanisotropic
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  rcases hsecondOdd with ⟨z, hzOdd, hz⟩
  have horderMod := hremark.previous_middle_modEq
  rw [Int.modEq_iff_dvd] at horderMod
  rcases horderMod with ⟨k, hk⟩
  have hk' : a.order (1 : Fin 3) - a.order (0 : Fin 3) = 2 * k := by
    change a.order (1 : Fin 3) - a.order (0 : Fin 3) = 2 * k at hk
    exact hk
  refine ⟨z + 2 * k, ?_, ?_⟩
  · rcases hzOdd with ⟨d, hd⟩
    exact ⟨d + k, by omega⟩
  · have hrelation := hremark.currentAlpha_eq
    change a.alphaValue (1 : Fin 2) =
        ((a.order (0 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) +
          a.alphaValue (0 : Fin 2) at hrelation
    rw [hz] at hrelation
    have hkQ : (a.order (1 : Fin 3) : ℚ) - a.order (0 : Fin 3) =
        2 * (k : ℚ) := by
      exact_mod_cast hk'
    push_cast at hrelation ⊢
    linarith

/-- The ambient quadratic-space part of Beli (2019), Lemma 9.5(ii), in the
isotropic branch.  The integral-lattice comparison is separated from this
field-space calculation because the displayed binary BONG is not an
orthogonal integral basis. -/
theorem beli2019Lemma95_ii_ambient_isotropic
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hisotropic : a.Lemma814FirstThreeIsotropic) :
    q.IsIsometric
      (unaryBinaryModelSpace
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 0)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 1)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 2)
        (a.beli2019Lemma95NormalForm_binaryAdmissible_one
          houter A₁ A₂ hA₁ hA₂)) :=
  a.beli2019Lemma95NormalForm_isIsometric_one
    houter A₁ A₂ hA₁ hA₂ hisotropic

/-- Beli (2019), Lemma 9.5(ii), isotropic branch, as an isometry of
integral lattices.  The target is the literal unary--binary model rather
than the diagonal span of its orthogonal BONG vectors. -/
theorem beli2019Lemma95_ii_isotropic
    [QuadraticDefectLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaSource : Beli2006AlphaLaws.{u, v} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hisotropic : a.Lemma814FirstThreeIsotropic) :
    Lattice.IsIsometric q
      (unaryBinaryModelSpace
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 0)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 1)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 2)
        (by
          letI : Beli2006AlphaLaws.{u, v} K := alphaSource
          exact a.beli2019Lemma95NormalForm_binaryAdmissible_one
            houter A₁ A₂ hA₁ hA₂))
      L (unaryBinaryModelLattice (K := K)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaSource
  have htwist : IsValuationUnit K ((1 : Kˣ) : K) := by
    change ord K (1 : K) = 0
    rw [ord_one]
  exact a.beli2019Lemma95NormalForm_latticeIsometric
    (alphaSource := alphaSource) (alphaModel := alphaModel)
    houter A₁ A₂ hA₁ hA₂ 1 htwist
    (a.beli2019Lemma95NormalForm_binaryAdmissible_one
      houter A₁ A₂ hA₁ hA₂)
    (a.beli2019Lemma95NormalForm_isIsometric_one
      houter A₁ A₂ hA₁ hA₂ hisotropic)

/-- The ambient quadratic-space part of Beli (2019), Lemma 9.5(ii), in the
anisotropic branch.  Part (i) supplies the oddness used to distinguish the
discriminant-twisted Hasse class. -/
theorem beli2019Lemma95_ii_ambient_anisotropic
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    q.IsIsometric
      (unaryBinaryModelSpace
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 0)
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 1)
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 2)
        (a.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
          houter A₁ A₂ hA₁ hA₂)) := by
  have hoddRational := a.beli2019Lemma95_i houter hanisotropic
  rcases hoddRational with ⟨z, hzOdd, hz⟩
  have hAz : A₁ = z := by
    have hcast : (A₁ : ℚ) = (z : ℚ) := hA₁.symm.trans hz
    exact_mod_cast hcast
  have hA₁Odd : Odd A₁ := by simpa [hAz] using hzOdd
  exact a.beli2019Lemma95NormalForm_isIsometric_discriminant
    houter A₁ A₂ hA₁ hA₂ hA₁Odd hanisotropic

/-- Beli (2019), Lemma 9.5(ii), anisotropic branch, as an isometry of
integral lattices. -/
theorem beli2019Lemma95_ii_anisotropic
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaSource : Beli2006AlphaLaws.{u, v} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    Lattice.IsIsometric q
      (unaryBinaryModelSpace
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 0)
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 1)
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 2)
        (by
          letI : Beli2006AlphaLaws.{u, v} K := alphaSource
          exact a.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
            houter A₁ A₂ hA₁ hA₂))
      L (unaryBinaryModelLattice (K := K)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaSource
  exact a.beli2019Lemma95NormalForm_latticeIsometric
    (alphaSource := alphaSource) (alphaModel := alphaModel)
    houter A₁ A₂ hA₁ hA₂ laws.discriminantUnit
    laws.discriminant_isValuationUnit
    (a.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
      houter A₁ A₂ hA₁ hA₂)
    (a.beli2019Lemma95_ii_ambient_anisotropic
      houter A₁ A₂ hA₁ hA₂ hanisotropic)

/-- Beli (2019), Lemma 9.5(iii).  The binary lattice displayed in part
(ii) is the hyperbolic plane at scale `(R₁ + R₂) / 2` whenever the first
alpha invariant attains its half-gap bound.

The integers `A₁,A₂` are explicit witnesses for the integrality of the two
alpha invariants.  Part (ii) supplies the binary BONG `b` with exactly the
two displayed values. -/
theorem beli2019Lemma95_iii
    [Beli2006AlphaLaws.{u, v} K]
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L 3) (b : BONG W r M 2)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hA₂ : a.alphaValue (1 : Fin 2) = (A₂ : ℚ))
    (hhalf : a.AttainsHalfGap (0 : Fin 2))
    (hvalueZero : b.valueUnit (0 : Fin 2) =
      uniformizerPowerUnit K (a.order (0 : Fin 3) + A₁))
    (hvalueOne : b.valueUnit (1 : Fin 2) =
      -(uniformizerPowerUnit K (a.order (0 : Fin 3) - A₂))) :
    Lattice.IsIsometric r
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K
          ((a.order (0 : Fin 3) + a.order (1 : Fin 3)) / 2)))
      M (Lattice.hyperbolicPlaneLattice (K := K)) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have halphaSumQ :
      a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) =
        2 * (ramificationIndex K : ℚ) := by
    simpa [remark87PreviousAlpha, remark87CurrentAlpha] using
      hremark.alphaSum_eq_twoE_iff.mpr hhalf
  have halphaSum : A₁ + A₂ = 2 * (ramificationIndex K : Int) := by
    rw [hA₁, hA₂] at halphaSumQ
    exact_mod_cast halphaSumQ
  have hhalfQ := hhalf
  unfold AttainsHalfGap halfGapValue orderGap at hhalfQ
  change a.alphaValue (0 : Fin 2) =
      ((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) / 2 +
        ramificationIndex K at hhalfQ
  rw [hA₁] at hhalfQ
  field_simp at hhalfQ
  have htwiceQ :
      (2 * (A₁ : ℚ)) =
        ((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) +
          2 * (ramificationIndex K : ℚ) := by
    push_cast at hhalfQ ⊢
    linarith
  have htwice :
      (2 * A₁ : Int) =
        a.order (1 : Fin 3) - a.order (0 : Fin 3) +
          2 * (ramificationIndex K : Int) := by
    exact_mod_cast htwiceQ
  have hparameter : b.binaryParameter =
      uniformizerPowerUnit K
          (-(2 * (ramificationIndex K : Int))) * (-1 : Kˣ) := by
    rw [binaryParameter, hvalueZero, hvalueOne]
    have hpower :
        uniformizerPowerUnit K (a.order (0 : Fin 3) - A₂) /
            uniformizerPowerUnit K (a.order (0 : Fin 3) + A₁) =
          uniformizerPowerUnit K (-(A₁ + A₂)) := by
      unfold uniformizerPowerUnit
      rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
      congr 1
      omega
    rw [neg_div, hpower, halphaSum]
    apply Units.ext
    simp
  have hminusOneUnit : IsValuationUnit K ((-1 : Kˣ) : K) := by
    change ord K (-1 : K) = 0
    rw [ord_neg, ord_one]
  have hminusMinusOneSquare : IsSquare (-(-1 : Kˣ)) := by
    refine ⟨1, ?_⟩
    simp
  have hclassBase :=
    unitSquareClass_uniformizerPower_mul_eq_negativeQuarter
      (K := K) (-(2 * (ramificationIndex K : Int))) (-1 : Kˣ)
      hminusOneUnit rfl hminusMinusOneSquare
  have hclass : b.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K) := by
    unfold binaryUnitSquareClass
    rw [hparameter]
    exact hclassBase
  have hbZeroOrder : b.order (0 : Fin 2) =
      a.order (0 : Fin 3) + A₁ := by
    rw [b.order_eq_ordUnit, hvalueZero,
      ordUnit_uniformizerPowerUnit]
  have hscale :
      b.order (0 : Fin 2) - ramificationIndex K =
        (a.order (0 : Fin 3) + a.order (1 : Fin 3)) / 2 := by
    rw [hbZeroOrder]
    omega
  have hisometric :=
    b.isIsometric_hyperbolicPlane_of_binaryUnitSquareClass_eq_negativeQuarter
      hclass
  rw [hscale] at hisometric
  exact hisometric

end BONG.GoodBONG

end Bong
