/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328FirstDeterminantCongruence
import Bong.Lattice.Omeara9328FirstComponentModels
import Bong.Lattice.OmearaFundamentalIdealMaximal
import Bong.Lattice.OmearaHyperbolicCancellation

/-!
# An explicit error unit from O'Meara's determinant congruence

O'Meara's notation `x ≅ 1 (mod I)` contains a square multiplier.  When
`x` is a valuation unit and `I` is contained in the maximal ideal, that
multiplier is itself a valuation unit.  Consequently the congruence gives
an actual unit `1 + lambda`, with `lambda ∈ I`, representing the same
refined square class as `x`.

This is the witness-level form needed in Steps 4--7 of 93:28.  It prevents
the square multiplier hidden in the printed congruence notation from being
silently discarded.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Explicit data extracted from a congruence `x ≅ 1 (mod I)` when `x` is
a valuation unit and every element of `I` lies in the maximal ideal. -/
structure ValuationUnitCongruenceErrorData
    (x : Kˣ) (I : Lattice.CoefficientIdeal (K := K)) where
  square : Kˣ
  error : K
  error_eq : error = (1 : K) / (x : K) / (square : K) ^ 2 - 1
  error_mem : error ∈ I
  error_maximal : IsInMaximalIdeal K error
  errorUnit : Kˣ
  errorUnit_coe : (errorUnit : K) = 1 + error
  errorUnit_isValuationUnit : IsValuationUnit K (errorUnit : K)
  square_isValuationUnit : IsValuationUnit K (square : K)
  unitSquareClass_eq_errorUnit :
    unitSquareClass K x = unitSquareClass K errorUnit

/-- Extract the actual congruence error and prove that its hidden square
multiplier has valuation zero. -/
noncomputable def valuationUnitCongruenceErrorData
    (x : Kˣ) (I : Lattice.CoefficientIdeal (K := K))
    (hx : IsValuationUnit K (x : K))
    (hmax : ∀ {z : K}, z ∈ I → IsInMaximalIdeal K z)
    (h : UnitsCongruentModulo x (1 : Kˣ) I) :
    ValuationUnitCongruenceErrorData x I := by
  let s : Kˣ := Classical.choose h
  have hs := Classical.choose_spec h
  let lambda : K := (1 : K) / (x : K) / (s : K) ^ 2 - 1
  have hlambdaMem : lambda ∈ I := by
    simpa [lambda, s] using hs
  have hlambdaMax : IsInMaximalIdeal K lambda := hmax hlambdaMem
  have honeLambda : IsValuationUnit K (1 + lambda) :=
    Lattice.isValuationUnit_one_add_of_isInMaximalIdeal hlambdaMax
  have honeLambdaNe : 1 + lambda ≠ 0 :=
    Lattice.ne_zero_of_isValuationUnit honeLambda
  let epsilon : Kˣ := Units.mk0 (1 + lambda) honeLambdaNe
  have hepsilonCoe : (epsilon : K) = 1 + lambda := rfl
  have hunitEquation : x * s ^ 2 * epsilon = (1 : Kˣ) := by
    apply Units.ext
    change (x : K) * (s : K) ^ 2 * (1 + lambda) = 1
    dsimp only [lambda]
    field_simp [Units.ne_zero x, Units.ne_zero s]
    <;> ring
  have hxOrder : ordUnit K x = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K x).1 hx
  have hepsilonOrder : ordUnit K epsilon = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K epsilon).1 <| by
      simpa only [hepsilonCoe] using honeLambda
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simp
  have hsOrder : ordUnit K s = 0 := by
    have hord := congrArg (ordUnit K) hunitEquation
    rw [ordUnit_mul, ordUnit_mul, ordUnit_pow,
      hxOrder, hepsilonOrder, honeOrder] at hord
    omega
  have hsUnit : IsValuationUnit K (s : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K s).2 hsOrder
  have hxsq : x * s ^ 2 = epsilon⁻¹ := by
    apply mul_right_cancel (b := epsilon)
    rw [hunitEquation]
    simp
  have hepsilonInvClass :
      unitSquareClass K epsilon⁻¹ = unitSquareClass K epsilon := by
    have hclass := unitSquareClass_mul_unit_square K epsilon⁻¹ epsilon
      (by simpa only [hepsilonCoe] using honeLambda)
    calc
      unitSquareClass K epsilon⁻¹ =
          unitSquareClass K (epsilon⁻¹ * epsilon ^ 2) := hclass.symm
      _ = unitSquareClass K epsilon := by
        apply congrArg (unitSquareClass K)
        simp [pow_two, ← mul_assoc]
  have hclass : unitSquareClass K x = unitSquareClass K epsilon := by
    calc
      unitSquareClass K x = unitSquareClass K (x * s ^ 2) :=
        (unitSquareClass_mul_unit_square K x s hsUnit).symm
      _ = unitSquareClass K epsilon⁻¹ := congrArg (unitSquareClass K) hxsq
      _ = unitSquareClass K epsilon := hepsilonInvClass
  exact
    { square := s
      error := lambda
      error_eq := rfl
      error_mem := hlambdaMem
      error_maximal := hlambdaMax
      errorUnit := epsilon
      errorUnit_coe := rfl
      errorUnit_isValuationUnit := by
        simpa only [hepsilonCoe] using honeLambda
      square_isValuationUnit := hsUnit
      unitSquareClass_eq_errorUnit := hclass }

end BONG.GoodBONG

open Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}
  [DyadicDiscriminantClassLaws K]

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- Rewrite condition 93:28(i) using the explicit discriminant unit in an
odd 93:18(iii) model of the target head. -/
theorem targetOddModel_d_congruentOne
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (D : Omeara9318RankFourOddData S.targetFirstNormalized
      (S.targetJordan.component 0).lattice S.firstNormGenerator) :
    BONG.GoodBONG.UnitsCongruentModulo D.congruence.parameters.d
      (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0) := by
  let det : Kˣ := determinantUnit S.targetFirstNormalized
    (S.targetJordan.component 0).lattice
  have hdet := S.targetFirstNormalized_determinantCongruentOne A conditions
  apply BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    det D.congruence.parameters.d (1 : Kˣ) (1 : Kˣ)
      (S.sourceJordan.fundamentalIdeal 0)
  · exact D.congruence.determinantClass_eq_d
  · rfl
  · exact hdet

/-- The determinant congruence for an odd target model supplies an actual
error unit `1 + lambda`, with `lambda` in the first fundamental ideal and
with the same refined square class as the model discriminant. -/
noncomputable def targetFirstOddCongruenceError
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (D : Omeara9318RankFourOddData S.targetFirstNormalized
      (S.targetJordan.component 0).lattice S.firstNormGenerator) :
    BONG.GoodBONG.ValuationUnitCongruenceErrorData
      D.congruence.parameters.d (S.sourceJordan.fundamentalIdeal 0) := by
  let P := D.congruence.parameters
  apply BONG.GoodBONG.valuationUnitCongruenceErrorData
  · change IsValuationUnit K (1 + P.alpha)
    exact P.discriminant_unit
  · intro z hz
    exact S.sourceJordan.isInMaximalIdeal_of_mem_fundamentalIdeal 0 hz
  · exact S.targetOddModel_d_congruentOne A conditions D

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
