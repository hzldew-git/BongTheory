/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328EqualOrderDeterminantCorrection
import Bong.Lattice.Omeara9328CongruenceError
import Bong.Lattice.Omeara9328SecondGeneratorErrorData

/-!
# Determinant normalization in the equal-order case of O'Meara 93:28

Condition 93:28(i) supplies an explicit unit `1 + z` representing the
determinant class of the normalized target head.  The construction in
`Omeara9328EqualOrderDeterminantCorrection` replaces the first two target
components.  This file proves that the determinant factor of the exchanged
binary plane is `-(1 + z)`, so the new quaternary head has determinant class
one, and packages the resulting saturated Jordan splitting.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- A normalized unimodular first component has a determinant representative
of valuation zero. -/
theorem targetFirstDeterminant_isValuationUnit :
    IsValuationUnit K
      (determinantUnit S.targetFirstNormalized
        (S.targetJordan.component 0).lattice : K) := by
  apply (isValuationUnit_iff_ordUnit_eq_zero K _).2
  apply WithTop.coe_injective
  rw [coe_ordUnit]
  change ord K (determinant S.targetFirstNormalized
    (S.targetJordan.component 0).lattice) = ((0 : Int) : WithTop Int)
  rw [← coe_volumeOrder,
    S.targetFirstNormalized_unimodular.volumeOrder_eq]
  simp

/-- Extract condition 93:28(i) directly at the normalized target head; no
odd-model choice is needed for this determinant correction. -/
noncomputable def targetFirstCongruenceError
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A) :
    BONG.GoodBONG.ValuationUnitCongruenceErrorData
      (determinantUnit S.targetFirstNormalized
        (S.targetJordan.component 0).lattice)
      (S.sourceJordan.fundamentalIdeal 0) := by
  apply BONG.GoodBONG.valuationUnitCongruenceErrorData
  · exact S.targetFirstDeterminant_isValuationUnit
  · intro z hz
    exact S.sourceJordan.isInMaximalIdeal_of_mem_fundamentalIdeal 0 hz
  · exact S.targetFirstNormalized_determinantCongruentOne A conditions

namespace EqualNormOrderErrorData

variable {S : Omeara9328RankFourReductionSystem J H}
  {z : K} (D : S.EqualNormOrderErrorData z)

/-- The exchanged plane contributes precisely the determinant factor
`-(1+z)`. -/
theorem newPlane_determinantClass
    (epsilon : Kˣ) (hepsilon : (epsilon : K) = 1 + z) :
    determinantClass D.exchangeSetup.newPlane
        (hyperbolicPlaneLattice (K := K)) =
      unitSquareClass K ((-1 : Kˣ) * epsilon) := by
  unfold Omeara9319ExchangeSetup.newPlane
  rw [determinantClass_omearaGeneralPlane]
  apply congrArg (unitSquareClass K)
  apply Units.ext
  change
    (D.exchangeSetup.alpha +
          (S.relativeSecondScale : K) * D.exchangeSetup.gamma) *
        D.exchangeSetup.beta - 1 =
      ((-1 : Kˣ) * epsilon : Kˣ)
  rw [D.exchangeSetup_newCoefficient]
  simp only [exchangeSetup, Omeara9319ExchangeSetup.zeroLeft_beta,
    Units.val_mul, Units.val_neg, Units.val_one]
  rw [show (D.secondGenerator : K) * -D.coefficient =
      -((D.secondGenerator : K) * D.coefficient) by ring,
    ← D.error_eq, hepsilon]
  ring

/-- The six-dimensional head ambient has the determinant class of a single
hyperbolic plane. -/
theorem headAmbient_determinantClass
    (epsilon : Kˣ) (hepsilon : (epsilon : K) = 1 + z)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hdet : determinantClass S.targetFirstNormalized
        (S.targetJordan.component 0).lattice =
      unitSquareClass K epsilon) :
    determinantClass D.headAmbient D.headAmbientLattice =
      unitSquareClass K (-1 : Kˣ) := by
  rw [determinantClass_orthogonalProduct,
    D.newPlane_determinantClass epsilon hepsilon, hdet,
    ← unitSquareClass_mul]
  have hsquare := unitSquareClass_mul_unit_square K
    (-1 : Kˣ) epsilon hepsilonUnit
  simpa only [pow_two, mul_assoc] using hsquare

/-- Splitting the displayed hyperbolic plane from the preceding ambient
lattice leaves a quaternary complement of determinant class one. -/
theorem newHead_determinantClass_eq_one
    (epsilon : Kˣ) (hepsilon : (epsilon : K) = 1 + z)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hdet : determinantClass S.targetFirstNormalized
        (S.targetJordan.component 0).lattice =
      unitSquareClass K epsilon) :
    determinantClass D.newHead D.newHeadLattice = 1 := by
  have hsplit := D.headSplit.decomposition.determinantClass_eq_mul_components
  have hhyper := determinantClass_eq_of_isometry D.headSplit.hyperbolic
  have hamb := D.headAmbient_determinantClass epsilon hepsilon
    hepsilonUnit hdet
  rw [hhyper, determinantClass_hyperbolicPlaneLattice] at hsplit
  simp only [one_pow, mul_one] at hsplit
  rw [hamb] at hsplit
  have hcancel := congrArg
    (fun c : UnitSquareClass K ↦
      (unitSquareClass K (-1 : Kˣ))⁻¹ * c) hsplit
  simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using hcancel.symm

end EqualNormOrderErrorData

/-- The scalar data required by the concrete 93:13/93:19 correction,
constructed from condition 93:28(i) in the case `U₂ = U₁`. -/
noncomputable def equalOrderErrorData
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    S.EqualNormOrderErrorData
      (S.targetFirstCongruenceError A conditions).error :=
  S.equalNormOrderErrorDataWith A
    (S.targetFirstCongruenceError A conditions).error
    (by
      rw [S.secondNormalizedNormGeneratorWith_order_eq A]
      exact hgap)
    (S.targetFirstCongruenceError A conditions).error_mem

/-- The corrected normalized quaternary head has determinant class one. -/
theorem equalOrder_newHead_determinantClass_eq_one
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    let C := S.targetFirstCongruenceError A conditions
    let D := S.equalOrderErrorData A conditions hgap
    determinantClass D.newHead D.newHeadLattice = 1 := by
  let C := S.targetFirstCongruenceError A conditions
  let D := S.equalOrderErrorData A conditions hgap
  change determinantClass D.newHead D.newHeadLattice = 1
  apply D.newHead_determinantClass_eq_one C.errorUnit
    C.errorUnit_coe C.errorUnit_isValuationUnit
  change unitSquareClass K
      (determinantUnit S.targetFirstNormalized
        (S.targetJordan.component 0).lattice) =
    unitSquareClass K C.errorUnit
  exact C.unitSquareClass_eq_errorUnit

/-- The saturated target Jordan splitting produced by the equal-order
determinant correction. -/
noncomputable def equalOrderJordanReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    Omeara9319JordanReplacement S.targetJordan :=
  (S.equalOrderErrorData A conditions hgap).jordanReplacement

/-- The displayed corrected head maps integrally onto the first component
of the installed replacement Jordan splitting. -/
noncomputable def equalOrderReplacementHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    let D := S.equalOrderErrorData A conditions hgap
    let R := S.equalOrderJordanReplacement A conditions hgap
    Isometry D.newHeadUnnormalized (R.target.component 0).space
      D.newHeadLattice (R.target.component 0).lattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let R := S.equalOrderJordanReplacement A conditions hgap
  change Isometry D.newHeadUnnormalized (R.target.component 0).space
    D.newHeadLattice (R.target.component 0).lattice
  rw [show R.target = S.targetJordan.replaceFirstPairOfIsometry
      D.firstPairReplacementIsometry
      D.newHeadUnnormalized_modular D.newTailUnnormalized_modular
      D.newHeadUnnormalized_scaleIdeal D.newTailUnnormalized_scaleIdeal
      D.newHeadUnnormalized_normIdeal D.newTailUnnormalized_normIdeal by rfl]
  exact S.targetJordan.replaceFirstPairOfIsometry_leftIsometry
    D.firstPairReplacementIsometry
    D.newHeadUnnormalized_modular D.newTailUnnormalized_modular
    D.newHeadUnnormalized_scaleIdeal D.newTailUnnormalized_scaleIdeal
    D.newHeadUnnormalized_normIdeal D.newTailUnnormalized_normIdeal

/-- Normalize the first component of the corrected target at the unchanged
first Jordan scale. -/
noncomputable abbrev equalOrderTargetFirstNormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    QuadraticSpace K
      ((S.equalOrderJordanReplacement A conditions hgap).target.component 0).carrier :=
  ((S.equalOrderJordanReplacement A conditions hgap).target.component 0).space
    |>.rescaleUnit S.firstScale⁻¹

/-- After normalization, the displayed corrected head is integrally
isometric to the actual first component of the replacement. -/
noncomputable def equalOrderNormalizedHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    let D := S.equalOrderErrorData A conditions hgap
    let R := S.equalOrderJordanReplacement A conditions hgap
    Isometry D.newHead
      (S.equalOrderTargetFirstNormalized A conditions hgap)
      D.newHeadLattice (R.target.component 0).lattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let R := S.equalOrderJordanReplacement A conditions hgap
  let head := S.equalOrderReplacementHeadIsometry A conditions hgap
  let scaled := head.rescaleUnitBoth S.firstScale⁻¹
  let collapseRaw := rescaleUnitMulLatticeIsometry D.newHead
    D.newHeadLattice S.firstScale S.firstScale⁻¹
  have hscale : S.firstScale⁻¹ * S.firstScale = (1 : Kˣ) := by simp
  let finish : Isometry (D.newHead.rescaleUnit
      (S.firstScale⁻¹ * S.firstScale)) D.newHead
      D.newHeadLattice D.newHeadLattice := by
    simpa only [hscale] using
      Isometry.rescaleUnitOne D.newHead D.newHeadLattice
  let collapse : Isometry
      (D.newHeadUnnormalized.rescaleUnit S.firstScale⁻¹) D.newHead
      D.newHeadLattice D.newHeadLattice := by
    simpa only [EqualNormOrderErrorData.newHeadUnnormalized] using
      collapseRaw.trans finish
  exact collapse.symm.trans scaled

/-- The actual normalized first component in the replacement has determinant
class one. -/
theorem equalOrderTargetFirstNormalized_determinantClass_eq_one
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    let R := S.equalOrderJordanReplacement A conditions hgap
    determinantClass
        (S.equalOrderTargetFirstNormalized A conditions hgap)
        (R.target.component 0).lattice = 1 := by
  let D := S.equalOrderErrorData A conditions hgap
  let R := S.equalOrderJordanReplacement A conditions hgap
  let f := S.equalOrderNormalizedHeadIsometry A conditions hgap
  have hdet := determinantClass_eq_of_isometry f
  exact hdet.symm.trans
    (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
