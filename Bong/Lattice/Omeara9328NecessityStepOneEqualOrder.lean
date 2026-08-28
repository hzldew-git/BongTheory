/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9310RankFourDeterminantCongruence
import Bong.Lattice.Omeara9328FirstFundamentalIdealCases
import Bong.Lattice.Omeara9328FirstDeterminantCongruence
import Bong.Lattice.Omeara9328StrictConditions

/-!
# O'Meara 93:28 necessity, Step 1: the equal norm-order branch

After the rank-four reduction, the normalized source head is hyperbolic and
the normalized target head is quaternary unimodular with the same norm group.
When the first two normalized norm orders agree, Example 93:27 identifies
the first fundamental ideal with the norm-times-weight ideal.  The
parity-free rank-four determinant calculation from Example 93:10 therefore
proves condition 93:28(i) at the first boundary, without assuming any of the
classification conditions.
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

/-- In the equal norm-order branch, the target normalized determinant is
congruent to one modulo the actual first fundamental ideal. -/
theorem targetFirstNormalized_determinantCongruentOne_of_equalNormOrder
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    BONG.GoodBONG.UnitsCongruentModulo
      (determinantUnit S.targetFirstNormalized
        (S.targetJordan.component 0).lattice)
      (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0) := by
  have hdet := determinantUnit_congruent_one_mod_norm_mul_weight
    S.targetFirstNormalized_unimodular S.targetFirstNormalized_finrank
      S.firstNormGenerator S.firstNormGenerator_target
  have hfundWeightOrder :
      weightIdealOrder
          (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
          (S.sourceJordan.fundamentalLattice 0) =
        S.sourceJordan.fundamentalWeightOrder 0 := rfl
  have hfirstScaleOrder : ordUnit K S.firstScale =
      S.sourceJordan.fundamentalScaleOrder 0 := by
    unfold fundamentalScaleOrder firstScale
    simp only [S.sourceJordan_scaleGenerator]
  have hideal :
      scalarIdeal (S.firstNormGenerator : K)
          (weightIdeal S.targetFirstNormalized
            (S.targetJordan.component 0).lattice) =
        S.sourceJordan.fundamentalIdeal 0 := by
    rw [← S.firstNormalized_weightIdeal_eq]
    rw [weightIdeal_eq_powerIdeal, scalarIdeal_powerIdeal_units]
    rw [S.firstFundamentalIdeal_eq_rightNorm_mul_leftWeight_of_normalized_eq
      hgap]
    unfold fundamentalWeightIdeal
    rw [weightIdeal_eq_powerIdeal, scalarIdeal_powerIdeal_units]
    apply le_antisymm <;> rw [powerIdeal_le_iff]
    · rw [ordUnit_mul, ordUnit_inv, hgap,
        S.sourceFirstNormalized_weightIdealOrder_eq_fundamental,
        hfundWeightOrder, hfirstScaleOrder]
      omega
    · rw [ordUnit_mul, ordUnit_inv, hgap,
        S.sourceFirstNormalized_weightIdealOrder_eq_fundamental,
        hfundWeightOrder, hfirstScaleOrder]
      omega
  rw [← hideal]
  exact hdet

/-- O'Meara 93:28(i) at the first unnormalized Jordan boundary in the
equal norm-order branch.  The common fourth power of the first scale is
cancelled only after transferring through the refined determinant classes.
-/
theorem firstBoundary_conditionI_of_equalNormOrder
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    BONG.GoodBONG.UnitsCongruentModulo
      (S.targetJordan.prefixDeterminantUnit 0)
      (S.sourceJordan.prefixDeterminantUnit 0)
      (S.sourceJordan.fundamentalIdeal 0) := by
  have hnormalized :=
    S.targetFirstNormalized_determinantCongruentOne_of_equalNormOrder hgap
  let c : Kˣ := S.firstScale ^ 4
  let x : Kˣ := determinantUnit S.targetFirstNormalized
    (S.targetJordan.component 0).lattice
  let sourcePrefix : Kˣ := S.sourceJordan.prefixDeterminantUnit 0
  let targetPrefix : Kˣ := S.targetJordan.prefixDeterminantUnit 0
  have htargetClass :
      unitSquareClass K targetPrefix = unitSquareClass K (c * x) := by
    change determinantClass
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      unitSquareClass K (c * x)
    rw [S.targetFirstPrefix_determinantClass]
    exact (unitSquareClass_mul K c x).symm
  have hsourceClass :
      unitSquareClass K sourcePrefix =
        unitSquareClass K (c * (1 : Kˣ)) := by
    change determinantClass
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      unitSquareClass K (c * (1 : Kˣ))
    rw [S.sourceFirstPrefix_determinantClass, mul_one]
  have hscaled : BONG.GoodBONG.UnitsCongruentModulo
      (c * x) (c * (1 : Kˣ))
      (S.sourceJordan.fundamentalIdeal 0) :=
    (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
      c x (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0)).2 hnormalized
  exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    (c * x) targetPrefix (c * (1 : Kˣ)) sourcePrefix
    (S.sourceJordan.fundamentalIdeal 0)
    htargetClass.symm hsourceClass.symm hscaled

/-- In the equal norm-order branch, the left threshold is contained in the
first fundamental ideal.  Consequently the proper-containment trigger in
93:28(iii) is impossible. -/
theorem firstBoundary_leftThreshold_le_fundamentalIdeal_of_equalNormOrder
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0) ≤
      S.sourceJordan.fundamentalIdeal 0 := by
  rw [S.firstFundamentalIdeal_eq_rightNorm_mul_leftWeight_of_normalized_eq
    hgap]
  unfold fourNormOverWeightIdeal fundamentalWeightIdeal
  rw [show boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) by ext; rfl,
    weightIdeal_eq_powerIdeal, scalarIdeal_powerIdeal_units,
    powerIdeal_le_iff]
  have hfirstOrder := S.firstNormGenerator_order
  have hweightOrder :=
    S.sourceFirstNormalized_weightIdealOrder_eq_fundamental
  have hweightLe :=
    S.sourceFirstNormalized_weightIdealOrder_le_ramificationIndex
  have hfundWeightOrder :
      weightIdealOrder
          (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
          (S.sourceJordan.fundamentalLattice 0) =
        S.sourceJordan.fundamentalWeightOrder 0 := rfl
  have hfirstScaleOrder : ordUnit K S.firstScale =
      S.sourceJordan.fundamentalScaleOrder 0 := by
    unfold fundamentalScaleOrder firstScale
    simp only [S.sourceJordan_scaleGenerator]
  rw [ordUnit_mul, ordUnit_inv, hgap, hfirstOrder,
    hfundWeightOrder, hfirstScaleOrder] at *
  omega

/-- Choice-independent form of the equal-order threshold bound. -/
theorem firstBoundary_leftThresholdWith_le_fundamentalIdeal_of_equalNormOrder
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    S.sourceJordan.fourNormOverWeightIdealWith A (boundaryLeftIndex 0) ≤
      S.sourceJordan.fundamentalIdeal 0 := by
  have hcanonical :=
    S.firstBoundary_leftThreshold_le_fundamentalIdeal_of_equalNormOrder hgap
  rw [← fourNormOverWeightIdealWith_canonical] at hcanonical
  unfold fourNormOverWeightIdealWith at hcanonical ⊢
  rw [A.value_order_eq_fundamentalNormGenerator]
  rw [(canonicalFundamentalNormGeneratorChoice
    S.sourceJordan).value_order_eq_fundamentalNormGenerator] at hcanonical
  exact hcanonical

/-- O'Meara 93:28(iii) at the first boundary with an arbitrary coherent
fundamental norm generator.  In the equal-order branch the strict trigger
is impossible. -/
theorem firstBoundary_strictConditionIIIWith_of_equalNormOrder
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    S.sourceJordan.fundamentalIdeal 0 <
        S.sourceJordan.fourNormOverWeightIdealWith A
          (boundaryLeftIndex 0) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex 0))) := by
  intro htrigger
  exact (not_lt_of_ge
    (S.firstBoundary_leftThresholdWith_le_fundamentalIdeal_of_equalNormOrder
      A hgap) htrigger).elim

/-- O'Meara 93:28(iii) at the first boundary in the equal norm-order
branch.  The printed theorem uses proper containment, so this implication
is vacuous exactly at the equality boundary. -/
theorem firstBoundary_strictConditionIII_of_equalNormOrder
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    S.sourceJordan.fundamentalIdeal 0 <
        S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (QuadraticSpace.scaledLine
    (S.sourceJordan.fundamentalNormGenerator
            (boundaryLeftIndex 0))) := by
  intro htrigger
  have h := S.firstBoundary_strictConditionIIIWith_of_equalNormOrder
    (canonicalFundamentalNormGeneratorChoice S.sourceJordan) hgap
  apply h
  simpa only [fourNormOverWeightIdealWith_canonical] using htrigger

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
