/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NecessityBoundaryRepresentation
import Bong.Lattice.Omeara9328NecessityStepOneEqualOrder
import Bong.Lattice.Omeara9328ScaleOneDispatcher

/-!
# O'Meara 93:28 necessity at the first boundary

This file combines the equal and strict normalized norm-order branches.
It proves clauses (i) and (iii) at the first boundary of the saturated
rank-four reduction, with no local-law parameter.
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

/-- The canonical second normalized norm order is no smaller than the
first one. -/
theorem firstNormGenerator_order_le_secondNormalizedNormGenerator :
    ordUnit K S.firstNormGenerator ≤
      ordUnit K S.secondNormalizedNormGenerator := by
  let A := canonicalFundamentalNormGeneratorChoice S.sourceJordan
  have h := S.firstNormGenerator_order_le_secondWith A
  have hchoice := S.secondNormalizedNormGeneratorWith_order_eq A
  omega

/-- O'Meara 93:28(i) at the first boundary, in all possible normalized
norm-order cases. -/
theorem firstBoundary_conditionI
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    BONG.GoodBONG.UnitsCongruentModulo
      (S.targetJordan.prefixDeterminantUnit 0)
      (S.sourceJordan.prefixDeterminantUnit 0)
      (S.sourceJordan.fundamentalIdeal 0) := by
  rcases lt_or_eq_of_le
      S.firstNormGenerator_order_le_secondNormalizedNormGenerator with
    hlt | heq
  · exact S.firstBoundary_conditionI_of_strictNormOrder f hlt
  · exact S.firstBoundary_conditionI_of_equalNormOrder heq.symm

/-- O'Meara 93:28(iii) at the first boundary for an arbitrary coherent
fundamental norm generator, in all possible normalized norm-order cases. -/
theorem firstBoundary_conditionIIIWith
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.sourceJordan.fundamentalIdeal 0 <
        S.sourceJordan.fourNormOverWeightIdealWith A
          (boundaryLeftIndex 0) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (QuadraticSpace.scaledLine
          (A.value (boundaryLeftIndex 0))) := by
  rcases lt_or_eq_of_le
      S.firstNormGenerator_order_le_secondNormalizedNormGenerator with
    hlt | heq
  · exact S.firstBoundary_strictConditionIIIWith_of_ltNormOrder f hlt A
  · exact S.firstBoundary_strictConditionIIIWith_of_equalNormOrder A heq.symm

/-- Canonical-generator form of O'Meara 93:28(iii) at the first boundary. -/
theorem firstBoundary_conditionIII
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
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
  have h := S.firstBoundary_conditionIIIWith
    (canonicalFundamentalNormGeneratorChoice S.sourceJordan) f
  apply h
  simpa only [fourNormOverWeightIdealWith_canonical] using htrigger

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
