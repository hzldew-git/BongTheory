/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328FirstComponentModels
import Bong.Lattice.Omeara9328SourceFirstDeterminant
import Bong.Lattice.Omeara9318DeterminantOneHyperbolicModel

/-!
# The exact odd source-head model in O'Meara 93:28

The source head in the rank-four reduction is hyperbolic and has refined
determinant class one.  O'Meara 93:18(vi) gives two determinant-one models.
The first is hyperbolic, while the two models are not field-isometric, so
the hyperbolic source cannot be the twisted second model.  This selects the
literal model `A(a,0) ⊥ A(b,0)` without any model-selection law.
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

/-- The normalized source head is the standard hyperbolic two-plane tower. -/
noncomputable def sourceFirstNormalizedHyperbolicTowerIsometry :
    QuadraticSpace.Isometry S.sourceFirstNormalized
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  let normalizeTower :=
    QuadraticSpace.scaledZeroOmearaTowerRescaleSpaceIsometry
      S.firstScale S.firstScale⁻¹ 2
  have hscale : S.firstScale⁻¹ * S.firstScale = (1 : Kˣ) := by
    simp
  exact S.sourceFirstNormalizedTowerIsometry.trans (by
    simpa only [hscale] using normalizeTower)

/-- Determinant-one 93:18(vi) data for the odd source head. -/
noncomputable def sourceFirstOddDeterminantOneData
    (hodd : Odd S.firstNormWeightParity) :
    Omeara9318viOddData S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice S.firstNormGenerator := by
  apply omeara9318viOddData S.sourceFirstNormalized_unimodular
    S.sourceFirstNormalized_finrank S.firstNormGenerator
    S.firstNormGenerator_source
  · simpa only [firstNormWeightParity] using hodd
  · exact S.sourceFirstNormalized_determinantClass

/-- In odd parity, the source head is integrally isometric to the untwisted
model `A(a,0) ⊥ A(b,0)`. -/
theorem sourceFirstOdd_isometric_j
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.sourceFirstOddDeterminantOneData hodd
    IsIsometric S.sourceFirstNormalized D.parameters.jData.space
      (S.sourceJordan.component 0).lattice D.parameters.jData.lattice := by
  let D := S.sourceFirstOddDeterminantOneData hodd
  change IsIsometric S.sourceFirstNormalized D.parameters.jData.space
    (S.sourceJordan.component 0).lattice D.parameters.jData.lattice
  rcases D.isometric_j_or_k with hj | hk
  · exact hj
  · exfalso
    apply D.parameters.j_not_isometric_k
    let jToTower := D.parameters.jSpaceToHyperbolicTowerIsometry D.alpha_zero
    let sourceToTower := S.sourceFirstNormalizedHyperbolicTowerIsometry
    let jToSource := jToTower.trans sourceToTower.symm
    let sourceToK := (Classical.choice hk).toQuadraticSpaceIsometry
    exact ⟨jToSource.trans sourceToK⟩

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
