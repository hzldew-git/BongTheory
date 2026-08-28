/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328RankFourAmbientReduction
import Bong.Lattice.OmearaJordanNegativeCancellation

/-!
# Lifting the rank-four reduction in O'Meara 93:28

The componentwise rank-four reduction is performed after adjoining the
negative source lattice.  A full integral isometry of the two residual block
products can therefore be enlarged by the common hyperbolic towers and
transported back to an isometry

`(-L) ⊥ L ≃ (-L) ⊥ M`.

Corollary 93:14a, iterated over the saturated source Jordan components,
cancels the negative copy and recovers `L ≃ M`.  This is the integral lift
that cannot be replaced by ordinary Witt cancellation of ambient spaces.
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

/-- Reinsert the common componentwise hyperbolic towers around an integral
isometry of the two rank-four residual products. -/
noncomputable def negativeAdjunctionIsometryOfResidualIsometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Isometry
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum r)
      (product L L) (product L M) := by
  let commonForm := BONG.blockOrthogonalForm (n + 1)
    S.commonTowerCarrier S.commonTowerForm
  let commonLattice := BONG.blockProductLattice (n + 1)
    S.commonTowerCarrier S.commonTowerLattice
  let commonResidual : Isometry
      (commonForm.orthogonalSum
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm))
      (commonForm.orthogonalSum
        (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm))
      (product commonLattice
        (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice))
      (product commonLattice
        (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :=
    (Isometry.refl commonForm commonLattice).orthogonalProductBasic f
  exact (sourceNegativeAdjunctionProductIsometry (J := J)).symm.trans <|
    S.sourceGatheredReduction.trans <|
      commonResidual.trans <|
        S.targetGatheredReduction.symm.trans
          (targetNegativeAdjunctionProductIsometry (J := J) (H := H))

/-- A full integral classification of the rank-four residual systems lifts
to the original saturated lattices with no additional cancellation law. -/
noncomputable def originalIsometryOfResidualIsometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Isometry q r L M :=
  cancelNegativeAdjunction J H S.sourceSaturated S.targetSaturated
    S.fundamentalType (S.negativeAdjunctionIsometryOfResidualIsometry f)

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
