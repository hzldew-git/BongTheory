/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma611
import Bong.Bong.He2023ADCQuaternaryBoundaryDiscrepancy

/-!
# The binary boundary of He (2025), Theorem 6.2

The published theorem includes `n = 2`.  The actual nonmaximal 2-ADC lattice
constructed for the Lemma 6.8(iv) audit lies in the other quaternary ambient
space and is not the exceptional lattice from Lemma 6.12.  It therefore also
refutes the binary instance of the printed Theorem 6.2 biconditional.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The exact `n = 2`, rank-four specialization of the biconditional printed
in Theorem 6.2. -/
def HeADC2025Theorem62BinaryStatement : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V),
    finrank K V = 4 →
      (Lattice.IsNADC.{u, u, u} q L 2 ↔
        Lattice.IsOMaximal q L ∨
          Lattice.IsIsometric q (heADCExceptionalQuaternaryForm (K := K)) L
            (heADCExceptionalQuaternaryLattice (K := K)))

/-- The boundary candidate and the Lemma 6.12 exceptional lattice have
nonisometric ambient quadratic spaces. -/
theorem heADCQuaternaryBoundaryCandidate_not_isometric_exceptional :
    ¬ Lattice.IsIsometric
      (heADCQuaternaryBoundaryForm (K := K))
      (heADCExceptionalQuaternaryForm (K := K))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heADCExceptionalQuaternaryLattice (K := K)) := by
  intro hiso
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let hdefined := heHuLemma43_evenSecondDefined (K := K) 1
  let wOne := heADCW1Even 1 δ
  let wTwo := heADCW2Even 1 δ hdefined
  have hboundary : (heADCQuaternaryBoundaryForm (K := K)).IsIsometric
      (BONG.coefficientDiagonalSpace wTwo) :=
    (heADCQuaternaryBoundaryCandidate (K := K)).ambientIsometric_of_diagonalRepresents
      wTwo rfl (heADCQuaternaryBoundaryCandidate_represents_second (K := K))
  have hexceptional : (heADCExceptionalQuaternaryForm (K := K)).IsIsometric
      (BONG.coefficientDiagonalSpace wOne) :=
    (heADCExceptionalQuaternaryCandidate (K := K)).ambientIsometric_of_diagonalRepresents
      wOne rfl (heADCExceptionalQuaternaryCandidate_represents_first (K := K))
  let g := (Classical.choice hboundary).symm |>.trans
    (Classical.choice hiso).toQuadraticSpaceIsometry |>.trans
      (Classical.choice hexceptional)
  have hrep : DiagonalRepresents (diagonalUnitCoefficients wTwo)
      (diagonalUnitCoefficients wOne) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents wTwo wOne).mp
      ⟨g.toRepresentation⟩
  exact (heADC2025Proposition42iEven 1 δ hdefined).nonisometric hrep

/-- The `n = 2` instance of the published Theorem 6.2 is false over every
field satisfying the paper's dyadic local hypotheses. -/
theorem not_heADC2025Theorem62BinaryStatement :
    ¬ HeADC2025Theorem62BinaryStatement (K := K) := by
  intro hclaim
  let q := heADCQuaternaryBoundaryForm (K := K)
  let L := heADCQuaternaryBoundaryLattice (K := K)
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let w := heADCW2Even 1 δ (heHuLemma43_evenSecondDefined (K := K) 1)
  have ambient : q.IsIsometric (BONG.coefficientDiagonalSpace w) :=
    (heADCQuaternaryBoundaryCandidate (K := K)).ambientIsometric_of_diagonalRepresents
      w rfl (heADCQuaternaryBoundaryCandidate_represents_second (K := K))
  have hrank := (Classical.choice ambient).toLinearEquiv.finrank_eq
  rw [finrank_fin_fun] at hrank
  have halternative := (hclaim q L hrank).mp
    (heADCQuaternaryBoundaryCandidate_is2ADC (K := K))
  exact halternative.elim
    (heADCQuaternaryBoundaryCandidate_not_isOMaximal (K := K))
    (heADCQuaternaryBoundaryCandidate_not_isometric_exceptional (K := K))

end BONG.GoodBONG

end Bong
