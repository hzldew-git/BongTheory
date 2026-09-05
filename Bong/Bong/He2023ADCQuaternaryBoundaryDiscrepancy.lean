/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryTesting

/-!
# The binary boundary of He (2025), Lemma 6.8(iv)

The published statement includes `n = 2`.  This file records that boundary
as a separate proposition and proves its negation using the actual integral
candidate.  It does not propose a replacement classification theorem.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The `n = 2` instance of the conclusion printed in Lemma 6.8(iv). -/
def HeADC2025Lemma68ivBinaryStatement : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V),
    Lattice.IsNADC.{u, u, u} q L 2 →
      q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even 1
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 1))) →
      Lattice.IsIsometric q
        (BONG.coefficientDiagonalSpace (heADCW2Even 1
          (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) 1))) L
        (heADCN2Even 1 (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) 1)).lattice

/-- The actual boundary candidate is not the maximal lattice asserted by Lemma 6.8(iv). -/
theorem heADCQuaternaryBoundaryCandidate_not_isIsometric_N2Delta :
    ¬ Lattice.IsIsometric (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW2Even 1
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 1)))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heADCN2Even 1 (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 1)).lattice := by
  intro hiso
  apply heADCQuaternaryBoundaryCandidate_not_isOMaximal (K := K)
  exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
    (Classical.choice hiso).symm

/-- The binary instance printed in Lemma 6.8(iv) is false over every stated dyadic context. -/
theorem not_heADC2025Lemma68ivBinaryStatement :
    ¬ HeADC2025Lemma68ivBinaryStatement (K := K) := by
  intro hclaim
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let w := heADCW2Even 1
    (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
    (heHuLemma43_evenSecondDefined (K := K) 1)
  have ambient : (heADCQuaternaryBoundaryForm (K := K)).IsIsometric
      (BONG.coefficientDiagonalSpace w) :=
    a.ambientIsometric_of_diagonalRepresents w rfl
      (heADCQuaternaryBoundaryCandidate_represents_second (K := K))
  exact heADCQuaternaryBoundaryCandidate_not_isIsometric_N2Delta (K := K)
    (hclaim (heADCQuaternaryBoundaryForm (K := K))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heADCQuaternaryBoundaryCandidate_is2ADC (K := K)) ambient)

end BONG.GoodBONG

end Bong
