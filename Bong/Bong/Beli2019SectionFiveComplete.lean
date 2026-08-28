/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralComplete
import Bong.Bong.Beli2019SectionFiveDefectComplete
import Bong.Bong.Beli2019SectionFiveLongDirect
import Bong.Bong.Beli2019SectionFiveOrderLaws

/-!
# Unconditional assembly of Beli (2019), Section 5

The four pointwise calculations are assembled here into the one-step
index-uniformizer theorem and hence into the `Beli2019SectionFiveLaws`
interface used by the prime-chain argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 0 in
/-- Complete Section 5 data for every literal index-uniformizer inclusion. -/
theorem sectionFiveData_complete
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (inclusion : Beli2019IndexPInclusion q M N) :
    Beli2019SectionFiveData a b := by
  cases n with
  | zero =>
      exact {
        toBeli2019SectionFiveDefectData := {
          certificate := by
            intro i
            have := i.pos
            have := i.lt_large
            omega
        }
        orderData := a.sectionFiveOrderData b inclusion
        centralCertificate := by
          intro i
          have := i.one_lt
          have := i.lt_large
          omega
        longCertificate := by
          intro i
          have := i.one_lt
          have := i.succ_lt_large
          omega
      }
  | succ n =>
      let D := Lattice.beli2019Lemma51Data q M N inclusion
      let R := Classical.choice
        (a.exists_sectionFiveReverseDualData b inclusion)
      let dualInclusion := inclusion.reverseDual
      let S := Classical.choice
        (R.sourceDual.exists_sectionFiveReverseDualData
          R.targetDual dualInclusion)
      let defectData := D.sectionFiveDefectData R
      let dualDefectData := R.lemma51.sectionFiveDefectData S
      exact {
        toBeli2019SectionFiveDefectData := defectData
        orderData := a.sectionFiveOrderData b inclusion
        centralCertificate := by
          intro i
          exact D.centralCertificate_complete R
            defectData.defectCondition dualDefectData.defectCondition i
        longCertificate := D.longCertificate_complete R
      }

end BONG.GoodBONG

/-- Beli's explicit Section 5 construction realizes the previously abstract
one-step law interface. -/
noncomputable instance beli2019SectionFiveLawsProved
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K] :
    Beli2019SectionFiveLaws.{u, v} K where
  data a b inclusion := a.sectionFiveData_complete b inclusion

end Bong
