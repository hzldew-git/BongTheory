/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrimeChainDecoration
import Bong.Bong.Beli2019SectionFourComplete
import Bong.Bong.Beli2019SectionFourDefectReduction
import Bong.Bong.Beli2019SectionFourCentralComplete
import Bong.Bong.Beli2019SectionFourLongComplete

/-!
# Beli (2019), Section 4: transitivity law instance

This file packages the proved key-lemma bounds, defect reduction, central
parity certificates, and long-prefix certificates into the Section 4 law
consumed by the prime-chain argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The complete local data constructed in Beli's Section 4. -/
theorem sectionFourTransitivityData
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl) :
    SectionFourTransitivityData a b c where
  keyLemma := a.sectionFourKeyLemmaBounds b c
    hab.orderCondition hab.defectCondition
    hbc.orderCondition hbc.defectCondition
  defectReduction := a.sectionFourDefectReduction b c
    hab.orderCondition hbc.orderCondition
  central := a.sectionFourCentralCertificates b c hab hbc
  long := a.sectionFourLongCertificates b c hab hbc

end BONG.GoodBONG

/-- Beli (2019), Section 4, with every certificate field discharged by the
proved construction above. -/
instance beli2019SectionFourLaws
    [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K] :
    Beli2019SectionFourLaws.{u, v} K where
  data a b c hab hbc :=
    a.sectionFourTransitivityData b c hab hbc

end Bong
