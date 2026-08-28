/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma317

/-!
# M83 Beli 2003, Lemma 3.17 parameter-classification smoke tests
-/

namespace BongTest.M83

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [QuadraticDefectLaws K]
  [UnitQuadraticDefectParityLaws K]
  [DyadicSquareDifferenceLaws K]
  [PerfectResidueFieldLaws K]
  [PrincipalUnitSquareClassFiltrationLaws K]
  [BinaryNormGeneratorLocalLaws.{u, u} K]

example (R : Int) (ε : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε)) :
    BONG.HasEveryEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε) ↔
      BONG.BeliLemma317ParameterCases (K := K) R ε :=
  BONG.hasEveryEqualNormGeneratorBasis_iff_parameterCases
    R ε hε ha

example (R : Int) (ε : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε)) :
    (BONG.HasSomeEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε) ↔
      BONG.HasEveryEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε)) ∧
    (BONG.HasEveryEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε) ↔
      BONG.BeliLemma317ParameterCases (K := K) R ε) :=
  BONG.beliLemma317 R ε hε ha

#print axioms Bong.BONG.beliLemma317ParameterCases_of_hasEvery
#print axioms Bong.BONG.hasEveryEqualNormGeneratorBasis_iff_parameterCases
#print axioms Bong.BONG.beliLemma317

end

end BongTest.M83
