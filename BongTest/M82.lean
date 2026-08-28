/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma317

/-!
# M82 Beli 2003, Lemma 3.17 normalized-model smoke tests
-/

namespace BongTest.M82

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    BONG.HasEqualNormGeneratorBasisWitness a c ↔
      BONG.HasEqualNormGeneratorBasisInModel a c :=
  BONG.hasEqualNormGeneratorBasisWitness_iff_inModel
    a c htwo hdiag

example (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a) :
    BONG.HasSomeEqualNormGeneratorBasis a ↔
      BONG.HasEveryEqualNormGeneratorBasis a :=
  BONG.hasSomeEqualNormGeneratorBasis_iff_hasEvery a ha

#print axioms Bong.BONG.hasEqualNormGeneratorBasisWitness_iff_inModel
#print axioms Bong.BONG.hasSomeEqualNormGeneratorBasis_iff_hasEvery

end

end BongTest.M82
