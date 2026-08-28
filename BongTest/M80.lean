/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma314

/-!
# M80 Beli 2003, Lemma 3.14 smoke test
-/

namespace BongTest.M80

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [QuadraticDefectLaws K]
  [BeliHilbertCongruenceLaws K]

example (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hb : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * η))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int)) :
    beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * η) =
      beliLemma314CongruenceFactor (K := K) R
          (quadraticDefect K (ε * η)) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) :=
  beliNormGeneratorSquareClassGroup_sup
    R ε η hε hη ha hb hRupper

#print axioms Bong.Dyadic.beliNormGeneratorSquareClassGroup_sup

end

end BongTest.M80
