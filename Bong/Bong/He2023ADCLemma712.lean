/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma710
import Bong.Bong.HeHu2022Lemma58

/-!
# He (2025), Lemma 7.12

This is the literal specialization of He--Hu, Lemma 5.8 used in the
published proof. Lemma 7.10 supplies its universality invariant hypotheses.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- He (2025), Lemma 7.12, for odd `n=2*k+3`. -/
theorem heADC2025Lemma712 (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let c := a.heHuLemma58Prefix (n := 2 * k + 1)
    ∃ hc : HeHuSharpDomain c,
      defectOrder (K := K) c =
          ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) ∧
        IsValuationUnit K (heHuSharp c hc : K) ∧
        defectOrder (K := K) (heHuSharp c hc) =
          (((2 * (ramificationIndex K : Int) +
              a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
            WithTop ℚ) := by
  have h710 := a.heADC2025Lemma710 k hADC
  exact a.heHu2022Lemma58 (m := 2 * k + 2) (n := 2 * k + 1)
    (by omega) ⟨k + 1, by omega⟩ (by omega) hADC.isIntegral
    h710.initial h710.boundary hAlpha hTrigger

end BONG.GoodBONG

end Bong
