/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma45

/-!
# He--Hu 2022, Theorem 4.1

This file instantiates the component assembly theorem with the complete
formalizations of Lemmas 4.2, 4.4, and 4.5.  The target rank is written
`2*k+2`, matching the even-rank part of the published theorem.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- He--Hu, Theorem 4.1, even target rank.  The formal ambient lattice
type does not build integrality into its definition, so the paper's
standing integral-lattice hypothesis is explicit here. -/
theorem heHu2022Theorem41Even
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L) :
    Lattice.IsNUniversal.{u, v, u} q L (2 * k + 2) ↔
      Lattice.IsIntegral q L ∧
        Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2) ∧
          a.HeHuEvenSectionConditions (2 * k + 2) (by omega) := by
  apply a.heHuTheorem41_of_component_equivalences
    (n := 2 * k + 1) (m := m + 2) (by omega) (by omega)
  · intro hAmbient
    exact a.heHu2022Lemma42 (m := m + 1) (t := 2 * k) hm
      ⟨k + 1, by omega⟩ hAIntegral hAmbient
  · intro hAmbient hI1
    exact a.heHu2022Lemma44 hm hAIntegral hI1 hAmbient
  · intro hAmbient hI1 hI2
    exact a.heHu2022Lemma45 sourceLaws hm hAIntegral hI1 hI2 hAmbient

end BONG.GoodBONG

end Bong
