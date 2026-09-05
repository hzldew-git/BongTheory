/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Proposition55

/-!
# He--Hu 2022, Theorem 5.1

This file derives the published odd-rank criterion from Proposition 5.5 and
Lemma 5.4.  In particular, the recovery of `I2^E(N-1)` and `I3^E(N-1)` from
the odd conditions is proved explicitly in the two alpha-boundary cases.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The forward comparison in the proof of Theorem 5.1:
`I1^E(N-1)` and `I2^E(N-1)` contain exactly the extra alpha alternative
needed to form `I1^O(N)`. -/
theorem heHuI1E_i2E_to_i1O
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega)) :
    a.HeHuI1O (2 * k + 3) (by omega) (by omega) := by
  apply (a.heHuI1O_iff_i1E_and_alpha
    (n := 2 * k + 3) (by omega) ⟨k + 1, by omega⟩ (by omega)).2
  refine ⟨hI1, ?_⟩
  unfold HeHuI2E at hI2
  rcases hI2 with hZero | ⟨hOne, _⟩
  · exact Or.inl hZero
  · exact Or.inr hOne

/-- Lemma 5.4(ii) supplies the exceptional capped-defect equality, so the
odd initial and middle conditions recover `I2^E(N-1)`. -/
theorem heHuI1O_i2O_to_i2E
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1O : a.HeHuI1O (2 * k + 3) (by omega) (by omega))
    (hI2O : a.HeHuI2O (2 * k + 3) (by omega) (by omega)) :
    a.HeHuI2E (2 * k + 2) (by omega) := by
  have hI1E : a.HeHuI1E (2 * k + 2) (by omega) := hI1O.toI1E
  unfold HeHuI2E
  rcases hI1O.2.2 with hZero | hOne
  · exact Or.inl hZero
  · exact Or.inr ⟨hOne,
      a.heHu2022Lemma54ii_defect (n := 2 * k + 3)
        (by omega) ⟨k + 1, by omega⟩ (by omega) hIntegral
        hI1E hI2O hOne⟩

/-- The second comparison in the proof of Theorem 5.1.  If `alpha_N=0`,
Lemma 5.4(i) and `I2^O` force the only possible large-gap endpoint; if
`alpha_N=1`, Lemma 5.4(ii) makes the large-gap antecedent impossible. -/
theorem heHuI1O_i2O_to_i3E
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hI1O : a.HeHuI1O (2 * k + 3) (by omega) (by omega))
    (hI2O : a.HeHuI2O (2 * k + 3) (by omega) (by omega)) :
    a.HeHuI3E (2 * k + 2) (by omega) := by
  have hI1E : a.HeHuI1E (2 * k + 2) (by omega) := hI1O.toI1E
  unfold HeHuI3E
  intro _hmStable hLargeGap
  rcases hI1O.2.2 with hZero | hOne
  · have hBoundary := a.heHu2022Lemma54i (n := 2 * k + 3)
      (by omega) ⟨k + 1, by omega⟩ (by omega) hI1E hZero
    have hNext := hI2O.1 hZero
    refine ⟨hBoundary, ?_⟩
    intro _hStableClause
    rcases hNext with hNextZero | hNextOne
    · rw [hNextZero, hBoundary] at hLargeGap
      omega
    · exact hNextOne
  · have hGapUpper := a.heHu2022Lemma54ii_gap (n := 2 * k + 3)
      (by omega) ⟨k + 1, by omega⟩ (by omega) hI1E hI2O hOne
    change 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩ at hLargeGap
    change a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩ ≤
      2 * (ramificationIndex K : Int) - 1 at hGapUpper
    exfalso
    omega

/-- He--Hu, Theorem 5.1, for odd target rank `N=2*k+3`. -/
theorem heHu2022Theorem51Odd
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [unitClassification : GoodBONGClassificationLaws.{u, u, u} K]
    [sourceClassification : GoodBONGClassificationLaws.{u, v, v} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L) :
    Lattice.IsNUniversal.{u, v, u} q L (2 * k + 3) ↔
      Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) ∧
        a.HeHuOddSectionConditions (2 * k + 3) (by omega) (by omega) := by
  constructor
  · intro hUniversal
    have h55iff := @heHu2022Proposition55 K _ _ _ _ _ V _ _ q L
      sourceLaws _ _ _ _ _ _ unitClassification sourceClassification
      m k a hm hAIntegral
    have h55 := h55iff.mp hUniversal
    exact ⟨h55.1,
      { i1 := a.heHuI1E_i2E_to_i1O hm h55.2.1 h55.2.2.1
        i2 := h55.2.2.2.2.1
        i3 := h55.2.2.2.2.2 }⟩
  · rintro ⟨hAmbient, hOdd⟩
    have hI1E : a.HeHuI1E (2 * k + 2) (by omega) := hOdd.i1.toI1E
    have hI2E := a.heHuI1O_i2O_to_i2E hm hAIntegral hOdd.i1 hOdd.i2
    have hI3E := a.heHuI1O_i2O_to_i3E hm hOdd.i1 hOdd.i2
    apply (@heHu2022Proposition55 K _ _ _ _ _ V _ _ q L
      sourceLaws _ _ _ _ _ _ unitClassification sourceClassification
      m k a hm hAIntegral).mpr
    exact ⟨hAmbient, hI1E, hI2E, hI3E, hOdd.i2, hOdd.i3⟩

end BONG.GoodBONG

end Bong
