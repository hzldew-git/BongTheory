/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma511
import Bong.Bong.HeHu2022Theorem41
import Bong.Bong.BeliUniversalSectionFour

/-!
# He--Hu 2022, Proposition 5.5

This file proves the odd-rank reduction in Proposition 5.5 of Zilong He
and Yong Hu, *On n-universal quadratic forms over dyadic local fields*,
Sci. China Math. 67 (2024), 1481--1506.

The paper uses without further comment that an `n`-universal lattice is
also `(n-1)`-universal.  We expose that step as a separate lemma: extend an
integral target by the standard integral unit line, apply `n`-universality,
and restrict the resulting representation to the first orthogonal factor.
-/

namespace Bong

open Dyadic

universe u v

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The monotonicity step used in He--Hu, Proposition 5.5: over the same
universe of target spaces, `(n+1)`-universality implies `n`-universality. -/
theorem IsNUniversal.pred {n : Nat}
    (h : IsNUniversal.{u, v, u} q L (n + 1)) :
    IsNUniversal.{u, v, u} q L n := by
  refine ⟨h.1, ?_⟩
  intro W _ _ r M hRank hIntegral
  letI : Module.Finite K W := M.moduleFinite
  let lineQ : QuadraticSpace K K := QuadraticSpace.line K
  let lineL : Lattice K K := BONG.unaryModelLattice (K := K)
  have hLineIntegral : IsIntegral lineQ lineL := by
    rw [isIntegral_iff_forall]
    intro x hx
    have hxIntegral : Dyadic.IsIntegral K x := by
      exact (mem_integerRing_iff K).1
        ((BONG.mem_unaryModelLattice_iff (K := K) x).1 hx)
    simpa only [lineQ, QuadraticSpace.line_quadratic, pow_two] using
      Dyadic.isIntegral_mul K hxIntegral hxIntegral
  have hProductIntegral :
      IsIntegral (r.orthogonalSum lineQ) (product M lineL) :=
    orthogonalProduct_isIntegral hIntegral hLineIntegral
  have hProductRank : Module.finrank K (W × K) = n + 1 := by
    rw [Module.finrank_prod, hRank]
    simp
  have hExtended := h.2 (r.orthogonalSum lineQ) (product M lineL)
    hProductRank hProductIntegral
  exact hExtended.trans
    ⟨Representation.orthogonalProductInl r lineQ M lineL⟩

end Lattice

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- He--Hu, Proposition 5.5.  For odd target rank `N=2*k+3`, lattice
`N`-universality is equivalent to ambient-space `N`-universality together
with the three even-prefix conditions and the two genuinely odd boundary
conditions.  The source paper fixes an integral lattice throughout the
section, so integrality is an explicit premise rather than a repeated
right-hand conjunct here. -/
theorem heHu2022Proposition55
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
        a.HeHuI1E (2 * k + 2) (by omega) ∧
        a.HeHuI2E (2 * k + 2) (by omega) ∧
        a.HeHuI3E (2 * k + 2) (by omega) ∧
        a.HeHuI2O (2 * k + 3) (by omega) (by omega) ∧
        a.HeHuI3O (2 * k + 3) (by omega) (by omega) := by
  constructor
  · intro hUniversal
    have hAmbient :
        Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) := by
      intro W _ _ r M hRank hIntegral
      exact (hUniversal.2 r M hRank hIntegral).ambient
    have hEvenUniversal :
        Lattice.IsNUniversal.{u, v, u} q L (2 * k + 2) := by
      have hPred := hUniversal.pred
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hPred
    have hEven :=
      (a.heHu2022Theorem41Even (m := m) (k := k) (by omega)
        hAIntegral).mp hEvenUniversal
    have hAll :=
      (a.heHuNUniversality_factorization
        (n := 2 * k + 2) (m := m + 2) (by omega)).mp hUniversal
    have hParts :=
      (a.heHuAllRepresentationConditions_iff_components
        (n := 2 * k + 2) (m := m + 2) (by omega)).mp hAll.2.2
    have h510 := a.heHu2022Lemma510 (m := m) (k := k) hm hAIntegral
      hEven.2.2.i1 hEven.2.2.i2 hEven.2.2.i3 hAmbient
    have hTests510 := h510.1.mp hParts.2.1
    have hI2O := h510.2.mp hTests510
    have h511 := @heHu2022Lemma511 K _ _ _ _ _ V _ _ q L
      sourceLaws _ _ _ _ unitClassification sourceClassification m k a hm
      hAIntegral hEven.2.2.i1 hEven.2.2.i2 hEven.2.2.i3 hI2O hAmbient
    have hTests511 := h511.1.mp hParts.2.2
    have hI3O := h511.2.mp hTests511
    exact ⟨hAmbient, hEven.2.2.i1, hEven.2.2.i2, hEven.2.2.i3,
      hI2O, hI3O⟩
  · rintro ⟨hAmbient, hI1, hI2, hI3, hI2O, hI3O⟩
    apply (a.heHuNUniversality_factorization
      (n := 2 * k + 2) (m := m + 2) (by omega)).mpr
    refine ⟨hAIntegral, hAmbient, ?_⟩
    apply (a.heHuAllRepresentationConditions_iff_components
      (n := 2 * k + 2) (m := m + 2) (by omega)).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro W _ _ r M b hB
      have h56 := a.heHu2022Lemma56 (m := m) (n := 2 * k + 1)
        (by omega) ⟨k + 1, by omega⟩ hm hAmbient hAIntegral hI1 hI2
      exact ⟨h56.1 b hB, h56.2 b hB⟩
    · exact a.heHu2022Lemma510I2O_to_universal
        (sourceLaws := sourceLaws) (m := m) (k := k) hm hAIntegral
        hI1 hI2 hI2O
    · exact a.heHu2022Lemma511I3O_to_universal sourceLaws
        (m := m) (k := k) hm hAIntegral hI1 hI2 hI3 hI3O

end BONG.GoodBONG

end Bong
