/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma58

/-!
# He (2024), Proposition 5.2

This file assembles the four representation conditions for odd target rank.
It also records the elementary rank-descent step used for necessity: classic
`(n+1)`-universality implies classic `n`-universality after adjoining an
integral unit line to the target.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice

/-- The standard unit line is classic integral. -/
theorem isClassicIntegral_scaledLine_one_unaryModel :
    IsClassicIntegral (QuadraticSpace.scaledLine (1 : Kˣ))
      (BONG.unaryModelLattice (K := K)) := by
  rw [isClassicIntegral_iff_forall]
  intro x y hx hy
  have hx' : Dyadic.IsIntegral K x := by
    rw [BONG.mem_unaryModelLattice_iff, mem_integerRing_iff] at hx
    exact hx
  have hy' : Dyadic.IsIntegral K y := by
    rw [BONG.mem_unaryModelLattice_iff, mem_integerRing_iff] at hy
    exact hy
  simp only [QuadraticSpace.scaledLine_bilin_apply, Units.val_one, one_mul]
  exact Dyadic.isIntegral_mul K hx' hy'

/-- Orthogonal products of classic integral lattices are classic integral. -/
theorem IsClassicIntegral.orthogonalProduct
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (hL : IsClassicIntegral q L) (hM : IsClassicIntegral r M) :
    IsClassicIntegral (q.orthogonalSum r) (product L M) := by
  rw [isClassicIntegral_iff_forall]
  intro x y hx hy
  rw [mem_product_iff] at hx hy
  rw [QuadraticSpace.orthogonalSum_bilin_apply]
  exact Dyadic.isIntegral_add K
    ((isClassicIntegral_iff_forall q L).1 hL x.1 y.1 hx.1 hy.1)
    ((isClassicIntegral_iff_forall r M).1 hM x.2 y.2 hx.2 hy.2)

/-- Classic universality descends by one rank. -/
theorem IsClassicNUniversal.oneRankLower {n : Nat}
    (h : IsClassicNUniversal.{u, v, u} q L (n + 1)) :
    IsClassicNUniversal.{u, v, u} q L n := by
  refine ⟨h.1, ?_⟩
  intro W _ _ r M hRank hM
  letI : Module.Finite K W := M.moduleFinite
  let lineQ := QuadraticSpace.scaledLine (1 : Kˣ)
  let lineL := BONG.unaryModelLattice (K := K)
  have hProductClassic : IsClassicIntegral (r.orthogonalSum lineQ)
      (product M lineL) := by
    exact hM.orthogonalProduct
      isClassicIntegral_scaledLine_one_unaryModel
  have hProductRank : Module.finrank K (W × K) = n + 1 := by
    rw [Module.finrank_prod, hRank]
    simp
  have hProduct := h.2 (r.orthogonalSum lineQ) (product M lineL)
    hProductRank hProductClassic
  have hLeft : Represents (r.orthogonalSum lineQ) r (product M lineL) M :=
    ⟨Representation.orthogonalProductInl r lineQ M lineL⟩
  exact hProduct.trans hLeft

end Lattice

namespace BONG.GoodBONG

/-- The five invariant conditions printed on the right of Proposition 5.2. -/
structure HeClassicProposition52Conditions {m : Nat}
    (a : GoodBONG q L (m + 5)) (k : Nat)
    (hSource : 2 * k + 6 <= m + 5) : Prop where
  j1E : a.HeClassicJ1E (2 * k + 2) (by omega)
  j2E : a.HeClassicJ2E (2 * k + 2) (by omega)
  j3E : a.HeClassicJ3E (2 * k + 2) (by omega)
  j2O : a.HeClassicJ2O (2 * k + 3) (by omega) (by omega)
  j3O : a.HeClassicJ3O (2 * k + 3) (by omega) (by omega)

/-- He (2024), Proposition 5.2, for odd paper rank `n=2*k+3`.
The paper's standing classic-integrality premise is displayed as a conjunct
because it is not built into the repository's universality predicate. -/
theorem he2022ClassicProposition52
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5) :
    Lattice.IsClassicNUniversal.{u, v, u} q L (2 * k + 3) ↔
      Lattice.IsClassicIntegral q L ∧
        Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) ∧
          a.HeClassicProposition52Conditions k hSource := by
  have hRank : 2 * k + 2 <= m + 4 := by omega
  constructor
  · intro hUniversal
    have hFactor := (a.heClassicNUniversality_factorization
      (n := 2 * k + 2) (m := m + 4) hRank).1 hUniversal
    have hClassic : Lattice.IsClassicIntegral q L := hFactor.1
    have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q
        (2 * k + 3) :=
      (Lattice.ambientlyClassicNUniversal_iff_ambientlyNUniversal
        q (2 * k + 3)).1 hFactor.2.1
    have hComponents :=
      (a.heClassicAllRepresentationConditionsPrime_iff_components
        (n := 2 * k + 2) (m := m + 4) hRank).1 hFactor.2.2
    have hLower : Lattice.IsClassicNUniversal.{u, v, u} q L
        (2 * k + 2) := by
      simpa only [show 2 * k + 3 = (2 * k + 2) + 1 by omega] using
        hUniversal.oneRankLower
    have hEven := (a.he2022ClassicTheorem41 (m := m + 1) (t := k)
      (by omega)).1
      hLower
    have hJ1 : a.HeClassicJ1E (2 * k + 2) (by omega) := hEven.2.2.j1
    have hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega) := hEven.2.2.j2
    have hJ3 : a.HeClassicJ3E (2 * k + 2) (by omega) := hEven.2.2.j3
    have hEquation := (a.he2022ClassicEquation43 (m := m + 4)
      (n := 2 * k + 2) (by omega) hClassic).2 ⟨hJ1, hJ2⟩
    have hJ1Prime := hEquation.1
    have hJ2O : a.HeClassicJ2O (2 * k + 3) (by omega) (by omega) :=
      a.he2022ClassicLemma57_tests_to_j2O hSource hClassic hJ1Prime hJ2
        (a.he2022ClassicLemma57_all_to_tests hSource hClassic hJ1Prime hJ2
          hComponents.2.1)
    have hJ3O : a.HeClassicJ3O (2 * k + 3) (by omega) (by omega) :=
      a.he2022ClassicLemma58_tests_to_j3O hSource hClassic hJ1Prime hJ2
        hJ2O (a.he2022ClassicLemma58_all_to_tests hSource hComponents.2.2)
    exact ⟨hClassic, hAmbient, ⟨hJ1, hJ2, hJ3, hJ2O, hJ3O⟩⟩
  · rintro ⟨hClassic, hAmbient, hConditions⟩
    letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
    have hAmbientClassic : Lattice.AmbientlyClassicNUniversal.{u, v, u} q
        (2 * k + 3) :=
      (Lattice.ambientlyClassicNUniversal_iff_ambientlyNUniversal
        q (2 * k + 3)).2 hAmbient
    have hEquation := (a.he2022ClassicEquation43 (m := m + 4)
      (n := 2 * k + 2) (by omega) hClassic).2
      ⟨hConditions.j1E, hConditions.j2E⟩
    have hInitial : HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * k + 2) a hRank :=
      (a.he2022ClassicLemma54 (m := m + 2) k (by omega) hClassic
        hAmbient hConditions.j2E).2 hEquation.1
    have hCentral : HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
        (n := 2 * k + 2) a :=
      a.he2022ClassicLemma57_all_of_j2O hSource hClassic hEquation.1
        hConditions.j2E hConditions.j2O
    have hLong : HeClassicAllLongRepresentationConditions.{u, v, u}
        (n := 2 * k + 2) a :=
      a.he2022ClassicLemma58_all_of_j3O hSource hClassic hEquation.1
        hConditions.j2E hConditions.j2O hConditions.j3O
    have hAll : HeClassicAllRepresentationConditionsPrime.{u, v, u} a hRank :=
      (a.heClassicAllRepresentationConditionsPrime_iff_components
        (n := 2 * k + 2) (m := m + 4) hRank).2
        ⟨hInitial, hCentral, hLong⟩
    exact (a.heClassicNUniversality_factorization
      (n := 2 * k + 2) (m := m + 4) hRank).2
        ⟨hClassic, hAmbientClassic, hAll⟩

end BONG.GoodBONG

end Bong
