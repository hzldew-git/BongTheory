/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Corollary46

/-!
# He--Hu 2022, Theorem 4.7

This file combines Theorem 4.1, the ambient-space rank classification,
Corollary 4.6, and the invariant conversion already proved at the end of
Section 4.  The source lattice below has rank `m + 3`; the target rank is
`2 * k + 2`.
-/

namespace Bong

open Dyadic Module

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The exceptional alternative `m = n + 2 = 4` of Theorem 4.7.  The
outer parameter `m` is rank minus three, so this is `k = 0`, `m = 1`.
The length cast is proof-only and does not alter the BONG. -/
def HeHuTheorem47ExceptionalConditions {m k : Nat}
    (a : GoodBONG q L ((m + 1) + 2)) : Prop :=
  ∃ hk : k = 0, ∃ hm : m = 1,
    (a.castLength (by omega : (m + 1) + 2 = 4)).HeHuCorollary46Invariants

/-- The complete right-hand side of He--Hu, Theorem 4.7. -/
def HeHuTheorem47Conditions {m k : Nat}
    (a : GoodBONG q L ((m + 1) + 2)) : Prop :=
  (∃ hmStable : 2 * k + 2 ≤ m,
      a.HeHuTheorem47StableConditions (2 * k + 2) (by omega)) ∨
    a.HeHuTheorem47ExceptionalConditions (k := k)

private theorem corollary46Invariants_castSelf
    (a : GoodBONG q L 4) (h : 4 = 4) :
    (a.castLength h).HeHuCorollary46Invariants ↔
      a.HeHuCorollary46Invariants := by
  have hh : h = (rfl : 4 = 4) := Subsingleton.elim _ _
  cases hh
  rfl

/-- He--Hu, Theorem 4.7, including both the stable range and the unique
split-quaternary exception. -/
theorem heHu2022Theorem47Even
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hIntegral : Lattice.IsIntegral q L) :
    Lattice.IsNUniversal.{u, v, u} q L (2 * k + 2) ↔
      a.HeHuTheorem47Conditions (k := k) := by
  letI : Module.Finite K V := L.moduleFinite
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  constructor
  · intro hUniversal
    have h41 :=
      (a.heHu2022Theorem41Even hm hIntegral).mp hUniversal
    have hrank : finrank K V = (m + 1) + 2 :=
      a.toBONG.length_eq_finrank.symm
    rcases
        (Lattice.ambientlyEvenUniversal_rank_classification
          (q := q) k).mp h41.2.1 with hstable | hexceptional
    · left
      have hmStable : 2 * k + 2 ≤ m := by
        omega
      refine ⟨hmStable, ?_⟩
      exact
        (a.heHuEvenSectionConditions_iff_theorem47StableConditions
          (by omega) (by omega) ⟨k + 1, by omega⟩).mp h41.2.2
    · right
      rcases hexceptional with ⟨hk, hfour, hsplit⟩
      have hmOne : m = 1 := by omega
      subst k
      subst m
      refine ⟨rfl, rfl, ?_⟩
      have hInvariant :=
        (a.heHu2022Corollary46_universal_iff_invariants hIntegral).mp
          hUniversal
      exact (corollary46Invariants_castSelf a _).mpr hInvariant
  · intro hConditions
    rcases hConditions with hstable | hexceptional
    · rcases hstable with ⟨hmStable, hstable⟩
      have hAmbient :
          Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2) :=
        Lattice.ambientlyNUniversal_of_rank_add_three_le
          (2 * k + 2) (by
            have hrank : finrank K V = (m + 1) + 2 :=
              a.toBONG.length_eq_finrank.symm
            omega)
      have hSection :
          a.HeHuEvenSectionConditions (2 * k + 2) (by omega) :=
        (a.heHuEvenSectionConditions_iff_theorem47StableConditions
          (by omega) (by omega) ⟨k + 1, by omega⟩).mpr hstable
      exact
        (a.heHu2022Theorem41Even hm hIntegral).mpr
          ⟨hIntegral, hAmbient, hSection⟩
    · rcases hexceptional with ⟨hk, hmOne, hInvariant⟩
      subst k
      subst m
      apply
        (a.heHu2022Corollary46_universal_iff_invariants hIntegral).mpr
      exact (corollary46Invariants_castSelf a _).mp hInvariant

end BONG.GoodBONG

end Bong
