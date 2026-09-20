/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma46
import Bong.Lattice.DeepRescale

/-!
# He (2024), Theorem 4.1

This file assembles Lemmas 4.2, 4.5, and 4.6 through Theorem 2.5 and
Equation (4.3).  It also proves that ambient universality tested using
classic integral presentations is equivalent to ordinary ambient
universality: every full lattice has a sufficiently deep rescaling on
which all bilinear pairings are integral.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice

/-- Every full lattice can be multiplied by a sufficiently deep
uniformizer power so that every bilinear pairing is integral. -/
theorem exists_classicIntegral_rescale
    (q : QuadraticSpace K V) (A : Lattice K V) :
    ∃ c : Kˣ, IsClassicIntegral q (rescale c A) := by
  obtain ⟨k, hk, hdual⟩ := exists_uniformizerPower_rescale_le A
    (dualLattice q A) 0
  let c : Kˣ := uniformizerPowerUnit K k
  have hcIntegral : (c : K) ∈ IntegerRing K := by
    rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit K c,
      ordUnit_uniformizerPowerUnit]
    exact_mod_cast hk
  have hself : rescale c A ≤ A :=
    rescale_le_self_of_mem_integerRing c A hcIntegral
  refine ⟨c, (isClassicIntegral_iff_forall q (rescale c A)).2 ?_⟩
  intro x y hx hy
  have hxDual : x ∈ dualLattice q A := hdual hx
  exact (mem_dualLattice_iff q A x).1 hxDual y (hself hy)

/-- The lattice used to present a target space does not affect ambient
universality.  A classic integral presentation exists after deep
rescaling, while classic integrality implies ordinary integrality. -/
theorem ambientlyClassicNUniversal_iff_ambientlyNUniversal
    (q : QuadraticSpace K V) (n : Nat) :
    AmbientlyClassicNUniversal.{u, v, w} q n ↔
      AmbientlyNUniversal.{u, v, w} q n := by
  constructor
  · intro hClassic W _ _ r M hRank _hIntegral
    obtain ⟨c, hc⟩ := exists_classicIntegral_rescale r M
    exact hClassic r (rescale c M) hRank hc
  · intro hAmbient W _ _ r M hRank hClassic
    exact hAmbient r M hRank hClassic.isIntegral

end Lattice

namespace BONG.GoodBONG

/-- He (2024), Theorem 4.1, for the even target rank `2*t+2`.
The formal lattice predicate does not build classic integrality into its
type, so the paper's standing classic-integral hypothesis is displayed as
the first conjunct on the right. -/
theorem he2022ClassicTheorem41
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m t : Nat} (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4) :
    Lattice.IsClassicNUniversal.{u, v, u} q L (2 * t + 2) ↔
      Lattice.IsClassicIntegral q L ∧
        Lattice.AmbientlyNUniversal.{u, v, u} q (2 * t + 2) ∧
          a.HeClassicEvenSectionConditions (2 * t + 2) (by omega) := by
  have hRank : 2 * t + 1 <= m + 3 := by omega
  constructor
  · intro hUniversal
    have hFactor : Lattice.IsClassicIntegral q L ∧
        Lattice.AmbientlyClassicNUniversal.{u, v, u} q (2 * t + 2) ∧
          HeClassicAllRepresentationConditionsPrime.{u, v, u} a hRank :=
      (a.heClassicNUniversality_factorization
        (n := 2 * t + 1) (m := m + 3) hRank).1 hUniversal
    have hClassic := hFactor.1
    have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q
        (2 * t + 2) :=
      (Lattice.ambientlyClassicNUniversal_iff_ambientlyNUniversal
        q (2 * t + 2)).1 hFactor.2.1
    have hComponents :
        HeClassicAllOrderAndDefectConditions.{u, v, u}
            (n := 2 * t + 1) a hRank ∧
          HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
              (n := 2 * t + 1) a ∧
            HeClassicAllLongRepresentationConditions.{u, v, u}
              (n := 2 * t + 1) a :=
      (a.heClassicAllRepresentationConditionsPrime_iff_components
        (n := 2 * t + 1) (m := m + 3) hRank).1 hFactor.2.2
    have hInitial : HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * t + 1) a hRank := hComponents.1
    have hCentral :
        HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
          (n := 2 * t + 1) a := hComponents.2.1
    have hLong : HeClassicAllLongRepresentationConditions.{u, v, u}
        (n := 2 * t + 1) a := hComponents.2.2
    have hPrime :
        a.HeClassicJ1EPrime (2 * t + 2) (by omega) ∧
          a.HeClassicJ2EPrime (2 * t + 2) (by omega) :=
      (a.he2022ClassicLemma42 (m := m + 1) t hSource hClassic).1
        hInitial
    have hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega) :=
      (a.he2022ClassicLemma45 t hSource hClassic hAmbient
        hPrime.1 hPrime.2).1 hCentral
    have hJ1 : a.HeClassicJ1E (2 * t + 2) (by omega) := hPrime.1.1
    have hJ3 : a.HeClassicJ3E (2 * t + 2) (by omega) :=
      (a.he2022ClassicLemma46 t hSource hPrime.1 hJ2).1 hLong
    exact ⟨hClassic, hAmbient, ⟨hJ1, hJ2, hJ3⟩⟩
  · rintro ⟨hClassic, hAmbient, hConditions⟩
    have hAmbientClassic :
        Lattice.AmbientlyClassicNUniversal.{u, v, u} q
          (2 * t + 2) :=
      (Lattice.ambientlyClassicNUniversal_iff_ambientlyNUniversal
        q (2 * t + 2)).2 hAmbient
    have hEquation :=
      (a.he2022ClassicEquation43 (m := m + 3)
        (n := 2 * t + 2) (by omega) hClassic).2
        ⟨hConditions.j1, hConditions.j2⟩
    have hInitial : HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * t + 1) a (by omega) :=
      (a.he2022ClassicLemma42 (m := m + 1) t hSource hClassic).2
        ⟨hEquation.1, hEquation.2.1⟩
    have hCentral :
        HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
          (n := 2 * t + 1) a :=
      (a.he2022ClassicLemma45 t hSource hClassic hAmbient
        hEquation.1 hEquation.2.1).2 hConditions.j2
    have hLong : HeClassicAllLongRepresentationConditions.{u, v, u}
        (n := 2 * t + 1) a :=
      (a.he2022ClassicLemma46 t hSource
        hEquation.1 hConditions.j2).2 hConditions.j3
    have hAll : HeClassicAllRepresentationConditionsPrime.{u, v, u}
        a hRank :=
      (a.heClassicAllRepresentationConditionsPrime_iff_components
        (n := 2 * t + 1) (m := m + 3) hRank).2
        ⟨hInitial, hCentral, hLong⟩
    exact (a.heClassicNUniversality_factorization
      (n := 2 * t + 1) (m := m + 3) hRank).2
        ⟨hClassic, hAmbientClassic, hAll⟩

end BONG.GoodBONG

end Bong
