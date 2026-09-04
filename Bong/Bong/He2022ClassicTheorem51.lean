/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicProposition52

/-!
# He (2024), Theorem 5.1

The odd-rank criterion is obtained from Proposition 5.2 using equation (5.2)
and Lemma 5.3.  The source-rank hypothesis is the literal `m >= n+3`; it also
supplies ambient `n`-universality of the quadratic space.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- He (2024), Theorem 5.1, at odd paper rank `n=2*k+3`. -/
theorem he2022ClassicTheorem51
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5) :
    Lattice.IsClassicNUniversal.{u, v, u} q L (2 * k + 3) ↔
      Lattice.IsClassicIntegral q L ∧
        a.HeClassicOddSectionConditions (2 * k + 3) (by omega) (by omega) := by
  constructor
  · intro hUniversal
    have h52 := (a.he2022ClassicProposition52 hSource).1 hUniversal
    have hJ1O : a.HeClassicJ1O (2 * k + 3) (by omega) (by omega) :=
      (a.heClassicJ1O_iff_j1E_and_j2E (by omega) ⟨k + 1, by omega⟩
        (by omega)).2 ⟨h52.2.2.j1E, h52.2.2.j2E⟩
    exact ⟨h52.1, ⟨hJ1O, h52.2.2.j2O, h52.2.2.j3O⟩⟩
  · rintro ⟨hClassic, hOdd⟩
    letI : Module.Finite K V := L.moduleFinite
    have hEvenConditions :=
      (a.heClassicJ1O_iff_j1E_and_j2E (by omega) ⟨k + 1, by omega⟩
        (by omega)).1 hOdd.j1
    have hRAt : a.order ⟨2 * k + 2, by omega⟩ = 0 :=
      hEvenConditions.1 ⟨2 * k + 2, by omega⟩
    have hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 :=
      hEvenConditions.2.1
    have hLemma53 := a.he2022ClassicLemma53
      (m := m + 3) (n := 2 * k + 3) (by omega)
      ⟨k + 1, by omega⟩ (by omega) hClassic hRAt hAlpha hOdd.j2
    have hJ3E : a.HeClassicJ3E (2 * k + 2) (by omega) := by
      intro _hStable
      have h' : a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩ <=
            2 * (ramificationIndex K : Int) - 1 := by
        simpa only [show 2 * k + 3 + 1 = 2 * k + 4 by omega] using
          hLemma53.1
      change a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩ <=
            2 * (ramificationIndex K : Int)
      omega
    have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q
        (2 * k + 3) :=
      Lattice.ambientlyNUniversal_of_rank_add_three_le (2 * k + 3) (by
        have hRank : Module.finrank K V = m + 5 :=
          a.toBONG.length_eq_finrank.symm
        omega)
    exact (a.he2022ClassicProposition52 hSource).2
      ⟨hClassic, hAmbient,
        ⟨hEvenConditions.1, hEvenConditions.2, hJ3E, hOdd.j2, hOdd.j3⟩⟩

end BONG.GoodBONG

end Bong
