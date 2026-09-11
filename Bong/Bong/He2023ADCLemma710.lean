/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma79
import Bong.Bong.HeHu2022Theorem41

/-!
# He (2025), Lemma 7.10

The necessary initial orders, terminal alpha alternative, and large-gap
condition follow from Lemma 7.9 and the already formalized He--Hu even-rank
universality criterion. Here the paper's odd rank is `2*k+3`.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The three conclusions of He (2025), Lemma 7.10, expressed through the
literal He--Hu invariant conditions from which the paper derives them. -/
structure HeADCLemma710Conclusions (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2)) : Prop where
  initial : a.HeHuI1E (2 * k + 2) (by omega)
  boundary : a.HeHuI2E (2 * k + 2) (by omega)
  largeGap : a.HeHuI3E (2 * k + 2) (by omega)

/-- He (2025), Lemma 7.10, for odd `n=2*k+3`. -/
theorem heADC2025Lemma710 (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) :
    a.HeADCLemma710Conclusions k := by
  letI : Beli2006AlphaLaws.{u, u} K := beliUniversalAlphaLaws
  have hrank : finrank K V = (2 * k + 3) + 2 := by
    have h := a.toBONG.length_eq_finrank.symm
    omega
  have hUniversal : Lattice.IsNUniversal.{u, u, u} q L (2 * k + 2) := by
    simpa only [show 2 * k + 3 - 1 = 2 * k + 2 by omega] using
      Lattice.heADC2025Lemma79 (2 * k + 3) (by omega)
        ⟨k + 1, by omega⟩ hrank hADC
  have hSection :=
    (a.heHu2022Theorem41Even (m := 2 * k + 2) (k := k)
      (by omega) hADC.isIntegral).mp hUniversal
  exact
    { initial := hSection.2.2.i1
      boundary := hSection.2.2.i2
      largeGap := hSection.2.2.i3 }

/-- Lemma 7.10(i), odd paper indices. -/
theorem HeADCLemma710Conclusions.oddOrder {k : Nat}
    {a : GoodBONG q L (((2 * k + 2) + 1) + 2)}
    (h : a.HeADCLemma710Conclusions k) (i : Fin (2 * k + 3))
    (hi : Odd (i.val + 1)) : a.order ⟨i.val, by omega⟩ = 0 :=
  h.initial.oddOrder i hi

/-- Lemma 7.10(i), even paper indices. -/
theorem HeADCLemma710Conclusions.evenOrder {k : Nat}
    {a : GoodBONG q L (((2 * k + 2) + 1) + 2)}
    (h : a.HeADCLemma710Conclusions k) (i : Fin (2 * k + 2))
    (hi : Even (i.val + 1)) :
    a.order ⟨i.val, by omega⟩ = -(2 * (ramificationIndex K : Int)) :=
  h.initial.evenOrder i hi

/-- Lemma 7.10(ii), with the bracketed defect retained literally. -/
theorem HeADCLemma710Conclusions.alphaAlternative {k : Nat}
    {a : GoodBONG q L (((2 * k + 2) + 1) + 2)}
    (h : a.HeADCLemma710Conclusions k) :
    a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 ∧
        a.heHuAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
          ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
            WithTop ℚ) := by
  simpa only [HeHuI2E] using h.boundary

/-- Lemma 7.10(iii), including the ternary prefix-defect boundary. -/
theorem HeADCLemma710Conclusions.largeGapConclusion {k : Nat}
    {a : GoodBONG q L (((2 * k + 2) + 1) + 2)}
    (h : a.HeADCLemma710Conclusions k)
    (hgap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩) :
    a.order ⟨2 * k + 3, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) ∧
      ((4 ≤ 2 * k + 2 ∨
          (2 * k + 2 = 2 ∧ a.heHuPrefixDefect 4 =
            (((2 * (ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ))) →
        a.order ⟨2 * k + 4, by omega⟩ = 1) := by
  exact h.largeGap (by omega) hgap

end BONG.GoodBONG

end Bong
