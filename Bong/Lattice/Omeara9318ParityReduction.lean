/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318Rescale
import Bong.Lattice.OmearaHighRankModularRecursion

/-!
# Parity and rank reduction for O'Meara 93:18(v)

The even-parity case is O'Meara 93:18(ii), already proved concretely.  After
normalizing the modular scale and choosing an actual norm generator, the only
remaining base cases for 93:18(v) are therefore the odd-parity quinary and
senary lattices.  This file records that exact reduction as a function
argument, not as a typeclass or an axiom.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The genuine low-rank remainder of O'Meara 93:18(v): a normalized
unimodular lattice of rank five or six in the odd norm-weight parity case. -/
abbrev Omeara9318vOddRankFiveOrSixConstructor :=
  {X : Type v} → [AddCommGroup X] → [Module K X] →
    (p : QuadraticSpace K X) → (A : Lattice K X) →
      IsModular p A (1 : Kˣ) →
        (finrank K X = 5 ∨ finrank K X = 6) →
          (b : Kˣ) → IsNormGeneratorValue p A b →
            Odd (ordUnit K b + weightIdealOrder p A) →
              Omeara9318vData p A (1 : Kˣ)

/-- The even theorem and an odd quinary/senary constructor produce the full
rank-five-or-six constructor at every modular scale. -/
noncomputable def omeara9318vRankFiveOrSixConstructorOfOdd
    (oddBase : Omeara9318vOddRankFiveOrSixConstructor.{u, v} (K := K)) :
    Omeara9318vRankFiveOrSixConstructor.{u, v} (K := K) := by
  intro X _ _ p A s hmodular hrank
  letI : Module.Finite K X := A.moduleFinite
  let p₀ := p.rescaleUnit s⁻¹
  have h₀ : IsModular p₀ A (1 : Kˣ) :=
    hmodular.isUnimodular_rescaleQuadraticInverse
  let hxExists := exists_isNormGenerator_of_finrank_pos p₀ A (by omega)
  let x : X := Classical.choose hxExists
  have hx : IsNormGenerator p₀ A x :=
    (Classical.choose_spec hxExists).1
  have hxne : p₀.quadratic x ≠ 0 :=
    (Classical.choose_spec hxExists).2
  let b : Kˣ := Units.mk0 (p₀.quadratic x) hxne
  have hb : IsNormGeneratorValue p₀ A b :=
    hx.isNormGeneratorValue hxne
  let parity : Int := ordUnit K b + weightIdealOrder p₀ A
  let D₀ : Omeara9318vData p₀ A (1 : Kˣ) := by
    by_cases heven : Even parity
    · exact omeara9318iiData h₀ (by omega) b hb heven
    · exact oddBase p₀ A h₀ hrank b hb
        (Int.not_even_iff_odd.mp heven)
  have hscale : s⁻¹ * s = (1 : Kˣ) := by simp
  let D : Omeara9318vData p₀ A (s⁻¹ * s) := by
    simpa only [hscale] using D₀
  exact D.unscaleQuadraticUnit s⁻¹ s hmodular

/-- Once the odd quinary and senary calculations are supplied, the geometric
rank recursion proves O'Meara 93:18(v) in every rank at least five. -/
noncomputable def omeara9318vDataOfOddRankFiveOrSix
    (oddBase : Omeara9318vOddRankFiveOrSixConstructor.{u, v} (K := K))
    {X : Type v} [AddCommGroup X] [Module K X]
    (p : QuadraticSpace K X) (A : Lattice K X) (s : Kˣ)
    (hmodular : IsModular p A s)
    (hrank : 5 ≤ finrank K X) :
    Omeara9318vData p A s :=
  omeara9318vDataOfRankFiveOrSix
    (omeara9318vRankFiveOrSixConstructorOfOdd oddBase)
      p A s hmodular hrank

end Lattice

end Bong
