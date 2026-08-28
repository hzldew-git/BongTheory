/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaArithmetic
import Bong.Bong.Beli2019Lemma76Early

/-!
# Beli (2019), Lemma 7.6: boundary dichotomy

At the type-I switch, two same-parity orders differ by one.  If the alpha at
the preceding boundary is at most one, its integrality forces it to be zero
or one.  Properties P2 and P3 then give exactly the two boundary alternatives
used in Lemma 7.6.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The arithmetic boundary dichotomy in Lemma 7.6.  Here `p` is the
zero-based index two positions before the first switched order. -/
theorem alternatingPrefixDefect_boundary_cases
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (p : Nat) (hp : p + 2 < n + 2)
    (ε : Kˣ)
    (hskip : b.order ⟨p + 2, hp⟩ = b.order ⟨p, by omega⟩ + 1)
    (hodd : Odd (b.orderGap ⟨p + 1, by omega⟩))
    (hprevAlpha : b.alphaValue ⟨p, by omega⟩ ≤ 1)
    (hlower :
      (((((b.order ⟨p, by omega⟩ - b.order ⟨p + 1, by omega⟩ : Int) :
          ℚ) + b.alphaValue ⟨p, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        b.truncatedPrefixDefect b ε 0 (p + 2)) :
    (b.orderGap ⟨p + 1, by omega⟩ ≤
          2 * (ramificationIndex K : Int) →
        b.truncatedPrefixDefect b ε 0 (p + 2) =
          (b.alphaValue ⟨p + 1, by omega⟩ : WithTop ℚ)) ∧
      (b.orderGap ⟨p + 1, by omega⟩ =
          2 * (ramificationIndex K : Int) + 1 →
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
          b.truncatedPrefixDefect b ε 0 (p + 2)) := by
  let previous : Fin (n + 1) := ⟨p, by omega⟩
  let current : Fin (n + 1) := ⟨p + 1, by omega⟩
  have hgapSum : b.orderGap previous + b.orderGap current = 1 := by
    change
      (b.order ⟨p + 1, by omega⟩ - b.order ⟨p, by omega⟩) +
        (b.order ⟨p + 2, hp⟩ - b.order ⟨p + 1, by omega⟩) = 1
    rw [hskip]
    ring
  have hpreviousDifference :
      b.order ⟨p, by omega⟩ - b.order ⟨p + 1, by omega⟩ =
        -b.orderGap previous := by
    change
      b.order ⟨p, by omega⟩ - b.order ⟨p + 1, by omega⟩ =
        -(b.order ⟨p + 1, by omega⟩ - b.order ⟨p, by omega⟩)
    ring
  have hupper : b.truncatedPrefixDefect b ε 0 (p + 2) ≤
      (b.alphaValue current : WithTop ℚ) := by
    have h := b.truncatedPrefixDefect_le_rightCap b ε 0 (p + 2)
    rw [b.prefixAlphaCap_of_internal (by omega) hp] at h
    have hindex : (⟨p + 2 - 1, by omega⟩ : Fin (n + 1)) = current := by
      apply Fin.ext
      simp only [current]
      omega
    rwa [hindex] at h
  constructor
  · intro hcurrentLe
    have hcurrentLe' : b.orderGap current ≤
        2 * (ramificationIndex K : Int) := by
      simpa only [current] using hcurrentLe
    have hodd' : Odd (b.orderGap current) := by
      simpa only [current] using hodd
    have hpreviousGap : -(2 * (ramificationIndex K : Int)) <
        b.orderGap previous := by
      have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
      omega
    have hpreviousAlphaNe : b.alphaValue previous ≠ 0 := by
      intro hzero
      have hgapEq := (b.alpha_p2 previous).2.mp hzero
      omega
    have hprevNonneg := (b.alpha_p2 previous).1
    have hePos := ramificationIndex_pos (K := K)
    have hprevTwoE : b.alphaValue previous ≤
        2 * (ramificationIndex K : ℚ) := by
      have hone : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
        exact_mod_cast (show (1 : Int) ≤
          2 * (ramificationIndex K : Int) by omega)
      exact hprevAlpha.trans hone
    have hprevIntegral : IsRationalInteger (b.alphaValue previous) := by
      rcases b.beli2009Corollary28_iii previous with hfinite | hinfinite
      · exact hfinite.2.2
      · exact (not_lt_of_ge hprevTwoE hinfinite.1).elim
    have hpreviousAlphaOne : b.alphaValue previous = 1 := by
      rcases hprevIntegral with ⟨z, hz⟩
      have hzNonneg : (0 : Int) ≤ z := by
        exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
          simpa only [← hz] using hprevNonneg)
      have hzLe : z ≤ (1 : Int) := by
        exact_mod_cast (show (z : ℚ) ≤ 1 by
          simpa only [← hz] using hprevAlpha)
      have hzNe : z ≠ 0 := by
        intro hzZero
        apply hpreviousAlphaNe
        rw [hz, hzZero]
        norm_num
      have hzOne : z = 1 := by omega
      rw [hz, hzOne]
      norm_num
    have hcurrentAlpha : b.alphaValue current =
        (b.orderGap current : ℚ) :=
      (b.alpha_p3 current hcurrentLe').2.mpr (Or.inr hodd')
    have hcritical :
        ((b.order ⟨p, by omega⟩ - b.order ⟨p + 1, by omega⟩ : Int) :
            ℚ) + b.alphaValue previous = b.alphaValue current := by
      rw [hpreviousAlphaOne, hcurrentAlpha]
      rw [hpreviousDifference]
      exact_mod_cast (show
        -b.orderGap previous + 1 = b.orderGap current by omega)
    apply le_antisymm hupper
    rw [hcritical] at hlower
    exact hlower
  · intro hcurrentEq
    have hcurrentEq' : b.orderGap current =
        2 * (ramificationIndex K : Int) + 1 := by
      simpa only [current] using hcurrentEq
    have hpreviousEq : b.orderGap previous =
        -(2 * (ramificationIndex K : Int)) := by
      omega
    have hpreviousAlphaZero : b.alphaValue previous = 0 :=
      (b.alpha_p2 previous).2.mpr hpreviousEq
    have hcritical :
        ((b.order ⟨p, by omega⟩ - b.order ⟨p + 1, by omega⟩ : Int) :
            ℚ) + b.alphaValue previous =
          2 * (ramificationIndex K : ℚ) := by
      rw [hpreviousAlphaZero]
      rw [hpreviousDifference, hpreviousEq]
      push_cast
      ring
    rw [hcritical] at hlower
    exact hlower

end BONG.GoodBONG

end Bong
