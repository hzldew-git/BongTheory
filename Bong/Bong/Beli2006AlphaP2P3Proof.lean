/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaParityProof

/-!
# Beli (2006), properties P2 and P3

The nonnegative lower bound is proved directly from the finite candidate
minimum.  The equality cases use the now-independent proof of Beli
(2009/2010), Lemma 2.7(iv): an alpha value different from the half-gap is an
odd rational integer.  This closes the last two fields of
`Beli2006AlphaLaws` without a circular instance.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- Beli (2006), property P2, including its equality case. -/
theorem satisfiesAlphaP2_proved
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    (b : GoodBONG q L (n + 1)) :
    b.SatisfiesAlphaP2 := by
  intro i
  refine ⟨b.zero_le_alphaValue i, ?_⟩
  constructor
  · intro halpha
    have hhalf : b.alphaValue i = b.halfGapValue i := by
      by_contra hne
      rcases b.beli2009Lemma27_iv_proved i hne with ⟨z, hzOdd, hzvalue⟩
      have hzQ : (z : ℚ) = 0 := hzvalue.symm.trans halpha
      have hz : z = 0 := by exact_mod_cast hzQ
      subst z
      simpa using hzOdd
    have hgapQ :
        (b.orderGap i : ℚ) =
          -(2 * (ramificationIndex K : ℚ)) := by
      unfold halfGapValue at hhalf
      push_cast at hhalf
      rw [halpha] at hhalf
      linarith
    exact_mod_cast hgapQ
  · intro hgap
    have hhalf : b.halfGapValue i = 0 := by
      unfold halfGapValue
      rw [hgap]
      push_cast
      ring
    apply le_antisymm
    · rw [← hhalf]
      exact b.alphaValue_le_halfGapValue_for_properties i
    · exact b.zero_le_alphaValue i

/-- Beli (2006), property P3, including both equality branches. -/
theorem satisfiesAlphaP3_proved
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    (b : GoodBONG q L (n + 1)) :
    b.SatisfiesAlphaP3 := by
  intro i hgap
  refine ⟨b.orderGap_le_alphaValue_of_le_twoE i hgap, ?_⟩
  constructor
  · intro halpha
    by_cases hhalf : b.alphaValue i = b.halfGapValue i
    · left
      have hgapHalf : (b.orderGap i : ℚ) = b.halfGapValue i :=
        halpha.symm.trans hhalf
      have hgapQ :
          (b.orderGap i : ℚ) =
            2 * (ramificationIndex K : ℚ) := by
        unfold halfGapValue at hgapHalf
        push_cast at hgapHalf
        linarith
      exact_mod_cast hgapQ
    · right
      rcases b.beli2009Lemma27_iv_proved i hhalf with
        ⟨z, hzOdd, hzvalue⟩
      have hzgapQ : (z : ℚ) = (b.orderGap i : ℚ) :=
        hzvalue.symm.trans halpha
      have hzgap : z = b.orderGap i := by exact_mod_cast hzgapQ
      simpa only [hzgap] using hzOdd
  · rintro (hendpoint | hodd)
    · have hp4 := b.satisfiesAlphaP4_proved i (le_of_eq hendpoint.symm)
      have hhalf : b.halfGapValue i = (b.orderGap i : ℚ) := by
        unfold halfGapValue
        rw [hendpoint]
        push_cast
        ring
      exact hp4.trans hhalf
    · exact b.alphaValue_eq_orderGap_of_odd_of_le_twoE i hgap hodd

end BONG.GoodBONG

/-- The remaining Beli (2006) alpha-law interface is derivable from the
concrete candidate calculation and Lemma 2.7(iv). -/
noncomputable instance beli2006AlphaLaws_proved
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K] :
    Beli2006AlphaLaws.{u, v} K where
  properties := fun b ↦
    ⟨BONG.GoodBONG.satisfiesAlphaP2_proved b,
      BONG.GoodBONG.satisfiesAlphaP3_proved b⟩

end Bong
