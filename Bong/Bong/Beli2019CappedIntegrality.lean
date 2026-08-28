/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019BoundaryRounding
import Bong.Bong.Beli2019Lemma79EvenTargetCapped

/-!
# Integral and nonintegral capped defects

A quadratic defect order is either infinite or an integer.  Consequently an
internal self-prefix capped defect is either integral or is exactly its final
alpha cap.  This isolates the integrality split used in Beli's proof of
Lemma 7.9(ii), case 3.
-/

namespace Bong

open Dyadic

universe u v

/-- A finite `WithTop ℚ` value represented by an integer. -/
def IsWithTopRationalInteger (x : WithTop ℚ) : Prop :=
  ∃ z : Int, x = ((z : ℚ) : WithTop ℚ)

namespace IsWithTopRationalInteger

/-- Integral values separated by less than one are already ordered. -/
theorem coe_le_of_sub_one_lt
    {x : WithTop ℚ} {y : ℚ}
    (hx : IsWithTopRationalInteger x)
    (hy : IsRationalInteger y)
    (h : ((y - 1 : ℚ) : WithTop ℚ) < x) :
    (y : WithTop ℚ) ≤ x := by
  rcases hx with ⟨z, rfl⟩
  rcases hy with ⟨w, rfl⟩
  apply WithTop.coe_le_coe.mpr
  have hq : (w : ℚ) - 1 < (z : ℚ) := WithTop.coe_lt_coe.mp h
  have hi : w - 1 < z := by exact_mod_cast hq
  exact_mod_cast (show w ≤ z by omega)

end IsWithTopRationalInteger

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A raw quadratic defect order is either infinite or integral. -/
theorem defectOrder_eq_top_or_isWithTopRationalInteger (x : Kˣ) :
    defectOrder (K := K) x = ⊤ ∨
      IsWithTopRationalInteger (defectOrder (K := K) x) := by
  cases hq : quadraticDefect K x with
  | top =>
      left
      unfold defectOrder
      rw [hq]
      rfl
  | coe m =>
      right
      refine ⟨(m : Int), ?_⟩
      unfold defectOrder
      rw [hq]
      rfl

/-- An internal capped self-prefix is integral unless its final alpha is the
active nonintegral cap. -/
theorem alternatingSelfCapped_integral_or_eq_nonintegral_alpha
    (c : GoodBONG q L (n + 2)) (epsilon : Kˣ) (i : Nat)
    (hiPos : 0 < i) (hiBound : i < n + 2) :
    IsWithTopRationalInteger
        (c.truncatedPrefixDefect c epsilon 0 i) ∨
      (c.truncatedPrefixDefect c epsilon 0 i =
          (c.alphaValue ⟨i - 1, by omega⟩ : WithTop ℚ) ∧
        ¬ IsRationalInteger (c.alphaValue ⟨i - 1, by omega⟩)) := by
  let product : Kˣ := epsilon * c.prefixProduct 0 * c.prefixProduct i
  let alpha : ℚ := c.alphaValue ⟨i - 1, by omega⟩
  have hformula : c.truncatedPrefixDefect c epsilon 0 i =
      min (defectOrder (K := K) product) (alpha : WithTop ℚ) := by
    unfold truncatedPrefixDefect
    rw [c.prefixAlphaCap_zero,
      c.prefixAlphaCap_of_internal hiPos hiBound]
    rw [min_eq_right le_top]
  rcases defectOrder_eq_top_or_isWithTopRationalInteger
      (K := K) product with htop | ⟨z, hz⟩
  · by_cases halpha : IsRationalInteger alpha
    · rcases halpha with ⟨w, hw⟩
      apply Or.inl
      refine ⟨w, ?_⟩
      rw [hformula, htop, min_eq_right le_top, hw]
    · exact Or.inr
        ⟨by rw [hformula, htop, min_eq_right le_top], halpha⟩
  · by_cases hraw : defectOrder (K := K) product ≤
        (alpha : WithTop ℚ)
    · apply Or.inl
      refine ⟨z, ?_⟩
      rw [hformula, min_eq_left hraw, hz]
    · have halphaRaw : (alpha : WithTop ℚ) ≤
          defectOrder (K := K) product := le_of_not_ge hraw
      by_cases halpha : IsRationalInteger alpha
      · rcases halpha with ⟨w, hw⟩
        apply Or.inl
        refine ⟨w, ?_⟩
        rw [hformula, min_eq_right halphaRaw, hw]
      · exact Or.inr
          ⟨by rw [hformula, min_eq_right halphaRaw], halpha⟩

/-- A nonintegral internal alternating self-prefix is strictly above `2e`. -/
theorem twoE_lt_alternatingSelfCapped_of_not_integral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (c : GoodBONG q L (n + 2)) (epsilon : Kˣ) (i : Nat)
    (hiPos : 0 < i) (hiBound : i < n + 2)
    (hnot : ¬ IsWithTopRationalInteger
      (c.truncatedPrefixDefect c epsilon 0 i)) :
    ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
      c.truncatedPrefixDefect c epsilon 0 i := by
  rcases c.alternatingSelfCapped_integral_or_eq_nonintegral_alpha
      epsilon i hiPos hiBound with hintegral | ⟨heq, halphaNot⟩
  · exact (hnot hintegral).elim
  · have halphaCases := c.beli2009Corollary28_iii
      ⟨i - 1, by omega⟩
    have halphaLarge : 2 * (ramificationIndex K : ℚ) <
        c.alphaValue ⟨i - 1, by omega⟩ := by
      rcases halphaCases with ⟨_, _, halphaIntegral⟩ | ⟨hlarge, _⟩
      · exact (halphaNot halphaIntegral).elim
      · exact hlarge
    rw [heq]
    exact WithTop.coe_lt_coe.mpr halphaLarge

end BONG.GoodBONG

end Bong
