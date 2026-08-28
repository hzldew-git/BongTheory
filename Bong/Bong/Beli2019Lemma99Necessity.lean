/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma98

/-!
# Beli (2019), Lemma 9.9: necessity

This file states the numerical existence criterion of Lemma 9.9 and proves
its necessity directly from Remark 8.7, Beli (2009/2010), Lemma 2.7, and the
anisotropic part of Lemma 9.5(i).  The determinant condition is expressed as
the parity of the valuation of a reference determinant.  This is the exact
formal counterpart of `det V = π^R ξ` with `ξ` a valuation unit.

The constructive converse and the odd-alpha refinement are developed in the
subsequent Lemma 9.9 files; no construction principle is assumed here.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L₀ : Lattice K V}

/-- The four numerical conditions in Beli (2019), Lemma 9.9.  The ambient
ternary space is presented by a reference good BONG `reference`; changing the
reference does not change `determinantOrder` because full determinant values
differ by a square. -/
structure Beli2019Lemma99Conditions
    (reference : GoodBONG q L₀ 3) (R₁ R₂ A₁ : Int) : Prop where
  /-- The paper's congruence `R₁ ≡ R₂ (mod 2)`. -/
  orderParity : Int.ModEq 2 R₁ R₂
  /-- The square-class condition `det V = π^R₁ ξ`, `ξ ∈ 𝓞ˣ`. -/
  determinantOrder : Int.ModEq 2
    (ordUnit K reference.toBONG.valueProduct) R₁
  /-- The lower bound `max {0, R₂ - R₁} ≤ α₁`. -/
  lower : max 0 (R₂ - R₁) ≤ A₁
  /-- The upper bound `α₁ ≤ (R₂ - R₁)/2 + e`. -/
  upper : (A₁ : ℚ) ≤ ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K
  /-- If `α₁` is even, it is the upper endpoint and the ternary space is
  isotropic. -/
  evenBoundary : Even A₁ →
    (A₁ : ℚ) = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K ∧
      reference.Lemma814FirstThreeIsotropic

/-- A lattice and good BONG realizing the orders and first alpha prescribed
in Lemma 9.9. -/
structure Beli2019Lemma99Realization
    (R₁ R₂ R₃ A₁ : Int) where
  lattice : Lattice K V
  bong : GoodBONG q lattice 3
  orders : ∀ i, bong.order i = ![R₁, R₂, R₃] i
  firstAlpha : bong.alphaValue (0 : Fin 2) = (A₁ : ℚ)

/-- The `moreover` clause of Lemma 9.9 in the odd-alpha case. -/
def Beli2019Lemma99OddRealization
    (R₁ R₂ R₃ A₁ : Int) : Prop :=
  ∃ D : Beli2019Lemma99Realization (q := q) R₁ R₂ R₃ A₁,
    D.bong.adjacentDefect (1 : Fin 2) = ((A₁ : ℚ) : WithTop ℚ)

namespace Beli2019Lemma99Realization

variable {R₁ R₂ R₃ A₁ : Int}

@[simp]
theorem order_zero
    (D : Beli2019Lemma99Realization (q := q) R₁ R₂ R₃ A₁) :
    D.bong.order (0 : Fin 3) = R₁ := by
  simpa using D.orders (0 : Fin 3)

@[simp]
theorem order_one
    (D : Beli2019Lemma99Realization (q := q) R₁ R₂ R₃ A₁) :
    D.bong.order (1 : Fin 3) = R₂ := by
  simpa using D.orders (1 : Fin 3)

@[simp]
theorem order_two
    (D : Beli2019Lemma99Realization (q := q) R₁ R₂ R₃ A₁) :
    D.bong.order (2 : Fin 3) = R₃ := by
  simpa using D.orders (2 : Fin 3)

theorem outerOrders
    (D : Beli2019Lemma99Realization (q := q) R₁ R₂ R₃ A₁)
    (houter : R₁ = R₃) :
    D.bong.order (0 : Fin 3) = D.bong.order (2 : Fin 3) := by
  rw [D.order_zero, D.order_two, houter]

/-- The order of the determinant of a realization is the sum displayed in
the paper. -/
theorem determinantOrder_eq
    (D : Beli2019Lemma99Realization (q := q) R₁ R₂ R₃ A₁) :
    ordUnit K D.bong.toBONG.valueProduct = R₁ + R₂ + R₃ := by
  rw [D.bong.toBONG.ordUnit_valueProduct_eq_sum_order]
  rw [Fin.sum_univ_three]
  change D.bong.order 0 + D.bong.order 1 + D.bong.order 2 = _
  rw [D.order_zero, D.order_one, D.order_two]

end Beli2019Lemma99Realization

/-- The determinant-order condition is independent of the chosen full
ternary good BONG. -/
theorem beli2019Lemma99_determinantOrder_of_sameSpace
    (reference : GoodBONG q L₀ 3)
    {L : Lattice K V} (b : GoodBONG q L 3) (R : Int)
    (hb : Int.ModEq 2 (ordUnit K b.toBONG.valueProduct) R) :
    Int.ModEq 2 (ordUnit K reference.toBONG.valueProduct) R := by
  rcases BONG.exists_valueProduct_eq_mul_square
      reference.toBONG b.toBONG with ⟨s, hs⟩
  have horders := congrArg (ordUnit K) hs
  rw [ordUnit_mul, ordUnit_pow] at horders
  rw [Int.modEq_iff_dvd] at hb ⊢
  rcases hb with ⟨k, hk⟩
  refine ⟨k + ordUnit K s, ?_⟩
  omega

/-- Beli (2019), Lemma 9.9, necessity.  No Lemma-9.9-specific law or
existence axiom is used. -/
theorem beli2019Lemma99_necessity
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (reference : GoodBONG q L₀ 3)
    (R₁ R₂ R₃ A₁ : Int) (houter : R₁ = R₃)
    (D : Beli2019Lemma99Realization (q := q) R₁ R₂ R₃ A₁) :
    Beli2019Lemma99Conditions reference R₁ R₂ A₁ := by
  have hbOuter := D.outerOrders houter
  have hremark := D.bong.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using hbOuter)
  have hparity : Int.ModEq 2 R₁ R₂ := by
    simpa [remark87PreviousValue, remark87MiddleValue,
      D.order_zero, D.order_one] using hremark.previous_middle_modEq
  have hdetB : Int.ModEq 2
      (ordUnit K D.bong.toBONG.valueProduct) R₁ := by
    rw [D.determinantOrder_eq, houter]
    rw [Int.modEq_iff_dvd] at hparity ⊢
    rcases hparity with ⟨k, hk⟩
    refine ⟨-R₁ - k, ?_⟩
    omega
  have hdet := beli2019Lemma99_determinantOrder_of_sameSpace
    reference D.bong R₁ hdetB
  have hsecondNonnegative : 0 ≤ D.bong.alphaValue (1 : Fin 2) :=
    (D.bong.beli2009Lemma27_i (1 : Fin 2)).1
  have hfirstUpper := D.bong.alphaValue_le_halfGapValue (0 : Fin 2)
  have hrelation := hremark.currentAlpha_eq
  change D.bong.alphaValue (1 : Fin 2) =
      ((D.bong.order (0 : Fin 3) - D.bong.order (1 : Fin 3) : Int) : ℚ) +
        D.bong.alphaValue (0 : Fin 2) at hrelation
  have hfirstUpper' : (A₁ : ℚ) ≤
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    simpa [halfGapValue, orderGap, D.firstAlpha] using hfirstUpper
  have hgapUpper : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) := by
    rw [D.order_zero, D.order_one, D.firstAlpha] at hrelation
    have hgapUpperQ : ((R₂ - R₁ : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      push_cast at hfirstUpper' hrelation ⊢
      linarith
    exact_mod_cast hgapUpperQ
  have hgapLowerQ : ((R₂ - R₁ : Int) : ℚ) ≤ (A₁ : ℚ) := by
    have h := (D.bong.beli2009Lemma27_iii (0 : Fin 2) (by
      unfold orderGap
      simpa [D.order_zero, D.order_one] using hgapUpper)).1
    simpa [orderGap, D.order_zero, D.order_one, D.firstAlpha] using h
  have hgapLower : R₂ - R₁ ≤ A₁ := by
    exact_mod_cast hgapLowerQ
  have hzeroLower : 0 ≤ A₁ := by
    have h := (D.bong.beli2009Lemma27_i (0 : Fin 2)).1
    rw [D.firstAlpha] at h
    exact_mod_cast h
  have hlower : max 0 (R₂ - R₁) ≤ A₁ := max_le hzeroLower hgapLower
  have hupper : (A₁ : ℚ) ≤
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    exact hfirstUpper'
  refine {
    orderParity := hparity
    determinantOrder := hdet
    lower := hlower
    upper := hupper
    evenBoundary := ?_
  }
  intro hA₁Even
  have hhalf := D.bong.attainsHalfGap_of_alphaInteger_even
    (0 : Fin 2) A₁ D.firstAlpha hA₁Even
  have heq : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    unfold AttainsHalfGap halfGapValue orderGap at hhalf
    simpa [D.order_zero, D.order_one, D.firstAlpha] using hhalf
  refine ⟨heq, ?_⟩
  have hDIsotropic : D.bong.Lemma814FirstThreeIsotropic := by
    by_contra hnot
    have hanisotropic :=
      (D.bong.not_firstThreeIsotropic_iff_anisotropic).mp hnot
    rcases D.bong.beli2019Lemma95_i hbOuter hanisotropic with
      ⟨z, hzOdd, hz⟩
    have hAz : A₁ = z := by
      exact_mod_cast D.firstAlpha.symm.trans hz
    have hA₁Odd : Odd A₁ := by simpa [hAz] using hzOdd
    exact Int.not_odd_iff_even.mpr hA₁Even hA₁Odd
  exact (lemma95_firstThreeIsotropic_iff_sameSpace reference D.bong).mpr
    hDIsotropic

end BONG.GoodBONG

end Bong
