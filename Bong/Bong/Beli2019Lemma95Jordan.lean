/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma95NormalForm
import Bong.Bong.Beli2019Lemma711
import Bong.Bong.Beli2009JordanCoordinates
import Bong.Bong.BeliLemmas48To410

/-!
# Beli (2019), Lemma 9.5(ii): Jordan invariants of the normal-form model

The field-space calculation in `Beli2019Lemma95NormalForm` constructs the
literal lattice `\<head\> ⊥ [first, second]`.  The remaining integral
calculation in lines 9527--9569 of the paper determines the good-BONG order
profile and the weight ideal of this model.  Those are the exact local
Jordan inputs isolated by `Beli2019UnaryBinaryJordanLaws` below.

This interface deliberately does not assert the desired lattice isometry or
an alpha equality.  The alpha equality is derived here from Beli (2009),
Lemma 2.14, and, in the negative-radius branch, from reverse duality.  The
lattice isometry then follows from the already proved Lemma 7.11.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Arithmetic data describing the standard lattice
`\<head\> ⊥ [first, second]` in the normalization used in Lemma 9.5.

Its displayed coefficient orders are
`s+r`, `s+r+A`, and `s-r-A`.  The expected good-BONG orders are
`s+r`, `s-r`, and `s+r`. -/
structure UnaryBinaryJordanData
    [BONGGoodExistenceLaws.{u, u} K]
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) where
  center : Int
  radius : Int
  alpha : Int
  head_order : ordUnit K head = center + radius
  first_order : ordUnit K first = center + radius + alpha
  second_order : ordUnit K second = center - radius - alpha
  alpha_nonnegative : 0 ≤ alpha
  /-- The second alpha parameter after reversing the three-dimensional model is
  `alpha + 2 * radius`; Beli's normal form requires it to be nonnegative as
  well. -/
  dual_alpha_nonnegative : 0 ≤ alpha + 2 * radius
  alpha_le_halfGap : alpha ≤ -radius + (ramificationIndex K : Int)
  alpha_half_or_odd :
    alpha = -radius + (ramificationIndex K : Int) ∨ Odd alpha

namespace UnaryBinaryJordanData

variable [BONGGoodExistenceLaws.{u, u} K]
  {head first second : Kˣ}
  {hadmissible : IsBinaryParameterAdmissible (second / first)}

/-- The chosen good BONG of the explicit model attached to the data. -/
noncomputable def goodBONG
    (D : UnaryBinaryJordanData head first second hadmissible) :
    GoodBONG
      (unaryBinaryModelSpace head first second hadmissible)
      (unaryBinaryModelLattice (K := K)) 3 :=
  unaryBinaryModelGoodBONG head first second hadmissible

end UnaryBinaryJordanData

end BONG

/-- The local Jordan and weight-ideal computation for the explicit
unary--binary model in Lemma 9.5(ii).

There is intentionally no default instance.  The three fields are lower-level
invariant calculations: the order profile, the weight order for nonnegative
radius, and the weight order of the reverse dual for negative radius. -/
class Beli2019UnaryBinaryJordanLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [BONGGoodExistenceLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K] : Prop where
  order_profile
    {head first second : Kˣ}
    {hadmissible : BONG.IsBinaryParameterAdmissible (second / first)}
    (D : BONG.UnaryBinaryJordanData head first second hadmissible) :
    ∀ i, D.goodBONG.order i =
      ![D.center + D.radius, D.center - D.radius,
        D.center + D.radius] i
  weight_order_of_radius_nonnegative
    {head first second : Kˣ}
    {hadmissible : BONG.IsBinaryParameterAdmissible (second / first)}
    (D : BONG.UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 ≤ D.radius) :
    Lattice.weightIdealOrder
        (BONG.unaryBinaryModelSpace head first second hadmissible)
        (BONG.unaryBinaryModelLattice (K := K)) =
      D.center + D.radius + D.alpha
  dual_weight_order_of_radius_negative
    {head first second : Kˣ}
    {hadmissible : BONG.IsBinaryParameterAdmissible (second / first)}
    (D : BONG.UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0)
    (c : BONG.GoodBONG
      (BONG.unaryBinaryModelSpace head first second hadmissible)
      (Lattice.dualLattice
        (BONG.unaryBinaryModelSpace head first second hadmissible)
        (BONG.unaryBinaryModelLattice (K := K))) 3)
    (hdual : D.goodBONG.IsReverseDualGoodBONG c) :
    Lattice.weightIdealOrder
        (BONG.unaryBinaryModelSpace head first second hadmissible)
        (Lattice.dualLattice
          (BONG.unaryBinaryModelSpace head first second hadmissible)
          (BONG.unaryBinaryModelLattice (K := K))) =
      -D.center - D.radius + (D.alpha + 2 * D.radius)

namespace BONG.UnaryBinaryJordanData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [BONGStructuralLaws.{u, u} K]
  [Beli2009WeightIdealData.{u, u} K]
  [Beli2019UnaryBinaryJordanLaws.{u} K]
  [Beli2009JordanWeightOrderLaws.{u, u} K]
  [Beli2006AlphaLaws.{u, u} K]
  {head first second : Kˣ}
  {hadmissible : IsBinaryParameterAdmissible (second / first)}

omit [Beli2009JordanWeightOrderLaws.{u, u} K]
  [Beli2006AlphaLaws.{u, u} K] in
/-- The good-BONG order profile computed by the local Jordan interface. -/
theorem goodBONG_order
    (D : UnaryBinaryJordanData head first second hadmissible) (i : Fin 3) :
    D.goodBONG.order i =
      ![D.center + D.radius, D.center - D.radius,
        D.center + D.radius] i :=
  Beli2019UnaryBinaryJordanLaws.order_profile D i

/-- The local Jordan/weight calculation determines the first alpha of the
explicit model.  For nonnegative radius this is Lemma 2.14 directly.  For
negative radius the same calculation is applied to the reverse dual, and
P7 plus Remark 8.7 transports the result back. -/
theorem goodBONG_alpha_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.goodBONG.alphaValue 0 = (D.alpha : ℚ) := by
  let b := D.goodBONG
  by_cases hradius : 0 ≤ D.radius
  · have hdescending : b.order 1 ≤ b.order 0 := by
      rw [show b.order 1 = D.center - D.radius by
          simpa [b] using D.goodBONG_order (1 : Fin 3),
        show b.order 0 = D.center + D.radius by
          simpa [b] using D.goodBONG_order (0 : Fin 3)]
      omega
    have hweight := b.beli2009Lemma214_of_firstBlock_not_unary hdescending
    have hweightOrder :=
      Beli2019UnaryBinaryJordanLaws.weight_order_of_radius_nonnegative
        D hradius
    rw [hweightOrder] at hweight
    have hzero : b.order 0 = D.center + D.radius := by
      simpa [b] using D.goodBONG_order (0 : Fin 3)
    rw [hzero] at hweight
    push_cast at hweight
    linarith
  · have hradiusNegative : D.radius < 0 := by omega
    rcases b.exists_reverseDual_with_alpha with
      ⟨c, hdual, _hvalues, horders, halphas⟩
    have hdescending : c.order 1 ≤ c.order 0 := by
      rw [horders, horders]
      have hrevOne : Fin.rev (1 : Fin 3) = (1 : Fin 3) := by decide
      have hrevZero : Fin.rev (0 : Fin 3) = (2 : Fin 3) := by decide
      rw [hrevOne, hrevZero]
      have hone : b.order 1 = D.center - D.radius := by
        simpa [b] using D.goodBONG_order (1 : Fin 3)
      have htwo : b.order 2 = D.center + D.radius := by
        simpa [b] using D.goodBONG_order (2 : Fin 3)
      rw [hone, htwo]
      omega
    have hweight := c.beli2009Lemma214_of_firstBlock_not_unary hdescending
    have hweightOrder :=
      Beli2019UnaryBinaryJordanLaws.dual_weight_order_of_radius_negative
        D hradiusNegative c hdual
    rw [hweightOrder] at hweight
    have hcZero : c.order 0 = -D.center - D.radius := by
      rw [horders]
      have hrevZero : Fin.rev (0 : Fin 3) = (2 : Fin 3) := by decide
      rw [hrevZero]
      have htwo : b.order 2 = D.center + D.radius := by
        simpa [b] using D.goodBONG_order (2 : Fin 3)
      rw [htwo]
      ring
    rw [hcZero] at hweight
    push_cast at hweight
    have hcAlpha : c.alphaValue 0 =
        ((D.alpha + 2 * D.radius : Int) : ℚ) := by
      push_cast
      linarith
    have hdualAlpha : c.alphaValue 0 = b.alphaValue 1 := by
      have hrevAlpha : Fin.rev (0 : Fin 2) = (1 : Fin 2) := by decide
      simpa [hrevAlpha] using halphas (0 : Fin 2)
    have houter : b.order 0 = b.order 2 := by
      rw [show b.order 0 = D.center + D.radius by
          simpa [b] using D.goodBONG_order (0 : Fin 3),
        show b.order 2 = D.center + D.radius by
          simpa [b] using D.goodBONG_order (2 : Fin 3)]
    have hremark := b.beli2019Remark87 (0 : Fin 1) (by
      change b.order 0 = b.order 2
      exact houter)
    have hrelation := hremark.currentAlpha_eq
    change b.alphaValue 1 =
        ((b.order 0 - b.order 1 : Int) : ℚ) + b.alphaValue 0 at hrelation
    have hzeroOrder : b.order 0 = D.center + D.radius := by
      simpa [b] using D.goodBONG_order (0 : Fin 3)
    have honeOrder : b.order 1 = D.center - D.radius := by
      simpa [b] using D.goodBONG_order (1 : Fin 3)
    rw [← hdualAlpha, hcAlpha, hzeroOrder, honeOrder] at hrelation
    push_cast at hrelation
    linarith

end BONG.UnaryBinaryJordanData

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Integral conclusion of Lemma 9.5(ii) for a normal-form coefficient list
whose ambient quadratic space has already been identified with the source.
The proof computes the target invariants and invokes Lemma 7.11. -/
theorem beli2019Lemma95NormalForm_latticeIsometric
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaSource : Beli2006AlphaLaws.{u, v} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (twist : Kˣ)
    (htwist : IsValuationUnit K (twist : K))
    (hadmissible : IsBinaryParameterAdmissible
      (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 2 /
        a.beli2019Lemma95NormalFormValues A₁ A₂ twist 1))
    (ambient : q.IsIsometric
      (unaryBinaryModelSpace
        (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 0)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 1)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 2)
        hadmissible)) :
    Lattice.IsIsometric q
      (unaryBinaryModelSpace
        (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 0)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 1)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 2)
        hadmissible)
      L (unaryBinaryModelLattice (K := K)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaSource
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hmod := hremark.previous_middle_modEq
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨k, hk⟩
  have hk' : a.order 1 - a.order 0 = 2 * k := by
    change a.order 1 - a.order 0 = 2 * k at hk
    exact hk
  let center : Int := a.order 0 + k
  let radius : Int := -k
  have hcenterRadius : center + radius = a.order 0 := by
    dsimp [center, radius]
    omega
  have hcenterMinusRadius : center - radius = a.order 1 := by
    dsimp [center, radius]
    omega
  have hrelation := a.beli2019Lemma95_alphaInteger_relation
    houter A₁ A₂ hA₁ hA₂
  have hA₂Relation : A₂ = A₁ + 2 * radius := by
    dsimp [radius]
    omega
  have horders := a.beli2019Lemma95NormalFormValues_orders
    A₁ A₂ twist htwist
  have hA₁Nonnegative : 0 ≤ A₁ := by
    have hnonnegative := (a.beli2009Lemma27_i (0 : Fin 2)).1
    rw [hA₁] at hnonnegative
    exact_mod_cast hnonnegative
  have hA₂Nonnegative : 0 ≤ A₂ := by
    have hnonnegative := (a.beli2009Lemma27_i (1 : Fin 2)).1
    rw [hA₂] at hnonnegative
    exact_mod_cast hnonnegative
  have hA₁Bound : A₁ ≤ -radius + (ramificationIndex K : Int) := by
    have hbound := a.alphaValue_le_halfGapValue (0 : Fin 2)
    unfold halfGapValue orderGap at hbound
    rw [hA₁] at hbound
    have hbound' : (A₁ : ℚ) ≤
        (-radius + (ramificationIndex K : Int) : Int) := by
      push_cast
      change (A₁ : ℚ) ≤
        ((a.order 1 - a.order 0 : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) at hbound
      have hkQ : ((a.order 1 - a.order 0 : Int) : ℚ) = 2 * (k : ℚ) := by
        exact_mod_cast hk'
      rw [hkQ] at hbound
      dsimp [radius]
      push_cast at hbound ⊢
      linarith
    exact_mod_cast hbound'
  have hA₁Shape :
      A₁ = -radius + (ramificationIndex K : Int) ∨ Odd A₁ := by
    by_cases heq : A₁ = -radius + (ramificationIndex K : Int)
    · exact Or.inl heq
    · apply Or.inr
      have hnotHalf : a.alphaValue 0 ≠ a.halfGapValue 0 := by
        intro hhalf
        unfold halfGapValue orderGap at hhalf
        rw [hA₁] at hhalf
        have hhalfInt : A₁ = -radius + (ramificationIndex K : Int) := by
          change (A₁ : ℚ) =
            ((a.order 1 - a.order 0 : Int) : ℚ) / 2 +
              (ramificationIndex K : ℚ) at hhalf
          have hkQ : ((a.order 1 - a.order 0 : Int) : ℚ) =
              2 * (k : ℚ) := by
            exact_mod_cast hk'
          rw [hkQ] at hhalf
          have hhalfQ : (A₁ : ℚ) =
              ((-radius + (ramificationIndex K : Int) : Int) : ℚ) := by
            dsimp [radius]
            push_cast at hhalf ⊢
            linarith
          exact_mod_cast hhalfQ
        exact heq hhalfInt
      rcases a.beli2009Lemma27_iv (0 : Fin 2) hnotHalf with
        ⟨z, hzOdd, hz⟩
      have hAz : A₁ = z := by
        have hcast : (A₁ : ℚ) = (z : ℚ) := hA₁.symm.trans hz
        exact_mod_cast hcast
      simpa [hAz] using hzOdd
  let D : UnaryBinaryJordanData
      (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 0)
      (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 1)
      (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 2)
      hadmissible := {
    center := center
    radius := radius
    alpha := A₁
    head_order := by
      simpa [hcenterRadius] using horders (0 : Fin 3)
    first_order := by
      simpa [hcenterRadius] using horders (1 : Fin 3)
    second_order := by
      have h : ordUnit K
          (a.beli2019Lemma95NormalFormValues A₁ A₂ twist 2) =
          a.order 0 - A₂ := by
        simpa using horders (2 : Fin 3)
      rw [h]
      omega
    alpha_nonnegative := hA₁Nonnegative
    dual_alpha_nonnegative := by omega
    alpha_le_halfGap := hA₁Bound
    alpha_half_or_odd := hA₁Shape }
  let b := D.goodBONG
  have hbOrders (i : Fin 3) : b.order i =
      ![center + radius, center - radius, center + radius] i := by
    simpa [b] using D.goodBONG_order i
  have hsameOrders : a.SameOrders b := by
    intro i
    fin_cases i
    · rw [hbOrders]
      simp [hcenterRadius]
    · rw [hbOrders]
      simp [hcenterMinusRadius]
    · rw [hbOrders]
      simp [hcenterRadius, houter]
  have hbAlpha : b.alphaValue 0 = (A₁ : ℚ) := by
    letI : Beli2006AlphaLaws.{u, u} K := alphaModel
    simpa [b] using D.goodBONG_alpha_zero
  exact (a.beli2019Lemma711_of_ambient_isometry
    (alphaV := alphaSource) (alphaW := alphaModel)
    ambient b hsameOrders houter).2 (hA₁.trans hbAlpha.symm)

end BONG.GoodBONG

end Bong
