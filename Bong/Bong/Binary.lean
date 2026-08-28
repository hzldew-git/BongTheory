/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Basic
import Bong.Dyadic.UnitSquareClass

/-!
# Binary BONG data

For a binary BONG with values `a₁, a₂`, Beli's scale-invariant binary parameter
is represented by `a₂ / a₁`; its order is `R₂ - R₁`.  The sign of this order
distinguishes improper modular, proper modular, and nonmodular binary lattices.

We retain the actual field unit, Beli's refined class modulo squares of
valuation units, and its image in the ordinary field square-class group.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- Beli's binary parameter, represented by `a₂ / a₁`. -/
noncomputable def binaryParameter (b : BONG V q L 2) : Kˣ :=
  b.valueUnit 1 / b.valueUnit 0

@[simp]
theorem coe_binaryParameter (b : BONG V q L 2) :
    (b.binaryParameter : K) = b.value 1 / b.value 0 := by
  simp [binaryParameter]

/-- The field square class of the binary parameter. -/
noncomputable def binarySquareClass (b : BONG V q L 2) : SquareClass K :=
  squareClass K b.binaryParameter

/-- Beli's binary parameter modulo squares of valuation units. -/
noncomputable def binaryUnitSquareClass (b : BONG V q L 2) : UnitSquareClass K :=
  unitSquareClass K b.binaryParameter

@[simp]
theorem binaryUnitSquareClass_toSquareClass (b : BONG V q L 2) :
    unitSquareClassToSquareClass K b.binaryUnitSquareClass = b.binarySquareClass :=
  rfl

/-- The order `R = R₂ - R₁` of the binary parameter. -/
noncomputable def binaryOrderGap (b : BONG V q L 2) : Int :=
  b.order 1 - b.order 0

/-- The valuation of the represented binary parameter. -/
noncomputable def binaryParameterOrder (b : BONG V q L 2) : Int :=
  (ord K (b.binaryParameter : K)).untop
    ((ord_eq_top_iff K).not.mpr (Units.ne_zero b.binaryParameter))

/-- The parameter `a₂ / a₁` has order `R₂ - R₁`. -/
theorem binaryParameterOrder_eq_orderGap (b : BONG V q L 2) :
    b.binaryParameterOrder = b.binaryOrderGap := by
  apply WithTop.coe_injective
  rw [binaryParameterOrder, binaryOrderGap, WithTop.coe_untop]
  rw [coe_binaryParameter, div_eq_mul_inv, ord_mul, AddValuation.map_inv]
  rw [← coe_order b 1, ← coe_order b 0]
  simp [sub_eq_add_neg]

/-- A binary BONG is of improper-modular order type when `R < 0`. -/
def IsImproperModular (b : BONG V q L 2) : Prop :=
  b.binaryOrderGap < 0

/-- A binary BONG is of proper-modular order type when `R = 0`. -/
def IsProperModular (b : BONG V q L 2) : Prop :=
  b.binaryOrderGap = 0

/-- A binary BONG is of nonmodular order type when `0 < R`. -/
def IsNonmodular (b : BONG V q L 2) : Prop :=
  0 < b.binaryOrderGap

/-- The three binary order types are exhaustive. -/
theorem binary_order_type_trichotomy (b : BONG V q L 2) :
    b.IsImproperModular ∨ b.IsProperModular ∨ b.IsNonmodular := by
  rcases lt_trichotomy b.binaryOrderGap 0 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem IsImproperModular.not_isProperModular {b : BONG V q L 2}
    (h : b.IsImproperModular) : ¬b.IsProperModular :=
  ne_of_lt h

theorem IsProperModular.not_isNonmodular {b : BONG V q L 2}
    (h : b.IsProperModular) : ¬b.IsNonmodular := by
  rw [IsNonmodular, h]
  exact lt_irrefl 0

theorem IsImproperModular.not_isNonmodular {b : BONG V q L 2}
    (h : b.IsImproperModular) : ¬b.IsNonmodular :=
  not_lt_of_ge h.le

end BONG

end Bong
