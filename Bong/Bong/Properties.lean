/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Good
import Mathlib.Tactic.Group

/-!
# Properties A and B for BONGs

This file formalizes the order-theoretic content of Beli (2003), Section 4.
For a BONG value `a_i` of order `R_i`, the normalized value

`ε_i = a_i * π ^ (-R_i)`

is proved to be a valuation unit.  It is then used to state property B exactly
in terms of `d(-ε_i ε_{i+1})`, including the endpoint conventions from
Definition 10.  Property A is the strict two-step order condition appearing in
Corollary 4.2 and Lemma 4.3.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- The valuation-unit factor `ε_i` in `a_i = π^{R_i} ε_i`. -/
noncomputable def normalizedValue (b : BONG V q L n) (i : Fin n) : Kˣ :=
  b.valueUnit i * uniformizerUnit K ^ (-b.order i)

/-- Recovering `a_i` from its order and normalized valuation-unit factor. -/
theorem uniformizer_zpow_mul_normalizedValue (b : BONG V q L n) (i : Fin n) :
    uniformizerUnit K ^ b.order i * b.normalizedValue i = b.valueUnit i := by
  rw [normalizedValue]
  calc
    uniformizerUnit K ^ b.order i *
          (b.valueUnit i * uniformizerUnit K ^ (-b.order i)) =
        b.valueUnit i *
          (uniformizerUnit K ^ b.order i *
            uniformizerUnit K ^ (-b.order i)) := by
      ac_rfl
    _ = b.valueUnit i := by simp

private theorem int_smul_one_withTop (m : Int) :
    m • (1 : WithTop Int) = (m : WithTop Int) := by
  cases m with
  | ofNat k => simp
  | negSucc k =>
      rw [Int.negSucc_eq, neg_zsmul]
      have hcast : (k : Int) + 1 = ((k + 1 : Nat) : Int) := by omega
      rw [hcast, natCast_zsmul]
      simp

/-- The normalized factor `ε_i` has valuation zero. -/
theorem normalizedValue_isValuationUnit (b : BONG V q L n) (i : Fin n) :
    IsValuationUnit K (b.normalizedValue i : K) := by
  rw [IsValuationUnit, normalizedValue, Units.val_mul, ord_mul,
    ord_coe_unit_zpow, coe_valueUnit]
  rw [← coe_order b i, coe_uniformizerUnit, ord_uniformizer]
  rw [int_smul_one_withTop]
  exact_mod_cast add_neg_cancel (b.order i)

/-- Squaring a normalized BONG value does not change a refined unit square class. -/
theorem unitSquareClass_mul_normalizedValue_sq (b : BONG V q L n)
    (i : Fin n) (a : Kˣ) :
    unitSquareClass K (a * b.normalizedValue i ^ 2) = unitSquareClass K a :=
  unitSquareClass_mul_unit_square K a (b.normalizedValue i)
    (b.normalizedValue_isValuationUnit i)

/-- The unit `-ε_i ε_{i+1}` in Beli's property B. -/
noncomputable def normalizedAdjacentProduct (b : BONG V q L (n + 1))
    (i : Fin n) : Kˣ :=
  -(b.normalizedValue i.castSucc * b.normalizedValue i.succ)

/-- The rationally embedded defect `d(-ε_i ε_{i+1})`. -/
noncomputable def normalizedAdjacentDefectOrder (b : BONG V q L (n + 1))
    (i : Fin n) : WithTop ℚ :=
  WithTop.map (fun m : Nat ↦ (m : ℚ))
    (quadraticDefect K (b.normalizedAdjacentProduct i))

/-- Property A in good-BONG coordinates: `R_i < R_{i+2}`. -/
def HasPropertyA (b : BONG V q L n) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 2 < n),
    b.order i < b.order ⟨i.1 + 2, hi⟩

/-- Property A implies that the underlying BONG is good. -/
theorem HasPropertyA.isGood {b : BONG V q L n} (hb : b.HasPropertyA) :
    b.IsGood := by
  intro i hi
  exact (hb i hi).le

/-- Property A is goodness together with strictness at every two-step comparison. -/
theorem hasPropertyA_iff_isGood_and_ne (b : BONG V q L n) :
    b.HasPropertyA ↔
      b.IsGood ∧
        ∀ (i : Fin n) (hi : i.1 + 2 < n),
          b.order i ≠ b.order ⟨i.1 + 2, hi⟩ := by
  constructor
  · intro hb
    exact ⟨hb.isGood, fun i hi ↦ ne_of_lt (hb i hi)⟩
  · rintro ⟨hgood, hne⟩ i hi
    exact lt_of_le_of_ne (hgood i hi) (hne i hi)

/-- Every BONG of length at most two satisfies property A. -/
theorem hasPropertyA_of_length_le_two (b : BONG V q L n) (hn : n ≤ 2) :
    b.HasPropertyA := by
  intro i hi
  omega

/-- Removing the first entry preserves property A. -/
theorem HasPropertyA.tail {b : BONG V q L (n + 1)} (hb : b.HasPropertyA) :
    b.tail.HasPropertyA := by
  intro i hi
  have hi' : i.succ.1 + 2 < n + 1 := by
    simp only [Fin.val_succ]
    omega
  have h := hb i.succ hi'
  have hind :
      (⟨i.1 + 2, hi⟩ : Fin n).succ =
        (⟨i.succ.1 + 2, hi'⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  rw [order_tail, order_tail, hind]
  exact h

/-- The exceptional adjacent-pair condition in Definition 10 of Beli (2003). -/
noncomputable def propertyBTrigger (b : BONG V q L (n + 1))
    (i : Fin n) : Prop :=
  let gap : Int := b.order i.succ - b.order i.castSucc
  (gap ≤ 2 * (ramificationIndex K : Int) + 1 ∧ Odd gap) ∨
    (Even gap ∧
      b.normalizedAdjacentDefectOrder i ≤
        ((((ramificationIndex K : ℚ) - (gap : ℚ) / 2) : ℚ) : WithTop ℚ))

/-!
The quantified neighboring indices encode Beli's endpoint convention without
artificial default values: at the left or right endpoint there is no index
satisfying the displayed adjacency equation, so that side is vacuous.
-/

/-- Property B with respect to the specified BONG, as in Definition 10. -/
noncomputable def HasPropertyB (b : BONG V q L (n + 1)) : Prop :=
  b.HasPropertyA ∧
    ∀ i : Fin n, b.propertyBTrigger i →
      (∀ j : Fin (n + 1), j.1 + 1 = i.1 →
        2 * (ramificationIndex K : Int) + 1 ≤
          b.order i.castSucc - b.order j) ∧
      (∀ k : Fin (n + 1), i.1 + 2 = k.1 →
        2 * (ramificationIndex K : Int) + 1 ≤
          b.order k - b.order i.succ)

/-- Property B includes property A. -/
theorem HasPropertyB.hasPropertyA {b : BONG V q L (n + 1)}
    (hb : b.HasPropertyB) : b.HasPropertyA :=
  hb.1

/-- A BONG satisfying property B is good. -/
theorem HasPropertyB.isGood {b : BONG V q L (n + 1)}
    (hb : b.HasPropertyB) : b.IsGood :=
  hb.hasPropertyA.isGood

end BONG

end Bong
