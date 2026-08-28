/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaBounds

/-!
# Beli (2006), properties P4--P6

P4 follows because every defect candidate is bounded below by the current
order gap.  P5 is then the elementary comparison with the dyadic endpoint
`2e`.  P6 follows by adding the two half-gap upper bounds when the two outer
orders agree.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- The finite alpha value is bounded by its half-gap candidate. -/
theorem alphaValue_le_halfGapValue_for_properties
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.alphaValue i ≤ b.halfGapValue i := by
  have hle := b.alpha_le_halfGapCandidate i
  rw [← b.coe_alphaValue, ← b.coe_halfGapValue] at hle
  exact_mod_cast hle

/-- When the gap is at most `2e`, the current gap is a lower bound for the
entire finite candidate set.  This is the inequality part of P3. -/
theorem orderGap_le_alphaValue_of_le_twoE
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : b.orderGap i ≤ 2 * (ramificationIndex K : Int)) :
    (b.orderGap i : ℚ) ≤ b.alphaValue i := by
  have hhalf :
      (((b.orderGap i : Int) : ℚ) : WithTop ℚ) ≤
        b.halfGapCandidate i := by
    change (((b.orderGap i : Int) : ℚ) : WithTop ℚ) ≤
      ((((b.orderGap i : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
    norm_cast
    rw [Rat.divInt_eq_div]
    push_cast
    have hgapQ : (b.orderGap i : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hgap
    linarith
  have halpha :
      (((b.orderGap i : Int) : ℚ) : WithTop ℚ) ≤ b.alpha i := by
    apply Finset.le_min' _ _ _
    intro x hx
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with hhalfEq | hleft | hright
    · rw [hhalfEq]
      exact hhalf
    · rcases hleft with ⟨j, hji, hj⟩
      rw [← hj]
      exact b.orderGapTop_le_leftDefectCandidate i j hji
    · rcases hright with ⟨j, hij, hj⟩
      rw [← hj]
      exact b.orderGapTop_le_rightDefectCandidate i j hij
  rw [← b.coe_alphaValue] at halpha
  exact_mod_cast halpha

/-- Above `2e`, the half-gap candidate lies below the current order gap. -/
theorem halfGapCandidate_le_orderGapTop_of_twoE_le
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap i) :
    b.halfGapCandidate i ≤
      (((b.orderGap i : Int) : ℚ) : WithTop ℚ) := by
  change ((((b.orderGap i : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
    (((b.orderGap i : Int) : ℚ) : WithTop ℚ)
  norm_cast
  rw [Rat.divInt_eq_div]
  push_cast
  have hgapQ : 2 * (ramificationIndex K : ℚ) ≤
      (b.orderGap i : ℚ) := by
    exact_mod_cast hgap
  linarith

/-- Beli (2006), property P4, proved from the finite candidate definition. -/
theorem satisfiesAlphaP4_proved (b : GoodBONG q L (n + 1)) :
    b.SatisfiesAlphaP4 := by
  intro i hgap
  apply WithTop.coe_injective
  rw [b.coe_alphaValue, b.coe_halfGapValue]
  apply le_antisymm (b.alpha_le_halfGapCandidate i)
  apply Finset.le_min' _ _ _
  intro x hx
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rcases hx with hhalfEq | hleft | hright
  · rw [hhalfEq]
  · rcases hleft with ⟨j, hji, hj⟩
    rw [← hj]
    exact (b.halfGapCandidate_le_orderGapTop_of_twoE_le i hgap).trans
      (b.orderGapTop_le_leftDefectCandidate i j hji)
  · rcases hright with ⟨j, hij, hj⟩
    rw [← hj]
    exact (b.halfGapCandidate_le_orderGapTop_of_twoE_le i hgap).trans
      (b.orderGapTop_le_rightDefectCandidate i j hij)

/-- The half-gap value is below `2e` exactly when the order gap is. -/
theorem halfGapValue_lt_twoE_iff
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.halfGapValue i < 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i < 2 * (ramificationIndex K : Int) := by
  unfold halfGapValue
  push_cast
  constructor
  · intro h
    have hq : (b.orderGap i : ℚ) <
        2 * (ramificationIndex K : ℚ) := by linarith
    exact_mod_cast hq
  · intro h
    have hq : (b.orderGap i : ℚ) <
        2 * (ramificationIndex K : ℚ) := by exact_mod_cast h
    linarith

/-- The half-gap value equals `2e` exactly at order gap `2e`. -/
theorem halfGapValue_eq_twoE_iff
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.halfGapValue i = 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i = 2 * (ramificationIndex K : Int) := by
  unfold halfGapValue
  push_cast
  constructor
  · intro h
    have hq : (b.orderGap i : ℚ) =
        2 * (ramificationIndex K : ℚ) := by linarith
    exact_mod_cast hq
  · intro h
    have hq : (b.orderGap i : ℚ) =
        2 * (ramificationIndex K : ℚ) := by exact_mod_cast h
    linarith

/-- The half-gap value is above `2e` exactly when the order gap is. -/
theorem twoE_lt_halfGapValue_iff
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    2 * (ramificationIndex K : ℚ) < b.halfGapValue i ↔
      2 * (ramificationIndex K : Int) < b.orderGap i := by
  unfold halfGapValue
  push_cast
  constructor
  · intro h
    have hq : 2 * (ramificationIndex K : ℚ) <
        (b.orderGap i : ℚ) := by linarith
    exact_mod_cast hq
  · intro h
    have hq : 2 * (ramificationIndex K : ℚ) <
        (b.orderGap i : ℚ) := by exact_mod_cast h
    linarith

/-- Beli (2006), property P5, as a consequence of P4. -/
theorem satisfiesAlphaP5_proved (b : GoodBONG q L (n + 1)) :
    b.SatisfiesAlphaP5 := by
  intro i
  have hupper := b.alphaValue_le_halfGapValue_for_properties i
  have hlt :
      b.alphaValue i < 2 * (ramificationIndex K : ℚ) ↔
        b.orderGap i < 2 * (ramificationIndex K : Int) := by
    constructor
    · intro halpha
      by_contra hnot
      have hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap i :=
        le_of_not_gt hnot
      have hp4 := b.satisfiesAlphaP4_proved i hgap
      have hhalf : 2 * (ramificationIndex K : ℚ) ≤
          b.halfGapValue i := by
        exact (not_lt.mp (mt (b.halfGapValue_lt_twoE_iff i).mp hnot))
      rw [hp4] at halpha
      exact (not_lt_of_ge hhalf) halpha
    · intro hgap
      exact hupper.trans_lt ((b.halfGapValue_lt_twoE_iff i).2 hgap)
  have heq :
      b.alphaValue i = 2 * (ramificationIndex K : ℚ) ↔
        b.orderGap i = 2 * (ramificationIndex K : Int) := by
    constructor
    · intro halpha
      have hhalfGe : 2 * (ramificationIndex K : ℚ) ≤
          b.halfGapValue i := by simpa [halpha] using hupper
      have hgapGe : 2 * (ramificationIndex K : Int) ≤
          b.orderGap i := by
        by_contra hnot
        have hgapLt : b.orderGap i <
            2 * (ramificationIndex K : Int) := lt_of_not_ge hnot
        have hhalfLt := (b.halfGapValue_lt_twoE_iff i).2 hgapLt
        exact (not_lt_of_ge hhalfGe) hhalfLt
      have hp4 := b.satisfiesAlphaP4_proved i hgapGe
      have hhalfEq : b.halfGapValue i =
          2 * (ramificationIndex K : ℚ) := hp4.symm.trans halpha
      exact (b.halfGapValue_eq_twoE_iff i).1 hhalfEq
    · intro hgap
      have hp4 := b.satisfiesAlphaP4_proved i hgap.ge
      exact hp4.trans ((b.halfGapValue_eq_twoE_iff i).2 hgap)
  have hgt :
      2 * (ramificationIndex K : ℚ) < b.alphaValue i ↔
        2 * (ramificationIndex K : Int) < b.orderGap i := by
    constructor
    · intro halpha
      have hhalf := halpha.trans_le hupper
      exact (b.twoE_lt_halfGapValue_iff i).1 hhalf
    · intro hgap
      have hp4 := b.satisfiesAlphaP4_proved i hgap.le
      rw [hp4]
      exact (b.twoE_lt_halfGapValue_iff i).2 hgap
  exact ⟨hlt, heq, hgt⟩

/-- The two neighboring half-gap values add to `2e` when the outer orders
agree. -/
theorem halfGapValue_add_next_eq_twoE_of_outer_orders_eq
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hi : i.val + 1 < n)
    (houter : b.order i.castSucc =
      b.order (⟨i.val + 1, hi⟩ : Fin n).succ) :
    b.halfGapValue i + b.halfGapValue ⟨i.val + 1, hi⟩ =
      2 * (ramificationIndex K : ℚ) := by
  let next : Fin n := ⟨i.val + 1, hi⟩
  have hmiddle : next.castSucc = i.succ := by
    apply Fin.ext
    rfl
  unfold halfGapValue orderGap
  rw [hmiddle, houter]
  push_cast
  ring

/-- Beli (2006), property P6. -/
theorem satisfiesAlphaP6_proved (b : GoodBONG q L (n + 1)) :
    b.SatisfiesAlphaP6 := by
  intro i hi houter
  let next : Fin n := ⟨i.val + 1, hi⟩
  have hleft := b.alphaValue_le_halfGapValue_for_properties i
  have hright := b.alphaValue_le_halfGapValue_for_properties next
  calc
    b.alphaValue i + b.alphaValue next ≤
        b.halfGapValue i + b.halfGapValue next := add_le_add hleft hright
    _ = 2 * (ramificationIndex K : ℚ) :=
      b.halfGapValue_add_next_eq_twoE_of_outer_orders_eq i hi houter

end BONG.GoodBONG

end Bong
