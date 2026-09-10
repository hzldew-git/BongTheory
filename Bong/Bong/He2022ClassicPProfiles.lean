/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma29

/-!
# He (2024), Sections 7.5--7.10: the auxiliary `P` lattices

This file realizes the two literal coefficient rows introduced immediately
after Lemma 7.4 of the published paper.  For paper target rank `n = 2r+2`,
the auxiliary source rank is `n+2 = 2r+4` and the displayed rows are

* `P₁^(n+2)(c) = H₀^r ⊥ ⟨1,-c,-1,c⟩`;
* `P₂^(n+2)(c) = H₀^r ⊥ ⟨1,-c,-c# ,c*c#⟩`.

The sharp parameter is explicit, just as it is for the `C₂` rows.  This is
essential for the two uses in Lemma 7.10: `ord(c#)=0` for `c=omega`, whereas
the displayed choice for `c=Delta` is a uniformizer and has order one.
-/

namespace Bong

open Dyadic BONG.GoodBONG AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem heClassicP_ordUnit_one : ordUnit K (1 : Kˣ) = 0 := by
  have h := ordUnit_mul K (1 : Kˣ) 1
  simp only [mul_one] at h
  omega

private noncomputable def heClassicEvenP1Tail (c : Kˣ) : Fin 2 → Kˣ :=
  fun i => if i = 0 then -1 else c

private noncomputable def heClassicEvenP2Tail
    (c cSharp : Kˣ) : Fin 2 → Kˣ :=
  fun i => if i = 0 then -cSharp else c * cSharp

@[simp]
private theorem heClassicEvenP1Tail_zero (c : Kˣ) :
    heClassicEvenP1Tail c 0 = -1 := by
  simp [heClassicEvenP1Tail]

@[simp]
private theorem heClassicEvenP1Tail_one (c : Kˣ) :
    heClassicEvenP1Tail c 1 = c := by
  simp [heClassicEvenP1Tail]

@[simp]
private theorem heClassicEvenP2Tail_zero (c cSharp : Kˣ) :
    heClassicEvenP2Tail c cSharp 0 = -cSharp := by
  simp [heClassicEvenP2Tail]

@[simp]
private theorem heClassicEvenP2Tail_one (c cSharp : Kˣ) :
    heClassicEvenP2Tail c cSharp 1 = c * cSharp := by
  simp [heClassicEvenP2Tail]

/-- The literal coefficient row `P₁^(2*pairs+4)(c)`. -/
noncomputable def heClassicEvenP1 (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 4) → Kˣ :=
  Fin.append (m := 2 * pairs + 2) (n := 2)
    (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenP1Tail c)

/-- The literal coefficient row `P₂^(2*pairs+4)(c)`. -/
noncomputable def heClassicEvenP2 (pairs : Nat) (c cSharp : Kˣ) :
    Fin (2 * pairs + 4) → Kˣ :=
  Fin.append (m := 2 * pairs + 2) (n := 2)
    (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenP2Tail c cSharp)

@[simp]
theorem heClassicEvenP1_prefix (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * pairs + 2)) :
    heClassicEvenP1 (K := K) pairs c (Fin.castAdd 2 i) =
      heClassicEvenC1 (K := K) pairs c i := by
  rw [heClassicEvenP1, Fin.append_left]

@[simp]
theorem heClassicEvenP1_tail (pairs : Nat) (c : Kˣ) (i : Fin 2) :
    heClassicEvenP1 (K := K) pairs c
        (Fin.natAdd (2 * pairs + 2) i) = heClassicEvenP1Tail c i := by
  rw [heClassicEvenP1, Fin.append_right]

@[simp]
theorem heClassicEvenP2_prefix (pairs : Nat) (c cSharp : Kˣ)
    (i : Fin (2 * pairs + 2)) :
    heClassicEvenP2 (K := K) pairs c cSharp (Fin.castAdd 2 i) =
      heClassicEvenC1 (K := K) pairs c i := by
  rw [heClassicEvenP2, Fin.append_left]

@[simp]
theorem heClassicEvenP2_tail (pairs : Nat) (c cSharp : Kˣ)
    (i : Fin 2) :
    heClassicEvenP2 (K := K) pairs c cSharp
        (Fin.natAdd (2 * pairs + 2) i) =
      heClassicEvenP2Tail c cSharp i := by
  rw [heClassicEvenP2, Fin.append_right]

@[simp]
theorem heClassicEvenP1_tail_zero_value (pairs : Nat) (c : Kˣ) :
    heClassicEvenP1 (K := K) pairs c
        (Fin.natAdd (2 * pairs + 2) (0 : Fin 2)) = -1 := by
  rw [heClassicEvenP1_tail]
  simp

@[simp]
theorem heClassicEvenP1_tail_one_value (pairs : Nat) (c : Kˣ) :
    heClassicEvenP1 (K := K) pairs c
        (Fin.natAdd (2 * pairs + 2) (1 : Fin 2)) = c := by
  rw [heClassicEvenP1_tail]
  simp

@[simp]
theorem heClassicEvenP2_tail_zero_value
    (pairs : Nat) (c cSharp : Kˣ) :
    heClassicEvenP2 (K := K) pairs c cSharp
        (Fin.natAdd (2 * pairs + 2) (0 : Fin 2)) = -cSharp := by
  rw [heClassicEvenP2_tail]
  simp

@[simp]
theorem heClassicEvenP2_tail_one_value
    (pairs : Nat) (c cSharp : Kˣ) :
    heClassicEvenP2 (K := K) pairs c cSharp
        (Fin.natAdd (2 * pairs + 2) (1 : Fin 2)) = c * cSharp := by
  rw [heClassicEvenP2_tail]
  simp

/-- If `c` is a unit, every coefficient in `P₁` has order zero. -/
theorem heClassicEvenP1_order_zero (pairs : Nat) (c : Kˣ)
    (hc : ordUnit K c = 0) (i : Fin (2 * pairs + 4)) :
    ordUnit K (heClassicEvenP1 (K := K) pairs c i) = 0 := by
  by_cases hprefix : i.val < 2 * pairs + 2
  · let j : Fin (2 * pairs + 2) := ⟨i.val, hprefix⟩
    have hi : i = Fin.castAdd 2 j := Fin.ext rfl
    rw [hi, heClassicEvenP1_prefix, heClassicEvenC1_order]
    simp [hc, j]
  · have htail : i.val = 2 * pairs + 2 ∨
        i.val = 2 * pairs + 3 := by omega
    rcases htail with hzero | hone
    · have hi : i = Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := by
        apply Fin.ext
        simpa using hzero
      rw [hi, heClassicEvenP1_tail]
      simp [heClassicP_ordUnit_one]
    · have hi : i = Fin.natAdd (2 * pairs + 2) (1 : Fin 2) := by
        apply Fin.ext
        simpa using hone
      rw [hi, heClassicEvenP1_tail]
      simpa using hc

/-- The first `2*pairs+2` orders of `P₂` vanish, and its two sharp
coefficients both have order `ord(cSharp)`. -/
theorem heClassicEvenP2_order (pairs : Nat) (c cSharp : Kˣ)
    (hc : ordUnit K c = 0) (i : Fin (2 * pairs + 4)) :
    ordUnit K (heClassicEvenP2 (K := K) pairs c cSharp i) =
      if i.val < 2 * pairs + 2 then 0 else ordUnit K cSharp := by
  by_cases hprefix : i.val < 2 * pairs + 2
  · let j : Fin (2 * pairs + 2) := ⟨i.val, hprefix⟩
    have hi : i = Fin.castAdd 2 j := Fin.ext rfl
    rw [hi, heClassicEvenP2_prefix, heClassicEvenC1_order]
    simp [hc, j, hprefix]
  · have htail : i.val = 2 * pairs + 2 ∨
        i.val = 2 * pairs + 3 := by omega
    rcases htail with hzero | hone
    · have hi : i = Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := by
        apply Fin.ext
        simpa using hzero
      rw [hi, heClassicEvenP2_tail]
      simp [hprefix]
    · have hi : i = Fin.natAdd (2 * pairs + 2) (1 : Fin 2) := by
        apply Fin.ext
        simpa using hone
      rw [hi, heClassicEvenP2_tail]
      rw [heClassicEvenP2Tail_one]
      rw [ordUnit_mul, hc]
      simp [hprefix]

/-- In particular, the `omega` instance of `P₂` has the all-zero order
profile in Lemma 7.6(ii). -/
theorem heClassicEvenP2_order_zero (pairs : Nat) (c cSharp : Kˣ)
    (hc : ordUnit K c = 0) (hcSharp : ordUnit K cSharp = 0)
    (i : Fin (2 * pairs + 4)) :
    ordUnit K (heClassicEvenP2 (K := K) pairs c cSharp i) = 0 := by
  rw [heClassicEvenP2_order pairs c cSharp hc, hcSharp]
  split <;> rfl

private theorem heClassicEvenP1_boundaryRatio
    (pairs : Nat) (c : Kˣ) :
    heClassicEvenP1 (K := K) pairs c
          ⟨2 * pairs + 2, by omega⟩ /
        heClassicEvenP1 (K := K) pairs c
          ⟨2 * pairs + 1, by omega⟩ = c⁻¹ := by
  have hleft :
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.castAdd 2 (⟨2 * pairs + 1, by omega⟩ :
          Fin (2 * pairs + 2)) := Fin.ext rfl
  have hright :
      (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := Fin.ext rfl
  rw [hleft, hright, heClassicEvenP1_prefix, heClassicEvenP1_tail]
  have hlast := heClassicEvenC1_tail (K := K) pairs c (1 : Fin 2)
  rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      Fin.natAdd (2 * pairs) (1 : Fin 2) by exact Fin.ext rfl,
    hlast]
  apply Units.ext
  simp only [heClassicEvenP1Tail_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero, Units.val_div_eq_div_val, Units.val_neg, Units.val_one,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero c]

private theorem heClassicEvenP2_boundaryRatio
    (pairs : Nat) (c cSharp : Kˣ) :
    heClassicEvenP2 (K := K) pairs c cSharp
          ⟨2 * pairs + 2, by omega⟩ /
        heClassicEvenP2 (K := K) pairs c cSharp
          ⟨2 * pairs + 1, by omega⟩ = cSharp / c := by
  have hleft :
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.castAdd 2 (⟨2 * pairs + 1, by omega⟩ :
          Fin (2 * pairs + 2)) := Fin.ext rfl
  have hright :
      (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := Fin.ext rfl
  rw [hleft, hright, heClassicEvenP2_prefix, heClassicEvenP2_tail]
  rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      Fin.natAdd (2 * pairs) (1 : Fin 2) by exact Fin.ext rfl,
    heClassicEvenC1_tail]
  apply Units.ext
  simp only [heClassicEvenP2Tail_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero, Units.val_div_eq_div_val, Units.val_neg]
  field_simp [Units.ne_zero c]

private theorem heClassicEvenP1_lastRatio
    (pairs : Nat) (c : Kˣ) :
    heClassicEvenP1 (K := K) pairs c
          ⟨2 * pairs + 3, by omega⟩ /
        heClassicEvenP1 (K := K) pairs c
          ⟨2 * pairs + 2, by omega⟩ = -c := by
  have hzero :
      (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := Fin.ext rfl
  have hone :
      (⟨2 * pairs + 3, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.natAdd (2 * pairs + 2) (1 : Fin 2) := Fin.ext rfl
  rw [hzero, hone, heClassicEvenP1_tail, heClassicEvenP1_tail]
  apply Units.ext
  simp only [heClassicEvenP1Tail_one, heClassicEvenP1Tail_zero,
    Units.val_div_eq_div_val, Units.val_neg, Units.val_one]
  field_simp

private theorem heClassicEvenP2_lastRatio
    (pairs : Nat) (c cSharp : Kˣ) :
    heClassicEvenP2 (K := K) pairs c cSharp
          ⟨2 * pairs + 3, by omega⟩ /
        heClassicEvenP2 (K := K) pairs c cSharp
          ⟨2 * pairs + 2, by omega⟩ = -c := by
  have hzero :
      (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := Fin.ext rfl
  have hone :
      (⟨2 * pairs + 3, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.natAdd (2 * pairs + 2) (1 : Fin 2) := Fin.ext rfl
  rw [hzero, hone, heClassicEvenP2_tail, heClassicEvenP2_tail]
  apply Units.ext
  simp only [heClassicEvenP2Tail_one, heClassicEvenP2Tail_zero,
    Units.val_div_eq_div_val, Units.val_neg, Units.val_mul]
  field_simp [Units.ne_zero cSharp]

/-- Every adjacent binary row in `P₁(c)` is admissible when `c` is a unit. -/
theorem heClassicEvenP1_adjacentAdmissible
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicEvenP1 (K := K) pairs c) := by
  intro i hi
  by_cases hprefix : i.val + 1 < 2 * pairs + 2
  · let j : Fin (2 * pairs + 2) := ⟨i.val, by omega⟩
    let k : Fin (2 * pairs + 2) := ⟨i.val + 1, hprefix⟩
    have hiCast : i = Fin.castAdd 2 j := Fin.ext rfl
    have hnextCast : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 4)) =
        Fin.castAdd 2 k := Fin.ext rfl
    have hcurrentValue : heClassicEvenP1 (K := K) pairs c i =
        heClassicEvenC1 (K := K) pairs c j := by
      rw [hiCast, heClassicEvenP1_prefix]
    have hnextValue : heClassicEvenP1 (K := K) pairs c
          ⟨i.val + 1, hi⟩ =
        heClassicEvenC1 (K := K) pairs c k := by
      rw [hnextCast, heClassicEvenP1_prefix]
    rw [hcurrentValue, hnextValue]
    have h := heClassicEvenC1_adjacentAdmissible
      (K := K) pairs c (by omega) j (by simpa [j] using hprefix)
    have hk : (⟨j.val + 1, by simpa [j] using hprefix⟩ :
        Fin (2 * pairs + 2)) = k := Fin.ext rfl
    rw [hk] at h
    exact h
  · have hcases : i.val = 2 * pairs + 1 ∨
        i.val = 2 * pairs + 2 := by omega
    rcases hcases with hboundary | hlast
    · have hiEq : i = ⟨2 * pairs + 1, by omega⟩ := Fin.ext hboundary
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 4)) =
          ⟨2 * pairs + 2, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      have hcurrentValue := congrArg
        (heClassicEvenP1 (K := K) pairs c) hiEq
      have hnextValue := congrArg
        (heClassicEvenP1 (K := K) pairs c) hnextEq
      rw [hcurrentValue, hnextValue, heClassicEvenP1_boundaryRatio]
      have hinv : ordUnit K c⁻¹ = 0 := by rw [ordUnit_inv, hc]; omega
      have hrewrite : c⁻¹ = -(-c⁻¹) := by simp
      rw [hrewrite]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        (-c⁻¹) (by rw [ordUnit_neg, hinv])
    · have hiEq : i = ⟨2 * pairs + 2, by omega⟩ := Fin.ext hlast
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 4)) =
          ⟨2 * pairs + 3, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      have hcurrentValue := congrArg
        (heClassicEvenP1 (K := K) pairs c) hiEq
      have hnextValue := congrArg
        (heClassicEvenP1 (K := K) pairs c) hnextEq
      rw [hcurrentValue, hnextValue, heClassicEvenP1_lastRatio]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg c
        (by omega)

/-- Every adjacent binary row in `P₂(c)` is admissible when `c` is a unit
and the selected sharp parameter has nonnegative order. -/
theorem heClassicEvenP2_adjacentAdmissible
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : 0 ≤ ordUnit K cSharp) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicEvenP2 (K := K) pairs c cSharp) := by
  intro i hi
  by_cases hprefix : i.val + 1 < 2 * pairs + 2
  · let j : Fin (2 * pairs + 2) := ⟨i.val, by omega⟩
    let k : Fin (2 * pairs + 2) := ⟨i.val + 1, hprefix⟩
    have hiCast : i = Fin.castAdd 2 j := Fin.ext rfl
    have hnextCast : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 4)) =
        Fin.castAdd 2 k := Fin.ext rfl
    have hcurrentValue : heClassicEvenP2 (K := K) pairs c cSharp i =
        heClassicEvenC1 (K := K) pairs c j := by
      rw [hiCast, heClassicEvenP2_prefix]
    have hnextValue : heClassicEvenP2 (K := K) pairs c cSharp
          ⟨i.val + 1, hi⟩ =
        heClassicEvenC1 (K := K) pairs c k := by
      rw [hnextCast, heClassicEvenP2_prefix]
    rw [hcurrentValue, hnextValue]
    have h := heClassicEvenC1_adjacentAdmissible
      (K := K) pairs c (by omega) j (by simpa [j] using hprefix)
    have hk : (⟨j.val + 1, by simpa [j] using hprefix⟩ :
        Fin (2 * pairs + 2)) = k := Fin.ext rfl
    rw [hk] at h
    exact h
  · have hcases : i.val = 2 * pairs + 1 ∨
        i.val = 2 * pairs + 2 := by omega
    rcases hcases with hboundary | hlast
    · have hiEq : i = ⟨2 * pairs + 1, by omega⟩ := Fin.ext hboundary
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 4)) =
          ⟨2 * pairs + 2, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      have hcurrentValue := congrArg
        (heClassicEvenP2 (K := K) pairs c cSharp) hiEq
      have hnextValue := congrArg
        (heClassicEvenP2 (K := K) pairs c cSharp) hnextEq
      rw [hcurrentValue, hnextValue, heClassicEvenP2_boundaryRatio]
      let x : Kˣ := -(cSharp / c)
      have hx : 0 ≤ ordUnit K x := by
        dsimp only [x]
        rw [ordUnit_neg, div_eq_mul_inv, ordUnit_mul, ordUnit_inv, hc]
        simpa using hcSharp
      have hrewrite : cSharp / c = -x := by simp [x]
      rw [hrewrite]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg x hx
    · have hiEq : i = ⟨2 * pairs + 2, by omega⟩ := Fin.ext hlast
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 4)) =
          ⟨2 * pairs + 3, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      have hcurrentValue := congrArg
        (heClassicEvenP2 (K := K) pairs c cSharp) hiEq
      have hnextValue := congrArg
        (heClassicEvenP2 (K := K) pairs c cSharp) hnextEq
      rw [hcurrentValue, hnextValue, heClassicEvenP2_lastRatio]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg c
        (by omega)

/-- Both parity chains in the unit `P₁` row are constant. -/
theorem heClassicEvenP1_weakTwoStep
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicEvenP1 (K := K) pairs c) := by
  intro i hi
  rw [heClassicEvenP1_order_zero pairs c hc,
    heClassicEvenP1_order_zero pairs c hc]

/-- Both parity chains in `P₂` are weakly increasing when the sharp
parameter has nonnegative order. -/
theorem heClassicEvenP2_weakTwoStep
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : 0 ≤ ordUnit K cSharp) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicEvenP2 (K := K) pairs c cSharp) := by
  intro i hi
  rw [heClassicEvenP2_order pairs c cSharp hc,
    heClassicEvenP2_order pairs c cSharp hc]
  have hcurrent : i.val < 2 * pairs + 2 := by omega
  rw [if_pos hcurrent]
  split
  · exact le_rfl
  · exact hcSharp

/-- Exact good BONG on the literal `P₁` coefficient row. -/
noncomputable def heClassicEvenP1GoodBONG
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :=
  heHuExactGoodBONG (heClassicEvenP1 (K := K) pairs c)
    (heClassicEvenP1_adjacentAdmissible pairs c hc)
    (heClassicEvenP1_weakTwoStep pairs c hc)

/-- Exact good BONG on the literal `P₂` coefficient row. -/
noncomputable def heClassicEvenP2GoodBONG
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : 0 ≤ ordUnit K cSharp) :=
  heHuExactGoodBONG (heClassicEvenP2 (K := K) pairs c cSharp)
    (heClassicEvenP2_adjacentAdmissible pairs c cSharp hc hcSharp)
    (heClassicEvenP2_weakTwoStep pairs c cSharp hc hcSharp)

/-- Each literal `P₁` model is classic integral. -/
theorem heClassicEvenP1_isClassicIntegral
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :
    let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace (heClassicEvenP1 (K := K) pairs c))
      (heHuExactRealization (heClassicEvenP1 (K := K) pairs c)
        (heClassicEvenP1_adjacentAdmissible pairs c hc)
        (heClassicEvenP1_weakTwoStep pairs c hc)).lattice := by
  dsimp only
  let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicEvenP1GoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenP1_order_zero pairs c hc,
    heClassicEvenP1_order_zero pairs c hc]
  exact ⟨le_rfl, le_rfl⟩

/-- Each literal `P₂` model with nonnegative sharp order is classic
integral. -/
theorem heClassicEvenP2_isClassicIntegral
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : 0 ≤ ordUnit K cSharp) :
    let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc hcSharp
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP2 (K := K) pairs c cSharp))
      (heHuExactRealization (heClassicEvenP2 (K := K) pairs c cSharp)
        (heClassicEvenP2_adjacentAdmissible pairs c cSharp hc hcSharp)
        (heClassicEvenP2_weakTwoStep pairs c cSharp hc hcSharp)).lattice := by
  dsimp only
  let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc hcSharp
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicEvenP2GoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenP2_order pairs c cSharp hc,
    heClassicEvenP2_order pairs c cSharp hc]
  simp

/-! ## Alpha profiles in Lemma 7.6 -/

/-- The `C₁` junction inside the literal `P₁` row has defect `d(c)`. -/
theorem heClassicEvenP1_anchorAdjacentDefect
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :
    let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
    b.adjacentDefect
        (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) =
      BONG.GoodBONG.defectOrder (K := K) c := by
  dsimp only
  unfold heClassicEvenP1GoodBONG
  rw [BONG.GoodBONG.heHuExactGoodBONG_adjacentDefect]
  have hleft : heClassicEvenP1 (K := K) pairs c
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 4)) = 1 := by
    rw [show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.castAdd 2 (⟨2 * pairs, by omega⟩ :
          Fin (2 * pairs + 2)) by exact Fin.ext rfl,
      heClassicEvenP1_prefix,
      show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
        Fin.natAdd (2 * pairs) (0 : Fin 2) by exact Fin.ext rfl,
      heClassicEvenC1_tail]
    rfl
  have hright : heClassicEvenP1 (K := K) pairs c
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 4)) = -c := by
    rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.castAdd 2 (⟨2 * pairs + 1, by omega⟩ :
          Fin (2 * pairs + 2)) by exact Fin.ext rfl,
      heClassicEvenP1_prefix,
      show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
        Fin.natAdd (2 * pairs) (1 : Fin 2) by exact Fin.ext rfl,
      heClassicEvenC1_tail]
    rfl
  have hcast :
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)).castSucc =
        (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 4)) := Fin.ext rfl
  have hsucc :
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)).succ =
        (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 4)) := Fin.ext rfl
  rw [hcast, hsucc, hleft, hright]
  simp

/-- The same junction inside the literal `P₂` row has defect `d(c)`. -/
theorem heClassicEvenP2_anchorAdjacentDefect
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : 0 ≤ ordUnit K cSharp) :
    let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc hcSharp
    b.adjacentDefect
        (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) =
      BONG.GoodBONG.defectOrder (K := K) c := by
  dsimp only
  unfold heClassicEvenP2GoodBONG
  rw [BONG.GoodBONG.heHuExactGoodBONG_adjacentDefect]
  have hleft : heClassicEvenP2 (K := K) pairs c cSharp
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 4)) = 1 := by
    rw [show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.castAdd 2 (⟨2 * pairs, by omega⟩ :
          Fin (2 * pairs + 2)) by exact Fin.ext rfl,
      heClassicEvenP2_prefix,
      show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
        Fin.natAdd (2 * pairs) (0 : Fin 2) by exact Fin.ext rfl,
      heClassicEvenC1_tail]
    rfl
  have hright : heClassicEvenP2 (K := K) pairs c cSharp
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 4)) = -c := by
    rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 4)) =
        Fin.castAdd 2 (⟨2 * pairs + 1, by omega⟩ :
          Fin (2 * pairs + 2)) by exact Fin.ext rfl,
      heClassicEvenP2_prefix,
      show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
        Fin.natAdd (2 * pairs) (1 : Fin 2) by exact Fin.ext rfl,
      heClassicEvenC1_tail]
    rfl
  have hcast :
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)).castSucc =
        (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 4)) := Fin.ext rfl
  have hsucc :
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)).succ =
        (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 4)) := Fin.ext rfl
  rw [hcast, hsucc, hleft, hright]
  simp

/-- Lemma 7.6(ii) for `P₁(omega)`, stated for any unit of defect one. -/
theorem heClassicEvenP1_alpha_eq_one
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c =
      ((1 : ℚ) : WithTop ℚ)) :
    let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
    ∀ i : Fin (2 * pairs + 3), b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
  apply b.he2022ClassicLemma29iii_alpha_of_zero_orders
    (heClassicEvenP1_isClassicIntegral (K := K) pairs c hc)
  · intro i
    simp only [b, heClassicEvenP1GoodBONG, heHuExactGoodBONG_order]
    exact heClassicEvenP1_order_zero pairs c hc i
  · refine ⟨⟨2 * pairs, by omega⟩, ?_⟩
    rw [heClassicEvenP1_anchorAdjacentDefect pairs c hc, hcDefect]

/-- Lemma 7.6(ii) for `P₂(omega)`, stated for any unit sharp choice. -/
theorem heClassicEvenP2_alpha_eq_one
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : ordUnit K cSharp = 0)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c =
      ((1 : ℚ) : WithTop ℚ)) :
    let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc
      (by omega)
    ∀ i : Fin (2 * pairs + 3), b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc
    (by omega)
  apply b.he2022ClassicLemma29iii_alpha_of_zero_orders
    (heClassicEvenP2_isClassicIntegral (K := K) pairs c cSharp hc
      (by omega))
  · intro i
    simp only [b, heClassicEvenP2GoodBONG, heHuExactGoodBONG_order]
    exact heClassicEvenP2_order_zero pairs c cSharp hc hcSharp i
  · refine ⟨⟨2 * pairs, by omega⟩, ?_⟩
    rw [heClassicEvenP2_anchorAdjacentDefect pairs c cSharp hc (by omega),
      hcDefect]

/-- Lemma 7.6(i): if the sharp parameter has order one, all alphas through
the last zero coefficient are one. -/
theorem heClassicEvenP2_alpha_eq_one_through_boundary
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : ordUnit K cSharp = 1) :
    let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc
      (by omega)
    ∀ i : Fin (2 * pairs + 3), i.val ≤ 2 * pairs + 1 →
      b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc
    (by omega)
  let boundary : Fin (2 * pairs + 3) := ⟨2 * pairs + 1, by omega⟩
  have hgap : b.orderGap boundary = 1 := by
    unfold BONG.GoodBONG.orderGap
    simp only [b, heClassicEvenP2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenP2_order pairs c cSharp hc,
      heClassicEvenP2_order pairs c cSharp hc, hcSharp]
    simp [boundary]
  have hboundaryAlpha : b.alphaValue boundary = 1 := by
    apply b.alphaValue_eq_one_of_orderGap_eq_endpoint boundary
    exact Or.inr hgap
  have horders : ∀ i : Fin (2 * pairs + 4),
      i ≤ boundary.castSucc → b.order i = 0 := by
    intro i hi
    simp only [b, heClassicEvenP2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenP2_order pairs c cSharp hc]
    rw [if_pos]
    have hle := Fin.mk_le_mk.mp hi
    simp only [boundary, Fin.val_castSucc] at hle
    omega
  have hprefix :=
    (b.he2022ClassicProposition24
      (heClassicEvenP2_isClassicIntegral (K := K) pairs c cSharp hc
        (by omega))).alphaOneOnZeroPrefix boundary horders boundary le_rfl
      (le_of_eq hboundaryAlpha)
  intro i hi
  by_cases hiboundary : i = boundary
  · simpa only [hiboundary] using hboundaryAlpha
  · apply hprefix i
    exact Fin.mk_lt_mk.mpr (lt_of_le_of_ne hi (by
      intro heq
      apply hiboundary
      exact Fin.ext heq))

/-! ## Determinants of the auxiliary rows -/

/-- Determinant of the literal even first-column row. -/
theorem diagonalUnitDeterminant_heClassicEvenC1
    (pairs : Nat) (c : Kˣ) :
    diagonalUnitDeterminant (heClassicEvenC1 (K := K) pairs c) =
      (-1 : Kˣ) ^ (pairs + 1) * c := by
  rw [heClassicEvenC1_eq_heHuEvenFirst,
    diagonalUnitDeterminant_heHuEvenFirst]

/-- Determinant of the literal even second-column row.  Its sharp parameter
contributes only a square. -/
theorem diagonalUnitDeterminant_heClassicEvenC2
    (pairs : Nat) (c cSharp : Kˣ) :
    diagonalUnitDeterminant (heClassicEvenC2 (K := K) pairs c cSharp) =
      (-1 : Kˣ) ^ (pairs + 1) * (cSharp ^ 2 * c) := by
  rw [heClassicEvenC2, heClassicScaledHyperbolicTower_zero,
    diagonalUnitDeterminant_append,
    diagonalUnitDeterminant_standardHyperbolicEndpointTower]
  simp [diagonalUnitDeterminant, Fin.prod_univ_two, pow_succ, pow_two]
  ac_rfl

/-- Both `P` columns have the determinant square class `(-1)^pairs`. -/
theorem diagonalUnitDeterminant_heClassicEvenP1
    (pairs : Nat) (c : Kˣ) :
    diagonalUnitDeterminant (heClassicEvenP1 (K := K) pairs c) =
      (-1 : Kˣ) ^ pairs * c ^ 2 := by
  rw [heClassicEvenP1, diagonalUnitDeterminant_append,
    diagonalUnitDeterminant_heClassicEvenC1]
  simp [heClassicEvenP1Tail, diagonalUnitDeterminant,
    Fin.prod_univ_two, pow_succ, pow_two]
  ac_rfl

theorem diagonalUnitDeterminant_heClassicEvenP2
    (pairs : Nat) (c cSharp : Kˣ) :
    diagonalUnitDeterminant (heClassicEvenP2 (K := K) pairs c cSharp) =
      (-1 : Kˣ) ^ pairs * (c * cSharp) ^ 2 := by
  rw [heClassicEvenP2, diagonalUnitDeterminant_append,
    diagonalUnitDeterminant_heClassicEvenC1]
  simp [heClassicEvenP2Tail, diagonalUnitDeterminant,
    Fin.prod_univ_two, pow_succ, pow_two]
  ac_rfl

/-! ## Full products and self-defects -/

/-- At full rank, the exact first `P` model has its displayed unit row. -/
theorem heClassicEvenP1_fullPrefixValueUnits
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :
    let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
    b.prefixValueUnits (2 * pairs + 4) le_rfl =
      heClassicEvenP1 (K := K) pairs c := by
  dsimp only
  funext i
  change (heClassicEvenP1GoodBONG (K := K) pairs c hc).valueUnit i =
    heClassicEvenP1 (K := K) pairs c i
  rw [heClassicEvenP1GoodBONG, heHuExactGoodBONG_valueUnit]

/-- At full rank, the exact second `P` model has its displayed unit row. -/
theorem heClassicEvenP2_fullPrefixValueUnits
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : 0 ≤ ordUnit K cSharp) :
    let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc hcSharp
    b.prefixValueUnits (2 * pairs + 4) le_rfl =
      heClassicEvenP2 (K := K) pairs c cSharp := by
  dsimp only
  funext i
  change (heClassicEvenP2GoodBONG
    (K := K) pairs c cSharp hc hcSharp).valueUnit i =
      heClassicEvenP2 (K := K) pairs c cSharp i
  rw [heClassicEvenP2GoodBONG, heHuExactGoodBONG_valueUnit]

/-- Full product of the first auxiliary row. -/
theorem heClassicEvenP1_prefixProduct_full
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :
    let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
    b.prefixProduct (2 * pairs + 4) =
      (-1 : Kˣ) ^ pairs * c ^ 2 := by
  dsimp only
  let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
  rw [← b.diagonalUnitDeterminant_prefixValueUnits
      (2 * pairs + 4) le_rfl,
    heClassicEvenP1_fullPrefixValueUnits pairs c hc,
    diagonalUnitDeterminant_heClassicEvenP1]

/-- Full product of the second auxiliary row. -/
theorem heClassicEvenP2_prefixProduct_full
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : 0 ≤ ordUnit K cSharp) :
    let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc hcSharp
    b.prefixProduct (2 * pairs + 4) =
      (-1 : Kˣ) ^ pairs * (c * cSharp) ^ 2 := by
  dsimp only
  let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc hcSharp
  rw [← b.diagonalUnitDeterminant_prefixValueUnits
      (2 * pairs + 4) le_rfl,
    heClassicEvenP2_fullPrefixValueUnits pairs c cSharp hc hcSharp,
    diagonalUnitDeterminant_heClassicEvenP2]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
private theorem heClassicP_signed_square
    (pairs : Nat) (c : Kˣ) :
    (-1 : Kˣ) ^ (pairs + 2) *
        ((-1 : Kˣ) ^ pairs * c ^ 2) = c ^ 2 := by
  calc
    (-1 : Kˣ) ^ (pairs + 2) *
        ((-1 : Kˣ) ^ pairs * c ^ 2) =
        (((-1 : Kˣ) ^ (pairs + 2) * (-1 : Kˣ) ^ pairs) *
          c ^ 2) := by ac_rfl
    _ = c ^ 2 := by
      rw [← pow_add]
      rw [(show Even ((pairs + 2) + pairs) from
        ⟨pairs + 1, by omega⟩).neg_one_pow]
      simp

/-- The signed full determinant of `P₁` is a square, hence its full
self-defect is infinite. -/
theorem heClassicEvenP1_fullSelfDefect
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :
    let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
    b.truncatedPrefixDefect b ((-1 : Kˣ) ^ (pairs + 2)) 0
        (2 * pairs + 4) = ⊤ := by
  dsimp only
  let b := heClassicEvenP1GoodBONG (K := K) pairs c hc
  unfold truncatedPrefixDefect
  rw [b.prefixAlphaCap_zero, b.prefixAlphaCap_last,
    min_eq_left le_top, BONG.GoodBONG.prefixProduct,
    b.toBONG.prefixProduct_zero,
    heClassicEvenP1_prefixProduct_full pairs c hc]
  simp only [mul_one]
  rw [
    heClassicP_signed_square,
    defectOrder_eq_top_of_isSquare ⟨c, pow_two c⟩]
  simp

/-- The signed full determinant of `P₂` is also a square. -/
theorem heClassicEvenP2_fullSelfDefect
    (pairs : Nat) (c cSharp : Kˣ) (hc : ordUnit K c = 0)
    (hcSharp : 0 ≤ ordUnit K cSharp) :
    let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc hcSharp
    b.truncatedPrefixDefect b ((-1 : Kˣ) ^ (pairs + 2)) 0
        (2 * pairs + 4) = ⊤ := by
  dsimp only
  let b := heClassicEvenP2GoodBONG (K := K) pairs c cSharp hc hcSharp
  unfold truncatedPrefixDefect
  rw [b.prefixAlphaCap_zero, b.prefixAlphaCap_last,
    min_eq_left le_top, BONG.GoodBONG.prefixProduct,
    b.toBONG.prefixProduct_zero,
    heClassicEvenP2_prefixProduct_full pairs c cSharp hc hcSharp]
  simp only [mul_one]
  rw [
    heClassicP_signed_square,
    defectOrder_eq_top_of_isSquare
      ⟨c * cSharp, pow_two (c * cSharp)⟩]
  simp

end Bong
