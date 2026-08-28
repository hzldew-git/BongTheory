/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.Valuation
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Data.ENat.Lattice

/-!
# Relative quadratic defect

For `a ∈ Kˣ`, the relative quadratic defect measures how closely `a` can be
approximated by a square.  We use the order-theoretic form of Beli's convention:
`n` is attainable when some `x` satisfies

`n ≤ ord (a⁻¹ (a - x²)) = ord (1 - x² / a)`.

The value is the supremum of all attainable natural numbers, hence lies in
`ℕ∞ = ℕ ∪ {∞}`.  This file proves square invariance and the domination
principle directly from the valuation axioms.
-/

namespace Bong.Dyadic

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K]

/-- The multiplicative square-class group `Kˣ / Kˣ²`. -/
abbrev SquareClass := Kˣ ⧸ Subgroup.square Kˣ

/-- The square class represented by a nonzero element. -/
def squareClass (a : Kˣ) : SquareClass K :=
  QuotientGroup.mk' (Subgroup.square Kˣ) a

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
@[simp]
theorem squareClass_mul_square (a s : Kˣ) :
    squareClass K (a * s ^ 2) = squareClass K a := by
  symm
  change QuotientGroup.mk' (Subgroup.square Kˣ) a =
    QuotientGroup.mk' (Subgroup.square Kˣ) (a * s ^ 2)
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨s ^ 2, ?_, rfl⟩
  exact ⟨s, by simp [pow_two]⟩

/-- `a` admits a relative quadratic approximation of depth at least `n`. -/
def IsQuadraticApproximation (a : Kˣ) (n : ℕ) : Prop :=
  ∃ x : K, (n : WithTop ℤ) ≤ ord K (1 - x ^ 2 / (a : K))

theorem isQuadraticApproximation_zero (a : Kˣ) :
    IsQuadraticApproximation K a 0 := by
  refine ⟨0, ?_⟩
  simp

theorem IsQuadraticApproximation.mono {a : Kˣ} {m n : ℕ} (hmn : m ≤ n)
    (h : IsQuadraticApproximation K a n) : IsQuadraticApproximation K a m := by
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hcast : (m : WithTop ℤ) ≤ (n : WithTop ℤ) := by exact_mod_cast hmn
  exact hcast.trans hx

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
private theorem normalizedError_mul_square (a s : Kˣ) (x : K) :
    1 - (x * (s : K)) ^ 2 / ((a * s ^ 2 : Kˣ) : K) =
      1 - x ^ 2 / (a : K) := by
  change 1 - (x * (s : K)) ^ 2 / ((a : K) * (s : K) ^ 2) =
    1 - x ^ 2 / (a : K)
  field_simp [Units.ne_zero a, Units.ne_zero s]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
private theorem normalizedError_div_square (a s : Kˣ) (x : K) :
    1 - (x / (s : K)) ^ 2 / (a : K) =
      1 - x ^ 2 / ((a * s ^ 2 : Kˣ) : K) := by
  change 1 - (x / (s : K)) ^ 2 / (a : K) =
    1 - x ^ 2 / ((a : K) * (s : K) ^ 2)
  field_simp [Units.ne_zero a, Units.ne_zero s]

theorem isQuadraticApproximation_mul_square_iff (a s : Kˣ) (n : ℕ) :
    IsQuadraticApproximation K (a * s ^ 2) n ↔ IsQuadraticApproximation K a n := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x / (s : K), ?_⟩
    rw [normalizedError_div_square]
    exact hx
  · rintro ⟨x, hx⟩
    refine ⟨x * (s : K), ?_⟩
    rw [normalizedError_mul_square]
    exact hx

/-- The order of the relative quadratic defect, valued in `ℕ ∪ {∞}`. -/
noncomputable def quadraticDefect (a : Kˣ) : ℕ∞ :=
  ⨆ n : {n : ℕ // IsQuadraticApproximation K a n}, (n.1 : ℕ∞)

theorem natCast_le_quadraticDefect {a : Kˣ} {n : ℕ}
    (h : IsQuadraticApproximation K a n) : (n : ℕ∞) ≤ quadraticDefect K a := by
  exact le_iSup (fun m : {m : ℕ // IsQuadraticApproximation K a m} ↦ (m.1 : ℕ∞)) ⟨n, h⟩

/-- An absolute square approximation whose error begins at
`ord(a) + k` gives relative quadratic defect at least `k`.

This is the valuation bridge between O'Meara's absolute defect ideal
`d(a)` and the relative defect used throughout the BONG formulas. -/
theorem quadraticDefect_ge_of_absolute_square_approximation
    (a : Kˣ) (x : K) (h : Int) (k : Nat)
    (haOrder : ordUnit K a = h)
    (herror : (((h + (k : Int) : Int)) : WithTop Int) ≤
      ord K ((a : K) - x ^ 2)) :
    (k : ℕ∞) ≤ quadraticDefect K a := by
  apply natCast_le_quadraticDefect K
  refine ⟨x, ?_⟩
  have hfield :
      1 - x ^ 2 / (a : K) = ((a : K) - x ^ 2) / (a : K) := by
    field_simp [Units.ne_zero a]
  rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
    ← coe_ordUnit, haOrder]
  have hadd := add_le_add_right herror (-(h : WithTop Int))
  calc
    ((k : Int) : WithTop Int) =
        ((h + (k : Int) : Int) : WithTop Int) +
          (-(h : WithTop Int)) := by
            norm_cast
            omega
    _ ≤ ord K ((a : K) - x ^ 2) + (-(h : WithTop Int)) := by
      simpa [add_comm] using hadd

theorem isQuadraticApproximation_iff_le_defect {a : Kˣ} {n : ℕ} :
    IsQuadraticApproximation K a n ↔ (n : ℕ∞) ≤ quadraticDefect K a := by
  constructor
  · exact natCast_le_quadraticDefect K
  · intro hn
    cases n with
    | zero => exact isQuadraticApproximation_zero K a
    | succ n =>
      have hsucc : (n : ℕ∞) < (n + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self n
      have hlt : (n : ℕ∞) < quadraticDefect K a := hsucc.trans_le hn
      rw [quadraticDefect, lt_iSup_iff] at hlt
      rcases hlt with ⟨⟨m, hm⟩, hnm⟩
      apply hm.mono
      exact_mod_cast hnm

theorem quadraticDefect_mul_square (a s : Kˣ) :
    quadraticDefect K (a * s ^ 2) = quadraticDefect K a := by
  apply le_antisymm
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n hn
    apply (isQuadraticApproximation_iff_le_defect K).1
    exact (isQuadraticApproximation_mul_square_iff K a s n).1
      ((isQuadraticApproximation_iff_le_defect K).2 hn)
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n hn
    apply (isQuadraticApproximation_iff_le_defect K).1
    exact (isQuadraticApproximation_mul_square_iff K a s n).2
      ((isQuadraticApproximation_iff_le_defect K).2 hn)

/-- Inversion does not change the relative quadratic defect. -/
theorem quadraticDefect_inv (a : Kˣ) :
    quadraticDefect K a⁻¹ = quadraticDefect K a := by
  have h := quadraticDefect_mul_square K a⁻¹ a
  simpa [pow_two] using h.symm

theorem quadraticDefect_eq_top_of_isSquare {a : Kˣ} (ha : IsSquare a) :
    quadraticDefect K a = ⊤ := by
  rcases ha with ⟨s, hs⟩
  have hsval : (a : K) = (s : K) * (s : K) := congrArg Units.val hs
  have happ (n : ℕ) : IsQuadraticApproximation K a n := by
    refine ⟨(s : K), ?_⟩
    have hquot : (s : K) ^ 2 / (a : K) = 1 := by
      rw [hsval, pow_two, div_self]
      exact mul_ne_zero (Units.ne_zero s) (Units.ne_zero s)
    rw [hquot]
    simp
  apply top_unique
  rw [← ENat.iSup_natCast]
  exact iSup_le fun n ↦ natCast_le_quadraticDefect K (happ n)

private theorem ord_normalizedTerm_nonneg {a : Kˣ} {n : ℕ} {x : K}
    (h : (n : WithTop ℤ) ≤ ord K (1 - x ^ 2 / (a : K))) :
    0 ≤ ord K (x ^ 2 / (a : K)) := by
  have hn : (0 : WithTop ℤ) ≤ (n : WithTop ℤ) := by positivity
  have herr : 0 ≤ ord K (1 - x ^ 2 / (a : K)) := hn.trans h
  have hadd := min_ord_le_ord_add K (1 : K) (-(1 - x ^ 2 / (a : K)))
  have hnonneg : 0 ≤ ord K (1 + -(1 - x ^ 2 / (a : K))) := by
    simpa only [ord_one, ord_neg, min_eq_left herr] using hadd
  have heq : 1 + -(1 - x ^ 2 / (a : K)) = x ^ 2 / (a : K) := by ring
  rw [heq] at hnonneg
  exact hnonneg

theorem IsQuadraticApproximation.mul {a b : Kˣ} {n : ℕ}
    (ha : IsQuadraticApproximation K a n) (hb : IsQuadraticApproximation K b n) :
    IsQuadraticApproximation K (a * b) n := by
  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩
  let u : K := x ^ 2 / (a : K)
  let v : K := y ^ 2 / (b : K)
  change (n : WithTop ℤ) ≤ ord K (1 - u) at hx
  change (n : WithTop ℤ) ≤ ord K (1 - v) at hy
  have hu : 0 ≤ ord K u := ord_normalizedTerm_nonneg K hx
  have huv : (n : WithTop ℤ) ≤ ord K (u * (1 - v)) := by
    rw [ord_mul]
    simpa using add_le_add hu hy
  refine ⟨x * y, ?_⟩
  have hratio : (x * y) ^ 2 / ((a * b : Kˣ) : K) = u * v := by
    change (x * y) ^ 2 / ((a : K) * (b : K)) =
      (x ^ 2 / (a : K)) * (y ^ 2 / (b : K))
    field_simp [Units.ne_zero a, Units.ne_zero b]
  rw [hratio]
  have hadd := min_ord_le_ord_add K (1 - u) (u * (1 - v))
  have hmin : (n : WithTop ℤ) ≤
      min (ord K (1 - u)) (ord K (u * (1 - v))) := le_min hx huv
  have hsum := hmin.trans hadd
  have heq : (1 - u) + u * (1 - v) = 1 - u * v := by ring
  rw [heq] at hsum
  exact hsum

/-- Beli's domination principle for the relative quadratic defect. -/
theorem quadraticDefect_mul_ge_min (a b : Kˣ) :
    min (quadraticDefect K a) (quadraticDefect K b) ≤ quadraticDefect K (a * b) := by
  rw [← ENat.forall_natCast_le_iff_le]
  intro n hn
  apply (isQuadraticApproximation_iff_le_defect K).1
  apply IsQuadraticApproximation.mul K
  · apply (isQuadraticApproximation_iff_le_defect K).2
    exact hn.trans (min_le_left _ _)
  · apply (isQuadraticApproximation_iff_le_defect K).2
    exact hn.trans (min_le_right _ _)

/-- If the two defects differ, the domination bound is an equality. -/
theorem quadraticDefect_mul_eq_left_of_lt_right {a b : Kˣ}
    (h : quadraticDefect K a < quadraticDefect K b) :
    quadraticDefect K (a * b) = quadraticDefect K a := by
  apply le_antisymm
  · by_contra hle
    have ha_lt_prod : quadraticDefect K a < quadraticDefect K (a * b) :=
      lt_of_not_ge hle
    have hsecond := quadraticDefect_mul_ge_min K (a * b) b
    have hsquare : quadraticDefect K ((a * b) * b) = quadraticDefect K a := by
      simpa [pow_two, mul_assoc] using quadraticDefect_mul_square K a b
    rw [hsquare] at hsecond
    exact (not_lt_of_ge hsecond) (lt_min ha_lt_prod h)
  · have hdom := quadraticDefect_mul_ge_min K a b
    simpa [min_eq_left h.le] using hdom

/-- Symmetric form of exact domination when the right defect is smaller. -/
theorem quadraticDefect_mul_eq_right_of_lt_left {a b : Kˣ}
    (h : quadraticDefect K b < quadraticDefect K a) :
    quadraticDefect K (a * b) = quadraticDefect K b := by
  simpa [mul_comm] using quadraticDefect_mul_eq_left_of_lt_right (K := K) h

/-- Beli's exact domination principle away from equal defects. -/
theorem quadraticDefect_mul_eq_min_of_ne {a b : Kˣ}
    (h : quadraticDefect K a ≠ quadraticDefect K b) :
    quadraticDefect K (a * b) = min (quadraticDefect K a) (quadraticDefect K b) := by
  rcases lt_or_gt_of_ne h with hab | hba
  · rw [quadraticDefect_mul_eq_left_of_lt_right (K := K) hab, min_eq_left hab.le]
  · rw [quadraticDefect_mul_eq_right_of_lt_left (K := K) hba, min_eq_right hba.le]

/--
The local classification properties of the concrete defect.  They are isolated
as a typeclass because proving the converse square criterion and the `2e` bound
requires the local square theorem, which is not currently available in mathlib.
-/
class QuadraticDefectLaws : Prop where
  eq_top_iff_isSquare (a : Kˣ) : quadraticDefect K a = ⊤ ↔ IsSquare a
  le_two_mul_e_of_not_isSquare (a : Kˣ) (ha : ¬IsSquare a) :
    quadraticDefect K a ≤ ((2 * ramificationIndex K : ℕ) : ℕ∞)

variable [QuadraticDefectLaws K]

theorem quadraticDefect_eq_top_iff_isSquare (a : Kˣ) :
    quadraticDefect K a = ⊤ ↔ IsSquare a :=
  QuadraticDefectLaws.eq_top_iff_isSquare a

theorem quadraticDefect_le_two_mul_e_of_not_isSquare {a : Kˣ} (ha : ¬IsSquare a) :
    quadraticDefect K a ≤ ((2 * ramificationIndex K : ℕ) : ℕ∞) :=
  QuadraticDefectLaws.le_two_mul_e_of_not_isSquare a ha

/-- The parity part of the dyadic unit-defect classification.  A unit defect
strictly below `2e` is odd.  This is separated from `QuadraticDefectLaws`
because it is needed only by the fine congruence formulas in Beli (2003). -/
class UnitQuadraticDefectParityLaws : Prop where
  odd_toNat_of_lt_two_mul_e
      (u : Kˣ) (hu : IsValuationUnit K (u : K))
      (hlt : quadraticDefect K u <
        ((2 * ramificationIndex K : ℕ) : ℕ∞)) :
      Odd (quadraticDefect K u).toNat

omit [QuadraticDefectLaws K] in
/-- A finite dyadic unit defect below `2e` has odd natural value. -/
theorem quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
    [UnitQuadraticDefectParityLaws K]
    (u : Kˣ) (hu : IsValuationUnit K (u : K))
    (hlt : quadraticDefect K u <
      ((2 * ramificationIndex K : ℕ) : ℕ∞)) :
    Odd (quadraticDefect K u).toNat :=
  UnitQuadraticDefectParityLaws.odd_toNat_of_lt_two_mul_e u hu hlt

/-- The two square-difference facts used at the boundary of the dyadic
square theorem.  The first is the usual parity assertion below depth `2e`.
The second identifies the nonsquare discriminant class at depth `2e` when
the residue field has two elements.  They are kept as local-field input,
separate from the order-theoretic definition of quadratic defect. -/
class DyadicSquareDifferenceLaws : Prop where
  even_order_one_sub_sq_of_lt_two_mul_e
      (x : K) (n : Int)
      (horder : ord K (1 - x ^ 2) = (n : WithTop Int))
      (hpos : 0 < n)
      (hlt : n < 2 * (ramificationIndex K : Int)) :
      Even n
  one_sub_four_mul_unit_ne_sq_of_residue_two
      (u x : K)
      (hu : IsValuationUnit K u)
      (hresidue : ∀ z : K,
        IsValuationUnit K z → IsInMaximalIdeal K (z - 1)) :
      1 - (2 : K) ^ 2 * u ≠ x ^ 2

variable [DyadicSquareDifferenceLaws K]

omit [QuadraticDefectLaws K] in
/-- Public form of the parity obstruction for a square difference below
the dyadic endpoint. -/
theorem even_order_one_sub_sq_of_lt_two_mul_e
    (x : K) (n : Int)
    (horder : ord K (1 - x ^ 2) = (n : WithTop Int))
    (hpos : 0 < n)
    (hlt : n < 2 * (ramificationIndex K : Int)) :
    Even n :=
  DyadicSquareDifferenceLaws.even_order_one_sub_sq_of_lt_two_mul_e
    x n horder hpos hlt

omit [QuadraticDefectLaws K] in
/-- Public form of the endpoint discriminant obstruction over a two-element
residue field. -/
theorem one_sub_four_mul_unit_ne_sq_of_residue_two
    (u x : K)
    (hu : IsValuationUnit K u)
    (hresidue : ∀ z : K,
      IsValuationUnit K z → IsInMaximalIdeal K (z - 1)) :
    1 - (2 : K) ^ 2 * u ≠ x ^ 2 :=
  DyadicSquareDifferenceLaws.one_sub_four_mul_unit_ne_sq_of_residue_two
    u x hu hresidue

end Bong.Dyadic
