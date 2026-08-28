/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaCompression
import Bong.Bong.Beli2006AlphaLaws

/-!
# Beli (2009/2010), Lemma 2.7 and Corollaries 2.8--2.9

This file records the arithmetic shape of the alpha invariants.  Rational
integrality is expressed by explicit integer witnesses, so the statements do
not depend on an implementation-specific rational denominator.
-/

namespace Bong

open Dyadic

universe u v

/-- A rational number represented by an integer. -/
def IsRationalInteger (x : ℚ) : Prop :=
  ∃ z : Int, x = (z : ℚ)

/-- A rational number represented by one half of an integer. -/
def IsRationalHalfInteger (x : ℚ) : Prop :=
  ∃ z : Int, x = (z : ℚ) / 2

/-- A rational number represented by an odd integer. -/
def IsOddRationalInteger (x : ℚ) : Prop :=
  ∃ z : Int, Odd z ∧ x = (z : ℚ)

theorem IsOddRationalInteger.isRationalInteger
    {x : ℚ} (h : IsOddRationalInteger x) : IsRationalInteger x := by
  rcases h with ⟨z, _, hz⟩
  exact ⟨z, hz⟩

theorem IsRationalInteger.isRationalHalfInteger
    {x : ℚ} (h : IsRationalInteger x) : IsRationalHalfInteger x := by
  rcases h with ⟨z, rfl⟩
  refine ⟨2 * z, ?_⟩
  push_cast
  ring

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

theorem alphaValue_le_halfGapValue
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.alphaValue i ≤ b.halfGapValue i := by
  have hle := b.alpha_le_halfGapCandidate i
  rw [← b.coe_alphaValue, ← b.coe_halfGapValue] at hle
  exact_mod_cast hle

theorem halfGapValue_isRationalHalfInteger
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    IsRationalHalfInteger (b.halfGapValue i) := by
  refine ⟨b.orderGap i + 2 * (ramificationIndex K : Int), ?_⟩
  unfold halfGapValue
  push_cast
  ring

theorem halfGapValue_isRationalInteger_of_even
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (heven : Even (b.orderGap i)) :
    IsRationalInteger (b.halfGapValue i) := by
  rcases heven with ⟨z, hz⟩
  refine ⟨z + (ramificationIndex K : Int), ?_⟩
  unfold halfGapValue
  rw [hz]
  push_cast
  ring

end BONG.GoodBONG

/-- The parity conclusion of Lemma 2.7(iv).  It has no default instance;
the other three parts of Lemma 2.7 are already P2--P4 from Beli (2006). -/
class Beli2009AlphaParityLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  odd_integer_unless_half
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    b.alphaValue i ≠ b.halfGapValue i →
      IsOddRationalInteger (b.alphaValue i)

namespace BONG.GoodBONG

variable [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]

/-- Beli (2009/2010), Lemma 2.7(i). -/
theorem beli2009Lemma27_i (b : GoodBONG q L (n + 1)) (i : Fin n) :
    0 ≤ b.alphaValue i ∧
      (b.alphaValue i = 0 ↔
        b.orderGap i = -(2 * (ramificationIndex K : Int))) :=
  b.alpha_p2 i

/-- Beli (2009/2010), Lemma 2.7(ii). -/
theorem beli2009Lemma27_ii
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap i) :
    b.alphaValue i = b.halfGapValue i :=
  b.alpha_p4 i hgap

/-- Beli (2009/2010), Lemma 2.7(iii). -/
theorem beli2009Lemma27_iii
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : b.orderGap i ≤ 2 * (ramificationIndex K : Int)) :
    (b.orderGap i : ℚ) ≤ b.alphaValue i ∧
      (b.alphaValue i = (b.orderGap i : ℚ) ↔
        b.orderGap i = 2 * (ramificationIndex K : Int) ∨
          Odd (b.orderGap i)) :=
  b.alpha_p3 i hgap

/-- Beli (2009/2010), Lemma 2.7(iv). -/
theorem beli2009Lemma27_iv
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hne : b.alphaValue i ≠ b.halfGapValue i) :
    IsOddRationalInteger (b.alphaValue i) :=
  Beli2009AlphaParityLaws.odd_integer_unless_half b i hne

/-- Beli (2009/2010), Corollary 2.8(i): outside the exceptional odd gap
strictly above `2e`, the alpha value is integral. -/
theorem beli2009Corollary28_i
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hnot : ¬(Odd (b.orderGap i) ∧
      2 * (ramificationIndex K : Int) < b.orderGap i)) :
    IsRationalInteger (b.alphaValue i) := by
  rcases le_or_gt (b.orderGap i)
      (2 * (ramificationIndex K : Int)) with hle | hgt
  · rcases Int.even_or_odd (b.orderGap i) with heven | hodd
    · by_cases halpha : b.alphaValue i = b.halfGapValue i
      · rw [halpha]
        exact b.halfGapValue_isRationalInteger_of_even i heven
      · exact (b.beli2009Lemma27_iv i halpha).isRationalInteger
    · have halpha := (b.beli2009Lemma27_iii i hle).2.mpr (Or.inr hodd)
      exact ⟨b.orderGap i, halpha⟩
  · have hnotodd : ¬Odd (b.orderGap i) := by
      intro hodd
      exact hnot ⟨hodd, hgt⟩
    have heven : Even (b.orderGap i) :=
      Int.not_odd_iff_even.mp hnotodd
    rw [b.beli2009Lemma27_ii i hgt.le]
    exact b.halfGapValue_isRationalInteger_of_even i heven

/-- Beli (2009/2010), Corollary 2.8(ii). -/
theorem beli2009Corollary28_ii
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.alphaValue i < 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i < 2 * (ramificationIndex K : Int)) ∧
    (b.alphaValue i = 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i = 2 * (ramificationIndex K : Int)) ∧
    (2 * (ramificationIndex K : ℚ) < b.alphaValue i ↔
      2 * (ramificationIndex K : Int) < b.orderGap i) :=
  b.alpha_p5 i

/-- Beli (2009/2010), Corollary 2.8(iii): alpha lies either in the integral
interval `[0, 2e]` or in the half-integral interval `(2e, infinity)`. -/
theorem beli2009Corollary28_iii
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (0 ≤ b.alphaValue i ∧
        b.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) ∧
        IsRationalInteger (b.alphaValue i)) ∨
      (2 * (ramificationIndex K : ℚ) < b.alphaValue i ∧
        IsRationalHalfInteger (b.alphaValue i)) := by
  have hnonnegative := (b.beli2009Lemma27_i i).1
  rcases le_or_gt (b.alphaValue i)
      (2 * (ramificationIndex K : ℚ)) with hle | hgt
  · apply Or.inl
    refine ⟨hnonnegative, hle, b.beli2009Corollary28_i i ?_⟩
    rintro ⟨_, hgap⟩
    have halpha :
        2 * (ramificationIndex K : ℚ) < b.alphaValue i :=
      (b.beli2009Corollary28_ii i).2.2.mpr hgap
    exact (not_lt_of_ge hle) halpha
  · apply Or.inr
    refine ⟨hgt, ?_⟩
    have hgap : 2 * (ramificationIndex K : Int) < b.orderGap i :=
      (b.beli2009Corollary28_ii i).2.2.mp hgt
    rw [b.beli2009Lemma27_ii i hgap.le]
    exact b.halfGapValue_isRationalHalfInteger i

/-- Beli (2009/2010), Corollary 2.9(i). -/
theorem beli2009Corollary29_i
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hcase :
      2 * (ramificationIndex K : Int) ≤ b.orderGap i ∨
      b.orderGap i = -(2 * (ramificationIndex K : Int)) ∨
      b.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
      b.orderGap i = 2 * (ramificationIndex K : Int) - 2) :
    b.alphaValue i = b.halfGapValue i := by
  rcases hcase with hlarge | hnegative | hleft | hright
  · exact b.beli2009Lemma27_ii i hlarge
  · have halpha := (b.beli2009Lemma27_i i).2.mpr hnegative
    rw [halpha]
    unfold halfGapValue
    rw [hnegative]
    push_cast
    ring
  · have hinteger : IsRationalInteger (b.alphaValue i) := by
      apply b.beli2009Corollary28_i i
      rintro ⟨_, hgt⟩
      rw [hleft] at hgt
      have he := ramificationIndex_pos (K := K)
      omega
    have hpositive : 0 < b.alphaValue i := by
      have hnonnegative := (b.beli2009Lemma27_i i).1
      apply lt_of_le_of_ne hnonnegative
      intro halpha
      have hgap := (b.beli2009Lemma27_i i).2.mp halpha.symm
      rw [hleft] at hgap
      omega
    have hhalf : b.halfGapValue i = 1 := by
      unfold halfGapValue
      rw [hleft]
      push_cast
      ring
    rcases hinteger with ⟨z, halphaz⟩
    have hzpositive : 0 < z := by
      exact_mod_cast (show 0 < (z : ℚ) by simpa [halphaz] using hpositive)
    have hzle : z ≤ 1 := by
      exact_mod_cast (show (z : ℚ) ≤ 1 by
        rw [← halphaz, ← hhalf]
        exact b.alphaValue_le_halfGapValue i)
    have hzvalue : z = 1 := by omega
    calc
      b.alphaValue i = (z : ℚ) := halphaz
      _ = 1 := by rw [hzvalue]; norm_num
      _ = b.halfGapValue i := hhalf.symm
  · have hle : b.orderGap i ≤ 2 * (ramificationIndex K : Int) := by
      rw [hright]
      omega
    have hlower := (b.beli2009Lemma27_iii i hle).1
    have heven : Even (b.orderGap i) := by
      rw [hright]
      refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
      ring
    have hnotodd : ¬Odd (b.orderGap i) :=
      Int.not_odd_iff_even.mpr heven
    have hstrict : (b.orderGap i : ℚ) < b.alphaValue i := by
      apply lt_of_le_of_ne hlower
      intro heq
      have hcases := (b.beli2009Lemma27_iii i hle).2.mp heq.symm
      rcases hcases with hequal | hodd
      · rw [hright] at hequal
        omega
      · exact hnotodd hodd
    have hinteger : IsRationalInteger (b.alphaValue i) := by
      apply b.beli2009Corollary28_i i
      rintro ⟨_, hgt⟩
      exact (not_lt_of_ge hle) hgt
    have hhalf :
        b.halfGapValue i = 2 * (ramificationIndex K : ℚ) - 1 := by
      unfold halfGapValue
      rw [hright]
      push_cast
      ring
    rcases hinteger with ⟨z, hz⟩
    have hzlower :
        2 * (ramificationIndex K : Int) - 2 < z := by
      have hcast :
          ((2 * (ramificationIndex K : Int) - 2 : Int) : ℚ) <
            (z : ℚ) := by
        rw [← hz, ← hright]
        exact hstrict
      exact_mod_cast hcast
    have hzupper : z ≤ 2 * (ramificationIndex K : Int) - 1 := by
      have hcast :
          (z : ℚ) ≤
            ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) := by
        push_cast
        rw [← hz, ← hhalf]
        exact b.alphaValue_le_halfGapValue i
      exact_mod_cast hcast
    have hzvalue : z = 2 * (ramificationIndex K : Int) - 1 := by
      omega
    rw [hz, hhalf, hzvalue]
    push_cast
    rfl

/-- Beli (2009/2010), Corollary 2.9(ii). -/
theorem beli2009Corollary29_ii
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hodd : Odd (b.orderGap i)) :
    b.alphaValue i = min (b.halfGapValue i) (b.orderGap i : ℚ) := by
  have hne : b.orderGap i ≠ 2 * (ramificationIndex K : Int) := by
    intro heq
    have heven : Even (b.orderGap i) := by
      rw [heq]
      exact even_two_mul (ramificationIndex K : Int)
    exact (Int.not_odd_iff_even.mpr heven) hodd
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have halpha :=
      (b.beli2009Lemma27_iii i hlt.le).2.mpr (Or.inr hodd)
    have hmin : (b.orderGap i : ℚ) ≤ b.halfGapValue i := by
      unfold halfGapValue
      have hcast :
          (b.orderGap i : ℚ) <
            (2 * (ramificationIndex K : Int) : ℚ) := by
        exact_mod_cast hlt
      push_cast at hcast
      linarith
    rw [halpha, min_eq_right hmin]
  · have halpha := b.beli2009Lemma27_ii i hgt.le
    have hmin : b.halfGapValue i ≤ (b.orderGap i : ℚ) := by
      unfold halfGapValue
      have hcast :
          (2 * (ramificationIndex K : Int) : ℚ) <
            (b.orderGap i : ℚ) := by
        exact_mod_cast hgt
      push_cast at hcast
      linarith
    rw [halpha, min_eq_left hmin]

end BONG.GoodBONG

end Bong
