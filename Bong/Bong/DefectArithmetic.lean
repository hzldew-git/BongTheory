/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Invariants

/-!
# Arithmetic of embedded quadratic-defect orders

This file collects the multiplicative facts about `defectOrder` used in both
Beli's representation and classification arguments.
-/

namespace Bong

open Dyadic

universe u

namespace Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A square class of odd valuation has zero relative quadratic defect.

This is the elementary valuation argument used in Beli (2006), property P3,
and later in Beli (2009/2010), Remark 5.2.  It belongs in the common defect
layer rather than in either of those downstream applications. -/
theorem quadraticDefect_eq_zero_of_odd_ordUnit
    (a : Kˣ) (hodd : Odd (ordUnit K a)) :
    quadraticDefect K a = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpos : 0 < quadraticDefect K a := lt_of_not_ge hnot
    have hone : (1 : ℕ∞) ≤ quadraticDefect K a := by
      cases hdefect : quadraticDefect K a with
      | top => exact le_top
      | coe d =>
          have hdpos : 0 < d := by
            have hcoe : (0 : ℕ∞) < (d : ℕ∞) := by
              simpa only [hdefect] using hpos
            exact_mod_cast hcoe
          exact_mod_cast (Nat.succ_le_iff.mpr hdpos)
    rcases (isQuadraticApproximation_iff_le_defect K).2 hone with
      ⟨x, hx⟩
    let err : K := 1 - x ^ 2 / (a : K)
    have herrPos : 0 < ord K err := by
      have hzeroOne : (0 : WithTop Int) < 1 := by norm_num
      exact hzeroOne.trans_le (by simpa [err] using hx)
    have hquotOrder : ord K (x ^ 2 / (a : K)) = 0 := by
      have hlt : ord K (1 : K) < ord K err := by
        simpa only [ord_one] using herrPos
      have hsub := (ord K).map_sub_eq_of_lt_left hlt
      have heq : 1 - err = x ^ 2 / (a : K) := by
        dsimp [err]
        ring
      rw [heq] at hsub
      simpa using hsub
    have hxne : x ≠ 0 := by
      intro hzero
      rw [hzero] at hquotOrder
      simp at hquotOrder
    let xu : Kˣ := Units.mk0 x hxne
    have hquotUnitOrder : ordUnit K (xu ^ 2 * a⁻¹) = 0 := by
      apply (isValuationUnit_iff_ordUnit_eq_zero K (xu ^ 2 * a⁻¹)).1
      rw [IsValuationUnit]
      have hval : ((xu ^ 2 * a⁻¹ : Kˣ) : K) =
          x ^ 2 / (a : K) := by
        simp [xu, div_eq_mul_inv]
      rw [hval]
      exact hquotOrder
    rw [ordUnit_mul, ordUnit_pow, ordUnit_inv] at hquotUnitOrder
    rcases hodd with ⟨z, hz⟩
    omega
  · exact bot_le

end Dyadic

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The domination principle after embedding quadratic-defect orders in
`WithTop ℚ`. -/
theorem defectOrder_mul_ge_min (a b : Kˣ) :
    min (defectOrder (K := K) a) (defectOrder (K := K) b) ≤
      defectOrder (K := K) (a * b) := by
  let f : Nat → ℚ := fun k ↦ (k : ℚ)
  have hf : Monotone f := by
    intro x y hxy
    change (x : ℚ) ≤ (y : ℚ)
    exact_mod_cast hxy
  have hmap : Monotone (WithTop.map f) :=
    WithTop.monotone_map_iff.mpr hf
  change min (WithTop.map f (quadraticDefect K a))
      (WithTop.map f (quadraticDefect K b)) ≤
    WithTop.map f (quadraticDefect K (a * b))
  rw [← hmap.map_min]
  exact hmap (quadraticDefect_mul_ge_min K a b)

/-- Multiplying by a square does not change the embedded defect order. -/
theorem defectOrder_mul_square (a s : Kˣ) :
    defectOrder (K := K) (a * s ^ 2) = defectOrder (K := K) a := by
  unfold defectOrder
  rw [quadraticDefect_mul_square]

/-- A concrete quadratic approximation of natural depth gives the
corresponding lower bound after embedding the defect in `WithTop ℚ`. -/
theorem natCast_le_defectOrder_of_isQuadraticApproximation
    (a : Kˣ) (n : Nat) (h : IsQuadraticApproximation K a n) :
    ((((n : Nat) : ℚ) : WithTop ℚ) ≤ defectOrder (K := K) a) := by
  have hraw := natCast_le_quadraticDefect K h
  by_cases htop : quadraticDefect K a = ⊤
  · unfold defectOrder
    rw [htop]
    exact le_top
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
    have hnm : n ≤ m := by
      rw [← hm] at hraw
      exact ENat.coe_le_coe.mp hraw
    unfold defectOrder
    rw [← hm]
    change (((n : Nat) : ℚ) : WithTop ℚ) ≤
      (((m : Nat) : ℚ) : WithTop ℚ)
    exact_mod_cast hnm

/-- Natural lower bounds on the embedded defect order are exactly the
corresponding lower bounds on the underlying extended-natural defect. -/
theorem natCast_le_defectOrder_iff (a : Kˣ) (n : Nat) :
    ((((n : Nat) : ℚ) : WithTop ℚ) ≤ defectOrder (K := K) a) ↔
      ((n : Nat) : ℕ∞) ≤ quadraticDefect K a := by
  let f : Nat → ℚ := Nat.castAddMonoidHom ℚ
  have hf : ∀ {m k : Nat}, f m ≤ f k ↔ m ≤ k := by
    intro m k
    change (m : ℚ) ≤ (k : ℚ) ↔ m ≤ k
    exact_mod_cast Iff.rfl
  unfold defectOrder
  change WithTop.map f (n : WithTop Nat) ≤
      WithTop.map f (quadraticDefect K a) ↔ _
  exact WithTop.map_le_iff f hf

/-- A square has infinite embedded quadratic-defect order. -/
theorem defectOrder_eq_top_of_isSquare {a : Kˣ} (ha : IsSquare a) :
    defectOrder (K := K) a = ⊤ := by
  unfold defectOrder
  rw [quadraticDefect_eq_top_of_isSquare K ha]
  rfl

/-- A defect order strictly beyond the dyadic endpoint `2e` can only be the
infinite defect of a square. -/
theorem isSquare_of_two_mul_e_lt_defectOrder
    [QuadraticDefectLaws K] (a : Kˣ)
    (h : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      defectOrder (K := K) a) :
    IsSquare a := by
  by_contra hnotSquare
  have hle := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnotSquare
  unfold defectOrder at h
  cases hdefect : quadraticDefect K a with
  | top =>
      exact hnotSquare
        ((quadraticDefect_eq_top_iff_isSquare K a).1 hdefect)
  | coe m =>
      rw [hdefect] at h hle
      have hlt : 2 * ramificationIndex K < m := by
        change ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (((m : Nat) : ℚ) : WithTop ℚ)) at h
        norm_cast at h
      have hmle : m ≤ 2 * ramificationIndex K := by
        change (m : WithTop Nat) ≤
          ((2 * ramificationIndex K : Nat) : WithTop Nat) at hle
        exact WithTop.coe_le_coe.mp hle
      omega

/-- Exact domination when the right factor has strictly smaller defect. -/
theorem defectOrder_mul_eq_right_of_lt_left {a b : Kˣ}
    (h : defectOrder (K := K) b < defectOrder (K := K) a) :
    defectOrder (K := K) (a * b) = defectOrder (K := K) b := by
  apply le_antisymm
  · by_contra hnot
    have hbmul : defectOrder (K := K) b <
        defectOrder (K := K) (a * b) := lt_of_not_ge hnot
    have hupper :
        min (defectOrder (K := K) a)
            (defectOrder (K := K) (a * b)) ≤
          defectOrder (K := K) b := by
      calc
        min (defectOrder (K := K) a)
              (defectOrder (K := K) (a * b)) ≤
            defectOrder (K := K) (a * (a * b)) :=
          defectOrder_mul_ge_min a (a * b)
        _ = defectOrder (K := K) (b * a ^ 2) := by
          apply congrArg (defectOrder (K := K))
          simp only [pow_two]
          ac_rfl
        _ = defectOrder (K := K) b := defectOrder_mul_square b a
    exact (not_lt_of_ge hupper) (lt_min h hbmul)
  · have hdom := defectOrder_mul_ge_min (K := K) a b
    rwa [min_eq_right h.le] at hdom

/-- Exact domination when the left factor has strictly smaller defect. -/
theorem defectOrder_mul_eq_left_of_lt_right {a b : Kˣ}
    (h : defectOrder (K := K) a < defectOrder (K := K) b) :
    defectOrder (K := K) (a * b) = defectOrder (K := K) a := by
  simpa only [mul_comm] using
    (defectOrder_mul_eq_right_of_lt_left (K := K) (a := b) (b := a) h)

/-- Exact domination whenever the two embedded defect orders differ. -/
theorem defectOrder_mul_eq_min_of_ne {a b : Kˣ}
    (h : defectOrder (K := K) a ≠ defectOrder (K := K) b) :
    defectOrder (K := K) (a * b) =
      min (defectOrder (K := K) a) (defectOrder (K := K) b) := by
  rcases lt_or_gt_of_ne h with hab | hba
  · rw [defectOrder_mul_eq_left_of_lt_right hab, min_eq_left hab.le]
  · rw [defectOrder_mul_eq_right_of_lt_left hba, min_eq_right hba.le]

/-- An upper bound for a sum of embedded rational defect orders reflects to
the same upper bound for the underlying extended-natural defects. -/
theorem quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE
    (a b : Kˣ)
    (h : defectOrder (K := K) a + defectOrder (K := K) b ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    quadraticDefect K a + quadraticDefect K b ≤
      ((2 * ramificationIndex K : Nat) : WithTop Nat) := by
  let f : Nat → ℚ := Nat.castAddMonoidHom ℚ
  have hf : ∀ {m n : Nat}, f m ≤ f n ↔ m ≤ n := by
    intro m n
    change (m : ℚ) ≤ (n : ℚ) ↔ m ≤ n
    exact_mod_cast Iff.rfl
  let da : WithTop Nat := quadraticDefect K a
  let db : WithTop Nat := quadraticDefect K b
  change da + db ≤ ((2 * ramificationIndex K : Nat) : WithTop Nat)
  apply (WithTop.map_le_iff f hf).mp
  rw [WithTop.map_add]
  change defectOrder (K := K) a + defectOrder (K := K) b ≤
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)
  exact h

/-- The rational embedding preserves an upper bound for a sum of two
extended-natural quadratic defects. -/
theorem defectOrder_add_le_twoE_of_quadraticDefect_add_le_twoE
    (a b : Kˣ)
    (h : quadraticDefect K a + quadraticDefect K b ≤
      ((2 * ramificationIndex K : Nat) : WithTop Nat)) :
    defectOrder (K := K) a + defectOrder (K := K) b ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  let f : Nat →+ ℚ := Nat.castAddMonoidHom ℚ
  have hf : Monotone (f : Nat → ℚ) := by
    intro m n hmn
    change (m : ℚ) ≤ (n : ℚ)
    exact_mod_cast hmn
  have hmap := (WithTop.monotone_map_iff.mpr hf) h
  calc
    defectOrder (K := K) a + defectOrder (K := K) b =
        WithTop.map (f : Nat → ℚ) (quadraticDefect K a) +
          WithTop.map (f : Nat → ℚ) (quadraticDefect K b) := by rfl
    _ = WithTop.map (f : Nat → ℚ)
        (quadraticDefect K a + quadraticDefect K b) :=
      (WithTop.map_add f _ _).symm
    _ ≤ WithTop.map (f : Nat → ℚ)
        ((2 * ramificationIndex K : Nat) : WithTop Nat) := hmap
    _ = (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by rfl

/-- The rational embedding preserves equality of a defect sum with the
dyadic endpoint. -/
theorem defectOrder_add_eq_twoE_of_quadraticDefect_add_eq_twoE
    (a b : Kˣ)
    (h : quadraticDefect K a + quadraticDefect K b =
      ((2 * ramificationIndex K : Nat) : WithTop Nat)) :
    defectOrder (K := K) a + defectOrder (K := K) b =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  let f : Nat →+ ℚ := Nat.castAddMonoidHom ℚ
  calc
    defectOrder (K := K) a + defectOrder (K := K) b =
        WithTop.map (f : Nat → ℚ) (quadraticDefect K a) +
          WithTop.map (f : Nat → ℚ) (quadraticDefect K b) := by rfl
    _ = WithTop.map (f : Nat → ℚ)
        (quadraticDefect K a + quadraticDefect K b) :=
      (WithTop.map_add f _ _).symm
    _ = WithTop.map (f : Nat → ℚ)
        ((2 * ramificationIndex K : Nat) : WithTop Nat) := by rw [h]
    _ = (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by rfl

/-- A zero embedded defect order reflects to a zero extended-natural
quadratic defect. -/
theorem quadraticDefect_eq_zero_of_defectOrder_eq_zero
    (a : Kˣ) (h : defectOrder (K := K) a = 0) :
    quadraticDefect K a = 0 := by
  let f : Nat → ℚ := Nat.castAddMonoidHom ℚ
  have hf : Function.Injective f := by
    intro m n hmn
    change (m : ℚ) = (n : ℚ) at hmn
    exact_mod_cast hmn
  apply WithTop.map_injective hf
  change defectOrder (K := K) a = (0 : WithTop ℚ)
  exact h

/-- The embedded quadratic-defect order of one is infinite. -/
theorem defectOrder_one : defectOrder (K := K) (1 : Kˣ) = ⊤ := by
  exact defectOrder_eq_top_of_isSquare ⟨1, (one_mul 1).symm⟩

end BONG.GoodBONG

end Bong
