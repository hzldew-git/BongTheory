/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DefectArithmetic

/-!
# Beli (2019), Lemma 1.3

This file proves the three min-replacement forms of Lemma 1.3 for the
embedded quadratic-defect order.  Keeping the value `top` is important:
square factors are covered without a separate finiteness hypothesis.
-/

namespace Bong

open Dyadic

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A rational offset added to an embedded quadratic-defect order. -/
noncomputable def shiftedDefect (x : ℚ) (a : Kˣ) : WithTop ℚ :=
  (x : WithTop ℚ) + defectOrder (K := K) a

/-- Lemma 1.3(a): strict separation of the offsets permits replacement of
`d(b)` by `d(ab)` under the outer minimum. -/
theorem shiftedDefect_min_eq_mul_of_lt
    (x y : ℚ) (z : WithTop ℚ) (a b : Kˣ) (hxy : x < y)
    (hbound : min (shiftedDefect (K := K) y b) z ≤
      shiftedDefect (K := K) x a) :
    min (shiftedDefect (K := K) y b) z =
      min (shiftedDefect (K := K) y (a * b)) z := by
  simp only [shiftedDefect] at hbound ⊢
  have hxy' : (x : WithTop ℚ) < (y : WithTop ℚ) := by
    exact_mod_cast hxy
  rcases lt_trichotomy (defectOrder (K := K) a)
      (defectOrder (K := K) b) with hab | heq | hba
  · rw [defectOrder_mul_eq_left_of_lt_right hab]
    have hxa_ne : defectOrder (K := K) a ≠ ⊤ := hab.ne_top
    have hxyA : (x : WithTop ℚ) + defectOrder (K := K) a <
        (y : WithTop ℚ) + defectOrder (K := K) a := by
      exact WithTop.add_lt_add_right hxa_ne hxy'
    have hyAB : (y : WithTop ℚ) + defectOrder (K := K) a <
        (y : WithTop ℚ) + defectOrder (K := K) b := by
      exact WithTop.add_lt_add_left WithTop.coe_ne_top hab
    have hmin_lt :
        min ((y : WithTop ℚ) + defectOrder (K := K) b) z <
          (y : WithTop ℚ) + defectOrder (K := K) b :=
      hbound.trans_lt (hxyA.trans hyAB)
    have hzlt : z < (y : WithTop ℚ) + defectOrder (K := K) b := by
      simpa only [min_lt_iff, lt_self_iff_false, false_or] using hmin_lt
    have hzle : z ≤ (x : WithTop ℚ) + defectOrder (K := K) a := by
      simpa only [min_eq_right hzlt.le] using hbound
    rw [min_eq_right hzlt.le]
    exact (min_eq_right (hzle.trans hxyA.le)).symm
  · have hdom := defectOrder_mul_ge_min (K := K) a b
    by_cases htop : defectOrder (K := K) a = ⊤
    · have hbtop : defectOrder (K := K) b = ⊤ := by
        rw [← heq, htop]
      have habtop : defectOrder (K := K) (a * b) = ⊤ := by
        apply top_unique
        simpa only [htop, hbtop, min_self] using hdom
      simp [hbtop, habtop]
    · have hxyA : (x : WithTop ℚ) + defectOrder (K := K) a <
          (y : WithTop ℚ) + defectOrder (K := K) a := by
        exact WithTop.add_lt_add_right htop hxy'
      rw [← heq] at hbound
      have hmin_lt :
          min ((y : WithTop ℚ) + defectOrder (K := K) a) z <
            (y : WithTop ℚ) + defectOrder (K := K) a :=
        hbound.trans_lt hxyA
      have hzlt : z < (y : WithTop ℚ) + defectOrder (K := K) a := by
        simpa only [min_lt_iff, lt_self_iff_false, false_or] using hmin_lt
      have hdefect : defectOrder (K := K) a ≤
          defectOrder (K := K) (a * b) := by
        simpa only [heq, min_self] using hdom
      have hshift : (y : WithTop ℚ) + defectOrder (K := K) a ≤
          (y : WithTop ℚ) + defectOrder (K := K) (a * b) := by
        simpa only [add_comm] using
          add_le_add_left hdefect (y : WithTop ℚ)
      rw [← heq, min_eq_right hzlt.le]
      exact (min_eq_right (hzlt.le.trans hshift)).symm
  · rw [defectOrder_mul_eq_right_of_lt_left hba]

/-- Lemma 1.3(b): the weak offset inequality is compensated by a strict
inequality against the outer minimum. -/
theorem shiftedDefect_min_eq_mul_of_le
    (x y : ℚ) (z : WithTop ℚ) (a b : Kˣ) (hxy : x ≤ y)
    (hbound : min (shiftedDefect (K := K) y b) z <
      shiftedDefect (K := K) x a) :
    min (shiftedDefect (K := K) y b) z =
      min (shiftedDefect (K := K) y (a * b)) z := by
  simp only [shiftedDefect] at hbound ⊢
  have hxy' : (x : WithTop ℚ) ≤ (y : WithTop ℚ) := by
    exact_mod_cast hxy
  rcases lt_trichotomy (defectOrder (K := K) a)
      (defectOrder (K := K) b) with hab | heq | hba
  · rw [defectOrder_mul_eq_left_of_lt_right hab]
    have hxyA : (x : WithTop ℚ) + defectOrder (K := K) a ≤
        (y : WithTop ℚ) + defectOrder (K := K) a := by
      simpa only [add_comm] using
        add_le_add_right hxy' (defectOrder (K := K) a)
    have hyAB : (y : WithTop ℚ) + defectOrder (K := K) a <
        (y : WithTop ℚ) + defectOrder (K := K) b := by
      exact WithTop.add_lt_add_left WithTop.coe_ne_top hab
    have hmin_lt :
        min ((y : WithTop ℚ) + defectOrder (K := K) b) z <
          (y : WithTop ℚ) + defectOrder (K := K) b :=
      (hbound.trans_le hxyA).trans hyAB
    have hzlt : z < (y : WithTop ℚ) + defectOrder (K := K) b := by
      simpa only [min_lt_iff, lt_self_iff_false, false_or] using hmin_lt
    have hzltA : z < (x : WithTop ℚ) + defectOrder (K := K) a := by
      simpa only [min_eq_right hzlt.le] using hbound
    rw [min_eq_right hzlt.le]
    exact (min_eq_right (hzltA.le.trans hxyA)).symm
  · have hdom := defectOrder_mul_ge_min (K := K) a b
    by_cases htop : defectOrder (K := K) a = ⊤
    · have hbtop : defectOrder (K := K) b = ⊤ := by
        rw [← heq, htop]
      have habtop : defectOrder (K := K) (a * b) = ⊤ := by
        apply top_unique
        simpa only [htop, hbtop, min_self] using hdom
      simp [hbtop, habtop]
    · rw [← heq] at hbound
      have hxyA : (x : WithTop ℚ) + defectOrder (K := K) a ≤
          (y : WithTop ℚ) + defectOrder (K := K) a := by
        simpa only [add_comm] using
          add_le_add_right hxy' (defectOrder (K := K) a)
      have hmin_lt :
          min ((y : WithTop ℚ) + defectOrder (K := K) a) z <
            (y : WithTop ℚ) + defectOrder (K := K) a :=
        hbound.trans_le hxyA
      have hzlt : z < (y : WithTop ℚ) + defectOrder (K := K) a := by
        simpa only [min_lt_iff, lt_self_iff_false, false_or] using hmin_lt
      have hdefect : defectOrder (K := K) a ≤
          defectOrder (K := K) (a * b) := by
        simpa only [heq, min_self] using hdom
      have hshift : (y : WithTop ℚ) + defectOrder (K := K) a ≤
          (y : WithTop ℚ) + defectOrder (K := K) (a * b) := by
        simpa only [add_comm] using
          add_le_add_left hdefect (y : WithTop ℚ)
      rw [← heq, min_eq_right hzlt.le]
      exact (min_eq_right (hzlt.le.trans hshift)).symm
  · rw [defectOrder_mul_eq_right_of_lt_left hba]

/-- Lemma 1.3(c): once `z` is below the shifted defect of `a`, the
replacement follows directly from domination. -/
theorem shiftedDefect_min_eq_mul_of_cut_le
    (y : ℚ) (z : WithTop ℚ) (a b : Kˣ)
    (hcut : z ≤ shiftedDefect (K := K) y a) :
    min (shiftedDefect (K := K) y b) z =
      min (shiftedDefect (K := K) y (a * b)) z := by
  simp only [shiftedDefect] at hcut ⊢
  rcases lt_trichotomy (defectOrder (K := K) a)
      (defectOrder (K := K) b) with hab | heq | hba
  · rw [defectOrder_mul_eq_left_of_lt_right hab]
    have hshift : (y : WithTop ℚ) + defectOrder (K := K) a ≤
        (y : WithTop ℚ) + defectOrder (K := K) b := by
      simpa only [add_comm] using
        add_le_add_left hab.le (y : WithTop ℚ)
    rw [min_eq_right (hcut.trans hshift), min_eq_right hcut]
  · have hdom := defectOrder_mul_ge_min (K := K) a b
    have hdefect : defectOrder (K := K) a ≤
        defectOrder (K := K) (a * b) := by
      simpa only [heq, min_self] using hdom
    have hshift : (y : WithTop ℚ) + defectOrder (K := K) a ≤
        (y : WithTop ℚ) + defectOrder (K := K) (a * b) := by
      simpa only [add_comm] using
        add_le_add_left hdefect (y : WithTop ℚ)
    rw [← heq, min_eq_right hcut, min_eq_right (hcut.trans hshift)]
  · rw [defectOrder_mul_eq_right_of_lt_left hba]

/-- Beli (2019), Lemma 1.3, packaged as its three alternatives. -/
theorem beli2019Lemma13
    (x y : ℚ) (z : WithTop ℚ) (a b : Kˣ)
    (hcase :
      (x < y ∧ min (shiftedDefect (K := K) y b) z ≤
        shiftedDefect (K := K) x a) ∨
      (x ≤ y ∧ min (shiftedDefect (K := K) y b) z <
        shiftedDefect (K := K) x a) ∨
      z ≤ shiftedDefect (K := K) y a) :
    min (shiftedDefect (K := K) y b) z =
      min (shiftedDefect (K := K) y (a * b)) z := by
  rcases hcase with ⟨hxy, hbound⟩ | ⟨hxy, hbound⟩ | hcut
  · exact shiftedDefect_min_eq_mul_of_lt x y z a b hxy hbound
  · exact shiftedDefect_min_eq_mul_of_le x y z a b hxy hbound
  · exact shiftedDefect_min_eq_mul_of_cut_le y z a b hcut

end BONG.GoodBONG

end Bong
