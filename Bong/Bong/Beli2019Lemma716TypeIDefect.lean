/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716OrderFailure
import Bong.Bong.Beli2019Lemma716DefectComposition
import Bong.Bong.Beli2019Lemma75Arithmetic
import Bong.Bong.Beli2019Corollary217

/-!
# Beli (2019), Lemma 7.16: the type-I mixed defect

The source prefix is the concatenation of the initial critical binary block
and the alternating block beginning at the third coefficient.  A type-I
failure profile gives a second alternating block in the comparison lattice.
Lemma 7.5 supplies a capped defect of at least `2e` for every block, and the
composition lemmas turn these into the mixed defect used in Corollary 2.17.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]

/-- The source prefix through paper index `s` has capped defect at least
`2e`.  Its sign is written as the product of the initial binary sign and
the sign of the later alternating block. -/
theorem lemma716_typeI_sourcePrefixDefect_ge_twoE
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩) :
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
      a.truncatedPrefixDefect a
        ((-1) * ((-1) ^ ((s - 2) / 2))) 0 s := by
  let first : Fin (n + 2) := ⟨0, by omega⟩
  have hinitialArithmetic := a.beli2019Lemma75_arithmetic
    first first R (le_rfl) (by simp) (by
      change a.order (0 : Fin (n + 3)) = R
      exact hfirst) (by
      change a.order (1 : Fin (n + 3)) =
        R - 2 * (ramificationIndex K : Int)
      exact hsecond)
  have hinitial :
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
        a.truncatedPrefixDefect a (-1) 0 2 := by
    simpa only [first, Fin.val_mk, Nat.zero_sub, zero_add,
      Nat.reduceDiv, pow_one] using
        hinitialArithmetic.defect_ge_two_mul_e
  by_cases hs : s = 2
  · simpa only [hs, Nat.reduceSub, Nat.zero_div, pow_zero, mul_one] using
      hinitial
  · have hsFour : 4 ≤ s := by
      have hsTwo := D.two_le
      rcases D.even with ⟨d, hd⟩
      omega
    have hsRank := D.le_rank
    let left : Fin (n + 2) := ⟨2, by omega⟩
    let right : Fin (n + 2) := ⟨s - 2, by omega⟩
    have hrightEven : Even (right.val - left.val) := by
      rcases D.even with ⟨d, hd⟩
      exact ⟨d - 2, by simp only [right, left]; omega⟩
    have hplateau := a.beli2019Lemma714_i R s
      D.toLemma714MinimalityData hsFour hthird
    have hleftOrder : a.order left.castSucc = R + 1 := by
      simpa only [left, Fin.castSucc_mk] using
        hplateau.high_positions 2 (by omega) (by omega) (by simp)
    have hrightOrder : a.order right.succ =
        R + 1 - 2 * (ramificationIndex K : Int) := by
      have h := hplateau.low_positions (s - 1) (by omega) (by omega) (by
        rcases D.even with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩)
      have hindex : right.succ =
          (⟨s - 1, by omega⟩ : Fin (n + 3)) := by
        apply Fin.ext
        simp only [right, Fin.val_succ]
        omega
      rw [hindex, h]
      ring
    have hleftRight : left ≤ right := by
      change 2 ≤ s - 2
      omega
    have htailArithmetic := a.beli2019Lemma75_arithmetic
      left right (R + 1) hleftRight
        hrightEven hleftOrder hrightOrder
    have htail :
        (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
          a.truncatedPrefixDefect a
            ((-1) ^ ((s - 2) / 2)) 2 s := by
      have hexponent :
          (right.val - left.val + 2) / 2 = (s - 2) / 2 := by
        simp only [right, left]
        omega
      have hleftLength : left.val = 2 := rfl
      have hrightLength : right.val + 2 = s := by
        simp only [right]
        omega
      have h := htailArithmetic.defect_ge_two_mul_e
      rw [hexponent] at h
      rw [hleftLength, hrightLength] at h
      exact h
    exact a.selfPrefixDefect_ge_of_split
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))
      (-1) ((-1) ^ ((s - 2) / 2))
      ((-1) * ((-1) ^ ((s - 2) / 2))) 2 s
      hinitial htail rfl

/-- The comparison prefix forced by a type-I failure has capped defect at
least `2e`; for `s = 2` the prefix is empty and the statement is the
endpoint convention `d[1] = ∞`. -/
theorem lemma716_typeI_comparisonPrefixDefect_ge_twoE
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (hsTwo : 2 ≤ s) (hsRank : s ≤ n + 3) (hsEven : Even s)
    (P : Beli2019Lemma716TypeIFailureProfile c R s hsTwo hsRank) :
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
      c.truncatedPrefixDefect c
        ((-1) ^ ((s - 2) / 2)) 0 (s - 2) := by
  by_cases hs : s = 2
  · subst s
    simp [truncatedPrefixDefect, GoodBONG.prefixProduct, defectOrder_one]
  · have hsFour : 4 ≤ s := by
      rcases hsEven with ⟨d, hd⟩
      omega
    let first : Fin (n + 2) := ⟨0, by omega⟩
    let last : Fin (n + 2) := ⟨s - 4, by omega⟩
    have hsegmentEven : Even (last.val - first.val) := by
      rcases hsEven with ⟨d, hd⟩
      exact ⟨d - 2, by simp only [last, first, Nat.sub_zero]; omega⟩
    have hterminal : c.order last.succ =
        (R + 1) - 2 * (ramificationIndex K : Int) := by
      have hlow := P.low (by omega)
      have hindex : last.succ = (⟨s - 3, by omega⟩ : Fin (n + 3)) := by
        apply Fin.ext
        simp only [last, Fin.val_succ]
        omega
      rw [hindex, hlow]
      ring
    have hcomparisonArithmetic := c.beli2019Lemma75_arithmetic
      first last (R + 1) (Fin.zero_le last)
        hsegmentEven (by
          change c.order (0 : Fin (n + 3)) = R + 1
          exact P.first)
        hterminal
    have hexponent :
        (last.val - first.val + 2) / 2 = (s - 2) / 2 := by
      simp only [last, first, Nat.sub_zero]
      omega
    have hleftLength : first.val = 0 := rfl
    have hrightLength : last.val + 2 = s - 2 := by
      simp only [last]
      omega
    have h := hcomparisonArithmetic.defect_ge_two_mul_e
    rw [hexponent] at h
    rw [hleftLength, hrightLength] at h
    exact h

/-- The exact mixed-defect estimate printed in the type-I part of the
proof of Lemma 7.16. -/
theorem lemma716_typeI_mixedPrefixDefect_ge_twoE
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (P : Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank) :
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
      a.truncatedPrefixDefect c (-1) s (s - 2) := by
  let theta : Kˣ := (-1) ^ ((s - 2) / 2)
  have hsource := a.lemma716_typeI_sourcePrefixDefect_ge_twoE
    R s D hfirst hsecond hthird
  have hcomparison := c.lemma716_typeI_comparisonPrefixDefect_ge_twoE
    R s D.two_le D.le_rank D.even P
  have htheta : theta * theta = 1 := by
    dsimp only [theta]
    rw [← mul_pow]
    simp
  have hsign : ((-1) * theta) * theta = (-1 : Kˣ) := by
    calc
      ((-1) * theta) * theta = (-1) * (theta * theta) := by ac_rfl
      _ = (-1 : Kˣ) := by rw [htheta]; simp
  exact mixedPrefixDefect_ge_of_selfPrefixDefects a c
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))
    ((-1) * theta) theta (-1) s (s - 2)
    (by simpa only [theta] using hsource)
    (by simpa only [theta] using hcomparison) hsign

/-- The type-I mixed defect is strictly above the Corollary 2.17 threshold:
the next source order is at least `R + 2`, whereas the last high comparison
order is `R + 1`. -/
theorem lemma716_typeI_previousDefect_gt_threshold
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI a R s) (hsInterior : s < n + 3)
    (P : Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank) :
    (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨s - 2, by omega⟩ : ℚ) -
        (a.order ⟨s, hsInterior⟩ : ℚ) : ℚ)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) s (s - 2) := by
  have hmixed := a.lemma716_typeI_mixedPrefixDefect_ge_twoE
    c R s D hfirst hsecond hthird P
  have hnext := a.lemma714_typeI_nextOrder_ge R s hI hsInterior
  have hnextQ : (R : ℚ) + 2 ≤ (a.order ⟨s, hsInterior⟩ : ℚ) := by
    exact_mod_cast hnext
  have hhigh : c.order ⟨s - 2, by omega⟩ = R + 1 := P.high
  have hthreshold :
      2 * (ramificationIndex K : ℚ) +
          (c.order ⟨s - 2, by omega⟩ : ℚ) -
          (a.order ⟨s, hsInterior⟩ : ℚ) <
        2 * (ramificationIndex K : ℚ) := by
    rw [hhigh]
    push_cast
    linarith
  exact (WithTop.coe_lt_coe.mpr hthreshold).trans_le hmixed

/-- A type-I failure profile activates the precise central trigger used by
condition 2.1(iii).  This is the formal Corollary 2.17 step in the paper. -/
theorem lemma716_typeI_failureProfile_alphaTrigger
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (horder : a.RepresentationOrderCondition c le_rfl)
    (hdefect : a.RepresentationDefectCondition c)
    (hI : Lemma714IsTypeI a R s) (hsInterior : s < n + 3)
    (P : Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank) :
    a.centralAlphaTrigger c
      { val := s
        one_lt := by have := D.two_le; omega
        lt_large := hsInterior
        le_small_succ := by omega } := by
  let i : CentralRepresentationIndex (n + 3) (n + 3) :=
    { val := s
      one_lt := by have := D.two_le; omega
      lt_large := hsInterior
      le_small_succ := by omega }
  have hnext := a.lemma714_typeI_nextOrder_ge R s hI hsInterior
  have hcross : c.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ < a.order ⟨i.val, i.lt_large⟩ := by
    change c.order ⟨s - 2, by omega⟩ < a.order ⟨s, hsInterior⟩
    rw [P.high]
    omega
  have hlarge := a.lemma716_typeI_previousDefect_gt_threshold
    c R s D hfirst hsecond hthird hI hsInterior P
  have htrigger := a.beli2019Corollary217_of_previousDefect c le_rfl
    horder hdefect i hcross (by
      change (((2 * (ramificationIndex K : ℚ) +
          (c.order ⟨s - 2, by omega⟩ : ℚ) -
          (a.order ⟨s, hsInterior⟩ : ℚ) : ℚ)) : WithTop ℚ) <
        a.centralPreviousDefect c i
      change _ < a.truncatedPrefixDefect c (-1) s (s - 2)
      exact hlarge)
  simpa only [i] using htrigger

end BONG.GoodBONG

end Bong
