/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeIDefect
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Lemma 7.16: the type-II mixed defect

In type II both length-`s` prefixes are alternating endpoint towers, so their
mixed capped defect is at least `2e`.  The next source pair has a strictly
positive alpha value by the stopping inequality.  Its capped adjacent defect
therefore lies strictly above the Corollary 2.17 threshold, and domination
extends the source prefix by two entries.
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

/-- The full comparison prefix forced by a type-II failure is an alternating
Lemma 7.5 block and hence has capped defect at least `2e`. -/
theorem lemma716_typeII_comparisonPrefixDefect_ge_twoE
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (hsTwo : 2 ≤ s) (hsInterior : s < n + 3) (hsEven : Even s)
    (P : Beli2019Lemma716TypeIIFailureProfile c R s hsTwo hsInterior) :
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
      c.truncatedPrefixDefect c ((-1) ^ (s / 2)) 0 s := by
  let first : Fin (n + 2) := ⟨0, by omega⟩
  let last : Fin (n + 2) := ⟨s - 2, by omega⟩
  have hsegmentEven : Even (last.val - first.val) := by
    rcases hsEven with ⟨d, hd⟩
    exact ⟨d - 1, by simp only [last, first, Nat.sub_zero]; omega⟩
  have hterminal : c.order last.succ =
      (R + 1) - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ =
        (⟨s - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      simp only [last, Fin.val_succ]
      omega
    rw [hindex, P.low]
    ring
  have hcomparisonArithmetic := c.beli2019Lemma75_arithmetic
    first last (R + 1) (Fin.zero_le last) hsegmentEven (by
      change c.order (0 : Fin (n + 3)) = R + 1
      exact P.first) hterminal
  have hexponent :
      (last.val - first.val + 2) / 2 = s / 2 := by
    simp only [last, first, Nat.sub_zero]
    omega
  have hleftLength : first.val = 0 := rfl
  have hrightLength : last.val + 2 = s := by
    simp only [last]
    omega
  have h := hcomparisonArithmetic.defect_ge_two_mul_e
  rw [hexponent] at h
  rw [hleftLength, hrightLength] at h
  exact h

/-- Before the final adjacent pair is attached, the two length-`s` prefixes
have mixed capped defect at least `2e`. -/
theorem lemma716_typeII_baseMixedDefect_ge_twoE
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hsInterior : s < n + 3)
    (P : Beli2019Lemma716TypeIIFailureProfile c R s D.two_le hsInterior) :
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
      a.truncatedPrefixDefect c 1 s s := by
  let theta : Kˣ := (-1) ^ (s / 2)
  have hsourceRaw := a.lemma716_typeI_sourcePrefixDefect_ge_twoE
    R s D hfirst hsecond hthird
  have hsourceSign :
      (-1 : Kˣ) * ((-1) ^ ((s - 2) / 2)) = theta := by
    change (-1 : Kˣ) * ((-1) ^ ((s - 2) / 2)) =
      (-1) ^ (s / 2)
    rcases D.even with ⟨d, hd⟩
    have hsHalf : s / 2 = d := by omega
    have hpreviousHalf : (s - 2) / 2 + 1 = d := by
      have := D.two_le
      omega
    rw [hsHalf]
    calc
      (-1 : Kˣ) * ((-1) ^ ((s - 2) / 2)) =
          ((-1) ^ ((s - 2) / 2)) * (-1) := by ac_rfl
      _ = (-1 : Kˣ) ^ ((s - 2) / 2 + 1) :=
        (pow_succ _ _).symm
      _ = (-1 : Kˣ) ^ d := by rw [hpreviousHalf]
  have hsource :
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
        a.truncatedPrefixDefect a theta 0 s := by
    rw [← hsourceSign]
    exact hsourceRaw
  have hcomparison := c.lemma716_typeII_comparisonPrefixDefect_ge_twoE
    R s D.two_le hsInterior D.even P
  have htheta : theta * theta = 1 := by
    dsimp only [theta]
    rw [← mul_pow]
    simp
  exact mixedPrefixDefect_ge_of_selfPrefixDefects a c
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))
    theta theta 1 s s hsource
    (by simpa only [theta] using hcomparison) htheta

/-- The stopping inequality makes the alpha value at the type-II boundary
strictly positive. -/
theorem lemma716_typeII_boundary_alpha_pos
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hII : Lemma714IsTypeII a R s) (hsNext : s + 2 ≤ n + 3) :
    0 < a.alphaValue ⟨s, by omega⟩ := by
  let current : Fin (n + 2) := ⟨s, by omega⟩
  have hnonnegative := (a.alpha_p2 current).1
  by_contra hnot
  change ¬0 < a.alphaValue current at hnot
  have hzero : a.alphaValue current = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonnegative
  have hgapEq := (a.alpha_p2 current).2.mp hzero
  have hcurrentOrder : a.order current.castSucc = R + 1 := by
    rcases hII with ⟨hsInterior, horder⟩
    have hindex : current.castSucc =
        (⟨s, hsInterior⟩ : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    rw [hindex, horder]
  have hnextOrder := D.at_stop hsNext
  unfold orderGap at hgapEq
  have hnextIndex : current.succ =
      (⟨s + 1, by omega⟩ : Fin (n + 3)) := by
    apply Fin.ext
    rfl
  rw [hnextIndex, hcurrentOrder] at hgapEq
  omega

/-- The final adjacent source pair lies strictly above the type-II central
threshold. -/
theorem lemma716_typeII_adjacentDefect_gt_threshold
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hII : Lemma714IsTypeII a R s) (hsNext : s + 2 ≤ n + 3)
    (P : Beli2019Lemma716TypeIIFailureProfile c R s D.two_le
      (Classical.choose hII)) :
    (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨s - 1, by omega⟩ : ℚ) -
        (a.order ⟨s + 1, by omega⟩ : ℚ) : ℚ)) : WithTop ℚ) <
      a.truncatedPrefixDefect a (-1) s (s + 2) := by
  let current : Fin (n + 2) := ⟨s, by omega⟩
  have halpha := a.lemma716_typeII_boundary_alpha_pos R s D hII hsNext
  have hcurrentOrder : a.order current.castSucc = R + 1 := by
    have hindex : current.castSucc =
        (⟨s, Classical.choose hII⟩ : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    rw [hindex, Classical.choose_spec hII]
  have hthreshold :
      2 * (ramificationIndex K : ℚ) +
          (c.order ⟨s - 1, by omega⟩ : ℚ) -
          (a.order ⟨s + 1, by omega⟩ : ℚ) <
        ((a.order current.castSucc - a.order current.succ : Int) : ℚ) +
          a.alphaValue current := by
    rw [P.low, hcurrentOrder]
    have hcurrentIndex : current = (⟨s, by omega⟩ : Fin (n + 2)) := rfl
    have hnextIndex : current.succ =
        (⟨s + 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    rw [hnextIndex]
    push_cast
    have halpha' : 0 < a.alphaValue current := by
      simpa only [current] using halpha
    linarith
  have hpair := a.order_sub_add_alpha_le_cappedAdjacent current
  have hpair' :
      (((((a.order current.castSucc - a.order current.succ : Int) : ℚ) +
          a.alphaValue current : ℚ)) : WithTop ℚ) ≤
        a.truncatedPrefixDefect a (-1) s (s + 2) := by
    simpa only [current] using hpair
  exact (WithTop.coe_lt_coe.mpr hthreshold).trans_le hpair'

/-- The exact following mixed defect used by Corollary 2.17 in the type-II
branch. -/
theorem lemma716_typeII_currentDefect_gt_threshold
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII a R s) (hsNext : s + 2 ≤ n + 3)
    (P : Beli2019Lemma716TypeIIFailureProfile c R s D.two_le
      (Classical.choose hII)) :
    (((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨s - 1, by omega⟩ : ℚ) -
        (a.order ⟨s + 1, by omega⟩ : ℚ) : ℚ)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) (s + 2) s := by
  let threshold : WithTop ℚ :=
    (((2 * (ramificationIndex K : ℚ) +
      (c.order ⟨s - 1, by omega⟩ : ℚ) -
      (a.order ⟨s + 1, by omega⟩ : ℚ) : ℚ)) : WithTop ℚ)
  have hbaseTwoE := a.lemma716_typeII_baseMixedDefect_ge_twoE
    c R s D hfirst hsecond hthird (Classical.choose hII) P
  have hstop := D.at_stop hsNext
  have hbaseThreshold : threshold < a.truncatedPrefixDefect c 1 s s := by
    apply lt_of_lt_of_le _ hbaseTwoE
    dsimp only [threshold]
    apply WithTop.coe_lt_coe.mpr
    rw [P.low]
    have hlowCast :
        ((R - 2 * (ramificationIndex K : Int) + 1 : Int) : ℚ) =
          (R : ℚ) - 2 * (ramificationIndex K : ℚ) + 1 := by
      push_cast
      ring
    rw [hlowCast]
    have hstopQ :
        (R : ℚ) - 2 * (ramificationIndex K : ℚ) + 1 <
          (a.order ⟨s + 1, by omega⟩ : ℚ) := by
      exact_mod_cast hstop
    linarith
  have hpairThreshold : threshold <
      a.truncatedPrefixDefect a (-1) s (s + 2) := by
    exact a.lemma716_typeII_adjacentDefect_gt_threshold
      c R s D hII hsNext P
  have hdomination := c.truncatedPrefixDefect_domination a a
    1 (-1) s s (s + 2)
  rw [one_mul] at hdomination
  rw [c.truncatedPrefixDefect_comm a 1 s s,
    c.truncatedPrefixDefect_comm a (-1) s (s + 2)] at hdomination
  exact (lt_min hbaseThreshold hpairThreshold).trans_le hdomination

/-- A type-II failure profile activates the central trigger at paper index
`s + 1`. -/
theorem lemma716_typeII_failureProfile_alphaTrigger
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (horder : a.RepresentationOrderCondition c le_rfl)
    (hdefect : a.RepresentationDefectCondition c)
    (hII : Lemma714IsTypeII a R s) (hsNext : s + 2 ≤ n + 3)
    (P : Beli2019Lemma716TypeIIFailureProfile c R s D.two_le
      (Classical.choose hII)) :
    a.centralAlphaTrigger c
      { val := s + 1
        one_lt := by have := D.two_le; omega
        lt_large := by omega
        le_small_succ := by omega } := by
  let i : CentralRepresentationIndex (n + 3) (n + 3) :=
    { val := s + 1
      one_lt := by have := D.two_le; omega
      lt_large := by omega
      le_small_succ := by omega }
  have hcross : c.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ < a.order ⟨i.val, i.lt_large⟩ := by
    change c.order ⟨s - 1, by omega⟩ < a.order ⟨s + 1, by omega⟩
    rw [P.low]
    exact D.at_stop hsNext
  have hlarge := a.lemma716_typeII_currentDefect_gt_threshold
    c R s D hfirst hsecond hthird hII hsNext P
  have htrigger := a.beli2019Corollary217_of_currentDefect c le_rfl
    horder hdefect i hcross (by
      change (((2 * (ramificationIndex K : ℚ) +
          (c.order ⟨s - 1, by omega⟩ : ℚ) -
          (a.order ⟨s + 1, by omega⟩ : ℚ) : ℚ)) : WithTop ℚ) <
        a.centralCurrentDefect c i
      change _ < a.truncatedPrefixDefect c (-1) (s + 2) s
      exact hlarge)
  simpa only [i] using htrigger

end BONG.GoodBONG

end Bong
