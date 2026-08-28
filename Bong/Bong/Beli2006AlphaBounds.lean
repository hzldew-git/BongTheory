/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaProperties
import Bong.Bong.Beli2006SectionTwo
import Bong.Bong.DefectArithmetic

/-!
# Beli (2006), elementary bounds for the alpha candidates

This file proves the common order and defect estimates used in properties
P2--P5.  The only arithmetic input is the binary admissibility of every
adjacent pair of a BONG.  In particular, no classification theorem or Jordan
decomposition is used here.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- Defect orders are nonnegative. -/
theorem defectOrder_nonneg_for_alpha (x : Kˣ) :
    (0 : WithTop ℚ) ≤ defectOrder (K := K) x := by
  by_cases htop : quadraticDefect K x = ⊤
  · unfold defectOrder
    rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    unfold defectOrder
    rw [← hd]
    change (0 : WithTop ℚ) ≤ ((d : ℚ) : WithTop ℚ)
    exact_mod_cast Nat.zero_le d

/-- The order form `ord(a) + d(a) ≥ 0` follows from an integral absolute
quadratic defect. -/
theorem nonneg_ordUnit_add_defectOrder_of_absolute
    (a : Kˣ) (h : HasNonnegativeAbsoluteQuadraticDefect a) :
    (0 : WithTop ℚ) ≤
      (((ordUnit K a : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K) a := by
  have hthreshold :=
    (hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le a).1 h
  by_cases htop : quadraticDefect K a = ⊤
  · have hdefect : defectOrder (K := K) a = ⊤ := by
      unfold defectOrder
      rw [htop]
      rfl
    rw [hdefect]
    simp
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    have hthresholdNat : absoluteDefectThreshold a ≤ d := by
      rw [← hd] at hthreshold
      exact WithTop.coe_le_coe.mp hthreshold
    have hsumInt : 0 ≤ ordUnit K a + (d : Int) := by
      by_cases horder : 0 ≤ ordUnit K a
      · omega
      · have horderNeg : ordUnit K a < 0 := lt_of_not_ge horder
        have hthresholdInt :=
          coe_absoluteDefectThreshold_eq_neg_of_neg horderNeg
        have hthresholdIntLe :
            (absoluteDefectThreshold a : Int) ≤ (d : Int) := by
          exact_mod_cast hthresholdNat
        omega
    have hdefect : defectOrder (K := K) a = (d : WithTop ℚ) := by
      unfold defectOrder
      rw [← hd]
      rfl
    rw [hdefect]
    exact_mod_cast hsumInt

/-- Operational binary admissibility supplies integral absolute defect for
the negative parameter. -/
theorem hasAbsoluteDefect_neg_of_admissible
    {a : Kˣ} (ha : IsBinaryParameterAdmissible a) :
    HasNonnegativeAbsoluteQuadraticDefect (-a) := by
  rw [hasNonnegativeAbsoluteQuadraticDefect_iff_exists_sub_sq_mem]
  rcases ha with ⟨c, _htwo, hdiag⟩
  refine ⟨c, ?_⟩
  have heq : (((-a : Kˣ) : K) - c ^ 2) =
      -(c ^ 2 + (a : K)) := by
    simp only [Units.val_neg]
    ring
  rw [heq]
  exact (IntegerRing K).neg_mem _ hdiag

/-- The adjacent product is the negative adjacent parameter times a square.
This is the square-class identity that lets binary admissibility control the
defect appearing in `alpha`. -/
theorem adjacentProduct_eq_neg_adjacentParameter_mul_square
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.adjacentProduct i =
      (-b.toBONG.adjacentParameter i.castSucc
          (Nat.add_lt_add_right i.isLt 1)) *
        b.valueUnit i.castSucc ^ 2 := by
  unfold adjacentProduct BONG.adjacentParameter
  have hnext :
      (⟨i.castSucc.val + 1, Nat.add_lt_add_right i.isLt 1⟩ :
        Fin (n + 1)) = i.succ := by
    apply Fin.ext
    rfl
  rw [hnext]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val]
  simp only [GoodBONG.valueUnit]
  field_simp [Units.ne_zero (b.valueUnit i.castSucc)]

/-- Every adjacent BONG pair satisfies Beli's local inequality
`0 ≤ R_{i+1} - R_i + d(-a_i a_{i+1})`. -/
theorem zero_le_orderGap_add_adjacentDefect
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (0 : WithTop ℚ) ≤
      (((b.orderGap i : Int) : ℚ) : WithTop ℚ) +
        b.adjacentDefect i := by
  let hi : i.castSucc.val + 1 < n + 1 :=
    Nat.add_lt_add_right i.isLt 1
  let parameter := b.toBONG.adjacentParameter i.castSucc hi
  have hadmissible : IsBinaryParameterAdmissible parameter :=
    b.toBONG.adjacentParameter_isBinaryParameterAdmissible i.castSucc hi
  have habsolute : HasNonnegativeAbsoluteQuadraticDefect (-parameter) :=
    hasAbsoluteDefect_neg_of_admissible hadmissible
  have hlocal :=
    nonneg_ordUnit_add_defectOrder_of_absolute (-parameter) habsolute
  have horder : ordUnit K (-parameter) = b.orderGap i := by
    rw [ordUnit_neg, b.toBONG.ordUnit_adjacentParameter i.castSucc hi]
    rfl
  have hdefect : defectOrder (K := K) (-parameter) =
      b.adjacentDefect i := by
    unfold adjacentDefect
    rw [b.adjacentProduct_eq_neg_adjacentParameter_mul_square i,
      defectOrder_mul_square]
  rwa [horder, hdefect] at hlocal

/-- Iteration of the defining two-step inequality of a good BONG. -/
theorem order_le_add_two_mul
    (b : GoodBONG q L (n + 1)) (p d : Nat)
    (hpd : p + 2 * d < n + 1) :
    b.order ⟨p, by omega⟩ ≤ b.order ⟨p + 2 * d, hpd⟩ := by
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      have hprevious : p + 2 * d < n + 1 := by omega
      have hstep := b.good ⟨p + 2 * d, hprevious⟩ (by omega)
      change b.order ⟨p + 2 * d, hprevious⟩ ≤
        b.order ⟨p + 2 * d + 2, by omega⟩ at hstep
      have hindex : p + 2 * d + 2 = p + 2 * Nat.succ d := by omega
      have hstep' :
          b.order ⟨p + 2 * d, hprevious⟩ ≤
            b.order ⟨p + 2 * Nat.succ d, hpd⟩ := by
        have htarget :
            (⟨p + 2 * d + 2, by omega⟩ : Fin (n + 1)) =
              ⟨p + 2 * Nat.succ d, hpd⟩ := by
          apply Fin.ext
          exact hindex
        rwa [htarget] at hstep
      exact (ih hprevious).trans hstep'

/-- Orders at two positions of the same parity are monotone. -/
theorem order_le_of_le_of_even_sub
    (b : GoodBONG q L (n + 1)) (i j : Fin (n + 1))
    (hij : i.val ≤ j.val) (heven : Even (j.val - i.val)) :
    b.order i ≤ b.order j := by
  rcases heven with ⟨d, hd⟩
  have hj : j.val = i.val + 2 * d := by omega
  have h := b.order_le_add_two_mul i.val d (by omega)
  have hleft : (⟨i.val, by omega⟩ : Fin (n + 1)) = i := by
    apply Fin.ext
    rfl
  have hright :
      (⟨i.val + 2 * d, by omega⟩ : Fin (n + 1)) = j := by
    apply Fin.ext
    exact hj.symm
  simpa only [hleft, hright] using h

/-- Every left defect candidate is at least the current order gap. -/
theorem orderGapTop_le_leftDefectCandidate
    (b : GoodBONG q L (n + 1)) (i j : Fin n) (hji : j ≤ i) :
    (((b.orderGap i : Int) : ℚ) : WithTop ℚ) ≤
      b.leftDefectCandidate i j := by
  have hdefect :=
    defectOrder_nonneg_for_alpha (K := K) (b.adjacentProduct j)
  have hlocal := b.zero_le_orderGap_add_adjacentDefect j
  have hoffset :
      (0 : WithTop ℚ) ≤
        (((b.order i.castSucc - b.order j.castSucc : Int) : ℚ) :
          WithTop ℚ) + b.adjacentDefect j := by
    rcases Nat.even_or_odd (i.val - j.val) with heven | hodd
    · have horder := b.order_le_of_le_of_even_sub j.castSucc i.castSucc
          (by exact hji) (by simpa using heven)
      have hcoeff :
          (0 : WithTop ℚ) ≤
            (((b.order i.castSucc - b.order j.castSucc : Int) : ℚ) :
              WithTop ℚ) := by
        exact_mod_cast (sub_nonneg.mpr horder)
      exact add_nonneg hcoeff hdefect
    · rcases hodd with ⟨d, hd⟩
      have hevenNext : Even (i.val - (j.val + 1)) := by
        refine ⟨d, ?_⟩
        omega
      have hnextLe : j.succ ≤ i.castSucc := by
        change j.val + 1 ≤ i.val
        omega
      have horder := b.order_le_of_le_of_even_sub j.succ i.castSucc
        hnextLe (by simpa using hevenNext)
      have hdiff :
          (0 : WithTop ℚ) ≤
            (((b.order i.castSucc - b.order j.succ : Int) : ℚ) :
              WithTop ℚ) := by
        exact_mod_cast (sub_nonneg.mpr horder)
      have hadd := add_le_add_left hlocal
        ((((b.order i.castSucc - b.order j.succ : Int) : ℚ) :
          WithTop ℚ))
      have hcast :
          (((b.order i.castSucc - b.order j.castSucc : Int) : ℚ) :
              WithTop ℚ) =
            (((b.orderGap j : Int) : ℚ) : WithTop ℚ) +
              (((b.order i.castSucc - b.order j.succ : Int) : ℚ) :
                WithTop ℚ) := by
        norm_cast
        unfold orderGap
        push_cast
        ring
      calc
        (0 : WithTop ℚ) ≤
            0 + (((b.order i.castSucc - b.order j.succ : Int) : ℚ) :
              WithTop ℚ) := by simpa using hdiff
        _ ≤ ((((b.orderGap j : Int) : ℚ) : WithTop ℚ) +
              b.adjacentDefect j) +
            (((b.order i.castSucc - b.order j.succ : Int) : ℚ) :
              WithTop ℚ) := hadd
        _ = (((b.order i.castSucc - b.order j.castSucc : Int) : ℚ) :
              WithTop ℚ) + b.adjacentDefect j := by
          rw [hcast]
          ac_rfl
  unfold leftDefectCandidate orderGap
  have hcast :
      (((b.order i.succ - b.order j.castSucc : Int) : ℚ) :
          WithTop ℚ) =
        (((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
            WithTop ℚ) +
          (((b.order i.castSucc - b.order j.castSucc : Int) : ℚ) :
            WithTop ℚ) := by
    norm_cast
    push_cast
    ring
  calc
    (((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
        WithTop ℚ) =
        (((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) + 0 := by simp
    _ ≤ (((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) +
        ((((b.order i.castSucc - b.order j.castSucc : Int) : ℚ) :
            WithTop ℚ) + b.adjacentDefect j) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hoffset
            ((((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
              WithTop ℚ))
    _ = (((b.order i.succ - b.order j.castSucc : Int) : ℚ) :
          WithTop ℚ) + b.adjacentDefect j := by
      rw [hcast]
      ac_rfl

/-- Every right defect candidate is at least the current order gap. -/
theorem orderGapTop_le_rightDefectCandidate
    (b : GoodBONG q L (n + 1)) (i j : Fin n) (hij : i ≤ j) :
    (((b.orderGap i : Int) : ℚ) : WithTop ℚ) ≤
      b.rightDefectCandidate i j := by
  have hdefect :=
    defectOrder_nonneg_for_alpha (K := K) (b.adjacentProduct j)
  have hlocal := b.zero_le_orderGap_add_adjacentDefect j
  have hoffset :
      (0 : WithTop ℚ) ≤
        (((b.order j.succ - b.order i.succ : Int) : ℚ) :
          WithTop ℚ) + b.adjacentDefect j := by
    rcases Nat.even_or_odd (j.val - i.val) with heven | hodd
    · have horder := b.order_le_of_le_of_even_sub i.succ j.succ
          (by
            change i.val + 1 ≤ j.val + 1
            omega) (by simpa using heven)
      have hcoeff :
          (0 : WithTop ℚ) ≤
            (((b.order j.succ - b.order i.succ : Int) : ℚ) :
              WithTop ℚ) := by
        exact_mod_cast (sub_nonneg.mpr horder)
      exact add_nonneg hcoeff hdefect
    · rcases hodd with ⟨d, hd⟩
      have hevenPrevious : Even (j.val - (i.val + 1)) := by
        refine ⟨d, ?_⟩
        omega
      have hnextLe : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        omega
      have horder := b.order_le_of_le_of_even_sub i.succ j.castSucc
        hnextLe (by simpa using hevenPrevious)
      have hdiff :
          (0 : WithTop ℚ) ≤
            (((b.order j.castSucc - b.order i.succ : Int) : ℚ) :
              WithTop ℚ) := by
        exact_mod_cast (sub_nonneg.mpr horder)
      have hadd := add_le_add_left hlocal
        ((((b.order j.castSucc - b.order i.succ : Int) : ℚ) :
          WithTop ℚ))
      have hcast :
          (((b.order j.succ - b.order i.succ : Int) : ℚ) :
              WithTop ℚ) =
            (((b.orderGap j : Int) : ℚ) : WithTop ℚ) +
              (((b.order j.castSucc - b.order i.succ : Int) : ℚ) :
                WithTop ℚ) := by
        norm_cast
        unfold orderGap
        push_cast
        ring
      calc
        (0 : WithTop ℚ) ≤
            0 + (((b.order j.castSucc - b.order i.succ : Int) : ℚ) :
              WithTop ℚ) := by simpa using hdiff
        _ ≤ ((((b.orderGap j : Int) : ℚ) : WithTop ℚ) +
              b.adjacentDefect j) +
            (((b.order j.castSucc - b.order i.succ : Int) : ℚ) :
              WithTop ℚ) := hadd
        _ = (((b.order j.succ - b.order i.succ : Int) : ℚ) :
              WithTop ℚ) + b.adjacentDefect j := by
          rw [hcast]
          ac_rfl
  unfold rightDefectCandidate orderGap
  have hcast :
      (((b.order j.succ - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) =
        (((b.order j.succ - b.order i.succ : Int) : ℚ) :
            WithTop ℚ) +
          (((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
            WithTop ℚ) := by
    norm_cast
    push_cast
    ring
  calc
    (((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
        WithTop ℚ) =
        0 + (((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) := by simp
    _ ≤ ((((b.order j.succ - b.order i.succ : Int) : ℚ) :
            WithTop ℚ) + b.adjacentDefect j) +
          (((b.order i.succ - b.order i.castSucc : Int) : ℚ) :
            WithTop ℚ) := by
      exact add_le_add_left hoffset _
    _ = (((b.order j.succ - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) + b.adjacentDefect j := by
      rw [hcast]
      ac_rfl

/-- Binary admissibility gives the universal lower endpoint
`-2e ≤ R_{i+1} - R_i`. -/
theorem orderGap_ge_neg_two_mul_e_for_properties
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    -(2 * (ramificationIndex K : Int)) ≤ b.orderGap i := by
  have hadmissible := b.toBONG.adjacentParameter_isBinaryParameterAdmissible
    i.castSucc (Nat.add_lt_add_right i.isLt 1)
  have hlower := hadmissible.ordUnit_ge_neg_two_mul_e
  rw [b.toBONG.ordUnit_adjacentParameter i.castSucc
    (Nat.add_lt_add_right i.isLt 1)] at hlower
  exact hlower

/-- The half-gap candidate is nonnegative. -/
theorem zero_le_halfGapCandidate
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (0 : WithTop ℚ) ≤ b.halfGapCandidate i := by
  change (0 : WithTop ℚ) ≤
    ((((b.orderGap i : Int) : ℚ) / 2 +
      (ramificationIndex K : ℕ) : ℚ) : WithTop ℚ)
  norm_cast
  rw [Rat.divInt_eq_div]
  have hlower := b.orderGap_ge_neg_two_mul_e_for_properties i
  have hlowerQ :
      -(2 * (ramificationIndex K : ℚ)) ≤ (b.orderGap i : ℚ) := by
    exact_mod_cast hlower
  linarith

/-- Every left defect candidate in the defining minimum is nonnegative. -/
theorem zero_le_leftDefectCandidate
    (b : GoodBONG q L (n + 1)) (i j : Fin n) (hji : j ≤ i) :
    (0 : WithTop ℚ) ≤ b.leftDefectCandidate i j := by
  have hdefect :=
    defectOrder_nonneg_for_alpha (K := K) (b.adjacentProduct j)
  have hlocal := b.zero_le_orderGap_add_adjacentDefect j
  unfold leftDefectCandidate
  rcases Nat.even_or_odd (i.val - j.val) with heven | hodd
  · have horder := b.order_le_of_le_of_even_sub j.succ i.succ
        (by
          change j.val + 1 ≤ i.val + 1
          omega) (by simpa using heven)
    have hdiff :
        (0 : WithTop ℚ) ≤
          (((b.order i.succ - b.order j.succ : Int) : ℚ) :
            WithTop ℚ) := by
      exact_mod_cast (sub_nonneg.mpr horder)
    have hcast :
        (((b.order i.succ - b.order j.castSucc : Int) : ℚ) :
            WithTop ℚ) =
          (((b.order i.succ - b.order j.succ : Int) : ℚ) :
              WithTop ℚ) +
            (((b.orderGap j : Int) : ℚ) : WithTop ℚ) := by
      norm_cast
      unfold orderGap
      push_cast
      ring
    rw [hcast]
    simpa only [add_assoc] using add_nonneg hdiff hlocal
  · rcases hodd with ⟨d, hd⟩
    have hevenNext : Even ((i.val + 1) - j.val) := by
      refine ⟨d + 1, ?_⟩
      omega
    have horder := b.order_le_of_le_of_even_sub j.castSucc i.succ
      (by
        change j.val ≤ i.val + 1
        omega) (by simpa using hevenNext)
    have hdiff :
        (0 : WithTop ℚ) ≤
          (((b.order i.succ - b.order j.castSucc : Int) : ℚ) :
            WithTop ℚ) := by
      exact_mod_cast (sub_nonneg.mpr horder)
    exact add_nonneg hdiff hdefect

/-- Every right defect candidate in the defining minimum is nonnegative. -/
theorem zero_le_rightDefectCandidate
    (b : GoodBONG q L (n + 1)) (i j : Fin n) (hij : i ≤ j) :
    (0 : WithTop ℚ) ≤ b.rightDefectCandidate i j := by
  have hdefect :=
    defectOrder_nonneg_for_alpha (K := K) (b.adjacentProduct j)
  have hlocal := b.zero_le_orderGap_add_adjacentDefect j
  unfold rightDefectCandidate
  rcases Nat.even_or_odd (j.val - i.val) with heven | hodd
  · have horder := b.order_le_of_le_of_even_sub i.castSucc j.castSucc
        (by exact hij) (by simpa using heven)
    have hdiff :
        (0 : WithTop ℚ) ≤
          (((b.order j.castSucc - b.order i.castSucc : Int) : ℚ) :
            WithTop ℚ) := by
      exact_mod_cast (sub_nonneg.mpr horder)
    have hcast :
        (((b.order j.succ - b.order i.castSucc : Int) : ℚ) :
            WithTop ℚ) =
          (((b.order j.castSucc - b.order i.castSucc : Int) : ℚ) :
              WithTop ℚ) +
            (((b.orderGap j : Int) : ℚ) : WithTop ℚ) := by
      norm_cast
      unfold orderGap
      push_cast
      ring
    rw [hcast]
    simpa only [add_assoc] using add_nonneg hdiff hlocal
  · rcases hodd with ⟨d, hd⟩
    have hevenNext : Even ((j.val + 1) - i.val) := by
      refine ⟨d + 1, ?_⟩
      omega
    have horder := b.order_le_of_le_of_even_sub i.castSucc j.succ
      (by
        change i.val ≤ j.val + 1
        omega) (by simpa using hevenNext)
    have hdiff :
        (0 : WithTop ℚ) ≤
          (((b.order j.succ - b.order i.castSucc : Int) : ℚ) :
            WithTop ℚ) := by
      exact_mod_cast (sub_nonneg.mpr horder)
    exact add_nonneg hdiff hdefect

/-- Beli's finite minimum defining `alpha` is nonnegative. -/
theorem zero_le_alphaValue
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    0 ≤ b.alphaValue i := by
  have halpha : (0 : WithTop ℚ) ≤ b.alpha i := by
    apply Finset.le_min' _ _ _
    intro x hx
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with hhalf | hleft | hright
    · rw [hhalf]
      exact b.zero_le_halfGapCandidate i
    · rcases hleft with ⟨j, hji, rfl⟩
      exact b.zero_le_leftDefectCandidate i j hji
    · rcases hright with ⟨j, hij, rfl⟩
      exact b.zero_le_rightDefectCandidate i j hij
  rw [← b.coe_alphaValue] at halpha
  exact_mod_cast halpha

end BONG.GoodBONG

end Bong
