/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIILocal

/-!
# Beli (2019), Lemma 7.14(ii): the two external binary boundaries

The ternary block supplied by Lemma 7.12 is already a good BONG.  To insert
it into the complete coefficient sequence, only its two external adjacent
parameters remain to be checked.

At the left boundary the order jump is `2e`, so admissibility is immediate.
At the right boundary the new parameter is the old adjacent parameter
multiplied by `η⁻¹`.  The old parameter is admissible, `d(η) = 2e - 1`, and
the stopping inequality gives enough room for both defects.  The ordinary
domination inequality therefore suffices; no exact-defect hypothesis is
needed.
-/

namespace Bong

open Dyadic

universe u v

namespace Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Converse to the order-to-integral-defect bridge used in Lemma 8.6.
Thus Beli's notation `ord(a) + d(a) >= 0` is exactly the existing absolute
quadratic-defect predicate, including the infinite-defect case. -/
theorem nonneg_add_defectOrder_of_hasNonnegativeAbsoluteQuadraticDefect
    [QuadraticDefectLaws K] (a : Kˣ)
    (h : HasNonnegativeAbsoluteQuadraticDefect a) :
    (0 : WithTop ℚ) ≤
      ((ordUnit K a : ℚ) : WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K) a := by
  have hthreshold :=
    (hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le a).1 h
  by_cases htop : quadraticDefect K a = ⊤
  · have hdefect : BONG.GoodBONG.defectOrder (K := K) a = ⊤ := by
      unfold BONG.GoodBONG.defectOrder
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
    have hdefect : BONG.GoodBONG.defectOrder (K := K) a =
        (d : WithTop ℚ) := by
      unfold BONG.GoodBONG.defectOrder
      rw [← hd]
      rfl
    rw [hdefect]
    exact_mod_cast hsumInt

/-- Absolute quadratic-defect integrality and the embedded order inequality
are interchangeable. -/
theorem hasNonnegativeAbsoluteQuadraticDefect_iff_nonneg_add_defectOrder
    [QuadraticDefectLaws K] (a : Kˣ) :
    HasNonnegativeAbsoluteQuadraticDefect a ↔
      (0 : WithTop ℚ) ≤
        ((ordUnit K a : ℚ) : WithTop ℚ) +
          BONG.GoodBONG.defectOrder (K := K) a := by
  constructor
  · exact nonneg_add_defectOrder_of_hasNonnegativeAbsoluteQuadraticDefect a
  · exact hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder a

end Dyadic

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The boundary from the unchanged prefix to the first value of the new
ternary block is admissible.  This is the first external-boundary sentence
in the proof of Lemma 7.14(ii). -/
theorem lemma714_typeII_leftBoundaryAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsFour : 4 ≤ s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K)) :
    IsBinaryParameterAdmissible
      (lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η 0 /
        b.valueUnit ⟨s - 1, by omega⟩) := by
  have P := b.beli2019Lemma714_i R s D.toLemma714MinimalityData
    hsFour hthird
  have hsOdd : Odd (s - 1) := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hprevious : b.order ⟨s - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int) + 1 :=
    P.low_positions (s - 1) (by omega) (by omega) hsOdd
  have hεOrder : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  have hcurrentOrder : ordUnit K (b.valueUnit ⟨s, hsCurrent⟩) =
      R + 1 := by
    change ordUnit K (b.toBONG.valueUnit ⟨s, hsCurrent⟩) = R + 1
    rw [← b.toBONG.order_eq_ordUnit]
    exact hcurrent
  have hpreviousOrder : ordUnit K (b.valueUnit ⟨s - 1, by omega⟩) =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    change ordUnit K (b.toBONG.valueUnit ⟨s - 1, by omega⟩) = _
    rw [← b.toBONG.order_eq_ordUnit]
    exact hprevious
  apply isBinaryParameterAdmissible_of_ordUnit_nonneg
  rw [lemma712TargetValues_zero, div_eq_mul_inv, ordUnit_mul,
    ordUnit_inv, ordUnit_mul, hεOrder, hcurrentOrder, hpreviousOrder]
  omega

/-- The right external parameter, before rewriting the third target value,
is admissible by defect domination. -/
theorem lemma714_typeII_rightBoundaryAdmissible_raw
    [QuadraticDefectLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (hsSuffix : s + 2 ≤ n + 3)
    (η : Kˣ) (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    IsBinaryParameterAdmissible
      (b.valueUnit ⟨s + 1, by omega⟩ /
        (b.valueUnit ⟨s, hsCurrent⟩ * η)) := by
  let current : Fin (n + 3) := ⟨s, hsCurrent⟩
  let next : Fin (n + 3) := ⟨s + 1, by omega⟩
  let oldParameter : Kˣ :=
    b.toBONG.adjacentParameter current (by
      dsimp only [current]
      omega)
  let newParameter : Kˣ :=
    b.valueUnit next / (b.valueUnit current * η)
  let gap : Int := b.order next - b.order current
  have hstop : R - 2 * (ramificationIndex K : Int) + 3 ≤
      b.order next := by
    simpa only [next] using
      b.lemma714_typeII_stopOrder_ge R s D
        ⟨hsCurrent, hcurrent⟩ hsSuffix
  have hgapEtaInt :
      0 ≤ gap + (2 * (ramificationIndex K : Int) - 1) := by
    have hcurrent' : b.order current = R + 1 := by
      simpa only [current] using hcurrent
    dsimp only [gap, current, next]
    dsimp only [current, next] at hcurrent' hstop
    omega
  have hηOrder : ordUnit K η = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K η).1 hηUnit
  have holdEq : oldParameter =
      b.valueUnit next / b.valueUnit current := by
    dsimp only [oldParameter]
    unfold BONG.adjacentParameter
    congr 2
  have hnewEq : newParameter = oldParameter * η⁻¹ := by
    rw [holdEq]
    dsimp only [newParameter]
    simp only [div_eq_mul_inv, mul_inv_rev]
    rw [mul_left_comm, mul_comm]
  have holdOrder : ordUnit K oldParameter = gap := by
    calc
      ordUnit K oldParameter =
          b.order ⟨current.val + 1, by
            dsimp only [current]
            omega⟩ - b.order current := by
        dsimp only [oldParameter]
        exact b.toBONG.ordUnit_adjacentParameter current (by
          dsimp only [current]
          omega)
      _ = b.order next - b.order current := by
        congr 2
      _ = gap := rfl
  have hnewOrder : ordUnit K newParameter = gap := by
    rw [hnewEq, ordUnit_mul, ordUnit_inv, hηOrder]
    simpa only [neg_zero, add_zero] using holdOrder
  have holdAdmissible : IsBinaryParameterAdmissible oldParameter := by
    dsimp only [oldParameter]
    exact b.toBONG.adjacentParameter_isBinaryParameterAdmissible
      current (by
        dsimp only [current]
        omega)
  have holdAbsolute :
      HasNonnegativeAbsoluteQuadraticDefect (-oldParameter) :=
    (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
      oldParameter).1 holdAdmissible |>.2
  have holdSum :=
    nonneg_add_defectOrder_of_hasNonnegativeAbsoluteQuadraticDefect
      (-oldParameter) holdAbsolute
  have hnegOldOrder : ordUnit K (-oldParameter) = gap := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, Units.val_neg, ord_neg, ← coe_ordUnit, holdOrder]
  rw [hnegOldOrder] at holdSum
  have hηInverseSum :
      (0 : WithTop ℚ) ≤ ((gap : ℚ) : WithTop ℚ) +
        defectOrder (K := K) η⁻¹ := by
    rw [defectOrder_inv, hηDefect]
    norm_cast
  have hminimumSum :
      (0 : WithTop ℚ) ≤ ((gap : ℚ) : WithTop ℚ) +
        min (defectOrder (K := K) (-oldParameter))
          (defectOrder (K := K) η⁻¹) := by
    rw [add_min]
    exact le_min holdSum hηInverseSum
  have hdomination :=
    defectOrder_mul_ge_min (K := K) (-oldParameter) η⁻¹
  have hproductSum :
      (0 : WithTop ℚ) ≤ ((gap : ℚ) : WithTop ℚ) +
        defectOrder (K := K) ((-oldParameter) * η⁻¹) :=
    hminimumSum.trans (add_le_add le_rfl hdomination)
  have hnegativeNew : -newParameter = (-oldParameter) * η⁻¹ := by
    rw [hnewEq]
    rw [neg_mul]
  apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
    newParameter).2
  constructor
  · rw [hnewOrder]
    have hePos := ramificationIndex_pos (K := K)
    dsimp only [gap, current, next] at hgapEtaInt ⊢
    omega
  · apply
      hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
    rw [hnegativeNew]
    have hnegativeOrder :
        ordUnit K ((-oldParameter) * η⁻¹) = gap := by
      rw [ordUnit_mul, ordUnit_inv, hηOrder]
      simpa only [neg_zero, add_zero] using hnegOldOrder
    rw [hnegativeOrder]
    exact hproductSum

/-- The right boundary in the exact coefficient notation of Lemma 7.12. -/
theorem lemma714_typeII_rightBoundaryAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (hsSuffix : s + 2 ≤ n + 3)
    (ε η : Kˣ) (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    IsBinaryParameterAdmissible
      (b.valueUnit ⟨s + 1, by omega⟩ /
        lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η 2) := by
  simpa only [lemma712TargetValues_two] using
    b.lemma714_typeII_rightBoundaryAdmissible_raw R s D hsCurrent
      hcurrent hsSuffix η hηUnit hηDefect

end BONG.GoodBONG

end Bong
