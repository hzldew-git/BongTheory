/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicModels
import Bong.Bong.Beli2019Lemma95NormalForm
import Bong.Dyadic.UnitDefectClassification

/-!
# He (2024), Lemmas 2.7 and 2.9: exact classic model profiles

This file supplies exact good-BONG realizations of the displayed rows from
Definition 2.6 and proves their order and alpha profiles.  The constructions
are coefficient-level, so the resulting lattice is not merely isometric to
the displayed diagonal row: its chosen good BONG has exactly those entries.
-/

namespace Bong

open Dyadic BONG.GoodBONG AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

private theorem ordUnit_one_unit : ordUnit K (1 : Kˣ) = 0 := by
  apply WithTop.coe_injective
  rw [coe_ordUnit]
  simp

/-- A nonnegative coefficient `c` makes the binary row `[1,-c]`
admissible.  This is the elementary boundary calculation used repeatedly
in He, Lemma 2.7. -/
theorem isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
    (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    IsBinaryParameterAdmissible (-c) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
    (-c)).2
  constructor
  · rw [ordUnit_neg]
    have he : 0 < (ramificationIndex K : Int) := by
      exact_mod_cast ramificationIndex_pos (K := K)
    omega
  · simpa only [neg_neg] using
      ((hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le c).2 <| by
        rw [absoluteDefectThreshold_eq_zero_of_nonneg hc]
        exact bot_le)

/-- The parameter `-1` is admissible. -/
theorem isBinaryParameterAdmissible_neg_one :
    IsBinaryParameterAdmissible (-1 : Kˣ) := by
  exact isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
    (K := K) 1 (by rw [ordUnit_one_unit])

end BONG

/-! ## Reusable calculations for the zero-scale hyperbolic head -/

/-- Every coefficient in the displayed `H₀` tower has order zero. -/
@[simp]
theorem heClassicScaledHyperbolicTower_zero_order
    (pairs : Nat) (i : Fin (2 * pairs)) :
    ordUnit K (heClassicScaledHyperbolicTower (K := K) 0 pairs i) = 0 := by
  unfold heClassicScaledHyperbolicTower
  split
  · simpa [uniformizerPowerUnit] using
      (BONG.ordUnit_one_unit (K := K))
  · rw [ordUnit_neg]
    simpa [uniformizerPowerUnit] using
      (BONG.ordUnit_one_unit (K := K))

/-- The order at an arbitrary position of `H_t^s` is `t` on the even
subsequence and `-t` on the odd subsequence. -/
theorem heClassicScaledHyperbolicTower_order
    (t pairs : Nat) (i : Fin (2 * pairs)) :
    ordUnit K (heClassicScaledHyperbolicTower (K := K) t pairs i) =
      if Even i.val then (t : Int) else -(t : Int) := by
  unfold heClassicScaledHyperbolicTower
  split
  · rw [ordUnit_uniformizerPowerUnit]
  · rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]

/-- Every internal adjacent quotient in the displayed `H₀` tower is `-1`. -/
theorem heClassicScaledHyperbolicTower_zero_adjacentRatio
    (pairs : Nat) (i : Fin (2 * pairs))
    (hi : i.val + 1 < 2 * pairs) :
    heClassicScaledHyperbolicTower (K := K) 0 pairs
          ⟨i.val + 1, hi⟩ /
        heClassicScaledHyperbolicTower (K := K) 0 pairs i = -1 := by
  rcases Nat.even_or_odd i.val with heven | hodd
  · have hnextOdd : ¬ Even (i.val + 1) :=
      Nat.not_even_iff_odd.mpr (Even.add_one heven)
    simp [heClassicScaledHyperbolicTower, heven, hnextOdd,
      uniformizerPowerUnit]
  · have hnotEven : ¬ Even i.val := Nat.not_even_iff_odd.mpr hodd
    have hnextEven : Even (i.val + 1) := Odd.add_one hodd
    simp [heClassicScaledHyperbolicTower, hnotEven, hnextEven,
      uniformizerPowerUnit]

/-- Quotients of selected uniformizer powers subtract their exponents. -/
theorem uniformizerPowerUnit_div_uniformizerPowerUnit
    (r s : Int) :
    uniformizerPowerUnit K r / uniformizerPowerUnit K s =
      uniformizerPowerUnit K (r - s) := by
  unfold uniformizerPowerUnit
  rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1

/-- Adjacent quotients in `H_t^s` alternate between the two displayed
even uniformizer powers. -/
theorem heClassicScaledHyperbolicTower_adjacentRatio
    (t pairs : Nat) (i : Fin (2 * pairs))
    (hi : i.val + 1 < 2 * pairs) :
    heClassicScaledHyperbolicTower (K := K) t pairs
          ⟨i.val + 1, hi⟩ /
        heClassicScaledHyperbolicTower (K := K) t pairs i =
      if Even i.val then
        -(uniformizerPowerUnit K (-(2 * (t : Int))))
      else -(uniformizerPowerUnit K (2 * (t : Int))) := by
  rcases Nat.even_or_odd i.val with heven | hodd
  · have hnextOdd : ¬ Even (i.val + 1) :=
      Nat.not_even_iff_odd.mpr (Even.add_one heven)
    rw [if_pos heven]
    simp only [heClassicScaledHyperbolicTower, heven, hnextOdd,
      ↓reduceIte, neg_div]
    rw [uniformizerPowerUnit_div_uniformizerPowerUnit]
    have hexponent : -(t : Int) - (t : Int) = -(2 * (t : Int)) := by
      ring
    rw [hexponent]
  · have hnotEven : ¬ Even i.val := Nat.not_even_iff_odd.mpr hodd
    have hnextEven : Even (i.val + 1) := Odd.add_one hodd
    rw [if_neg hnotEven]
    simp only [heClassicScaledHyperbolicTower, hnotEven, hnextEven,
      ↓reduceIte, div_neg]
    rw [uniformizerPowerUnit_div_uniformizerPowerUnit]
    have hexponent : (t : Int) - -(t : Int) = 2 * (t : Int) := by
      ring
    rw [hexponent]

/-- The negative extremal quotient `-π^(-2e)` is admissible because its
negative is a square and its order is exactly `-2e`. -/
theorem isBinaryParameterAdmissible_neg_uniformizerPower_negTwoE :
    BONG.IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K
        (-(2 * (ramificationIndex K : Int))))) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  apply (BONG.isBinaryParameterAdmissible_iff_beli _).2
  apply Or.inr
  constructor
  · simpa only [neg_neg] using
      (isSquare_uniformizerPowerUnit_of_even (K := K)
        (-(2 * (ramificationIndex K : Int)))
        ⟨-(ramificationIndex K : Int), by ring⟩)
  · rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]

/-- The positive extremal quotient `-π^(2e)` is admissible. -/
theorem isBinaryParameterAdmissible_neg_uniformizerPower_twoE :
    BONG.IsBinaryParameterAdmissible
      (-(uniformizerPowerUnit K
        (2 * (ramificationIndex K : Int)))) := by
  apply BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
  rw [ordUnit_uniformizerPowerUnit]
  have he : 0 < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos (K := K)
  omega

/-- The terminal `H_e` quotient is admissible for the two classes appearing
in Definition 2.6: the trivial class and the discriminant class. -/
theorem heClassicEvenH_terminalAdmissible
    (c : Kˣ)
    (hc : c = 1 ∨
      c = (inferInstance :
        DyadicDiscriminantClassLaws K).discriminantUnit) :
    BONG.IsBinaryParameterAdmissible
      (-(c * uniformizerPowerUnit K
        (-(2 * (ramificationIndex K : Int))))) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  rcases hc with rfl | rfl
  · simpa only [one_mul] using
      (isBinaryParameterAdmissible_neg_uniformizerPower_negTwoE
        (K := K))
  · let laws : DyadicDiscriminantClassLaws K := inferInstance
    apply (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
      _).2
    constructor
    · rw [ordUnit_neg, ordUnit_mul, ordUnit_uniformizerPowerUnit]
      have hdelta : ordUnit K laws.discriminantUnit = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
          laws.discriminant_isValuationUnit
      rw [hdelta]
      omega
    · simp only [neg_neg]
      have heven : Even (-(2 * (ramificationIndex K : Int))) :=
        ⟨-(ramificationIndex K : Int), by ring⟩
      have h :=
        hasNonnegativeAbsoluteQuadraticDefect_uniformizerPower_mul_discriminant
          (K := K) (-(2 * (ramificationIndex K : Int))) heven (by omega)
      simpa only [mul_comm] using h

/-! ## The even first-column row -/

@[simp]
theorem heClassicEvenC1_head (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * pairs)) :
    heClassicEvenC1 (K := K) pairs c (Fin.castAdd 2 i) =
      heClassicScaledHyperbolicTower (K := K) 0 pairs i := by
  rw [heClassicEvenC1, Fin.append_left]

@[simp]
theorem heClassicEvenC1_tail (pairs : Nat) (c : Kˣ)
    (i : Fin 2) :
    heClassicEvenC1 (K := K) pairs c (Fin.natAdd (2 * pairs) i) =
      ![1, -c] i := by
  rw [heClassicEvenC1, Fin.append_right]

/-- The literal order profile of `C_1^(2*pairs+2)(c)`. -/
theorem heClassicEvenC1_order (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * pairs + 2)) :
    ordUnit K (heClassicEvenC1 (K := K) pairs c i) =
      if i.val = 2 * pairs + 1 then ordUnit K c else 0 := by
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    have hi : i = Fin.castAdd 2 j := Fin.ext rfl
    rw [hi, heClassicEvenC1_head]
    have hjOrder : ordUnit K
        (heClassicScaledHyperbolicTower (K := K) 0 pairs j) = 0 := by
      rw [heClassicScaledHyperbolicTower_zero]
      unfold standardHyperbolicEndpointTower
      split
      · exact BONG.ordUnit_one_unit
      · rw [ordUnit_neg, BONG.ordUnit_one_unit]
    rw [hjOrder]
    simp
    omega
  · have htail : i.val = 2 * pairs ∨
        i.val = 2 * pairs + 1 := by omega
    rcases htail with hzero | hone
    · have hi : i = Fin.natAdd (2 * pairs) (0 : Fin 2) := by
        apply Fin.ext
        simpa using hzero
      rw [hi, heClassicEvenC1_tail]
      rw [show ![1, -c] (0 : Fin 2) = (1 : Kˣ) by rfl,
        BONG.ordUnit_one_unit]
      simp
    · have hi : i = Fin.natAdd (2 * pairs) (1 : Fin 2) := by
        apply Fin.ext
        simpa using hone
      rw [hi, heClassicEvenC1_tail]
      simp [hone]

/-- Every adjacent ratio before the terminal binary pair is `-1`. -/
theorem heClassicEvenC1_adjacentRatio_beforeLast
    (pairs : Nat) (c : Kˣ) (i : Fin (2 * pairs + 2))
    (hi : i.val < 2 * pairs) :
    heClassicEvenC1 (K := K) pairs c
          ⟨i.val + 1, by omega⟩ /
        heClassicEvenC1 (K := K) pairs c i = -1 := by
  by_cases hnext : i.val + 1 < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hi⟩
    let k : Fin (2 * pairs) := ⟨i.val + 1, hnext⟩
    have hiCast : (i : Fin (2 * pairs + 2)) = Fin.castAdd 2 j :=
      Fin.ext rfl
    have hnextCast :
        (⟨i.val + 1, by omega⟩ : Fin (2 * pairs + 2)) =
          Fin.castAdd 2 k := Fin.ext rfl
    have hcurrentValue :
        heClassicEvenC1 (K := K) pairs c i =
          heClassicScaledHyperbolicTower (K := K) 0 pairs j := by
      calc
        _ = heClassicEvenC1 (K := K) pairs c (Fin.castAdd 2 j) :=
          congrArg (heClassicEvenC1 (K := K) pairs c) hiCast
        _ = _ := heClassicEvenC1_head pairs c j
    have hnextValue :
        heClassicEvenC1 (K := K) pairs c
            ⟨i.val + 1, by omega⟩ =
          heClassicScaledHyperbolicTower (K := K) 0 pairs k := by
      calc
        _ = heClassicEvenC1 (K := K) pairs c (Fin.castAdd 2 k) :=
          congrArg (heClassicEvenC1 (K := K) pairs c) hnextCast
        _ = _ := heClassicEvenC1_head pairs c k
    rw [hcurrentValue, hnextValue]
    rcases Nat.even_or_odd i.val with heven | hodd
    · have hnextOdd : ¬ Even (i.val + 1) :=
        Nat.not_even_iff_odd.mpr (Even.add_one heven)
      simp [heClassicScaledHyperbolicTower, j, k, heven,
        hnextOdd, uniformizerPowerUnit]
    · have hnotEven : ¬ Even i.val :=
        Nat.not_even_iff_odd.mpr hodd
      have hnextEven : Even (i.val + 1) := Odd.add_one hodd
      simp [heClassicScaledHyperbolicTower, j, k, hnotEven,
        hnextEven, uniformizerPowerUnit]
  · have hboundary : i.val + 1 = 2 * pairs := by omega
    let j : Fin (2 * pairs) := ⟨i.val, hi⟩
    have hiCast : (i : Fin (2 * pairs + 2)) = Fin.castAdd 2 j :=
      Fin.ext rfl
    have hnextCast :
        (⟨i.val + 1, by omega⟩ : Fin (2 * pairs + 2)) =
          Fin.natAdd (2 * pairs) (0 : Fin 2) := by
      apply Fin.ext
      simpa using hboundary
    have hnotEven : ¬ Even i.val := by
      intro heven
      rcases heven with ⟨z, hz⟩
      omega
    have hcurrentValue :
        heClassicEvenC1 (K := K) pairs c i =
          heClassicScaledHyperbolicTower (K := K) 0 pairs j := by
      calc
        _ = heClassicEvenC1 (K := K) pairs c (Fin.castAdd 2 j) :=
          congrArg (heClassicEvenC1 (K := K) pairs c) hiCast
        _ = _ := heClassicEvenC1_head pairs c j
    have hnextValue :
        heClassicEvenC1 (K := K) pairs c
            ⟨i.val + 1, by omega⟩ = 1 := by
      calc
        _ = heClassicEvenC1 (K := K) pairs c
            (Fin.natAdd (2 * pairs) (0 : Fin 2)) :=
          congrArg (heClassicEvenC1 (K := K) pairs c) hnextCast
        _ = 1 := by rw [heClassicEvenC1_tail]; rfl
    rw [hcurrentValue, hnextValue]
    simp [heClassicScaledHyperbolicTower, j, hnotEven,
      uniformizerPowerUnit]

/-- The final adjacent ratio is `-c`. -/
theorem heClassicEvenC1_adjacentRatio_last
    (pairs : Nat) (c : Kˣ) :
    heClassicEvenC1 (K := K) pairs c
          ⟨2 * pairs + 1, by omega⟩ /
        heClassicEvenC1 (K := K) pairs c
          ⟨2 * pairs, by omega⟩ = -c := by
  have hzero :
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
        Fin.natAdd (2 * pairs) (0 : Fin 2) := Fin.ext rfl
  have hone :
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
        Fin.natAdd (2 * pairs) (1 : Fin 2) := Fin.ext rfl
  rw [hzero, hone, heClassicEvenC1_tail,
    heClassicEvenC1_tail]
  simp

/-- The even first-column row satisfies every adjacent binary condition. -/
theorem heClassicEvenC1_adjacentAdmissible
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicEvenC1 (K := K) pairs c) := by
  intro i hi
  by_cases hlast : i.val = 2 * pairs
  · have hiEq : i = ⟨2 * pairs, by omega⟩ := Fin.ext hlast
    have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 2)) =
        ⟨2 * pairs + 1, by omega⟩ := by
      apply Fin.ext
      simpa [hlast]
    have hcurrentValue := congrArg
      (heClassicEvenC1 (K := K) pairs c) hiEq
    have hnextValue := congrArg
      (heClassicEvenC1 (K := K) pairs c) hnextEq
    rw [hcurrentValue, hnextValue,
      heClassicEvenC1_adjacentRatio_last]
    exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg c hc
  · have hbefore : i.val < 2 * pairs := by omega
    rw [heClassicEvenC1_adjacentRatio_beforeLast pairs c i hbefore]
    exact BONG.isBinaryParameterAdmissible_neg_one (K := K)

/-- The two parity chains in the even first-column row are weakly
increasing whenever `ord(c) ≥ 0`. -/
theorem heClassicEvenC1_weakTwoStep
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicEvenC1 (K := K) pairs c) := by
  intro i hi
  rw [heClassicEvenC1_order, heClassicEvenC1_order]
  by_cases hfinal : i.val + 2 = 2 * pairs + 1
  · rw [if_pos hfinal]
    have hcurrent : i.val ≠ 2 * pairs + 1 := by omega
    rw [if_neg hcurrent]
    exact hc
  · rw [if_neg hfinal]
    have hcurrent : i.val ≠ 2 * pairs + 1 := by omega
    rw [if_neg hcurrent]

/-- Exact good BONG carried by the displayed `C_1` coefficient row. -/
noncomputable def heClassicEvenC1GoodBONG
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :=
  heHuExactGoodBONG (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenC1_adjacentAdmissible pairs c hc)
    (heClassicEvenC1_weakTwoStep pairs c hc)

/-- Proposition 2.8(iii), first even column: every displayed `C_1` row
with order-zero or order-one determinant parameter is classic integral. -/
theorem heClassicEvenC1_isClassicIntegral
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) pairs c))
      (heHuExactRealization
        (heClassicEvenC1 (K := K) pairs c)
        (heClassicEvenC1_adjacentAdmissible pairs c hc)
        (heClassicEvenC1_weakTwoStep pairs c hc)).lattice := by
  dsimp only
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicEvenC1GoodBONG,
    heHuExactGoodBONG_order]
  rw [heClassicEvenC1_order, heClassicEvenC1_order]
  by_cases hpairs : pairs = 0
  · simp [hpairs, hc]
  · simp [hpairs]

/-! ## The even second-column row -/

@[simp]
theorem heClassicEvenC2_head (pairs : Nat) (c cSharp : Kˣ)
    (i : Fin (2 * pairs)) :
    heClassicEvenC2 (K := K) pairs c cSharp (Fin.castAdd 2 i) =
      heClassicScaledHyperbolicTower (K := K) 0 pairs i := by
  rw [heClassicEvenC2, Fin.append_left]

@[simp]
theorem heClassicEvenC2_tail (pairs : Nat) (c cSharp : Kˣ)
    (i : Fin 2) :
    heClassicEvenC2 (K := K) pairs c cSharp
        (Fin.natAdd (2 * pairs) i) = ![cSharp, -(cSharp * c)] i := by
  rw [heClassicEvenC2, Fin.append_right]

/-- Lemma 2.9(i), order profile of the even second-column row. -/
theorem heClassicEvenC2_order (pairs : Nat) (c cSharp : Kˣ)
    (hcSharp : ordUnit K cSharp = 0)
    (i : Fin (2 * pairs + 2)) :
    ordUnit K (heClassicEvenC2 (K := K) pairs c cSharp i) =
      if i.val = 2 * pairs + 1 then ordUnit K c else 0 := by
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    have hi : i = Fin.castAdd 2 j := Fin.ext rfl
    rw [hi, heClassicEvenC2_head,
      heClassicScaledHyperbolicTower_zero_order]
    simp [j]
    omega
  · have htail : i.val = 2 * pairs ∨
        i.val = 2 * pairs + 1 := by omega
    rcases htail with hzero | hone
    · have hi : i = Fin.natAdd (2 * pairs) (0 : Fin 2) := by
        apply Fin.ext
        simpa using hzero
      rw [hi, heClassicEvenC2_tail]
      simp [hcSharp]
    · have hi : i = Fin.natAdd (2 * pairs) (1 : Fin 2) := by
        apply Fin.ext
        simpa using hone
      rw [hi, heClassicEvenC2_tail]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [ordUnit_neg, ordUnit_mul, hcSharp]
      simp

/-- The even second-column row satisfies every adjacent binary condition. -/
theorem heClassicEvenC2_adjacentAdmissible
    (pairs : Nat) (c cSharp : Kˣ)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicEvenC2 (K := K) pairs c cSharp) := by
  intro i hi
  by_cases hinternal : i.val + 1 < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, by omega⟩
    let k : Fin (2 * pairs) := ⟨i.val + 1, hinternal⟩
    have hiCast : (i : Fin (2 * pairs + 2)) = Fin.castAdd 2 j :=
      Fin.ext rfl
    have hnextCast :
        (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 2)) =
          Fin.castAdd 2 k := Fin.ext rfl
    have hcurrentValue :
        heClassicEvenC2 (K := K) pairs c cSharp i =
          heClassicScaledHyperbolicTower (K := K) 0 pairs j := by
      calc
        _ = heClassicEvenC2 (K := K) pairs c cSharp
            (Fin.castAdd 2 j) :=
          congrArg (heClassicEvenC2 (K := K) pairs c cSharp) hiCast
        _ = _ := heClassicEvenC2_head pairs c cSharp j
    have hnextValue :
        heClassicEvenC2 (K := K) pairs c cSharp
            ⟨i.val + 1, hi⟩ =
          heClassicScaledHyperbolicTower (K := K) 0 pairs k := by
      calc
        _ = heClassicEvenC2 (K := K) pairs c cSharp
            (Fin.castAdd 2 k) :=
          congrArg (heClassicEvenC2 (K := K) pairs c cSharp) hnextCast
        _ = _ := heClassicEvenC2_head pairs c cSharp k
    rw [hcurrentValue, hnextValue]
    have hratio := heClassicScaledHyperbolicTower_zero_adjacentRatio
      (K := K) pairs j (by simpa [j] using hinternal)
    have hk : (⟨j.val + 1, by simpa [j] using hinternal⟩ :
        Fin (2 * pairs)) = k := Fin.ext rfl
    rw [hk] at hratio
    rw [hratio]
    exact BONG.isBinaryParameterAdmissible_neg_one (K := K)
  · have hboundaryOrLast :
        i.val + 1 = 2 * pairs ∨ i.val = 2 * pairs := by omega
    rcases hboundaryOrLast with hboundary | hlast
    · have hiHead : i.val < 2 * pairs := by omega
      let j : Fin (2 * pairs) := ⟨i.val, hiHead⟩
      have hiCast : (i : Fin (2 * pairs + 2)) = Fin.castAdd 2 j :=
        Fin.ext rfl
      have hnextCast :
          (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 2)) =
            Fin.natAdd (2 * pairs) (0 : Fin 2) := by
        apply Fin.ext
        simpa using hboundary
      have hcurrentValue :
          heClassicEvenC2 (K := K) pairs c cSharp i = -1 := by
        calc
          _ = heClassicScaledHyperbolicTower (K := K) 0 pairs j := by
            rw [hiCast, heClassicEvenC2_head]
          _ = -1 := by
            have hodd : ¬ Even i.val := by
              intro heven
              rcases heven with ⟨z, hz⟩
              omega
            simp [heClassicScaledHyperbolicTower, j, hodd,
              uniformizerPowerUnit]
      have hnextValue :
          heClassicEvenC2 (K := K) pairs c cSharp
              ⟨i.val + 1, hi⟩ = cSharp := by
        rw [hnextCast, heClassicEvenC2_tail]
        rfl
      rw [hcurrentValue, hnextValue]
      have hquotient : cSharp / (-1 : Kˣ) = -cSharp := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_one]
        field_simp
      rw [hquotient]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        cSharp (by omega)
    · have hiEq : i = ⟨2 * pairs, by omega⟩ := Fin.ext hlast
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 2)) =
          ⟨2 * pairs + 1, by omega⟩ := by
        apply Fin.ext
        simpa [hlast]
      have hzero :
          (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
            Fin.natAdd (2 * pairs) (0 : Fin 2) := Fin.ext rfl
      have hone :
          (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
            Fin.natAdd (2 * pairs) (1 : Fin 2) := Fin.ext rfl
      have hcurrentValue :
          heClassicEvenC2 (K := K) pairs c cSharp i = cSharp := by
        calc
          _ = heClassicEvenC2 (K := K) pairs c cSharp
              ⟨2 * pairs, by omega⟩ :=
            congrArg (heClassicEvenC2 (K := K) pairs c cSharp) hiEq
          _ = heClassicEvenC2 (K := K) pairs c cSharp
              (Fin.natAdd (2 * pairs) (0 : Fin 2)) :=
            congrArg (heClassicEvenC2 (K := K) pairs c cSharp) hzero
          _ = cSharp := by rw [heClassicEvenC2_tail]; rfl
      have hnextValue :
          heClassicEvenC2 (K := K) pairs c cSharp
              ⟨i.val + 1, hi⟩ = -(cSharp * c) := by
        calc
          _ = heClassicEvenC2 (K := K) pairs c cSharp
              ⟨2 * pairs + 1, by omega⟩ :=
            congrArg (heClassicEvenC2 (K := K) pairs c cSharp) hnextEq
          _ = heClassicEvenC2 (K := K) pairs c cSharp
              (Fin.natAdd (2 * pairs) (1 : Fin 2)) :=
            congrArg (heClassicEvenC2 (K := K) pairs c cSharp) hone
          _ = -(cSharp * c) := by rw [heClassicEvenC2_tail]; rfl
      rw [hcurrentValue, hnextValue]
      have hquotient : -(cSharp * c) / cSharp = -c := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_mul]
        field_simp [Units.ne_zero cSharp]
      rw [hquotient]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg c hc

/-- The two parity chains in the even second-column row are weakly
increasing. -/
theorem heClassicEvenC2_weakTwoStep
    (pairs : Nat) (c cSharp : Kˣ)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicEvenC2 (K := K) pairs c cSharp) := by
  intro i hi
  rw [heClassicEvenC2_order pairs c cSharp hcSharp,
    heClassicEvenC2_order pairs c cSharp hcSharp]
  by_cases hfinal : i.val + 2 = 2 * pairs + 1
  · rw [if_pos hfinal]
    have hcurrent : i.val ≠ 2 * pairs + 1 := by omega
    rw [if_neg hcurrent]
    exact hc
  · rw [if_neg hfinal]
    have hcurrent : i.val ≠ 2 * pairs + 1 := by omega
    rw [if_neg hcurrent]

/-- Exact good BONG carried by the displayed even `C₂` coefficient row. -/
noncomputable def heClassicEvenC2GoodBONG
    (pairs : Nat) (c cSharp : Kˣ)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0) :=
  heHuExactGoodBONG (heClassicEvenC2 (K := K) pairs c cSharp)
    (heClassicEvenC2_adjacentAdmissible pairs c cSharp hc hcSharp)
    (heClassicEvenC2_weakTwoStep pairs c cSharp hc hcSharp)

/-- Proposition 2.8(iii), second even column. -/
theorem heClassicEvenC2_isClassicIntegral
    (pairs : Nat) (c cSharp : Kˣ)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0) :
    let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) pairs c cSharp))
      (heHuExactRealization
        (heClassicEvenC2 (K := K) pairs c cSharp)
        (heClassicEvenC2_adjacentAdmissible pairs c cSharp hc hcSharp)
        (heClassicEvenC2_weakTwoStep pairs c cSharp hc hcSharp)).lattice := by
  dsimp only
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenC2_order pairs c cSharp hcSharp,
    heClassicEvenC2_order pairs c cSharp hcSharp]
  by_cases hpairs : pairs = 0
  · simp [hpairs, hc, hcSharp]
  · simp [hpairs]

/-! ## The odd first-column row -/

@[simp]
theorem heClassicOddC1_head (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * (pairs + 1))) :
    heClassicOddC1 (K := K) pairs c i.castSucc =
      heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) i := by
  rw [heClassicOddC1, Fin.snoc_castSucc]

@[simp]
theorem heClassicOddC1_last (pairs : Nat) (c : Kˣ) :
    heClassicOddC1 (K := K) pairs c (Fin.last (2 * pairs + 2)) = c := by
  simp [heClassicOddC1, Fin.snoc]

/-- Lemma 2.9(ii), order profile of the odd first-column row. -/
theorem heClassicOddC1_order (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * pairs + 3)) :
    ordUnit K (heClassicOddC1 (K := K) pairs c i) =
      if i.val = 2 * pairs + 2 then ordUnit K c else 0 := by
  by_cases hlast : i.val = 2 * pairs + 2
  · have hi : i = Fin.last (2 * pairs + 2) := Fin.ext hlast
    rw [hi, heClassicOddC1_last]
    simp
  · have hhead : i.val < 2 * (pairs + 1) := by omega
    let j : Fin (2 * (pairs + 1)) := ⟨i.val, hhead⟩
    have hi : i = j.castSucc := Fin.ext rfl
    rw [hi, heClassicOddC1_head,
      heClassicScaledHyperbolicTower_zero_order]
    simp [j]
    omega

/-- The odd first-column row satisfies every adjacent binary condition. -/
theorem heClassicOddC1_adjacentAdmissible
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicOddC1 (K := K) pairs c) := by
  intro i hi
  by_cases hinternal : i.val + 1 < 2 * (pairs + 1)
  · let j : Fin (2 * (pairs + 1)) := ⟨i.val, by omega⟩
    let k : Fin (2 * (pairs + 1)) := ⟨i.val + 1, hinternal⟩
    have hiCast : i = j.castSucc := Fin.ext rfl
    have hnextCast :
        (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) = k.castSucc :=
      Fin.ext rfl
    have hcurrentValue :
        heClassicOddC1 (K := K) pairs c i =
          heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) j := by
      calc
        _ = heClassicOddC1 (K := K) pairs c j.castSucc :=
          congrArg (heClassicOddC1 (K := K) pairs c) hiCast
        _ = _ := heClassicOddC1_head pairs c j
    have hnextValue :
        heClassicOddC1 (K := K) pairs c ⟨i.val + 1, hi⟩ =
          heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) k := by
      calc
        _ = heClassicOddC1 (K := K) pairs c k.castSucc :=
          congrArg (heClassicOddC1 (K := K) pairs c) hnextCast
        _ = _ := heClassicOddC1_head pairs c k
    rw [hcurrentValue, hnextValue]
    have hratio := heClassicScaledHyperbolicTower_zero_adjacentRatio
      (K := K) (pairs + 1) j (by simpa [j] using hinternal)
    have hk : (⟨j.val + 1, by simpa [j] using hinternal⟩ :
        Fin (2 * (pairs + 1))) = k := Fin.ext rfl
    rw [hk] at hratio
    rw [hratio]
    exact BONG.isBinaryParameterAdmissible_neg_one (K := K)
  · have hboundary : i.val + 1 = 2 * (pairs + 1) := by omega
    have hiHead : i.val < 2 * (pairs + 1) := by omega
    let j : Fin (2 * (pairs + 1)) := ⟨i.val, hiHead⟩
    have hiCast : i = j.castSucc := Fin.ext rfl
    have hnextLast :
        (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
          Fin.last (2 * pairs + 2) := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_last]
      omega
    have hcurrentValue :
        heClassicOddC1 (K := K) pairs c i = -1 := by
      calc
        _ = heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) j := by
          rw [hiCast, heClassicOddC1_head]
        _ = -1 := by
          have hodd : ¬ Even i.val := by
            intro heven
            rcases heven with ⟨z, hz⟩
            omega
          simp [heClassicScaledHyperbolicTower, j, hodd,
            uniformizerPowerUnit]
    have hnextValue :
        heClassicOddC1 (K := K) pairs c ⟨i.val + 1, hi⟩ = c := by
      calc
        _ = heClassicOddC1 (K := K) pairs c
            (Fin.last (2 * pairs + 2)) :=
          congrArg (heClassicOddC1 (K := K) pairs c) hnextLast
        _ = c := heClassicOddC1_last pairs c
    rw [hcurrentValue, hnextValue]
    have hquotient : c / (-1 : Kˣ) = -c := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_one]
      field_simp
    rw [hquotient]
    exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg c hc

/-- The two parity chains in the odd first-column row are weakly
increasing. -/
theorem heClassicOddC1_weakTwoStep
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicOddC1 (K := K) pairs c) := by
  intro i hi
  rw [heClassicOddC1_order, heClassicOddC1_order]
  by_cases hfinal : i.val + 2 = 2 * pairs + 2
  · rw [if_pos hfinal]
    have hcurrent : i.val ≠ 2 * pairs + 2 := by omega
    rw [if_neg hcurrent]
    exact hc
  · rw [if_neg hfinal]
    have hcurrent : i.val ≠ 2 * pairs + 2 := by omega
    rw [if_neg hcurrent]

/-- Exact good BONG carried by the displayed odd `C₁` coefficient row. -/
noncomputable def heClassicOddC1GoodBONG
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :=
  heHuExactGoodBONG (heClassicOddC1 (K := K) pairs c)
    (heClassicOddC1_adjacentAdmissible pairs c hc)
    (heClassicOddC1_weakTwoStep pairs c hc)

/-- Proposition 2.8(iii), first odd column. -/
theorem heClassicOddC1_isClassicIntegral
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicOddC1GoodBONG (K := K) pairs c hc
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1 (K := K) pairs c))
      (heHuExactRealization
        (heClassicOddC1 (K := K) pairs c)
        (heClassicOddC1_adjacentAdmissible pairs c hc)
        (heClassicOddC1_weakTwoStep pairs c hc)).lattice := by
  dsimp only
  let b := heClassicOddC1GoodBONG (K := K) pairs c hc
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
  rw [heClassicOddC1_order, heClassicOddC1_order]
  simp

/-! ## The odd-order branch of the odd second-column row -/

@[simp]
theorem heClassicOddC2Odd_head (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * pairs)) :
    heClassicOddC2Odd (K := K) pairs c (Fin.castAdd 3 i) =
      heClassicScaledHyperbolicTower (K := K) 0 pairs i := by
  rw [heClassicOddC2Odd, Fin.append_left]

@[simp]
theorem heClassicOddC2Odd_tail (pairs : Nat) (c : Kˣ)
    (i : Fin 3) :
    heClassicOddC2Odd (K := K) pairs c
        (Fin.natAdd (2 * pairs) i) =
      let delta :=
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      ![1, -delta, c * delta] i := by
  rw [heClassicOddC2Odd, Fin.append_right]

/-- Lemma 2.9(ii), order profile of the odd-order `C₂` row. -/
theorem heClassicOddC2Odd_order (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * pairs + 3)) :
    ordUnit K (heClassicOddC2Odd (K := K) pairs c i) =
      if i.val = 2 * pairs + 2 then ordUnit K c else 0 := by
  let laws : DyadicDiscriminantClassLaws K := inferInstance
  let delta := laws.discriminantUnit
  have hdelta : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1
      laws.discriminant_isValuationUnit
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    have hi : i = Fin.castAdd 3 j := Fin.ext rfl
    rw [hi, heClassicOddC2Odd_head,
      heClassicScaledHyperbolicTower_zero_order]
    simp [j]
    omega
  · have htail : i.val = 2 * pairs ∨
        i.val = 2 * pairs + 1 ∨ i.val = 2 * pairs + 2 := by omega
    rcases htail with hzero | hone | htwo
    · have hi : i = Fin.natAdd (2 * pairs) (0 : Fin 3) := by
        apply Fin.ext
        simpa using hzero
      rw [hi, heClassicOddC2Odd_tail]
      simp only [Matrix.cons_val_zero]
      rw [BONG.ordUnit_one_unit]
      simp
    · have hi : i = Fin.natAdd (2 * pairs) (1 : Fin 3) := by
        apply Fin.ext
        simpa using hone
      rw [hi, heClassicOddC2Odd_tail]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [ordUnit_neg, hdelta]
      simp
    · have hi : i = Fin.natAdd (2 * pairs) (2 : Fin 3) := by
        apply Fin.ext
        simpa using htwo
      rw [hi, heClassicOddC2Odd_tail]
      simp only [Matrix.cons_val, Matrix.cons_val_zero]
      rw [ordUnit_mul, hdelta]
      simp

/-- The odd-order `C₂` row satisfies every adjacent binary condition. -/
theorem heClassicOddC2Odd_adjacentAdmissible
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicOddC2Odd (K := K) pairs c) := by
  let laws : DyadicDiscriminantClassLaws K := inferInstance
  let delta := laws.discriminantUnit
  have hdelta : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1
      laws.discriminant_isValuationUnit
  intro i hi
  by_cases hinternal : i.val + 1 < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, by omega⟩
    let k : Fin (2 * pairs) := ⟨i.val + 1, hinternal⟩
    have hiCast : (i : Fin (2 * pairs + 3)) = Fin.castAdd 3 j :=
      Fin.ext rfl
    have hnextCast :
        (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
          Fin.castAdd 3 k := Fin.ext rfl
    have hcurrentValue :
        heClassicOddC2Odd (K := K) pairs c i =
          heClassicScaledHyperbolicTower (K := K) 0 pairs j := by
      calc
        _ = heClassicOddC2Odd (K := K) pairs c (Fin.castAdd 3 j) :=
          congrArg (heClassicOddC2Odd (K := K) pairs c) hiCast
        _ = _ := heClassicOddC2Odd_head pairs c j
    have hnextValue :
        heClassicOddC2Odd (K := K) pairs c ⟨i.val + 1, hi⟩ =
          heClassicScaledHyperbolicTower (K := K) 0 pairs k := by
      calc
        _ = heClassicOddC2Odd (K := K) pairs c (Fin.castAdd 3 k) :=
          congrArg (heClassicOddC2Odd (K := K) pairs c) hnextCast
        _ = _ := heClassicOddC2Odd_head pairs c k
    rw [hcurrentValue, hnextValue]
    have hratio := heClassicScaledHyperbolicTower_zero_adjacentRatio
      (K := K) pairs j (by simpa [j] using hinternal)
    have hk : (⟨j.val + 1, by simpa [j] using hinternal⟩ :
        Fin (2 * pairs)) = k := Fin.ext rfl
    rw [hk] at hratio
    rw [hratio]
    exact BONG.isBinaryParameterAdmissible_neg_one (K := K)
  · have hcases : i.val + 1 = 2 * pairs ∨
        i.val = 2 * pairs ∨ i.val = 2 * pairs + 1 := by omega
    rcases hcases with hboundary | hfirstTail | hsecondTail
    · have hiHead : i.val < 2 * pairs := by omega
      let j : Fin (2 * pairs) := ⟨i.val, hiHead⟩
      have hiCast : i = Fin.castAdd 3 j := Fin.ext rfl
      have hnextCast :
          (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
            Fin.natAdd (2 * pairs) (0 : Fin 3) := by
        apply Fin.ext
        simpa using hboundary
      have hcurrentValue :
          heClassicOddC2Odd (K := K) pairs c i = -1 := by
        calc
          _ = heClassicScaledHyperbolicTower (K := K) 0 pairs j := by
            rw [hiCast, heClassicOddC2Odd_head]
          _ = -1 := by
            have hodd : ¬ Even i.val := by
              intro heven
              rcases heven with ⟨z, hz⟩
              omega
            simp [heClassicScaledHyperbolicTower, j, hodd,
              uniformizerPowerUnit]
      have hnextValue :
          heClassicOddC2Odd (K := K) pairs c ⟨i.val + 1, hi⟩ = 1 := by
        rw [hnextCast, heClassicOddC2Odd_tail]
        rfl
      rw [hcurrentValue, hnextValue]
      have hquotient : (1 : Kˣ) / (-1) = -1 := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_one]
        field_simp
      rw [hquotient]
      exact BONG.isBinaryParameterAdmissible_neg_one (K := K)
    · have hiEq : i = ⟨2 * pairs, by omega⟩ := Fin.ext hfirstTail
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
          ⟨2 * pairs + 1, by omega⟩ := by
        apply Fin.ext
        simpa [hfirstTail]
      have hcurrentValue :
          heClassicOddC2Odd (K := K) pairs c i = 1 := by
        calc
          _ = heClassicOddC2Odd (K := K) pairs c
              ⟨2 * pairs, by omega⟩ :=
            congrArg (heClassicOddC2Odd (K := K) pairs c) hiEq
          _ = 1 := by
            rw [show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) =
              Fin.natAdd (2 * pairs) (0 : Fin 3) by exact Fin.ext rfl,
              heClassicOddC2Odd_tail]
            rfl
      have hnextValue :
          heClassicOddC2Odd (K := K) pairs c ⟨i.val + 1, hi⟩ =
            -delta := by
        calc
          _ = heClassicOddC2Odd (K := K) pairs c
              ⟨2 * pairs + 1, by omega⟩ :=
            congrArg (heClassicOddC2Odd (K := K) pairs c) hnextEq
          _ = -delta := by
            rw [show (⟨2 * pairs + 1, by omega⟩ :
                Fin (2 * pairs + 3)) =
              Fin.natAdd (2 * pairs) (1 : Fin 3) by exact Fin.ext rfl,
              heClassicOddC2Odd_tail]
            rfl
      rw [hcurrentValue, hnextValue]
      have hquotient : (-delta) / (1 : Kˣ) = -delta := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_one]
        field_simp
      rw [hquotient]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        delta (by omega)
    · have hiEq : i = ⟨2 * pairs + 1, by omega⟩ := Fin.ext hsecondTail
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
          ⟨2 * pairs + 2, by omega⟩ := by
        apply Fin.ext
        simpa [hsecondTail]
      have hcurrentValue :
          heClassicOddC2Odd (K := K) pairs c i = -delta := by
        calc
          _ = heClassicOddC2Odd (K := K) pairs c
              ⟨2 * pairs + 1, by omega⟩ :=
            congrArg (heClassicOddC2Odd (K := K) pairs c) hiEq
          _ = -delta := by
            rw [show (⟨2 * pairs + 1, by omega⟩ :
                Fin (2 * pairs + 3)) =
              Fin.natAdd (2 * pairs) (1 : Fin 3) by exact Fin.ext rfl,
              heClassicOddC2Odd_tail]
            rfl
      have hnextValue :
          heClassicOddC2Odd (K := K) pairs c ⟨i.val + 1, hi⟩ =
            c * delta := by
        calc
          _ = heClassicOddC2Odd (K := K) pairs c
              ⟨2 * pairs + 2, by omega⟩ :=
            congrArg (heClassicOddC2Odd (K := K) pairs c) hnextEq
          _ = c * delta := by
            rw [show (⟨2 * pairs + 2, by omega⟩ :
                Fin (2 * pairs + 3)) =
              Fin.natAdd (2 * pairs) (2 : Fin 3) by exact Fin.ext rfl,
              heClassicOddC2Odd_tail]
            rfl
      rw [hcurrentValue, hnextValue]
      have hquotient : (c * delta) / (-delta) = -c := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_mul]
        field_simp [Units.ne_zero delta]
      rw [hquotient]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg c hc

/-- The two parity chains in the odd-order `C₂` row are weakly increasing. -/
theorem heClassicOddC2Odd_weakTwoStep
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicOddC2Odd (K := K) pairs c) := by
  intro i hi
  rw [heClassicOddC2Odd_order, heClassicOddC2Odd_order]
  by_cases hfinal : i.val + 2 = 2 * pairs + 2
  · rw [if_pos hfinal]
    have hcurrent : i.val ≠ 2 * pairs + 2 := by omega
    rw [if_neg hcurrent]
    exact hc
  · rw [if_neg hfinal]
    have hcurrent : i.val ≠ 2 * pairs + 2 := by omega
    rw [if_neg hcurrent]

/-- Exact good BONG carried by the odd-order `C₂` row. -/
noncomputable def heClassicOddC2OddGoodBONG
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :=
  heHuExactGoodBONG (heClassicOddC2Odd (K := K) pairs c)
    (heClassicOddC2Odd_adjacentAdmissible pairs c hc)
    (heClassicOddC2Odd_weakTwoStep pairs c hc)

/-- Proposition 2.8(iii), odd-order branch of the second odd column. -/
theorem heClassicOddC2Odd_isClassicIntegral
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicOddC2OddGoodBONG (K := K) pairs c hc
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC2Odd (K := K) pairs c))
      (heHuExactRealization
        (heClassicOddC2Odd (K := K) pairs c)
        (heClassicOddC2Odd_adjacentAdmissible pairs c hc)
        (heClassicOddC2Odd_weakTwoStep pairs c hc)).lattice := by
  dsimp only
  let b := heClassicOddC2OddGoodBONG (K := K) pairs c hc
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicOddC2OddGoodBONG, heHuExactGoodBONG_order]
  rw [heClassicOddC2Odd_order, heClassicOddC2Odd_order]
  simp

/-! ## The even-order branch of the odd second-column row -/

@[simp]
theorem heClassicOddC2Even_head (pairs : Nat)
    (c omega omegaSharp : Kˣ) (i : Fin (2 * pairs)) :
    heClassicOddC2Even (K := K) pairs c omega omegaSharp
        (Fin.castAdd 3 i) =
      heClassicScaledHyperbolicTower (K := K) 0 pairs i := by
  rw [heClassicOddC2Even, Fin.append_left]

@[simp]
theorem heClassicOddC2Even_tail (pairs : Nat)
    (c omega omegaSharp : Kˣ) (i : Fin 3) :
    heClassicOddC2Even (K := K) pairs c omega omegaSharp
        (Fin.natAdd (2 * pairs) i) =
      ![c * omegaSharp, -(c * omegaSharp * omega), c * omega] i := by
  rw [heClassicOddC2Even, Fin.append_right]

/-- Lemma 2.9(ii), the zero order profile of the even-order `C₂` row. -/
theorem heClassicOddC2Even_order_zero (pairs : Nat)
    (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0)
    (i : Fin (2 * pairs + 3)) :
    ordUnit K
      (heClassicOddC2Even (K := K) pairs c omega omegaSharp i) = 0 := by
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    have hi : i = Fin.castAdd 3 j := Fin.ext rfl
    rw [hi, heClassicOddC2Even_head,
      heClassicScaledHyperbolicTower_zero_order]
  · have htail : i.val = 2 * pairs ∨
        i.val = 2 * pairs + 1 ∨ i.val = 2 * pairs + 2 := by omega
    rcases htail with hzero | hone | htwo
    · have hi : i = Fin.natAdd (2 * pairs) (0 : Fin 3) := by
        apply Fin.ext
        simpa using hzero
      rw [hi, heClassicOddC2Even_tail]
      simp only [Matrix.cons_val_zero]
      rw [ordUnit_mul, hc, homegaSharp]
      omega
    · have hi : i = Fin.natAdd (2 * pairs) (1 : Fin 3) := by
        apply Fin.ext
        simpa using hone
      rw [hi, heClassicOddC2Even_tail]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [ordUnit_neg, ordUnit_mul, ordUnit_mul, hc,
        homegaSharp, homega]
      omega
    · have hi : i = Fin.natAdd (2 * pairs) (2 : Fin 3) := by
        apply Fin.ext
        simpa using htwo
      rw [hi, heClassicOddC2Even_tail]
      simp only [Matrix.cons_val, Matrix.cons_val_zero]
      rw [ordUnit_mul, hc, homega]
      omega

/-- The even-order `C₂` row satisfies every adjacent binary condition. -/
theorem heClassicOddC2Even_adjacentAdmissible
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicOddC2Even (K := K) pairs c omega omegaSharp) := by
  intro i hi
  by_cases hinternal : i.val + 1 < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, by omega⟩
    let k : Fin (2 * pairs) := ⟨i.val + 1, hinternal⟩
    have hiCast : (i : Fin (2 * pairs + 3)) = Fin.castAdd 3 j :=
      Fin.ext rfl
    have hnextCast :
        (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
          Fin.castAdd 3 k := Fin.ext rfl
    have hcurrentValue :
        heClassicOddC2Even (K := K) pairs c omega omegaSharp i =
          heClassicScaledHyperbolicTower (K := K) 0 pairs j := by
      calc
        _ = heClassicOddC2Even (K := K) pairs c omega omegaSharp
            (Fin.castAdd 3 j) :=
          congrArg
            (heClassicOddC2Even (K := K) pairs c omega omegaSharp) hiCast
        _ = _ := heClassicOddC2Even_head pairs c omega omegaSharp j
    have hnextValue :
        heClassicOddC2Even (K := K) pairs c omega omegaSharp
            ⟨i.val + 1, hi⟩ =
          heClassicScaledHyperbolicTower (K := K) 0 pairs k := by
      calc
        _ = heClassicOddC2Even (K := K) pairs c omega omegaSharp
            (Fin.castAdd 3 k) :=
          congrArg
            (heClassicOddC2Even (K := K) pairs c omega omegaSharp) hnextCast
        _ = _ := heClassicOddC2Even_head pairs c omega omegaSharp k
    rw [hcurrentValue, hnextValue]
    have hratio := heClassicScaledHyperbolicTower_zero_adjacentRatio
      (K := K) pairs j (by simpa [j] using hinternal)
    have hk : (⟨j.val + 1, by simpa [j] using hinternal⟩ :
        Fin (2 * pairs)) = k := Fin.ext rfl
    rw [hk] at hratio
    rw [hratio]
    exact BONG.isBinaryParameterAdmissible_neg_one (K := K)
  · have hcases : i.val + 1 = 2 * pairs ∨
        i.val = 2 * pairs ∨ i.val = 2 * pairs + 1 := by omega
    rcases hcases with hboundary | hfirstTail | hsecondTail
    · have hiHead : i.val < 2 * pairs := by omega
      let j : Fin (2 * pairs) := ⟨i.val, hiHead⟩
      have hiCast : i = Fin.castAdd 3 j := Fin.ext rfl
      have hnextCast :
          (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
            Fin.natAdd (2 * pairs) (0 : Fin 3) := by
        apply Fin.ext
        simpa using hboundary
      have hcurrentValue :
          heClassicOddC2Even (K := K) pairs c omega omegaSharp i = -1 := by
        calc
          _ = heClassicScaledHyperbolicTower (K := K) 0 pairs j := by
            rw [hiCast, heClassicOddC2Even_head]
          _ = -1 := by
            have hodd : ¬ Even i.val := by
              intro heven
              rcases heven with ⟨z, hz⟩
              omega
            simp [heClassicScaledHyperbolicTower, j, hodd,
              uniformizerPowerUnit]
      have hnextValue :
          heClassicOddC2Even (K := K) pairs c omega omegaSharp
              ⟨i.val + 1, hi⟩ = c * omegaSharp := by
        rw [hnextCast, heClassicOddC2Even_tail]
        rfl
      rw [hcurrentValue, hnextValue]
      have hquotient : (c * omegaSharp) / (-1 : Kˣ) =
          -(c * omegaSharp) := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_one,
          Units.val_mul]
        field_simp
      rw [hquotient]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        (c * omegaSharp) (by rw [ordUnit_mul, hc, homegaSharp]; omega)
    · have hiEq : i = ⟨2 * pairs, by omega⟩ := Fin.ext hfirstTail
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
          ⟨2 * pairs + 1, by omega⟩ := by
        apply Fin.ext
        simpa [hfirstTail]
      have hcurrentValue :
          heClassicOddC2Even (K := K) pairs c omega omegaSharp i =
            c * omegaSharp := by
        calc
          _ = heClassicOddC2Even (K := K) pairs c omega omegaSharp
              ⟨2 * pairs, by omega⟩ :=
            congrArg
              (heClassicOddC2Even (K := K) pairs c omega omegaSharp) hiEq
          _ = c * omegaSharp := by
            rw [show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) =
              Fin.natAdd (2 * pairs) (0 : Fin 3) by exact Fin.ext rfl,
              heClassicOddC2Even_tail]
            rfl
      have hnextValue :
          heClassicOddC2Even (K := K) pairs c omega omegaSharp
              ⟨i.val + 1, hi⟩ = -(c * omegaSharp * omega) := by
        calc
          _ = heClassicOddC2Even (K := K) pairs c omega omegaSharp
              ⟨2 * pairs + 1, by omega⟩ :=
            congrArg
              (heClassicOddC2Even (K := K) pairs c omega omegaSharp) hnextEq
          _ = -(c * omegaSharp * omega) := by
            rw [show (⟨2 * pairs + 1, by omega⟩ :
                Fin (2 * pairs + 3)) =
              Fin.natAdd (2 * pairs) (1 : Fin 3) by exact Fin.ext rfl,
              heClassicOddC2Even_tail]
            rfl
      rw [hcurrentValue, hnextValue]
      have hquotient : -(c * omegaSharp * omega) / (c * omegaSharp) =
          -omega := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_mul]
        field_simp [Units.ne_zero c, Units.ne_zero omegaSharp]
      rw [hquotient]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        omega (by omega)
    · have hiEq : i = ⟨2 * pairs + 1, by omega⟩ := Fin.ext hsecondTail
      have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 3)) =
          ⟨2 * pairs + 2, by omega⟩ := by
        apply Fin.ext
        simpa [hsecondTail]
      have hcurrentValue :
          heClassicOddC2Even (K := K) pairs c omega omegaSharp i =
            -(c * omegaSharp * omega) := by
        calc
          _ = heClassicOddC2Even (K := K) pairs c omega omegaSharp
              ⟨2 * pairs + 1, by omega⟩ :=
            congrArg
              (heClassicOddC2Even (K := K) pairs c omega omegaSharp) hiEq
          _ = -(c * omegaSharp * omega) := by
            rw [show (⟨2 * pairs + 1, by omega⟩ :
                Fin (2 * pairs + 3)) =
              Fin.natAdd (2 * pairs) (1 : Fin 3) by exact Fin.ext rfl,
              heClassicOddC2Even_tail]
            rfl
      have hnextValue :
          heClassicOddC2Even (K := K) pairs c omega omegaSharp
              ⟨i.val + 1, hi⟩ = c * omega := by
        calc
          _ = heClassicOddC2Even (K := K) pairs c omega omegaSharp
              ⟨2 * pairs + 2, by omega⟩ :=
            congrArg
              (heClassicOddC2Even (K := K) pairs c omega omegaSharp) hnextEq
          _ = c * omega := by
            rw [show (⟨2 * pairs + 2, by omega⟩ :
                Fin (2 * pairs + 3)) =
              Fin.natAdd (2 * pairs) (2 : Fin 3) by exact Fin.ext rfl,
              heClassicOddC2Even_tail]
            rfl
      rw [hcurrentValue, hnextValue]
      let inverseSharp : Kˣ := omegaSharp⁻¹
      have hinverseOrder : ordUnit K inverseSharp = 0 := by
        dsimp only [inverseSharp]
        rw [ordUnit_inv, homegaSharp]
        omega
      have hquotient : (c * omega) / (-(c * omegaSharp * omega)) =
          -inverseSharp := by
        apply Units.ext
        simp only [inverseSharp, Units.val_div_eq_div_val, Units.val_neg,
          Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp [Units.ne_zero c, Units.ne_zero omega,
          Units.ne_zero omegaSharp]
      rw [hquotient]
      exact BONG.isBinaryParameterAdmissible_neg_of_ordUnit_nonneg
        inverseSharp (by omega)

/-- The two parity chains in the even-order `C₂` row are constant. -/
theorem heClassicOddC2Even_weakTwoStep
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicOddC2Even (K := K) pairs c omega omegaSharp) := by
  intro i hi
  rw [heClassicOddC2Even_order_zero pairs c omega omegaSharp hc homega
      homegaSharp,
    heClassicOddC2Even_order_zero pairs c omega omegaSharp hc homega
      homegaSharp]

/-- Exact good BONG carried by the even-order odd `C₂` row. -/
noncomputable def heClassicOddC2EvenGoodBONG
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :=
  heHuExactGoodBONG
    (heClassicOddC2Even (K := K) pairs c omega omegaSharp)
    (heClassicOddC2Even_adjacentAdmissible pairs c omega omegaSharp hc
      homega homegaSharp)
    (heClassicOddC2Even_weakTwoStep pairs c omega omegaSharp hc homega
      homegaSharp)

/-- Proposition 2.8(iii), even-order branch of the second odd column. -/
theorem heClassicOddC2Even_isClassicIntegral
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :
    let b := heClassicOddC2EvenGoodBONG (K := K) pairs c omega omegaSharp
      hc homega homegaSharp
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC2Even (K := K) pairs c omega omegaSharp))
      (heHuExactRealization
        (heClassicOddC2Even (K := K) pairs c omega omegaSharp)
        (heClassicOddC2Even_adjacentAdmissible pairs c omega omegaSharp hc
          homega homegaSharp)
        (heClassicOddC2Even_weakTwoStep pairs c omega omegaSharp hc
          homega homegaSharp)).lattice := by
  dsimp only
  let b := heClassicOddC2EvenGoodBONG (K := K) pairs c omega omegaSharp
    hc homega homegaSharp
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_order]
  rw [heClassicOddC2Even_order_zero pairs c omega omegaSharp hc homega
      homegaSharp,
    heClassicOddC2Even_order_zero pairs c omega omegaSharp hc homega
      homegaSharp]
  omega

/-! ## The even exceptional `H_e` rows -/

@[simp]
theorem heClassicEvenH_head (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * pairs)) :
    heClassicEvenH (K := K) pairs c (Fin.castAdd 2 i) =
      heClassicScaledHyperbolicTower (K := K)
        (ramificationIndex K) pairs i := by
  rw [heClassicEvenH, Fin.append_left]

@[simp]
theorem heClassicEvenH_tail (pairs : Nat) (c : Kˣ) (i : Fin 2) :
    heClassicEvenH (K := K) pairs c (Fin.natAdd (2 * pairs) i) =
      ![uniformizerPowerUnit K (ramificationIndex K : Int),
        -(c * uniformizerPowerUnit K
          (-(ramificationIndex K : Int)))] i := by
  rw [heClassicEvenH, Fin.append_right]

/-- Away from its final coefficient, `H_e^n(c)` is literally one longer
`H_e` tower. -/
theorem heClassicEvenH_beforeLast (pairs : Nat) (c : Kˣ)
    (i : Fin (2 * pairs + 2)) (hi : i.val < 2 * pairs + 1) :
    heClassicEvenH (K := K) pairs c i =
      heClassicScaledHyperbolicTower (K := K)
        (ramificationIndex K) (pairs + 1) i := by
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    have hiCast : i = Fin.castAdd 2 j := Fin.ext rfl
    rw [hiCast, heClassicEvenH_head]
    simp [heClassicScaledHyperbolicTower, j]
  · have hboundary : i.val = 2 * pairs := by omega
    have hiTail : i = Fin.natAdd (2 * pairs) (0 : Fin 2) := by
      apply Fin.ext
      simpa using hboundary
    rw [hiTail, heClassicEvenH_tail]
    simp [heClassicScaledHyperbolicTower]

/-- The final coefficient of `H_e^n(c)` is `-cπ^{-e}`. -/
theorem heClassicEvenH_last (pairs : Nat) (c : Kˣ) :
    heClassicEvenH (K := K) pairs c
        ⟨2 * pairs + 1, by omega⟩ =
      -(c * uniformizerPowerUnit K
        (-(ramificationIndex K : Int))) := by
  rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      Fin.natAdd (2 * pairs) (1 : Fin 2) by exact Fin.ext rfl,
    heClassicEvenH_tail]
  rfl

/-- Lemma 2.9(i), exact alternating order profile of the exceptional rows. -/
theorem heClassicEvenH_order (pairs : Nat) (c : Kˣ)
    (hc : ordUnit K c = 0) (i : Fin (2 * pairs + 2)) :
    ordUnit K (heClassicEvenH (K := K) pairs c i) =
      if Even i.val then (ramificationIndex K : Int)
      else -(ramificationIndex K : Int) := by
  by_cases hlast : i.val = 2 * pairs + 1
  · have hi : i = ⟨2 * pairs + 1, by omega⟩ := Fin.ext hlast
    rw [hi, heClassicEvenH_last, ordUnit_neg, ordUnit_mul,
      ordUnit_uniformizerPowerUnit, hc]
    have hodd : ¬ Even (2 * pairs + 1) :=
      Nat.not_even_two_mul_add_one pairs
    rw [if_neg hodd]
    omega
  · have hbefore : i.val < 2 * pairs + 1 := by omega
    rw [heClassicEvenH_beforeLast pairs c i hbefore,
      heClassicScaledHyperbolicTower_order]

/-- Every adjacent quotient in the exceptional row is admissible for the
two parameters retained in Definition 2.6. -/
theorem heClassicEvenH_adjacentAdmissible
    (pairs : Nat) (c : Kˣ)
    (hc : c = 1 ∨
      c = (inferInstance :
        DyadicDiscriminantClassLaws K).discriminantUnit) :
    BONG.CoefficientAdjacentAdmissible
      (heClassicEvenH (K := K) pairs c) := by
  intro i hi
  by_cases hlast : i.val = 2 * pairs
  · have hiEq : i = ⟨2 * pairs, by omega⟩ := Fin.ext hlast
    have hnextEq : (⟨i.val + 1, hi⟩ : Fin (2 * pairs + 2)) =
        ⟨2 * pairs + 1, by omega⟩ := by
      apply Fin.ext
      simpa [hlast]
    have hcurrentValue :
        heClassicEvenH (K := K) pairs c i =
          uniformizerPowerUnit K (ramificationIndex K : Int) := by
      calc
        _ = heClassicEvenH (K := K) pairs c
            ⟨2 * pairs, by omega⟩ :=
          congrArg (heClassicEvenH (K := K) pairs c) hiEq
        _ = heClassicEvenH (K := K) pairs c
            (Fin.natAdd (2 * pairs) (0 : Fin 2)) :=
          congrArg (heClassicEvenH (K := K) pairs c) (Fin.ext rfl)
        _ = _ := by rw [heClassicEvenH_tail]; rfl
    have hnextValue :
        heClassicEvenH (K := K) pairs c ⟨i.val + 1, hi⟩ =
          -(c * uniformizerPowerUnit K
            (-(ramificationIndex K : Int))) := by
      calc
        _ = heClassicEvenH (K := K) pairs c
            ⟨2 * pairs + 1, by omega⟩ :=
          congrArg (heClassicEvenH (K := K) pairs c) hnextEq
        _ = _ := heClassicEvenH_last pairs c
    rw [hcurrentValue, hnextValue]
    have hquotient :
        -(c * uniformizerPowerUnit K
            (-(ramificationIndex K : Int))) /
          uniformizerPowerUnit K (ramificationIndex K : Int) =
        -(c * uniformizerPowerUnit K
          (-(2 * (ramificationIndex K : Int)))) := by
      rw [neg_div]
      congr 1
      calc
        c * uniformizerPowerUnit K (-(ramificationIndex K : Int)) /
            uniformizerPowerUnit K (ramificationIndex K : Int) =
            c * (uniformizerPowerUnit K (-(ramificationIndex K : Int)) /
              uniformizerPowerUnit K (ramificationIndex K : Int)) := by
          simp only [div_eq_mul_inv]
          ac_rfl
        _ = c * uniformizerPowerUnit K
            (-(2 * (ramificationIndex K : Int))) := by
          rw [uniformizerPowerUnit_div_uniformizerPowerUnit]
          congr 2
          ring
    rw [hquotient]
    exact heClassicEvenH_terminalAdmissible c hc
  · have hbefore : i.val < 2 * pairs := by omega
    have hcurrentBefore : i.val < 2 * pairs + 1 := by omega
    have hnextBefore : i.val + 1 < 2 * pairs + 1 := by omega
    have hcurrentValue := heClassicEvenH_beforeLast pairs c i hcurrentBefore
    have hnextValue := heClassicEvenH_beforeLast pairs c
      ⟨i.val + 1, hi⟩ hnextBefore
    rw [hcurrentValue, hnextValue]
    have hratio := heClassicScaledHyperbolicTower_adjacentRatio
      (K := K) (ramificationIndex K) (pairs + 1) i hi
    rw [hratio]
    by_cases heven : Even i.val
    · rw [if_pos heven]
      exact isBinaryParameterAdmissible_neg_uniformizerPower_negTwoE
        (K := K)
    · rw [if_neg heven]
      exact isBinaryParameterAdmissible_neg_uniformizerPower_twoE
        (K := K)

/-- The two parity chains in each exceptional row are constant. -/
theorem heClassicEvenH_weakTwoStep
    (pairs : Nat) (c : Kˣ) (hc : ordUnit K c = 0) :
    BONG.CoefficientWeakTwoStep (K := K)
      (heClassicEvenH (K := K) pairs c) := by
  intro i hi
  rw [heClassicEvenH_order pairs c hc,
    heClassicEvenH_order pairs c hc]
  rcases Nat.even_or_odd i.val with heven | hodd
  · have hnextEven : Even (i.val + 2) := by
      rcases heven with ⟨z, hz⟩
      exact ⟨z + 1, by omega⟩
    rw [if_pos heven, if_pos hnextEven]
  · have hnotEven : ¬ Even i.val := Nat.not_even_iff_odd.mpr hodd
    have hnextOdd : Odd (i.val + 2) := by
      rcases hodd with ⟨z, hz⟩
      exact ⟨z + 1, by omega⟩
    have hnextNotEven : ¬ Even (i.val + 2) :=
      Nat.not_even_iff_odd.mpr hnextOdd
    rw [if_neg hnotEven, if_neg hnextNotEven]

/-- Exact good BONG carried by either exceptional `H_e` row. -/
noncomputable def heClassicEvenHGoodBONG
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (inferInstance :
        DyadicDiscriminantClassLaws K).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :=
  heHuExactGoodBONG (heClassicEvenH (K := K) pairs c)
    (heClassicEvenH_adjacentAdmissible pairs c hcClass)
    (heClassicEvenH_weakTwoStep pairs c hcOrder)

/-- Proposition 2.8(iii), the exceptional even rows are classic integral. -/
theorem heClassicEvenH_isClassicIntegral
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (inferInstance :
        DyadicDiscriminantClassLaws K).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicEvenH (K := K) pairs c))
      (heHuExactRealization
        (heClassicEvenH (K := K) pairs c)
        (heClassicEvenH_adjacentAdmissible pairs c hcClass)
        (heClassicEvenH_weakTwoStep pairs c hcOrder)).lattice := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  rw [b.isClassicIntegral_iff_firstOrders]
  simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenH_order pairs c hcOrder,
    heClassicEvenH_order pairs c hcOrder]
  have hePos : 0 ≤ (ramificationIndex K : Int) := by
    exact_mod_cast (Nat.zero_le (ramificationIndex K))
  simp [hePos]

end Bong
