/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicProfiles
import Bong.Bong.Beli2009AlphaCompression

/-!
# He (2024), Lemma 2.9(iii)

This file isolates the invariant argument in Lemma 2.9(iii).  Once the first
`n - 1` BONG orders vanish, the final order is `1 - d`, and the final adjacent
defect is `d \in {0,1}`, Proposition 2.3 fixes the final alpha invariant and
Proposition 2.4 propagates the value one through the whole zero-order prefix.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Adjacent defects of an exact coefficient model reduce definitionally to
the two displayed coefficients. -/
theorem heHuExactGoodBONG_adjacentDefect {n : Nat}
    (coeff : Fin (n + 1) → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible coeff)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) coeff)
    (j : Fin n) :
    (heHuExactGoodBONG coeff hadj hweak).adjacentDefect j =
      defectOrder (K := K) (-(coeff j.castSucc * coeff j.succ)) := by
  unfold adjacentDefect adjacentProduct
  rw [heHuExactGoodBONG_valueUnit, heHuExactGoodBONG_valueUnit]

/-- The alpha-invariant part of He, Lemma 2.9(iii), stated in the exact
zero-based indexing used by the formalization. -/
theorem he2022ClassicLemma29iii_alpha {n : Nat}
    (a : GoodBONG q L (n + 2))
    (hClassic : Lattice.IsClassicIntegral q L)
    (d : Int) (hd : d = 0 ∨ d = 1)
    (horders : ∀ i : Fin (n + 2), i.val ≤ n → a.order i = 0)
    (hlastOrder :
      a.order (⟨n + 1, by omega⟩ : Fin (n + 2)) = 1 - d)
    (hlastDefect :
      a.adjacentDefect (⟨n, by omega⟩ : Fin (n + 1)) =
        (((d : Int) : ℚ) : WithTop ℚ)) :
    ∀ i : Fin (n + 1), a.alphaValue i = 1 := by
  let lastGap : Fin (n + 1) := ⟨n, by omega⟩
  have hlastLeftOrder : a.order lastGap.castSucc = 0 := by
    apply horders
    simp only [lastGap, Fin.val_castSucc]
    exact le_rfl
  have hlastRightIndex : lastGap.succ =
      (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [lastGap, Fin.val_succ]
  have hlastGap : a.orderGap lastGap = 1 - d := by
    unfold orderGap
    rw [hlastLeftOrder, hlastRightIndex, hlastOrder]
    omega
  have hlastDefect' : a.adjacentDefect lastGap =
      (((d : Int) : ℚ) : WithTop ℚ) := by
    simpa only [lastGap] using hlastDefect
  have hlastAlpha : a.alphaValue lastGap = 1 := by
    rcases hd with rfl | rfl
    · apply a.alphaValue_eq_one_of_orderGap_eq_endpoint lastGap
      right
      simpa only [sub_zero] using hlastGap
    · apply (a.he2022ClassicProposition23 lastGap).rawDefectCriterion
      rw [hlastGap, hlastDefect']
      norm_num
  have hprefixOrders :
      ∀ i : Fin (n + 2), i ≤ lastGap.castSucc → a.order i = 0 := by
    intro i hi
    apply horders i
    exact Fin.mk_le_mk.mp hi
  have hprefixAlpha :=
    (a.he2022ClassicProposition24 hClassic).alphaOneOnZeroPrefix
      lastGap hprefixOrders lastGap le_rfl (le_of_eq hlastAlpha)
  intro i
  by_cases hi : i = lastGap
  · simpa only [hi] using hlastAlpha
  · apply hprefixAlpha i
    have hle : i ≤ lastGap := by
      exact Fin.mk_le_mk.mpr (Nat.le_of_lt_succ i.isLt)
    exact lt_of_le_of_ne hle hi

/-- The corrected candidate-level form needed by the even-order odd `C₂`
row.  In that row the defect-one candidate occurs one gap before the final
gap, not at the final adjacent product.  This is exactly what the minimum in
formula (2.4) permits. -/
theorem he2022ClassicLemma29iii_alpha_of_zero_orders {n : Nat}
    (a : GoodBONG q L (n + 2))
    (hClassic : Lattice.IsClassicIntegral q L)
    (horders : ∀ i : Fin (n + 2), a.order i = 0)
    (hanchor : ∃ k : Fin (n + 1),
      a.adjacentDefect k = ((1 : ℚ) : WithTop ℚ)) :
    ∀ i : Fin (n + 1), a.alphaValue i = 1 := by
  let lastGap : Fin (n + 1) := ⟨n, by omega⟩
  rcases hanchor with ⟨k, hk⟩
  have hlastGap : a.orderGap lastGap = 0 := by
    unfold orderGap
    rw [horders lastGap.castSucc, horders lastGap.succ]
    omega
  have hlastNe : a.alphaValue lastGap ≠ 0 := by
    intro hzero
    have hendpoint :=
      (a.he2022ClassicProposition23 lastGap).alphaZero.mp hzero
    rw [hlastGap] at hendpoint
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hlastLower : 1 ≤ a.alphaValue lastGap :=
    a.heHuOne_le_alphaValue_of_ne_zero lastGap hlastNe
  have hcandidate : a.leftDefectCandidate lastGap k =
      ((1 : ℚ) : WithTop ℚ) := by
    unfold leftDefectCandidate
    rw [horders lastGap.succ, horders k.castSucc, hk]
    norm_num
  have hlastUpperTop : (a.alphaValue lastGap : WithTop ℚ) ≤
      ((1 : ℚ) : WithTop ℚ) := by
    rw [a.coe_alphaValue, ← hcandidate]
    exact a.alpha_le_leftDefectCandidate (Fin.le_last k)
  have hlastUpper : a.alphaValue lastGap ≤ 1 := by
    exact_mod_cast hlastUpperTop
  have hlastAlpha : a.alphaValue lastGap = 1 :=
    le_antisymm hlastUpper hlastLower
  have hprefixOrders :
      ∀ i : Fin (n + 2), i ≤ lastGap.castSucc → a.order i = 0 := by
    intro i _hi
    exact horders i
  have hprefixAlpha :=
    (a.he2022ClassicProposition24 hClassic).alphaOneOnZeroPrefix
      lastGap hprefixOrders lastGap le_rfl (le_of_eq hlastAlpha)
  intro i
  by_cases hi : i = lastGap
  · simpa only [hi] using hlastAlpha
  · apply hprefixAlpha i
    have hle : i ≤ lastGap := by
      exact Fin.mk_le_mk.mpr (Nat.le_of_lt_succ i.isLt)
    exact lt_of_le_of_ne hle hi

end BONG.GoodBONG

/-! ## Exact terminal defects of the displayed `C` rows -/

/-- The final adjacent defect of `C₁^(2r+2)(c)` is `d(c)`. -/
theorem heClassicEvenC1_lastAdjacentDefect
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
    b.adjacentDefect (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) =
      BONG.GoodBONG.defectOrder (K := K) c := by
  dsimp only
  unfold heClassicEvenC1GoodBONG
  rw [BONG.GoodBONG.heHuExactGoodBONG_adjacentDefect]
  have hleft : heClassicEvenC1 (K := K) pairs c
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) = 1 := by
    rw [show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
      Fin.natAdd (2 * pairs) (0 : Fin 2) by exact Fin.ext rfl,
      heClassicEvenC1_tail]
    rfl
  have hright : heClassicEvenC1 (K := K) pairs c
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) = -c := by
    rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      Fin.natAdd (2 * pairs) (1 : Fin 2) by exact Fin.ext rfl,
      heClassicEvenC1_tail]
    rfl
  have hcast : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)).castSucc =
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) := Fin.ext rfl
  have hsucc : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)).succ =
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) := Fin.ext rfl
  rw [hcast, hsucc, hleft, hright]
  simp

/-- The square multiplier `cSharp` does not change the final defect of
`C₂^(2r+2)(c)`. -/
theorem heClassicEvenC2_lastAdjacentDefect
    (pairs : Nat) (c cSharp : Kˣ)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0) :
    let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
    b.adjacentDefect (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) =
      BONG.GoodBONG.defectOrder (K := K) c := by
  dsimp only
  unfold heClassicEvenC2GoodBONG
  rw [BONG.GoodBONG.heHuExactGoodBONG_adjacentDefect]
  have hleft : heClassicEvenC2 (K := K) pairs c cSharp
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) = cSharp := by
    rw [show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
      Fin.natAdd (2 * pairs) (0 : Fin 2) by exact Fin.ext rfl,
      heClassicEvenC2_tail]
    rfl
  have hright : heClassicEvenC2 (K := K) pairs c cSharp
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
        -(cSharp * c) := by
    rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      Fin.natAdd (2 * pairs) (1 : Fin 2) by exact Fin.ext rfl,
      heClassicEvenC2_tail]
    rfl
  have hcast : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)).castSucc =
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) := Fin.ext rfl
  have hsucc : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)).succ =
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) := Fin.ext rfl
  rw [hcast, hsucc, hleft, hright]
  have hfactor : -(cSharp * (-(cSharp * c))) = c * cSharp ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hfactor, BONG.GoodBONG.defectOrder_mul_square]

/-- The final adjacent defect of the odd first row is again `d(c)`. -/
theorem heClassicOddC1_lastAdjacentDefect
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicOddC1GoodBONG (K := K) pairs c hc
    b.adjacentDefect (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      BONG.GoodBONG.defectOrder (K := K) c := by
  dsimp only
  unfold heClassicOddC1GoodBONG
  rw [BONG.GoodBONG.heHuExactGoodBONG_adjacentDefect]
  let k : Fin (2 * (pairs + 1)) := ⟨2 * pairs + 1, by omega⟩
  have hleft : heClassicOddC1 (K := K) pairs c
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) = -1 := by
    have hcast : (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) =
        k.castSucc := Fin.ext rfl
    rw [hcast, heClassicOddC1_head]
    have hodd : ¬ Even k.val := by
      dsimp only [k]
      exact Nat.not_even_two_mul_add_one pairs
    simp [heClassicScaledHyperbolicTower, k, hodd, uniformizerPowerUnit]
  have hright : heClassicOddC1 (K := K) pairs c
      (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 3)) = c := by
    rw [show (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 3)) =
      Fin.last (2 * pairs + 2) by exact Fin.ext rfl,
      heClassicOddC1_last]
  have hcast :
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)).castSucc =
        (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) := Fin.ext rfl
  have hsucc :
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)).succ =
        (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 3)) := Fin.ext rfl
  rw [hcast, hsucc, hleft, hright]
  simp

/-- In the odd-order branch of the odd second row, the discriminant factor
is squared and hence leaves the final defect equal to `d(c)`. -/
theorem heClassicOddC2Odd_lastAdjacentDefect
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicOddC2OddGoodBONG (K := K) pairs c hc
    b.adjacentDefect (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      BONG.GoodBONG.defectOrder (K := K) c := by
  dsimp only
  unfold heClassicOddC2OddGoodBONG
  rw [BONG.GoodBONG.heHuExactGoodBONG_adjacentDefect]
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have hleft : heClassicOddC2Odd (K := K) pairs c
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) = -delta := by
    rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) =
      Fin.natAdd (2 * pairs) (1 : Fin 3) by exact Fin.ext rfl,
      heClassicOddC2Odd_tail]
    rfl
  have hright : heClassicOddC2Odd (K := K) pairs c
      (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 3)) = c * delta := by
    rw [show (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 3)) =
      Fin.natAdd (2 * pairs) (2 : Fin 3) by exact Fin.ext rfl,
      heClassicOddC2Odd_tail]
    rfl
  have hcast :
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)).castSucc =
        (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) := Fin.ext rfl
  have hsucc :
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)).succ =
        (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 3)) := Fin.ext rfl
  rw [hcast, hsucc, hleft, hright]
  have hfactor : -((-delta) * (c * delta)) = c * delta ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hfactor, BONG.GoodBONG.defectOrder_mul_square]

/-- In the even-order branch of the odd second row, the preceding adjacent
product is `omega` times a square.  This is the actual defect-one candidate
used by formula (2.4). -/
theorem heClassicOddC2Even_anchorAdjacentDefect
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :
    let b := heClassicOddC2EvenGoodBONG (K := K) pairs c omega omegaSharp
      hc homega homegaSharp
    b.adjacentDefect (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
      BONG.GoodBONG.defectOrder (K := K) omega := by
  dsimp only
  unfold heClassicOddC2EvenGoodBONG
  rw [BONG.GoodBONG.heHuExactGoodBONG_adjacentDefect]
  have hleft : heClassicOddC2Even (K := K) pairs c omega omegaSharp
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) = c * omegaSharp := by
    rw [show (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) =
      Fin.natAdd (2 * pairs) (0 : Fin 3) by exact Fin.ext rfl,
      heClassicOddC2Even_tail]
    rfl
  have hright : heClassicOddC2Even (K := K) pairs c omega omegaSharp
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) =
        -(c * omegaSharp * omega) := by
    rw [show (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) =
      Fin.natAdd (2 * pairs) (1 : Fin 3) by exact Fin.ext rfl,
      heClassicOddC2Even_tail]
    rfl
  have hcast : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)).castSucc =
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 3)) := Fin.ext rfl
  have hsucc : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)).succ =
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 3)) := Fin.ext rfl
  rw [hcast, hsucc, hleft, hright]
  have hfactor : -((c * omegaSharp) * (-(c * omegaSharp * omega))) =
      omega * (c * omegaSharp) ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hfactor, BONG.GoodBONG.defectOrder_mul_square]

/-! ## Lemma 2.9(iii) for every displayed row -/

/-- Lemma 2.9(iii) for the even first-column row. -/
theorem heClassicEvenC1_alpha_eq_one
    (pairs : Nat) (c : Kˣ) (d : Int)
    (hc : 0 ≤ ordUnit K c) (hd : d = 0 ∨ d = 1)
    (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
    ∀ i : Fin (2 * pairs + 1), b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  apply b.he2022ClassicLemma29iii_alpha
    (heClassicEvenC1_isClassicIntegral (K := K) pairs c hc) d hd
  · intro i hi
    simp only [b, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    simp only [if_neg (by omega : i.val ≠ 2 * pairs + 1)]
  · simp only [b, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    simp [hcOrder]
  · rw [heClassicEvenC1_lastAdjacentDefect pairs c hc, hcDefect]

/-- Lemma 2.9(iii) for the even second-column row. -/
theorem heClassicEvenC2_alpha_eq_one
    (pairs : Nat) (c cSharp : Kˣ) (d : Int)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0)
    (hd : d = 0 ∨ d = 1) (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
    ∀ i : Fin (2 * pairs + 1), b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  apply b.he2022ClassicLemma29iii_alpha
    (heClassicEvenC2_isClassicIntegral (K := K) pairs c cSharp hc hcSharp)
      d hd
  · intro i hi
    simp only [b, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order pairs c cSharp hcSharp]
    simp only [if_neg (by omega : i.val ≠ 2 * pairs + 1)]
  · simp only [b, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order pairs c cSharp hcSharp]
    simp [hcOrder]
  · rw [heClassicEvenC2_lastAdjacentDefect pairs c cSharp hc hcSharp,
      hcDefect]

/-- Lemma 2.9(iii) for the odd first-column row. -/
theorem heClassicOddC1_alpha_eq_one
    (pairs : Nat) (c : Kˣ) (d : Int)
    (hc : 0 ≤ ordUnit K c) (hd : d = 0 ∨ d = 1)
    (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    let b := heClassicOddC1GoodBONG (K := K) pairs c hc
    ∀ i : Fin (2 * pairs + 2), b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicOddC1GoodBONG (K := K) pairs c hc
  apply b.he2022ClassicLemma29iii_alpha
    (heClassicOddC1_isClassicIntegral (K := K) pairs c hc) d hd
  · intro i hi
    simp only [b, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order]
    simp only [if_neg (by omega : i.val ≠ 2 * pairs + 2)]
  · simp only [b, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order]
    simp [hcOrder]
  · rw [heClassicOddC1_lastAdjacentDefect pairs c hc, hcDefect]

/-- Lemma 2.9(iii), defect-zero odd-order branch of the odd second row. -/
theorem heClassicOddC2Odd_alpha_eq_one
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcOrder : ordUnit K c = 1)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c =
      ((0 : ℚ) : WithTop ℚ)) :
    let b := heClassicOddC2OddGoodBONG (K := K) pairs c hc
    ∀ i : Fin (2 * pairs + 2), b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicOddC2OddGoodBONG (K := K) pairs c hc
  apply b.he2022ClassicLemma29iii_alpha
    (heClassicOddC2Odd_isClassicIntegral (K := K) pairs c hc) 0
      (Or.inl rfl)
  · intro i hi
    simp only [b, heClassicOddC2OddGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC2Odd_order]
    simp only [if_neg (by omega : i.val ≠ 2 * pairs + 2)]
  · simp only [b, heClassicOddC2OddGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC2Odd_order]
    simp [hcOrder]
  · rw [heClassicOddC2Odd_lastAdjacentDefect pairs c hc, hcDefect]
    norm_num

/-- Lemma 2.9(iii), defect-one even-order branch of the odd second row.
The proof uses the preceding `omega`-defect candidate verified above. -/
theorem heClassicOddC2Even_alpha_eq_one
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0)
    (homegaDefect : BONG.GoodBONG.defectOrder (K := K) omega =
      ((1 : ℚ) : WithTop ℚ)) :
    let b := heClassicOddC2EvenGoodBONG (K := K) pairs c omega omegaSharp
      hc homega homegaSharp
    ∀ i : Fin (2 * pairs + 2), b.alphaValue i = 1 := by
  dsimp only
  let b := heClassicOddC2EvenGoodBONG (K := K) pairs c omega omegaSharp
    hc homega homegaSharp
  apply b.he2022ClassicLemma29iii_alpha_of_zero_orders
    (heClassicOddC2Even_isClassicIntegral (K := K) pairs c omega omegaSharp
      hc homega homegaSharp)
  · intro i
    simp only [b, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC2Even_order_zero pairs c omega omegaSharp hc homega
      homegaSharp i
  · refine ⟨⟨2 * pairs, by omega⟩, ?_⟩
    rw [heClassicOddC2Even_anchorAdjacentDefect pairs c omega omegaSharp hc
      homega homegaSharp, homegaDefect]

end Bong
