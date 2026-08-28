/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma910Assembly
import Bong.Bong.Beli2019DominationOrderBound

/-!
# Beli (2019), Lemma 9.10: the junction with the unchanged tail

This file verifies the two Beli-2006 numerical conditions for the coefficient
family `[b₁,b₂,b₃,a₄,…,aₙ]`.  All old adjacent pairs inherit admissibility
from one of the two BONGs.  Consequently the only genuinely new local
condition is admissibility of `a₄ / b₃`.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {M : Lattice K V} {P : Lattice K W} {N : Nat}

@[simp]
theorem valueUnit_castLength
    {m n : Nat} {L : Lattice K V}
    (b : GoodBONG q L m) (h : m = n) (i : Fin n) :
    (b.castLength h).valueUnit i =
      b.valueUnit ⟨i.1, by omega⟩ := by
  subst n
  rfl

/-- Replacing a quotient by the corresponding product does not change the
relative defect: the two arguments differ by the square of the denominator. -/
theorem defectOrder_neg_div_eq_neg_mul
    [QuadraticDefectLaws K] (x y : Kˣ) :
    defectOrder (K := K) (-(x / y)) =
      defectOrder (K := K) (-(x * y)) := by
  have hfactor : -(x * y) = (-(x / y)) * y ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero y]
  rw [hfactor, defectOrder_mul_square]

/-- If two ternary BONGs lie in the same quadratic space, the product of
their last coefficients has the same defect as the product of their first
adjacent products.  This is the determinant-square step in Lemma 9.10. -/
theorem defectOrder_ternaryLastProduct_eq_adjacentProducts
    [QuadraticDefectLaws K]
    {L Q : Lattice K V}
    (b : GoodBONG q L 3) (c : GoodBONG q Q 3) :
    defectOrder (K := K)
        (b.valueUnit (2 : Fin 3) * c.valueUnit (2 : Fin 3)) =
      defectOrder (K := K)
        (b.adjacentProduct (0 : Fin 2) *
          c.adjacentProduct (0 : Fin 2)) := by
  rcases BONG.exists_valueProduct_eq_mul_square
      b.toBONG c.toBONG with ⟨p, hp⟩
  have hbProduct : b.toBONG.valueProduct =
      b.toBONG.valueUnit (0 : Fin 3) *
        b.toBONG.valueUnit (1 : Fin 3) *
          b.toBONG.valueUnit (2 : Fin 3) := by
    unfold BONG.valueProduct
    rw [b.toBONG.prefixProduct_succ 2 (by omega),
      b.toBONG.prefixProduct_succ 1 (by omega),
      b.toBONG.prefixProduct_succ 0 (by omega),
      b.toBONG.prefixProduct_zero]
    simp only [one_mul]
    congr 1
  have hcProduct : c.toBONG.valueProduct =
      c.toBONG.valueUnit (0 : Fin 3) *
        c.toBONG.valueUnit (1 : Fin 3) *
          c.toBONG.valueUnit (2 : Fin 3) := by
    unfold BONG.valueProduct
    rw [c.toBONG.prefixProduct_succ 2 (by omega),
      c.toBONG.prefixProduct_succ 1 (by omega),
      c.toBONG.prefixProduct_succ 0 (by omega),
      c.toBONG.prefixProduct_zero]
    simp only [one_mul]
    congr 1
  let firstPairs : Kˣ :=
    b.adjacentProduct (0 : Fin 2) * c.adjacentProduct (0 : Fin 2)
  let lastPair : Kˣ :=
    b.valueUnit (2 : Fin 3) * c.valueUnit (2 : Fin 3)
  have htotal : firstPairs * lastPair =
      (b.toBONG.valueProduct * p) ^ 2 := by
    rw [pow_two]
    rw [show b.toBONG.valueProduct * p *
          (b.toBONG.valueProduct * p) =
        b.toBONG.valueProduct *
          (b.toBONG.valueProduct * p ^ 2) by
        simp only [pow_two]
        ac_rfl,
      ← hp, hbProduct, hcProduct]
    dsimp only [firstPairs, lastPair, adjacentProduct, valueUnit]
    change (-(b.toBONG.valueUnit (0 : Fin 3) *
          b.toBONG.valueUnit (1 : Fin 3)) *
          -(c.toBONG.valueUnit (0 : Fin 3) *
            c.toBONG.valueUnit (1 : Fin 3))) *
        (b.toBONG.valueUnit (2 : Fin 3) *
          c.toBONG.valueUnit (2 : Fin 3)) =
      (b.toBONG.valueUnit (0 : Fin 3) *
          b.toBONG.valueUnit (1 : Fin 3) *
            b.toBONG.valueUnit (2 : Fin 3)) *
        (c.toBONG.valueUnit (0 : Fin 3) *
          c.toBONG.valueUnit (1 : Fin 3) *
            c.toBONG.valueUnit (2 : Fin 3))
    rw [neg_mul_neg]
    ac_rfl
  have hfactor : lastPair = firstPairs⁻¹ *
      (b.toBONG.valueProduct * p) ^ 2 := by
    calc
      lastPair = firstPairs⁻¹ * (firstPairs * lastPair) := by group
      _ = firstPairs⁻¹ *
          (b.toBONG.valueProduct * p) ^ 2 := by
        rw [htotal]
  rw [show b.valueUnit (2 : Fin 3) * c.valueUnit (2 : Fin 3) =
      lastPair by rfl,
    show b.adjacentProduct (0 : Fin 2) *
        c.adjacentProduct (0 : Fin 2) = firstPairs by rfl,
    hfactor, defectOrder_mul_square, defectOrder_inv]

/-- The defect of the boundary quotient is the defect obtained by joining
the old last adjacent pair to the ternary determinant comparison. -/
theorem defectOrder_neg_div_eq_boundaryProduct
    [QuadraticDefectLaws K] (x y z : Kˣ) :
    defectOrder (K := K) (-(y / z)) =
      defectOrder (K := K) (-(x * y) * (x * z)) := by
  have hproduct : -(x * y) * (x * z) =
      (-(y * z)) * x ^ 2 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val]
    ring
  calc
    defectOrder (K := K) (-(y / z)) =
        defectOrder (K := K) (-(y * z)) :=
      defectOrder_neg_div_eq_neg_mul y z
    _ = defectOrder (K := K) (-(x * y) * (x * z)) := by
      rw [hproduct, defectOrder_mul_square]

/-- The unique new binary junction in Lemma 9.10 is admissible.  This is
the paper's determinant-square and defect-domination argument, including
both bounds `β₁ ≤ α₁ + 2` and `β₁ ≤ α₃`. -/
theorem beli2019Lemma910_boundaryAdmissible
    [QuadraticDefectLaws K]
    [alphaAmbient : Beli2006AlphaLaws.{u, v} K]
    [alphaPrefix : Beli2006AlphaLaws.{u, w} K]
    {R₁ R₂ A₁ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha :
      reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd N i))
    (hfourth : ∀ hN : 0 < N,
      R₂ + 2 ≤ a.order
        (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)))
    (hLower : A₁ ≤ β₁) (hUpper : β₁ ≤ A₁ + 2)
    (hThird : ∀ hN : 0 < N,
      (β₁ : ℚ) ≤
        (a.castLength (show 3 + N = N + 3 by omega)).alphaValue
          (⟨2, by omega⟩ : Fin (N + 2))) :
    ∀ hN : 0 < N,
      IsBinaryParameterAdmissible
        (a.valueUnit (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)) /
          D.bong.valueUnit (2 : Fin 3)) := by
  intro hN
  letI : Beli2006AlphaLaws.{u, w} K := alphaPrefix
  let tailZero : Fin N := ⟨0, hN⟩
  let third : Fin (3 + N) := Fin.castAdd N (2 : Fin 3)
  let fourth : Fin (3 + N) := Fin.natAdd 3 tailZero
  let hlength : 3 + N = N + 3 := by omega
  let ambient : GoodBONG q M (N + 3) := a.castLength hlength
  let boundary : Fin (N + 2) := ⟨2, by omega⟩
  have hboundaryCastOrder :
      ambient.order boundary.castSucc = a.order third := by
    rw [GoodBONG.order_castLength]
    congr 1
  have hboundarySuccOrder :
      ambient.order boundary.succ = a.order fourth := by
    rw [GoodBONG.order_castLength]
    congr 1
  have hboundaryCastValue :
      ambient.valueUnit boundary.castSucc = a.valueUnit third := by
    rw [valueUnit_castLength]
    congr 1
  have hboundarySuccValue :
      ambient.valueUnit boundary.succ = a.valueUnit fourth := by
    rw [valueUnit_castLength]
    congr 1
  have hthirdOrder : a.order third = R₁ := by
    simpa [third] using horders (2 : Fin 3)
  have hfourthOrder : R₂ + 2 ≤ a.order fourth := by
    simpa only [fourth, tailZero] using hfourth hN
  have hbetaThird : (β₁ : ℚ) ≤ ambient.alphaValue boundary := by
    simpa only [ambient, hlength, boundary] using hThird hN
  have hA₁NonnegativeQ : (0 : ℚ) ≤ (A₁ : ℚ) := by
    rw [← hrefFirstAlpha]
    exact (reference.alpha_p2 (0 : Fin 2)).1
  have hA₁Nonnegative : 0 ≤ A₁ := by
    exact_mod_cast hA₁NonnegativeQ
  have hbetaNonnegative : 0 ≤ β₁ := hA₁Nonnegative.trans hLower

  let lower : ℚ := ((R₁ - (R₂ + 2) : Int) : ℚ) + (β₁ : ℚ)
  have hrefRaw :=
    reference.order_sub_add_alpha_le_adjacentDefect (0 : Fin 2)
  change (((((reference.order (0 : Fin 3) -
      reference.order (1 : Fin 3) : Int) : ℚ) +
        reference.alphaValue (0 : Fin 2) : ℚ)) : WithTop ℚ) ≤
      reference.adjacentDefect (0 : Fin 2) at hrefRaw
  rw [hrefOrders (0 : Fin 3), hrefOrders (1 : Fin 3),
    hrefFirstAlpha] at hrefRaw
  have hUpperQ : (β₁ : ℚ) ≤ (A₁ : ℚ) + 2 := by
    exact_mod_cast hUpper
  have hlowerReferenceQ : lower ≤
      ((R₁ - R₂ : Int) : ℚ) + (A₁ : ℚ) := by
    dsimp only [lower]
    push_cast
    linarith
  have hlowerReferenceTop : (lower : WithTop ℚ) ≤
      (((R₁ - R₂ : Int) : ℚ) + (A₁ : ℚ) : ℚ) := by
    exact_mod_cast hlowerReferenceQ
  have hrefLower : (lower : WithTop ℚ) ≤
      reference.adjacentDefect (0 : Fin 2) :=
    hlowerReferenceTop.trans hrefRaw

  have hDRaw :=
    D.bong.order_sub_add_alpha_le_adjacentDefect (0 : Fin 2)
  change (((((D.bong.order (0 : Fin 3) -
      D.bong.order (1 : Fin 3) : Int) : ℚ) +
        D.bong.alphaValue (0 : Fin 2) : ℚ)) : WithTop ℚ) ≤
      D.bong.adjacentDefect (0 : Fin 2) at hDRaw
  rw [D.order_zero, D.order_one, D.firstAlpha] at hDRaw
  have hDLower : (lower : WithTop ℚ) ≤
      D.bong.adjacentDefect (0 : Fin 2) := by
    simpa only [lower] using hDRaw

  have hpairDomination := defectOrder_mul_ge_min (K := K)
    (reference.adjacentProduct (0 : Fin 2))
    (D.bong.adjacentProduct (0 : Fin 2))
  change min (reference.adjacentDefect (0 : Fin 2))
      (D.bong.adjacentDefect (0 : Fin 2)) ≤
    defectOrder (K := K)
      (reference.adjacentProduct (0 : Fin 2) *
        D.bong.adjacentProduct (0 : Fin 2)) at hpairDomination
  have hpairLower : (lower : WithTop ℚ) ≤
      defectOrder (K := K)
        (reference.adjacentProduct (0 : Fin 2) *
          D.bong.adjacentProduct (0 : Fin 2)) :=
    (le_min hrefLower hDLower).trans hpairDomination
  have hlastDefect :=
    defectOrder_ternaryLastProduct_eq_adjacentProducts reference D.bong
  have hcrossReference : (lower : WithTop ℚ) ≤
      defectOrder (K := K)
        (reference.valueUnit (2 : Fin 3) *
          D.bong.valueUnit (2 : Fin 3)) := by
    rw [hlastDefect]
    exact hpairLower
  have hcross : (lower : WithTop ℚ) ≤
      defectOrder (K := K)
        (a.valueUnit third * D.bong.valueUnit (2 : Fin 3)) := by
    rw [← hprefix (2 : Fin 3)]
    exact hcrossReference

  let junctionLower : ℚ :=
    ((a.order third - a.order fourth : Int) : ℚ) + (β₁ : ℚ)
  letI : Beli2006AlphaLaws.{u, v} K := alphaAmbient
  have hlocalRaw := ambient.order_sub_add_alpha_le_adjacentDefect boundary
  change (((((ambient.order boundary.castSucc -
      ambient.order boundary.succ : Int) : ℚ) +
      ambient.alphaValue boundary : ℚ)) : WithTop ℚ) ≤
    ambient.adjacentDefect boundary at hlocalRaw
  rw [hboundaryCastOrder, hboundarySuccOrder] at hlocalRaw
  have hbetaThirdTop : ((β₁ : ℚ) : WithTop ℚ) ≤
      (ambient.alphaValue boundary : WithTop ℚ) := by
    exact_mod_cast hbetaThird
  have hlocalShift := add_le_add_left hbetaThirdTop
    ((((a.order third - a.order fourth : Int) : ℚ)) : WithTop ℚ)
  have hjunctionCoe : (junctionLower : WithTop ℚ) =
      (((((a.order third - a.order fourth : Int) : ℚ)) : WithTop ℚ) +
        (((β₁ : ℚ)) : WithTop ℚ)) := by
    dsimp only [junctionLower]
    norm_cast
  have hlocalLower : (junctionLower : WithTop ℚ) ≤
      ambient.adjacentDefect boundary := by
    have hshifted : (junctionLower : WithTop ℚ) ≤
        (((((a.order third - a.order fourth : Int) : ℚ)) : WithTop ℚ) +
          (ambient.alphaValue boundary : WithTop ℚ)) := by
      rw [hjunctionCoe]
      simpa only [add_comm] using hlocalShift
    exact hshifted.trans hlocalRaw
  have hboundaryProduct : ambient.adjacentProduct boundary =
      -(a.valueUnit third * a.valueUnit fourth) := by
    unfold adjacentProduct
    rw [hboundaryCastValue, hboundarySuccValue]
  unfold adjacentDefect at hlocalLower
  rw [hboundaryProduct] at hlocalLower

  let shift : ℚ := (a.order fourth - R₁ : Int)
  have hcrossBaseInt :
      0 ≤ (a.order fourth - R₁) +
        (R₁ - (R₂ + 2) + β₁) := by
    omega
  have hcrossBase : (0 : WithTop ℚ) ≤
      (shift : WithTop ℚ) + (lower : WithTop ℚ) := by
    have hcrossBaseQ : (0 : ℚ) ≤ shift + lower := by
      dsimp only [shift, lower]
      exact_mod_cast hcrossBaseInt
    exact_mod_cast hcrossBaseQ
  have hcrossSum : (0 : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          (a.valueUnit third * D.bong.valueUnit (2 : Fin 3)) :=
    hcrossBase.trans (by
      simpa only [add_comm] using
        add_le_add_left hcross (shift : WithTop ℚ))
  have hlocalBaseInt :
      0 ≤ (a.order fourth - R₁) +
        (a.order third - a.order fourth + β₁) := by
    omega
  have hlocalBase : (0 : WithTop ℚ) ≤
      (shift : WithTop ℚ) + (junctionLower : WithTop ℚ) := by
    have hlocalBaseQ : (0 : ℚ) ≤ shift + junctionLower := by
      dsimp only [shift, junctionLower]
      exact_mod_cast hlocalBaseInt
    exact_mod_cast hlocalBaseQ
  have hlocalSum : (0 : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          (-(a.valueUnit third * a.valueUnit fourth)) :=
    hlocalBase.trans (by
      simpa only [add_comm] using
        add_le_add_left hlocalLower (shift : WithTop ℚ))
  have hminimumSum : (0 : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        min
          (defectOrder (K := K)
            (-(a.valueUnit third * a.valueUnit fourth)))
          (defectOrder (K := K)
            (a.valueUnit third * D.bong.valueUnit (2 : Fin 3))) :=
    withTop_le_shift_add_min 0 shift _ _ hlocalSum hcrossSum
  have hboundaryDomination := defectOrder_mul_ge_min (K := K)
    (-(a.valueUnit third * a.valueUnit fourth))
    (a.valueUnit third * D.bong.valueUnit (2 : Fin 3))
  have hproductSum : (0 : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          (-(a.valueUnit third * a.valueUnit fourth) *
            (a.valueUnit third * D.bong.valueUnit (2 : Fin 3))) :=
    hminimumSum.trans (by
      simpa only [add_comm] using
        add_le_add_left hboundaryDomination (shift : WithTop ℚ))
  have htargetSum : (0 : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          (-(a.valueUnit fourth / D.bong.valueUnit (2 : Fin 3))) := by
    rw [defectOrder_neg_div_eq_boundaryProduct
      (a.valueUnit third) (a.valueUnit fourth)
        (D.bong.valueUnit (2 : Fin 3))]
    exact hproductSum

  have hratioOrder :
      ordUnit K (a.valueUnit fourth / D.bong.valueUnit (2 : Fin 3)) =
        a.order fourth - R₁ := by
    change ordUnit K
        (a.toBONG.valueUnit fourth /
          D.bong.toBONG.valueUnit (2 : Fin 3)) =
      a.toBONG.order fourth - R₁
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      ← a.toBONG.order_eq_ordUnit fourth,
      ← D.bong.toBONG.order_eq_ordUnit (2 : Fin 3)]
    change a.order fourth + -D.bong.order (2 : Fin 3) =
      a.order fourth - R₁
    rw [D.order_two]
    rfl
  have hnegativeRatioOrder :
      ordUnit K (-(a.valueUnit fourth /
        D.bong.valueUnit (2 : Fin 3))) = a.order fourth - R₁ := by
    rw [ordUnit_neg, hratioOrder]
  have hDAdmissible :=
    D.bong.toBONG.adjacentParameter_isBinaryParameterAdmissible
      (0 : Fin 3) (by omega)
  have hDOrderLower := hDAdmissible.ordUnit_ge_neg_two_mul_e
  have hDGap := D.bong.toBONG.ordUnit_adjacentParameter
    (0 : Fin 3) (by omega)
  change ordUnit K
      (D.bong.toBONG.adjacentParameter (0 : Fin 3) (by omega)) =
    D.bong.order (1 : Fin 3) - D.bong.order (0 : Fin 3) at hDGap
  rw [D.order_zero, D.order_one] at hDGap
  rw [hDGap] at hDOrderLower
  change IsBinaryParameterAdmissible
    (a.valueUnit fourth / D.bong.valueUnit (2 : Fin 3))
  apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
    (a.valueUnit fourth / D.bong.valueUnit (2 : Fin 3))).2
  constructor
  · rw [hratioOrder]
    omega
  · apply
      Dyadic.hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
    rw [hnegativeRatioOrder]
    exact htargetSum

/-- The weak two-step inequalities for `[b₁,b₂,b₃,a₄,…,aₙ]` follow
from goodness of the original BONG and the single paper hypothesis
`R₄ ≥ R₂ + 2`. -/
theorem beli2019Lemma910Values_weakTwoStep
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hfourth : ∀ hN : 0 < N,
      R₂ + 2 ≤ a.order
        (Fin.natAdd 3 (⟨0, hN⟩ : Fin N))) :
    ∀ (i : Fin (3 + N)) (hi : i.1 + 2 < 3 + N),
      ordUnit K (beli2019Lemma910Values D a i) ≤
        ordUnit K
          (beli2019Lemma910Values D a ⟨i.1 + 2, hi⟩) := by
  intro i hi
  by_cases hi0 : i.1 = 0
  · have hleft : i = Fin.castAdd N (0 : Fin 3) := by
      apply Fin.ext
      simpa using hi0
    have hright : (⟨i.1 + 2, hi⟩ : Fin (3 + N)) =
        Fin.castAdd N (2 : Fin 3) := by
      apply Fin.ext
      simp [hi0]
    rw [hright, hleft, ordUnit_beli2019Lemma910Values_left,
      ordUnit_beli2019Lemma910Values_left, D.order_zero, D.order_two]
  by_cases hi1 : i.1 = 1
  · have hN : 0 < N := by omega
    let j : Fin N := ⟨0, hN⟩
    have hleft : i = Fin.castAdd N (1 : Fin 3) := by
      apply Fin.ext
      simpa using hi1
    have hright : (⟨i.1 + 2, hi⟩ : Fin (3 + N)) =
        Fin.natAdd 3 j := by
      apply Fin.ext
      simp [hi1, j]
    rw [hright, hleft, ordUnit_beli2019Lemma910Values_left,
      ordUnit_beli2019Lemma910Values_right, D.order_one]
    exact hfourth hN
  by_cases hi2 : i.1 = 2
  · have hN : 0 < N := by omega
    let j : Fin N := ⟨1, by omega⟩
    have hleft : i = Fin.castAdd N (2 : Fin 3) := by
      apply Fin.ext
      simpa using hi2
    have hright : (⟨i.1 + 2, hi⟩ : Fin (3 + N)) =
        Fin.natAdd 3 j := by
      apply Fin.ext
      simp [hi2, j]
    calc
      ordUnit K (beli2019Lemma910Values D a i) = R₁ := by
        rw [hleft, ordUnit_beli2019Lemma910Values_left, D.order_two]
      _ = a.order i := by
        rw [hleft, horders (2 : Fin 3)]
        rfl
      _ ≤ a.order ⟨i.1 + 2, hi⟩ := a.good i hi
      _ = ordUnit K
          (beli2019Lemma910Values D a ⟨i.1 + 2, hi⟩) := by
        rw [hright, ordUnit_beli2019Lemma910Values_right]
  · have hthree : 3 ≤ i.1 := by omega
    let j : Fin N := ⟨i.1 - 3, by omega⟩
    let k : Fin N := ⟨i.1 + 2 - 3, by omega⟩
    have hleft : i = Fin.natAdd 3 j := by
      apply Fin.ext
      simp [j]
      omega
    have hright : (⟨i.1 + 2, hi⟩ : Fin (3 + N)) =
        Fin.natAdd 3 k := by
      apply Fin.ext
      simp [k]
      omega
    rw [hright, hleft, ordUnit_beli2019Lemma910Values_right,
      ordUnit_beli2019Lemma910Values_right]
    rw [← hleft, ← hright]
    exact a.good i hi

/-- Apart from the new pair `(b₃,a₄)`, all adjacent parameters of the
assembled coefficient family already occur in one of the two input BONGs. -/
theorem beli2019Lemma910Values_adjacentAdmissible
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (hboundary : ∀ hN : 0 < N,
      IsBinaryParameterAdmissible
        (a.valueUnit (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)) /
          D.bong.valueUnit (2 : Fin 3))) :
    ∀ (i : Fin (3 + N)) (hi : i.1 + 1 < 3 + N),
      IsBinaryParameterAdmissible
        (beli2019Lemma910Values D a ⟨i.1 + 1, hi⟩ /
          beli2019Lemma910Values D a i) := by
  intro i hi
  by_cases hfirst : i.1 < 2
  · let j : Fin 3 := ⟨i.1, by omega⟩
    have hj : j.1 + 1 < 3 := by
      dsimp only [j]
      omega
    have hleft : i = Fin.castAdd N j := by
      apply Fin.ext
      rfl
    have hright : (⟨i.1 + 1, hi⟩ : Fin (3 + N)) =
        Fin.castAdd N ⟨j.1 + 1, hj⟩ := by
      apply Fin.ext
      rfl
    rw [hright, hleft, beli2019Lemma910Values_left,
      beli2019Lemma910Values_left]
    change IsBinaryParameterAdmissible
      (D.bong.toBONG.valueUnit ⟨j.1 + 1, hj⟩ /
        D.bong.toBONG.valueUnit j)
    exact D.bong.toBONG.adjacentParameter_isBinaryParameterAdmissible j hj
  by_cases hboundaryIndex : i.1 = 2
  · have hN : 0 < N := by omega
    let j : Fin N := ⟨0, hN⟩
    have hleft : i = Fin.castAdd N (2 : Fin 3) := by
      apply Fin.ext
      simpa using hboundaryIndex
    have hright : (⟨i.1 + 1, hi⟩ : Fin (3 + N)) =
        Fin.natAdd 3 j := by
      apply Fin.ext
      simp [hboundaryIndex, j]
    rw [hright, hleft, beli2019Lemma910Values_left,
      beli2019Lemma910Values_right]
    exact hboundary hN
  · have hthree : 3 ≤ i.1 := by omega
    let j : Fin N := ⟨i.1 - 3, by omega⟩
    let k : Fin N := ⟨i.1 + 1 - 3, by omega⟩
    have hleft : i = Fin.natAdd 3 j := by
      apply Fin.ext
      simp [j]
      omega
    have hright : (⟨i.1 + 1, hi⟩ : Fin (3 + N)) =
        Fin.natAdd 3 k := by
      apply Fin.ext
      simp [k]
      omega
    rw [hright, hleft, beli2019Lemma910Values_right,
      beli2019Lemma910Values_right]
    change IsBinaryParameterAdmissible
      (a.toBONG.valueUnit (Fin.natAdd 3 k) /
        a.toBONG.valueUnit (Fin.natAdd 3 j))
    rw [← hleft, ← hright]
    exact a.toBONG.adjacentParameter_isBinaryParameterAdmissible i hi

/-- The full coefficient realization after reducing Lemma 9.10 to its
single new binary junction. -/
theorem exists_beli2019Lemma910FullCoefficientRealization_of_boundary
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd N i))
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hfourth : ∀ hN : 0 < N,
      R₂ + 2 ≤ a.order
        (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)))
    (hboundary : ∀ hN : 0 < N,
      IsBinaryParameterAdmissible
        (a.valueUnit (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)) /
          D.bong.valueUnit (2 : Fin 3))) :
    Nonempty (BONG.PrescribedValuesGoodBONGData q (3 + N)
      (beli2019Lemma910Values D a)) := by
  apply exists_beli2019Lemma910FullCoefficientRealization
    reference a D hprefix
  · exact beli2019Lemma910Values_weakTwoStep a D horders hfourth
  · exact beli2019Lemma910Values_adjacentAdmissible a D hboundary

/-- Lemma 9.10's full coefficient realization, with the new junction
discharged from the paper's alpha bounds rather than assumed separately. -/
theorem exists_beli2019Lemma910FullCoefficientRealization_of_alphaBounds
    [QuadraticDefectLaws K]
    [alphaAmbient : Beli2006AlphaLaws.{u, v} K]
    [alphaPrefix : Beli2006AlphaLaws.{u, w} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    {R₁ R₂ A₁ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha :
      reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd N i))
    (hfourth : ∀ hN : 0 < N,
      R₂ + 2 ≤ a.order
        (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)))
    (hLower : A₁ ≤ β₁) (hUpper : β₁ ≤ A₁ + 2)
    (hThird : ∀ hN : 0 < N,
      (β₁ : ℚ) ≤
        (a.castLength (show 3 + N = N + 3 by omega)).alphaValue
          (⟨2, by omega⟩ : Fin (N + 2))) :
    Nonempty (BONG.PrescribedValuesGoodBONGData q (3 + N)
      (beli2019Lemma910Values D a)) := by
  apply exists_beli2019Lemma910FullCoefficientRealization_of_boundary
    reference a D hprefix horders hfourth
  exact beli2019Lemma910_boundaryAdmissible
    (alphaAmbient := alphaAmbient) (alphaPrefix := alphaPrefix)
    reference a D hrefOrders hrefFirstAlpha horders hprefix hfourth
      hLower hUpper hThird

end BONG.GoodBONG

end Bong
