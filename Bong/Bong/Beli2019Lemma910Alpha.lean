/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma910IndexP
import Bong.Bong.InitialTernaryAlpha

/-!
# Beli (2019), Lemma 9.10: the first alpha invariant

This file formalizes the final paragraph of Lemma 9.10.  The first alpha is
localized to the inserted ternary prefix.  Pairs lying in the unchanged tail
are bounded by the old third alpha, while the unique new pair `(b₃,a₄)` is
handled by the determinant-square and defect-domination calculation already
used to prove its admissibility.
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

/-- The new boundary pair contributes a right-defect candidate no smaller
than `β₁`.  This is the strengthened form of the defect calculation in the
last paragraph of Beli (2019), Lemma 9.10. -/
theorem beli2019Lemma910_boundaryDefectCandidate_lower
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
    (hUpper : β₁ ≤ A₁ + 2)
    (hThird : ∀ hN : 0 < N,
      (β₁ : ℚ) ≤
        (a.castLength (show 3 + N = N + 3 by omega)).alphaValue
          (⟨2, by omega⟩ : Fin (N + 2)))
    (hN : 0 < N) :
    ((β₁ : ℚ) : WithTop ℚ) ≤
      ((((a.order (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)) - R₁ : Int) : ℚ) :
          WithTop ℚ) +
        defectOrder (K := K)
          (-(a.valueUnit (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)) *
            D.bong.valueUnit (2 : Fin 3)))) := by
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
      β₁ ≤ (a.order fourth - R₁) +
        (R₁ - (R₂ + 2) + β₁) := by
    omega
  have hcrossBase : ((β₁ : ℚ) : WithTop ℚ) ≤
      (shift : WithTop ℚ) + (lower : WithTop ℚ) := by
    have hcrossBaseQ : (β₁ : ℚ) ≤ shift + lower := by
      dsimp only [shift, lower]
      exact_mod_cast hcrossBaseInt
    exact_mod_cast hcrossBaseQ
  have hcrossSum : ((β₁ : ℚ) : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          (a.valueUnit third * D.bong.valueUnit (2 : Fin 3)) :=
    hcrossBase.trans (by
      simpa only [add_comm] using
        add_le_add_left hcross (shift : WithTop ℚ))
  have hlocalBaseInt :
      β₁ ≤ (a.order fourth - R₁) +
        (a.order third - a.order fourth + β₁) := by
    omega
  have hlocalBase : ((β₁ : ℚ) : WithTop ℚ) ≤
      (shift : WithTop ℚ) + (junctionLower : WithTop ℚ) := by
    have hlocalBaseQ : (β₁ : ℚ) ≤ shift + junctionLower := by
      dsimp only [shift, junctionLower]
      exact_mod_cast hlocalBaseInt
    exact_mod_cast hlocalBaseQ
  have hlocalSum : ((β₁ : ℚ) : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          (-(a.valueUnit third * a.valueUnit fourth)) :=
    hlocalBase.trans (by
      simpa only [add_comm] using
        add_le_add_left hlocalLower (shift : WithTop ℚ))
  have hminimumSum : ((β₁ : ℚ) : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        min
          (defectOrder (K := K)
            (-(a.valueUnit third * a.valueUnit fourth)))
          (defectOrder (K := K)
            (a.valueUnit third * D.bong.valueUnit (2 : Fin 3))) :=
    withTop_le_shift_add_min _ shift _ _ hlocalSum hcrossSum
  have hboundaryDomination := defectOrder_mul_ge_min (K := K)
    (-(a.valueUnit third * a.valueUnit fourth))
    (a.valueUnit third * D.bong.valueUnit (2 : Fin 3))
  have hproductSum : ((β₁ : ℚ) : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          (-(a.valueUnit third * a.valueUnit fourth) *
            (a.valueUnit third * D.bong.valueUnit (2 : Fin 3))) :=
    hminimumSum.trans (by
      simpa only [add_comm] using
        add_le_add_left hboundaryDomination (shift : WithTop ℚ))
  have htargetSum : ((β₁ : ℚ) : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          (-(a.valueUnit fourth / D.bong.valueUnit (2 : Fin 3))) := by
    rw [defectOrder_neg_div_eq_boundaryProduct
      (a.valueUnit third) (a.valueUnit fourth)
        (D.bong.valueUnit (2 : Fin 3))]
    exact hproductSum
  rw [defectOrder_neg_div_eq_neg_mul] at htargetSum
  simpa only [shift, fourth, tailZero] using htargetSum

/-- Every right-defect candidate outside the inserted ternary prefix is at
least `β₁`.  The first such candidate is the new boundary calculation above;
all later candidates are inherited from the old third alpha. -/
theorem beli2019Lemma910_outsideRightDefectCandidate_lower
    [QuadraticDefectLaws K]
    [alphaAmbient : Beli2006AlphaLaws.{u, v} K]
    [alphaPrefix : Beli2006AlphaLaws.{u, w} K]
    {L : Lattice K V} {R₁ R₂ A₁ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (c : GoodBONG q L (N + 3))
    (hvalues : ∀ i : Fin (N + 3),
      c.valueUnit i =
        beli2019Lemma910Values D a ⟨i.1, by omega⟩)
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
    (hUpper : β₁ ≤ A₁ + 2)
    (hThird : ∀ hN : 0 < N,
      (β₁ : ℚ) ≤
        (a.castLength (show 3 + N = N + 3 by omega)).alphaValue
          (⟨2, by omega⟩ : Fin (N + 2)))
    (j : Fin (N + 2)) (hj : 2 ≤ j.1) :
    ((β₁ : ℚ) : WithTop ℚ) ≤
      c.rightDefectCandidate (0 : Fin (N + 2)) j := by
  let hlength : 3 + N = N + 3 := by omega
  let ambient : GoodBONG q M (N + 3) := a.castLength hlength
  by_cases hjTwo : j.1 = 2
  · have hN : 0 < N := by omega
    let boundary : Fin (N + 2) := ⟨2, by omega⟩
    let tailZero : Fin N := ⟨0, hN⟩
    let fourth : Fin (3 + N) := Fin.natAdd 3 tailZero
    have hjEq : j = boundary := by
      apply Fin.ext
      exact hjTwo
    have hboundaryCastValue :
        c.valueUnit boundary.castSucc = D.bong.valueUnit (2 : Fin 3) := by
      rw [hvalues boundary.castSucc]
      rw [show (⟨boundary.castSucc.1, by omega⟩ : Fin (3 + N)) =
          Fin.castAdd N (2 : Fin 3) by
        apply Fin.ext
        rfl]
      exact beli2019Lemma910Values_left D a (2 : Fin 3)
    have hboundarySuccValue :
        c.valueUnit boundary.succ = a.valueUnit fourth := by
      rw [hvalues boundary.succ]
      rw [show (⟨boundary.succ.1, by omega⟩ : Fin (3 + N)) = fourth by
        apply Fin.ext
        rfl]
      exact beli2019Lemma910Values_right D a tailZero
    have hboundarySuccOrder : c.order boundary.succ = a.order fourth := by
      change c.toBONG.order boundary.succ = a.toBONG.order fourth
      rw [c.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit]
      exact congrArg (ordUnit K) hboundarySuccValue
    have hzeroValue :
        c.valueUnit (0 : Fin (N + 3)) = D.bong.valueUnit (0 : Fin 3) := by
      rw [hvalues (0 : Fin (N + 3))]
      rw [show (⟨(0 : Fin (N + 3)).1, by omega⟩ : Fin (3 + N)) =
          Fin.castAdd N (0 : Fin 3) by
        apply Fin.ext
        rfl]
      exact beli2019Lemma910Values_left D a (0 : Fin 3)
    have hzeroOrder : c.order (0 : Fin (N + 3)) = R₁ := by
      calc
        c.order (0 : Fin (N + 3)) = D.bong.order (0 : Fin 3) := by
          change c.toBONG.order (0 : Fin (N + 3)) =
            D.bong.toBONG.order (0 : Fin 3)
          rw [c.toBONG.order_eq_ordUnit, D.bong.toBONG.order_eq_ordUnit]
          exact congrArg (ordUnit K) hzeroValue
        _ = R₁ := D.order_zero
    have hzeroCast : (0 : Fin (N + 2)).castSucc =
        (0 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hraw := beli2019Lemma910_boundaryDefectCandidate_lower
      (alphaAmbient := alphaAmbient) (alphaPrefix := alphaPrefix)
      reference a D hrefOrders hrefFirstAlpha horders hprefix hfourth
        hUpper hThird hN
    rw [hjEq]
    unfold rightDefectCandidate adjacentDefect adjacentProduct
    rw [hboundarySuccOrder, hzeroCast, hzeroOrder, hboundaryCastValue,
      hboundarySuccValue]
    simpa only [fourth, tailZero, mul_comm] using hraw
  · have hjThree : 3 ≤ j.1 := by omega
    let pivot : Fin (N + 2) := ⟨2, by omega⟩
    letI : Beli2006AlphaLaws.{u, v} K := alphaAmbient
    have hbetaAlphaValue : (β₁ : ℚ) ≤ ambient.alphaValue pivot := by
      simpa only [ambient, hlength, pivot] using hThird (by omega)
    have hbetaAlpha : ((β₁ : ℚ) : WithTop ℚ) ≤ ambient.alpha pivot := by
      rw [← ambient.coe_alphaValue]
      exact_mod_cast hbetaAlphaValue
    have hpivotj : pivot ≤ j := by
      change 2 ≤ j.1
      exact hj
    have hambientCandidate : ((β₁ : ℚ) : WithTop ℚ) ≤
        ambient.rightDefectCandidate pivot j :=
      hbetaAlpha.trans (ambient.alpha_le_rightDefectCandidate hpivotj)
    have htailValue : ∀ (i : Fin (N + 3)), 3 ≤ i.1 →
        c.valueUnit i = ambient.valueUnit i := by
      intro i hi
      let k : Fin N := ⟨i.1 - 3, by omega⟩
      rw [hvalues i, valueUnit_castLength]
      rw [show (⟨i.1, by omega⟩ : Fin (3 + N)) = Fin.natAdd 3 k by
        apply Fin.ext
        simp [k]
        omega]
      rw [beli2019Lemma910Values_right]
    have htailCastValue :
        c.valueUnit j.castSucc = ambient.valueUnit j.castSucc :=
      htailValue j.castSucc hjThree
    have htailSuccValue :
        c.valueUnit j.succ = ambient.valueUnit j.succ :=
      htailValue j.succ (by
        change 3 ≤ j.1 + 1
        omega)
    have htailSuccOrder : c.order j.succ = ambient.order j.succ := by
      change c.toBONG.order j.succ = ambient.toBONG.order j.succ
      rw [c.toBONG.order_eq_ordUnit, ambient.toBONG.order_eq_ordUnit]
      exact congrArg (ordUnit K) htailSuccValue
    have htailDefect : c.adjacentDefect j = ambient.adjacentDefect j := by
      unfold adjacentDefect adjacentProduct
      rw [htailCastValue, htailSuccValue]
    have hzeroValue :
        c.valueUnit (0 : Fin (N + 3)) = D.bong.valueUnit (0 : Fin 3) := by
      rw [hvalues (0 : Fin (N + 3))]
      rw [show (⟨(0 : Fin (N + 3)).1, by omega⟩ : Fin (3 + N)) =
          Fin.castAdd N (0 : Fin 3) by
        apply Fin.ext
        rfl]
      exact beli2019Lemma910Values_left D a (0 : Fin 3)
    have hzeroOrder : c.order (0 : Fin (N + 3)) = R₁ := by
      calc
        c.order (0 : Fin (N + 3)) = D.bong.order (0 : Fin 3) := by
          change c.toBONG.order (0 : Fin (N + 3)) =
            D.bong.toBONG.order (0 : Fin 3)
          rw [c.toBONG.order_eq_ordUnit, D.bong.toBONG.order_eq_ordUnit]
          exact congrArg (ordUnit K) hzeroValue
        _ = R₁ := D.order_zero
    have hpivotOrder : ambient.order pivot.castSucc = R₁ := by
      rw [GoodBONG.order_castLength]
      rw [show (⟨pivot.castSucc.1, by omega⟩ : Fin (3 + N)) =
          Fin.castAdd N (2 : Fin 3) by
        apply Fin.ext
        rfl]
      simpa using horders (2 : Fin 3)
    have hzeroCast : (0 : Fin (N + 2)).castSucc =
        (0 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hcandidate : c.rightDefectCandidate (0 : Fin (N + 2)) j =
        ambient.rightDefectCandidate pivot j := by
      unfold rightDefectCandidate
      rw [htailSuccOrder, htailDefect, hzeroCast, hzeroOrder, hpivotOrder]
    rw [hcandidate]
    exact hambientCandidate

/-- A good BONG carrying the coefficients constructed in Lemma 9.10 has
first alpha exactly `β₁`. -/
theorem beli2019Lemma910_firstAlphaValue_of_values
    [QuadraticDefectLaws K]
    [alphaAmbient : Beli2006AlphaLaws.{u, v} K]
    [alphaPrefix : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    {L : Lattice K V} {R₁ R₂ A₁ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (c : GoodBONG q L (N + 3))
    (hvalues : ∀ i : Fin (N + 3),
      c.valueUnit i =
        beli2019Lemma910Values D a ⟨i.1, by omega⟩)
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
    (hUpper : β₁ ≤ A₁ + 2)
    (hThird : ∀ hN : 0 < N,
      (β₁ : ℚ) ≤
        (a.castLength (show 3 + N = N + 3 by omega)).alphaValue
          (⟨2, by omega⟩ : Fin (N + 2))) :
    c.alphaValue (0 : Fin (N + 2)) = (β₁ : ℚ) := by
  rcases c.toBONG.exists_segmentWitness 0 3 (by omega) with ⟨initial⟩
  let first := initial.toGoodBONG c.good
  have hfirstValues : ∀ i : Fin 3,
      first.valueUnit i = D.bong.valueUnit i := by
    intro i
    change initial.bong.valueUnit i = D.bong.valueUnit i
    calc
      initial.bong.valueUnit i =
          c.toBONG.valueUnit (initial.sourceIndex i) := initial.valueUnit_eq i
      _ = c.valueUnit (initial.sourceIndex i) := rfl
      _ = beli2019Lemma910Values D a
          ⟨(initial.sourceIndex i).1, by omega⟩ := hvalues _
      _ = beli2019Lemma910Values D a (Fin.castAdd N i) := by
        congr 1
        apply Fin.ext
        simp [BONG.SegmentWitness.sourceIndex, Fin.castAdd]
      _ = D.bong.valueUnit i := beli2019Lemma910Values_left D a i
  have hfirstAlpha : first.alphaValue (0 : Fin 2) = (β₁ : ℚ) := by
    calc
      first.alphaValue (0 : Fin 2) =
          D.bong.alphaValue (0 : Fin 2) :=
        first.alphaValue_eq_of_valueUnits_eq D.bong hfirstValues
          (0 : Fin 2)
      _ = (β₁ : ℚ) := D.firstAlpha
  have houtside : ∀ j : Fin (N + 2), 2 ≤ j.1 →
      (first.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
        c.rightDefectCandidate (0 : Fin (N + 2)) j := by
    intro j hj
    rw [hfirstAlpha]
    exact beli2019Lemma910_outsideRightDefectCandidate_lower
      (alphaAmbient := alphaAmbient) (alphaPrefix := alphaPrefix)
      reference a D c hvalues hrefOrders hrefFirstAlpha horders hprefix
        hfourth hUpper hThird j hj
  have hglobal := c.firstAlphaValue_eq_initialTernary_of_outsideRightCandidate
    initial houtside
  exact hglobal.trans hfirstAlpha

/-- The full output of Beli (2019), Lemma 9.10: a literal index-uniformizer
sublattice, a good BONG with the prescribed orders and unchanged tail, and
the required first alpha invariant. -/
structure Beli2019Lemma910Data
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁) where
  lattice : Lattice K V
  bong : GoodBONG q lattice (3 + N)
  inclusion : Beli2019IndexPInclusion q M lattice
  values : ∀ i, bong.valueUnit i = beli2019Lemma910Values D a i
  firstAlpha :
    (bong.castLength (show 3 + N = N + 3 by omega)).alphaValue
      (0 : Fin (N + 2)) = (β₁ : ℚ)

/-- Assemble all parts of Lemma 9.10 once its Lemma 9.9 ternary realization
and ternary representation have been supplied. -/
theorem exists_beli2019Lemma910Data_of_realization
    [QuadraticDefectLaws K]
    [alphaAmbient : Beli2006AlphaLaws.{u, v} K]
    [alphaPrefix : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [structuralAmbient : BONGStructuralLaws.{u, v} K]
    [structuralPrefix : BONGStructuralLaws.{u, w} K]
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
          (⟨2, by omega⟩ : Fin (N + 2)))
    (hternary : Lattice.Represents r r P D.lattice) :
    Nonempty (Beli2019Lemma910Data a D) := by
  rcases exists_beli2019Lemma910FullCoefficientRealization_of_alphaBounds
      (alphaAmbient := alphaAmbient) (alphaPrefix := alphaPrefix)
      reference a D hrefOrders hrefFirstAlpha horders hprefix hfourth
        hLower hUpper hThird with ⟨C⟩
  rcases exists_beli2019Lemma910IndexPData
      (structuralAmbient := structuralAmbient)
      (structuralPrefix := structuralPrefix)
      reference a D C hprefix hternary horders with ⟨E⟩
  let hlength : 3 + N = N + 3 := by omega
  let output : GoodBONG q E.lattice (N + 3) := E.bong.castLength hlength
  have houtputValues : ∀ i : Fin (N + 3),
      output.valueUnit i =
        beli2019Lemma910Values D a ⟨i.1, by omega⟩ := by
    intro i
    rw [show output = E.bong.castLength hlength by rfl,
      valueUnit_castLength, E.values]
  have hfirstAlpha : output.alphaValue (0 : Fin (N + 2)) =
      (β₁ : ℚ) :=
    beli2019Lemma910_firstAlphaValue_of_values
      (alphaAmbient := alphaAmbient) (alphaPrefix := alphaPrefix)
      reference a D output houtputValues hrefOrders hrefFirstAlpha horders
        hprefix hfourth hUpper hThird
  exact ⟨{
    lattice := E.lattice
    bong := E.bong
    inclusion := E.inclusion
    values := E.values
    firstAlpha := by
      simpa only [output, hlength] using hfirstAlpha
  }⟩

/-- Beli (2019), Lemma 9.10, after Corollary 8.11 has chosen a BONG whose
initial ternary segment realizes the first alpha.  Lemma 9.9 and Lemma 9.8 are
invoked internally; the conclusion contains the literal index-`p` sublattice,
all prescribed orders and coefficients, and `α₁(N) = β₁`. -/
theorem beli2019Lemma910
    [QuadraticDefectLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [constructionAmbient : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoAmbient : Beli2006SectionTwoLaws.{u, v} K]
    [constructionPrefix : BeliLemma43ConstructionLaws.{u, w} K]
    [sectionTwoPrefix : Beli2006SectionTwoLaws.{u, w} K]
    [structuralAmbient : BONGStructuralLaws.{u, v} K]
    [structuralPrefix : BONGStructuralLaws.{u, w} K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaAmbient : Beli2006AlphaLaws.{u, v} K]
    [alphaPrefix : Beli2006AlphaLaws.{u, w} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, w, u} K]
    {R₁ R₂ A₁ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha :
      reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd N i))
    (conditions :
      Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁)
    (hfourth : ∀ hN : 0 < N,
      R₂ + 2 ≤ a.order
        (Fin.natAdd 3 (⟨0, hN⟩ : Fin N)))
    (hLower : A₁ ≤ β₁) (hUpper : β₁ ≤ A₁ + 2)
    (hThird : ∀ hN : 0 < N,
      (β₁ : ℚ) ≤
        (a.castLength (show 3 + N = N + 3 by omega)).alphaValue
          (⟨2, by omega⟩ : Fin (N + 2))) :
    ∃ D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁,
      Nonempty (Beli2019Lemma910Data a D) := by
  letI : BeliLemma43ConstructionLaws.{u, w} K := constructionPrefix
  letI : Beli2006SectionTwoLaws.{u, w} K := sectionTwoPrefix
  letI : Beli2006AlphaLaws.{u, w} K := alphaPrefix
  rcases beli2019Lemma910_ternary
      (structuralModel := structuralModel)
      (alphaSource := alphaPrefix) (alphaModel := alphaModel)
      (classificationModel := classificationModel)
      reference R₁ R₂ A₁ β₁ hrefOrders hrefFirstAlpha conditions
        hLower hUpper with ⟨T⟩
  letI : BeliLemma43ConstructionLaws.{u, v} K := constructionAmbient
  letI : Beli2006SectionTwoLaws.{u, v} K := sectionTwoAmbient
  letI : Beli2006AlphaLaws.{u, v} K := alphaAmbient
  refine ⟨T.realization, ?_⟩
  exact exists_beli2019Lemma910Data_of_realization
    (alphaAmbient := alphaAmbient) (alphaPrefix := alphaPrefix)
    (structuralAmbient := structuralAmbient)
    (structuralPrefix := structuralPrefix)
    reference a T.realization hrefOrders hrefFirstAlpha horders hprefix
      hfourth hLower hUpper hThird T.represents

end BONG.GoodBONG

end Bong
