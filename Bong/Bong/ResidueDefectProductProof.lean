/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DefectArithmetic
import Bong.Bong.QuadraticApproximationExact
import Bong.Bong.ResidueDefectProduct
import Bong.Dyadic.QuadraticDefectHensel
import Bong.Dyadic.UnitDefectClassification

/-!
# Products of equal dyadic quadratic defects

This file proves the residue-field calculation isolated in Beli (2019),
Lemma 8.1.  Every positive finite-defect class is first represented by a
principal unit `1 + t` whose error has exact order equal to the defect.

* If the residue field has more than two elements, a residue coefficient is
  chosen so that neither the second error nor the product error cancels.
* If the residue field has two elements, equal leading coefficients cancel,
  so the product error lies at least one step deeper.

Thus `DyadicResidueDefectProductLaws` is a theorem of the concrete dyadic
local-field setup, rather than an external law boundary.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

local instance defect : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

/-- The converse parity implication needed below, proved here at the common
defect layer so that the residue calculation does not depend on the later
2019 unit-choice module. -/
private theorem odd_ordUnit_of_quadraticDefect_eq_zero_local
    (x : Kˣ) (hx : quadraticDefect K x = 0) :
    Odd (ordUnit K x) := by
  rcases Int.even_or_odd (ordUnit K x) with heven | hodd
  · rcases heven with ⟨k, hk⟩
    let s : Kˣ := uniformizerPowerUnit K k
    let u : Kˣ := x / s ^ 2
    have hsOrder : ordUnit K s = k :=
      ordUnit_uniformizerPowerUnit (K := K) k
    have huOrder : ordUnit K u = 0 := by
      dsimp only [u]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
        hsOrder]
      omega
    have huUnit : IsValuationUnit K (u : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder
    have hfactor : u * s ^ 2 = x := by
      dsimp only [u]
      simp
    have huDefect : quadraticDefect K u = 0 := by
      calc
        quadraticDefect K u = quadraticDefect K (u * s ^ 2) :=
          (quadraticDefect_mul_square K u s).symm
        _ = quadraticDefect K x := congrArg (quadraticDefect K) hfactor
        _ = 0 := hx
    have huFinite : quadraticDefect K u ≠ ⊤ := by
      rw [huDefect]
      exact WithTop.zero_ne_top
    have hpos := quadraticDefect_toNat_pos_of_unit_of_ne_top
      u huUnit huFinite
    rw [huDefect] at hpos
    simp at hpos
  · exact hodd

private theorem one_le_ord_of_pos {x : K} (h : 0 < ord K x) :
    (1 : WithTop Int) ≤ ord K x := by
  by_cases htop : ord K x = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hd] at h ⊢
    have hdpos : (0 : Int) < d := by exact_mod_cast h
    exact_mod_cast (show (1 : Int) ≤ d by omega)

/-- A principal unit `v = 1 + t` whose error has positive odd order `d < 2e`
has quadratic defect exactly `d`. -/
theorem quadraticDefect_eq_of_principal_exact_odd
    (v : Kˣ) (t : K) (d : Nat)
    (hv : (v : K) = 1 + t)
    (ht : ord K t = ((d : Int) : WithTop Int))
    (hdPos : 0 < d) (hdOdd : Odd d)
    (hdLt : d < 2 * ramificationIndex K) :
    quadraticDefect K v = (d : ℕ∞) := by
  have htPos : (0 : WithTop Int) < ord K t := by
    rw [ht]
    exact_mod_cast hdPos
  have hvUnit : IsValuationUnit K (v : K) := by
    rw [IsValuationUnit, hv]
    have hlt : ord K (1 : K) < ord K t := by
      simpa only [ord_one] using htPos
    simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hlt
  have hlower : (d : ℕ∞) ≤ quadraticDefect K v := by
    apply natCast_le_quadraticDefect K
    refine ⟨1, ?_⟩
    have hfield : 1 - (1 : K) ^ 2 / (v : K) = t / (v : K) := by
      calc
        1 - (1 : K) ^ 2 / (v : K) =
            ((v : K) - 1) / (v : K) := by
              field_simp [Units.ne_zero v]
        _ = t / (v : K) := by rw [hv]; ring
    rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      hvUnit, ht]
    simp
  have hupper : quadraticDefect K v ≤ (d : ℕ∞) := by
    by_contra hnot
    have hstrict : (d : ℕ∞) < quadraticDefect K v :=
      lt_of_not_ge hnot
    have hnext : ((d + 1 : Nat) : ℕ∞) ≤ quadraticDefect K v := by
      have hadd : (d : ℕ∞) + 1 ≤ quadraticDefect K v :=
        (ENat.add_one_le_iff (ENat.coe_ne_top d)).2 hstrict
      simpa only [ENat.coe_add, ENat.coe_one] using hadd
    obtain ⟨y, hy⟩ :=
      (isQuadraticApproximation_iff_le_defect K).2 hnext
    have hdeep : (((d + 1 : Nat) : Int) : WithTop Int) ≤
        ord K ((v : K) - y ^ 2) := by
      have hfield : 1 - y ^ 2 / (v : K) =
          ((v : K) - y ^ 2) / (v : K) := by
        field_simp [Units.ne_zero v]
      rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
        hvUnit] at hy
      simpa using hy
    have htLt : ord K t < ord K ((v : K) - y ^ 2) := by
      apply lt_of_lt_of_le _ hdeep
      rw [ht]
      exact_mod_cast (show (d : Int) < (d + 1 : Nat) by omega)
    have honeSubOrder : ord K (1 - y ^ 2) =
        ((d : Int) : WithTop Int) := by
      have hsub := (ord K).map_sub_eq_of_lt_right htLt
      have hfield : ((v : K) - y ^ 2) - t = 1 - y ^ 2 := by
        rw [hv]
        ring
      simpa only [hfield, ht] using hsub
    have hdEvenInt : Even (d : Int) :=
      even_order_one_sub_sq_of_lt_two_mul_e_proved y (d : Int)
        honeSubOrder (by exact_mod_cast hdPos) (by exact_mod_cast hdLt)
    have hdOddInt : Odd (d : Int) := by exact_mod_cast hdOdd
    exact (Int.not_odd_iff_even.mpr hdEvenInt hdOddInt).elim
  exact le_antisymm hupper hlower

private theorem natCast_le_quadraticDefect_of_principal_depth
    (v : Kˣ) (t : K) (n : Nat)
    (hv : (v : K) = 1 + t)
    (hvUnit : IsValuationUnit K (v : K))
    (ht : (((n : Nat) : Int) : WithTop Int) ≤ ord K t) :
    (n : ℕ∞) ≤ quadraticDefect K v := by
  apply natCast_le_quadraticDefect K
  refine ⟨1, ?_⟩
  have hfield : 1 - (1 : K) ^ 2 / (v : K) = t / (v : K) := by
    calc
      1 - (1 : K) ^ 2 / (v : K) =
          ((v : K) - 1) / (v : K) := by
            field_simp [Units.ne_zero v]
      _ = t / (v : K) := by rw [hv]; ring
  rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv, hvUnit]
  simpa using ht

/-- Every nonzero finite quadratic-defect class has, up to a square, a
valuation-unit representative `v = 1 + t` whose principal error has order
exactly equal to the defect.  This is the normalization used both in the
residue product calculation and in O'Meara's explicit negative-partner
construction for Hilbert nondegeneracy. -/
theorem exists_exact_principal_representation
    (a : Kˣ)
    (hfinite : quadraticDefect K a ≠ ⊤)
    (hzero : quadraticDefect K a ≠ 0) :
    ∃ v r : Kˣ, ∃ t : K,
      IsValuationUnit K (v : K) ∧
        quadraticDefect K v = quadraticDefect K a ∧
        a = v * r ^ 2 ∧
        (v : K) = 1 + t ∧
        ord K t =
          ((((quadraticDefect K a).toNat : Nat) : Int) : WithTop Int) := by
  have heven : Even (ordUnit K a) := by
    rcases Int.even_or_odd (ordUnit K a) with heven | hodd
    · exact heven
    · exact (hzero (quadraticDefect_eq_zero_of_odd_ordUnit a hodd)).elim
  rcases heven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let a₀ : Kˣ := a / s ^ 2
  have hsOrder : ordUnit K s = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have ha₀Order : ordUnit K a₀ = 0 := by
    dsimp only [a₀]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder]
    omega
  have ha₀Unit : IsValuationUnit K (a₀ : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K a₀).2 ha₀Order
  have ha₀Factor : a₀ * s ^ 2 = a := by
    dsimp only [a₀]
    simp
  have ha₀Defect : quadraticDefect K a₀ = quadraticDefect K a := by
    calc
      quadraticDefect K a₀ = quadraticDefect K (a₀ * s ^ 2) :=
        (quadraticDefect_mul_square K a₀ s).symm
      _ = quadraticDefect K a := congrArg (quadraticDefect K) ha₀Factor
  have ha₀Finite : quadraticDefect K a₀ ≠ ⊤ := by
    rwa [ha₀Defect]
  obtain ⟨x, hx⟩ := exists_quadraticApproximation_exact_order a₀ ha₀Finite
  let d := (quadraticDefect K a).toNat
  have hdPos : 0 < d := by
    have := quadraticDefect_toNat_pos_of_unit_of_ne_top
      a₀ ha₀Unit ha₀Finite
    simpa only [d, ha₀Defect] using this
  have hxErrorPos : (0 : WithTop Int) <
      ord K (1 - x ^ 2 / (a₀ : K)) := by
    rw [hx, ha₀Defect]
    exact_mod_cast hdPos
  have hratioOrder : ord K (x ^ 2 / (a₀ : K)) = 0 := by
    have hlt : ord K (1 : K) <
        ord K (1 - x ^ 2 / (a₀ : K)) := by
      simpa only [ord_one] using hxErrorPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have hfield : 1 - (1 - x ^ 2 / (a₀ : K)) =
        x ^ 2 / (a₀ : K) := by ring
    simpa only [hfield, ord_one] using hsub
  have hxNe : x ≠ 0 := by
    intro hxZero
    subst x
    simp at hratioOrder
  let xu : Kˣ := Units.mk0 x hxNe
  have hxuOrder : ordUnit K xu = 0 := by
    have hratioUnitOrder : ordUnit K (xu ^ 2 * a₀⁻¹) = 0 := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      have hval : ((xu ^ 2 * a₀⁻¹ : Kˣ) : K) =
          x ^ 2 / (a₀ : K) := by
        simp [xu, div_eq_mul_inv]
      rw [hval]
      exact hratioOrder
    rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, ha₀Order] at hratioUnitOrder
    omega
  let v : Kˣ := a₀ / xu ^ 2
  have hvOrder : ordUnit K v = 0 := by
    dsimp only [v]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      ha₀Order, hxuOrder]
    omega
  have hvUnit : IsValuationUnit K (v : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K v).2 hvOrder
  have hvFactor : v * xu ^ 2 = a₀ := by
    dsimp only [v]
    simp
  have hvDefect : quadraticDefect K v = quadraticDefect K a := by
    calc
      quadraticDefect K v = quadraticDefect K (v * xu ^ 2) :=
        (quadraticDefect_mul_square K v xu).symm
      _ = quadraticDefect K a₀ := congrArg (quadraticDefect K) hvFactor
      _ = quadraticDefect K a := ha₀Defect
  let r : Kˣ := xu * s
  have hfactor : a = v * r ^ 2 := by
    rw [← ha₀Factor, ← hvFactor]
    dsimp only [r]
    rw [mul_pow]
    ac_rfl
  let t : K := (v : K) - 1
  have hvField : (v : K) = 1 + t := by
    dsimp only [t]
    ring
  have htField : t = (1 - x ^ 2 / (a₀ : K)) * (v : K) := by
    have hvVal : (v : K) = (a₀ : K) / x ^ 2 := by
      simp [v, xu]
    dsimp only [t]
    rw [hvVal]
    field_simp [Units.ne_zero a₀, hxNe]
  have htOrder : ord K t = ((d : Int) : WithTop Int) := by
    rw [htField, ord_mul, hx, ha₀Defect, hvUnit]
    simp only [d, add_zero]
  exact ⟨v, r, t, hvUnit, hvDefect, hfactor, hvField, by simpa [d] using htOrder⟩

private theorem exists_same_defect_product_of_large_residue_proved
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : Kˣ)
    (hfinite : quadraticDefect K a ≠ ⊤)
    (hzero : quadraticDefect K a ≠ 0)
    (htwoE : quadraticDefect K a ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ b : Kˣ,
      quadraticDefect K b = quadraticDefect K a ∧
        quadraticDefect K (a * b) = quadraticDefect K a := by
  obtain ⟨v, r, t, hvUnit, hvDefect, hfactor, hvField, htOrder⟩ :=
    exists_exact_principal_representation a hfinite hzero
  let d := (quadraticDefect K a).toNat
  have htOrderD : ord K t = ((d : Int) : WithTop Int) := by
    simpa only [d] using htOrder
  have hdefectCoe : quadraticDefect K a = (d : ℕ∞) := by
    simpa only [d] using (ENat.coe_toNat hfinite).symm
  have hdPos : 0 < d := by
    have hvFinite : quadraticDefect K v ≠ ⊤ := by rwa [hvDefect]
    have hp := quadraticDefect_toNat_pos_of_unit_of_ne_top
      v hvUnit hvFinite
    simpa only [hvDefect, d] using hp
  have haNotSquare : ¬IsSquare a := by
    intro hsquare
    exact hfinite (quadraticDefect_eq_top_of_isSquare K hsquare)
  have hdefectLe := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) haNotSquare
  have hdefectLt : quadraticDefect K a <
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    lt_of_le_of_ne hdefectLe htwoE
  have hdLt : d < 2 * ramificationIndex K := by
    rw [hdefectCoe] at hdefectLt
    exact_mod_cast hdefectLt
  have hdOdd : Odd d := by
    have hvLt : quadraticDefect K v <
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      rwa [hvDefect]
    have := quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
      (K := K) v hvUnit hvLt
    simpa only [hvDefect, d] using this
  obtain ⟨zeta, hzetaUnit, hzetaPlusUnit⟩ :=
    hres.exists_unit_add_one_unit
  let q : K := zeta * t
  have hqOrder : ord K q = ((d : Int) : WithTop Int) := by
    dsimp only [q]
    rw [ord_mul, hzetaUnit, htOrderD]
    simp
  have hqPos : (0 : WithTop Int) < ord K q := by
    rw [hqOrder]
    exact_mod_cast hdPos
  have hbOrder : ord K (1 + q) = 0 := by
    have hlt : ord K (1 : K) < ord K q := by
      simpa only [ord_one] using hqPos
    simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hlt
  have hbNe : 1 + q ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hbOrder]
    exact WithTop.coe_ne_top
  let b : Kˣ := Units.mk0 (1 + q) hbNe
  have hbField : (b : K) = 1 + q := rfl
  have hbDefect : quadraticDefect K b = (d : ℕ∞) :=
    quadraticDefect_eq_of_principal_exact_odd b q d hbField hqOrder
      hdPos hdOdd hdLt
  let productTerm : K := (1 + zeta) * t + zeta * t ^ 2
  have hfirstOrder : ord K ((1 + zeta) * t) =
      ((d : Int) : WithTop Int) := by
    have hzetaPlusUnit' : IsValuationUnit K (1 + zeta) := by
      simpa only [add_comm] using hzetaPlusUnit
    rw [ord_mul, hzetaPlusUnit', htOrderD]
    simp
  have hsecondOrder : ord K (zeta * t ^ 2) =
      ((d : Int) : WithTop Int) + ((d : Int) : WithTop Int) := by
    rw [ord_mul, hzetaUnit, ord_pow, htOrderD]
    simp [two_nsmul]
  have hordersLt : ord K ((1 + zeta) * t) < ord K (zeta * t ^ 2) := by
    rw [hfirstOrder, hsecondOrder]
    exact_mod_cast (show (d : Int) < (d : Int) + (d : Int) by omega)
  have hproductTermOrder : ord K productTerm =
      ((d : Int) : WithTop Int) := by
    dsimp only [productTerm]
    simpa only [hfirstOrder] using
      (ord K).map_add_eq_of_lt_left hordersLt
  have hvbField : ((v * b : Kˣ) : K) = 1 + productTerm := by
    rw [Units.val_mul, hvField, hbField]
    dsimp only [q, productTerm]
    ring
  have hvbDefect : quadraticDefect K (v * b) = (d : ℕ∞) :=
    quadraticDefect_eq_of_principal_exact_odd (v * b) productTerm d
      hvbField hproductTermOrder hdPos hdOdd hdLt
  refine ⟨b, ?_, ?_⟩
  · exact hbDefect.trans hdefectCoe.symm
  · have habFactor : a * b = (v * b) * r ^ 2 := by
      rw [hfactor]
      simp only [pow_two]
      ac_rfl
    rw [habFactor, quadraticDefect_mul_square, hvbDefect, ← hdefectCoe]

private theorem product_defect_strict_of_residue_two_proved
    (hres : ¬HasResidueFieldMoreThanTwoElements (K := K))
    (a b : Kˣ)
    (heq : quadraticDefect K a = quadraticDefect K b)
    (hfinite : quadraticDefect K a ≠ ⊤) :
    quadraticDefect K a < quadraticDefect K (a * b) := by
  by_cases hzero : quadraticDefect K a = 0
  · have haOdd := odd_ordUnit_of_quadraticDefect_eq_zero_local a hzero
    have hbZero : quadraticDefect K b = 0 := heq.symm.trans hzero
    have hbOdd := odd_ordUnit_of_quadraticDefect_eq_zero_local b hbZero
    have habEven : Even (ordUnit K (a * b)) := by
      rw [ordUnit_mul]
      exact Odd.add_odd haOdd hbOdd
    have habNonzero : quadraticDefect K (a * b) ≠ 0 := by
      intro habZero
      have habOdd :=
        odd_ordUnit_of_quadraticDefect_eq_zero_local (a * b) habZero
      exact (Int.not_odd_iff_even.mpr habEven habOdd).elim
    rw [hzero]
    exact lt_of_le_of_ne bot_le (Ne.symm habNonzero)
  · have hbFinite : quadraticDefect K b ≠ ⊤ := by
      rwa [← heq]
    have hbNonzero : quadraticDefect K b ≠ 0 := by
      rwa [← heq]
    obtain ⟨v, r, t, hvUnit, hvDefect, hfactorA, hvField, htOrder⟩ :=
      exists_exact_principal_representation a hfinite hzero
    obtain ⟨w, s, q, hwUnit, hwDefect, hfactorB, hwField, hqOrder⟩ :=
      exists_exact_principal_representation b hbFinite hbNonzero
    let d := (quadraticDefect K a).toNat
    have htOrderD : ord K t = ((d : Int) : WithTop Int) := by
      simpa only [d] using htOrder
    have hdefectCoe : quadraticDefect K a = (d : ℕ∞) := by
      simpa only [d] using (ENat.coe_toNat hfinite).symm
    have hdPos : 0 < d := by
      have hvFinite : quadraticDefect K v ≠ ⊤ := by rwa [hvDefect]
      have hp := quadraticDefect_toNat_pos_of_unit_of_ne_top
        v hvUnit hvFinite
      simpa only [hvDefect, d] using hp
    have hqOrderA : ord K q = ((d : Int) : WithTop Int) := by
      simpa only [heq, d] using hqOrder
    have hresidue : ∀ z : K,
        IsValuationUnit K z → IsInMaximalIdeal K (z - 1) := by
      intro z hz
      by_contra hzNot
      exact hres ⟨z, hz, hzNot⟩
    have htNe : t ≠ 0 := by
      apply (ord_eq_top_iff K).not.mp
      rw [htOrderD]
      exact WithTop.coe_ne_top
    let z : K := q / t
    have hzUnit : IsValuationUnit K z := by
      rw [IsValuationUnit]
      dsimp only [z]
      rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
        hqOrderA, htOrderD]
      simp
    have hzMinus : IsInMaximalIdeal K (z - 1) := hresidue z hzUnit
    have hzPlus : IsInMaximalIdeal K (1 + z) := by
      have hadd := isInMaximalIdeal_add K hzMinus (two_isInMaximalIdeal K)
      have hfield : (z - 1) + 2 = 1 + z := by ring
      simpa only [hfield] using hadd
    have honeZDepth : (1 : WithTop Int) ≤ ord K (1 + z) :=
      one_le_ord_of_pos hzPlus
    have htqDepth : (((d + 1 : Nat) : Int) : WithTop Int) ≤
        ord K (t + q) := by
      have hfield : t + q = t * (1 + z) := by
        dsimp only [z]
        field_simp [htNe]
      rw [hfield, ord_mul, htOrderD]
      have hadd := add_le_add_left honeZDepth
        ((d : Int) : WithTop Int)
      norm_cast at hadd ⊢
      simpa [add_comm] using hadd
    have htqProductDepth : (((d + 1 : Nat) : Int) : WithTop Int) ≤
        ord K (t * q) := by
      rw [ord_mul, htOrderD, hqOrderA]
      exact_mod_cast (show (d + 1 : Int) ≤ (d : Int) + d by omega)
    let productTerm : K := (t + q) + t * q
    have hproductTermDepth :
        (((d + 1 : Nat) : Int) : WithTop Int) ≤
          ord K productTerm := by
      exact (le_min htqDepth htqProductDepth).trans
        (min_ord_le_ord_add K (t + q) (t * q))
    have hvwField : ((v * w : Kˣ) : K) = 1 + productTerm := by
      rw [Units.val_mul, hvField, hwField]
      dsimp only [productTerm]
      ring
    have hvwUnit : IsValuationUnit K ((v * w : Kˣ) : K) :=
      (valuationUnitSubgroup K).mul_mem hvUnit hwUnit
    have hvwDepth : ((d + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K (v * w) :=
      natCast_le_quadraticDefect_of_principal_depth
        (v * w) productTerm (d + 1) hvwField hvwUnit hproductTermDepth
    have habFactor : a * b = (v * w) * (r * s) ^ 2 := by
      rw [hfactorA, hfactorB]
      simp only [pow_two]
      ac_rfl
    have habDepth : ((d + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K (a * b) := by
      rw [habFactor, quadraticDefect_mul_square]
      exact hvwDepth
    rw [hdefectCoe]
    have hstep : (d : ℕ∞) < ((d + 1 : Nat) : ℕ∞) := by
      exact_mod_cast Nat.lt_succ_self d
    exact hstep.trans_le habDepth

noncomputable instance dyadicResidueDefectProductLawsProved :
    DyadicResidueDefectProductLaws K where
  exists_same_defect_product_of_large_residue :=
    exists_same_defect_product_of_large_residue_proved
  product_defect_strict_of_residue_two :=
    product_defect_strict_of_residue_two_proved

end BONG

end Bong
