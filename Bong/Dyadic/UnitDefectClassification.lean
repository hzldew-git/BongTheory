/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.CongruenceSubgroup
import Bong.Dyadic.QuadraticDefectHensel

/-!
# Dyadic unit quadratic-defect classification

This file proves the parts of O'Meara, Proposition 63:2 and Remark 63:6 used
by the Beli formalization.  The proofs use only the normalized discrete
valuation, perfection of the residue field, and the local square theorem:

* a positive order of `1 - x²` below `2e` is even;
* the endpoint `1 - 4u` is not a square when the residue field has two
  elements;
* the even steps of the principal-unit square-class filtration collapse;
* a finite unit defect below `2e` is odd;
* every positive odd depth below `2e` occurs as a unit defect.
-/

namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem one_le_ord_of_pos {x : K} (h : 0 < ord K x) :
    (1 : WithTop Int) ≤ ord K x := by
  by_cases htop : ord K x = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hd] at h
    have hdpos : (0 : Int) < d := by exact_mod_cast h
    rw [← hd]
    exact_mod_cast (show (1 : Int) ≤ d by omega)

private theorem ord_eq_zero_of_ord_sq_eq_zero (x : K)
    (h : ord K (x ^ 2) = 0) : ord K x = 0 := by
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp at h
  let xu : Kˣ := Units.mk0 x hx
  have hunit : ordUnit K (xu ^ 2) = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (x ^ 2) = 0
    exact h
  rw [ordUnit_pow] at hunit
  have hxUnit : ordUnit K xu = 0 := by omega
  change ord K (xu : K) = 0
  rw [← coe_ordUnit]
  exact_mod_cast hxUnit

theorem even_order_one_sub_sq_of_lt_two_mul_e_proved
    (x : K) (n : Int)
    (horder : ord K (1 - x ^ 2) = (n : WithTop Int))
    (hpos : 0 < n)
    (hlt : n < 2 * (ramificationIndex K : Int)) :
    Even n := by
  have herrorPos : (0 : WithTop Int) < ord K (1 - x ^ 2) := by
    rw [horder]
    exact_mod_cast hpos
  have hxSqOrder : ord K (x ^ 2) = 0 := by
    have hstrict : ord K (1 : K) < ord K (1 - x ^ 2) := by
      simpa only [ord_one] using herrorPos
    have hsub := (ord K).map_sub_eq_of_lt_left hstrict
    have heq : 1 - (1 - x ^ 2) = x ^ 2 := by ring
    simpa only [heq, ord_one] using hsub
  have hxUnit : IsValuationUnit K x :=
    ord_eq_zero_of_ord_sq_eq_zero x hxSqOrder
  have herrorNe : 1 - x ^ 2 ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [horder]
    exact WithTop.coe_ne_top
  have hfactor : (1 - x) * (1 + x) = 1 - x ^ 2 := by ring
  have hleftNe : 1 - x ≠ 0 := by
    intro hzero
    apply herrorNe
    rw [← hfactor, hzero, zero_mul]
  have hrightNe : 1 + x ≠ 0 := by
    intro hzero
    apply herrorNe
    rw [← hfactor, hzero, mul_zero]
  let left : Kˣ := Units.mk0 (1 - x) hleftNe
  let right : Kˣ := Units.mk0 (1 + x) hrightNe
  have hsum : ordUnit K left + ordUnit K right = n := by
    apply WithTop.coe_injective
    rw [WithTop.coe_add, coe_ordUnit, coe_ordUnit]
    change ord K (1 - x) + ord K (1 + x) = (n : WithTop Int)
    rw [← ord_mul, hfactor, horder]
  have htwoX : ord K ((2 : K) * x) =
      ((ramificationIndex K : Int) : WithTop Int) := by
    rw [ord_mul, hxUnit, add_zero]
    exact (ramificationIndex_spec K).symm
  have hcase : ordUnit K left < (ramificationIndex K : Int) ∨
      ordUnit K right < (ramificationIndex K : Int) := by
    omega
  rcases hcase with hleft | hright
  · have hleftCast : ord K (1 - x) < ord K ((2 : K) * x) := by
      change ord K (left : K) < ord K ((2 : K) * x)
      rw [← coe_ordUnit, htwoX]
      exact_mod_cast hleft
    have hrightEq : ord K (1 + x) = ord K (1 - x) := by
      have hadd := (ord K).map_add_eq_of_lt_left hleftCast
      have heq : (1 - x) + 2 * x = 1 + x := by ring
      simpa only [heq] using hadd
    have hordersEq : ordUnit K right = ordUnit K left := by
      apply WithTop.coe_injective
      simpa [left, right] using hrightEq
    refine ⟨ordUnit K left, ?_⟩
    omega
  · have hrightCast : ord K (1 + x) < ord K (-(2 : K) * x) := by
      have hnegTwoX : ord K (-(2 : K) * x) =
          ((ramificationIndex K : Int) : WithTop Int) := by
        rw [ord_mul, ord_neg, hxUnit, add_zero]
        exact (ramificationIndex_spec K).symm
      change ord K (right : K) < ord K (-(2 : K) * x)
      rw [← coe_ordUnit, hnegTwoX]
      exact_mod_cast hright
    have hleftEq : ord K (1 - x) = ord K (1 + x) := by
      have hadd := (ord K).map_add_eq_of_lt_left hrightCast
      have heq : (1 + x) + (-2) * x = 1 - x := by ring
      simpa only [heq] using hadd
    have hordersEq : ordUnit K left = ordUnit K right := by
      apply WithTop.coe_injective
      simpa [left, right] using hleftEq
    refine ⟨ordUnit K right, ?_⟩
    omega

theorem one_sub_four_mul_unit_ne_sq_of_residue_two_proved
    (u x : K)
    (hu : IsValuationUnit K u)
    (hresidue : ∀ z : K,
      IsValuationUnit K z → IsInMaximalIdeal K (z - 1)) :
    1 - (2 : K) ^ 2 * u ≠ x ^ 2 := by
  intro hsquare
  have hfourOrder : ord K ((2 : K) ^ 2 * u) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) := by
    rw [ord_mul, ord_pow, hu, add_zero, ← ramificationIndex_spec]
    rw [two_nsmul]
    exact_mod_cast (show (ramificationIndex K : Int) +
      (ramificationIndex K : Int) = 2 * (ramificationIndex K : Int) by ring)
  have hfourPos : (0 : WithTop Int) < ord K ((2 : K) ^ 2 * u) := by
    rw [hfourOrder]
    exact_mod_cast (show 0 < 2 * (ramificationIndex K : Int) by
      have := ramificationIndex_pos (K := K)
      omega)
  have hxSqOrder : ord K (x ^ 2) = 0 := by
    rw [← hsquare]
    have hstrict : ord K (1 : K) < ord K ((2 : K) ^ 2 * u) := by
      simpa only [ord_one] using hfourPos
    simpa only [ord_one] using (ord K).map_sub_eq_of_lt_left hstrict
  have hxUnit : IsValuationUnit K x :=
    ord_eq_zero_of_ord_sq_eq_zero x hxSqOrder
  have huNe : u ≠ 0 := by
    intro hzero
    subst u
    simp [IsValuationUnit] at hu
  have hproduct : (x - 1) * (x + 1) = -((2 : K) ^ 2 * u) := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = (1 - (2 : K) ^ 2 * u) - 1 := by rw [← hsquare]
      _ = -((2 : K) ^ 2 * u) := by ring
  have hleftNe : x - 1 ≠ 0 := by
    intro hzero
    have : -((2 : K) ^ 2 * u) = 0 := by rw [← hproduct, hzero, zero_mul]
    exact (mul_ne_zero (pow_ne_zero 2 (by norm_num)) huNe) (neg_eq_zero.mp this)
  have hrightNe : x + 1 ≠ 0 := by
    intro hzero
    have : -((2 : K) ^ 2 * u) = 0 := by rw [← hproduct, hzero, mul_zero]
    exact (mul_ne_zero (pow_ne_zero 2 (by norm_num)) huNe) (neg_eq_zero.mp this)
  let left : Kˣ := Units.mk0 (x - 1) hleftNe
  let right : Kˣ := Units.mk0 (x + 1) hrightNe
  have hsum : ordUnit K left + ordUnit K right =
      2 * (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [WithTop.coe_add, coe_ordUnit, coe_ordUnit]
    change ord K (x - 1) + ord K (x + 1) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int)
    rw [← ord_mul, hproduct, ord_neg, hfourOrder]
  have hleftPos : 0 < ordUnit K left := by
    have hmax := hresidue x hxUnit
    change 0 < ord K (x - 1) at hmax
    have hcast : (0 : WithTop Int) < ((ordUnit K left : Int) : WithTop Int) := by
      rw [coe_ordUnit]
      change 0 < ord K (x - 1)
      exact hmax
    exact_mod_cast hcast
  have hleftEq : ordUnit K left = (ramificationIndex K : Int) := by
    rcases lt_trichotomy (ordUnit K left)
        (ramificationIndex K : Int) with hlt | heq | hgt
    · have hcast : ord K (x - 1) < ord K (2 : K) := by
        change ord K (left : K) < ord K (2 : K)
        rw [← coe_ordUnit, ← ramificationIndex_spec]
        exact_mod_cast hlt
      have hrightOrder : ord K (x + 1) = ord K (x - 1) := by
        have hadd := (ord K).map_add_eq_of_lt_left hcast
        have hfield : (x - 1) + 2 = x + 1 := by ring
        simpa only [hfield] using hadd
      have hrightEq : ordUnit K right = ordUnit K left := by
        apply WithTop.coe_injective
        simpa [left, right] using hrightOrder
      omega
    · exact heq
    · have hcast : ord K (2 : K) < ord K (x - 1) := by
        change ord K (2 : K) < ord K (left : K)
        rw [← coe_ordUnit, ← ramificationIndex_spec]
        exact_mod_cast hgt
      have hrightOrder : ord K (x + 1) = ord K (2 : K) := by
        have hadd := (ord K).map_add_eq_of_lt_right hcast
        have hfield : (x - 1) + 2 = x + 1 := by ring
        simpa only [hfield] using hadd
      have hrightEq : ordUnit K right = (ramificationIndex K : Int) := by
        apply WithTop.coe_injective
        rw [coe_ordUnit]
        change ord K (x + 1) =
          ((ramificationIndex K : Int) : WithTop Int)
        rw [hrightOrder]
        exact (ramificationIndex_spec K).symm
      omega
  have hrightEq : ordUnit K right = (ramificationIndex K : Int) := by
    omega
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwoOrder : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact (ramificationIndex_spec K).symm
  let t : Kˣ := left / two
  have htOrder : ordUnit K t = 0 := by
    dsimp only [t]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, hleftEq, htwoOrder]
    omega
  have htUnit : IsValuationUnit K (t : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K t).2 htOrder
  have htMinus : IsInMaximalIdeal K ((t : K) - 1) :=
    hresidue (t : K) htUnit
  have htPlus : IsInMaximalIdeal K ((t : K) + 1) := by
    have hsumMax := isInMaximalIdeal_add K htMinus (two_isInMaximalIdeal K)
    have hfield : ((t : K) - 1) + 2 = (t : K) + 1 := by ring
    simpa only [hfield] using hsumMax
  have htPlusOrder : ord K ((t : K) + 1) = 0 := by
    have hfield : (t : K) + 1 = (x + 1) / 2 := by
      dsimp only [t, left, two]
      norm_num
      field_simp
      ring
    rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv]
    change ord K (right : K) + -ord K (two : K) = 0
    rw [← coe_ordUnit, ← coe_ordUnit, hrightEq, htwoOrder]
    norm_num
  change 0 < ord K ((t : K) + 1) at htPlus
  rw [htPlusOrder] at htPlus
  exact (lt_irrefl 0 htPlus).elim

noncomputable instance dyadicSquareDifferenceLawsProved :
    DyadicSquareDifferenceLaws K where
  even_order_one_sub_sq_of_lt_two_mul_e :=
    even_order_one_sub_sq_of_lt_two_mul_e_proved
  one_sub_four_mul_unit_ne_sq_of_residue_two :=
    one_sub_four_mul_unit_ne_sq_of_residue_two_proved

private theorem exists_deeper_principal_unit_square_class
    (n : Nat) (hpos : 0 < n)
    (hlt : n < 2 * ramificationIndex K) (heven : Even n)
    (a : Kˣ) (ha : a ∈ principalUnitSubgroup K n) :
    ∃ b : Kˣ, b ∈ principalUnitSubgroup K (n + 1) ∧
      ∃ s : Kˣ, a = b * s ^ 2 := by
  have hbase : ((n : Int) : WithTop Int) ≤ ord K ((a : K) - 1) :=
    (Lattice.mem_powerIdeal_iff (K := K) (n : Int) _).1 ha.2
  by_cases hdeep : (((n + 1 : Nat) : Int) : WithTop Int) ≤
      ord K ((a : K) - 1)
  · refine ⟨a, ⟨ha.1, ?_⟩, 1, ?_⟩
    · exact (Lattice.mem_powerIdeal_iff (K := K)
        ((n + 1 : Nat) : Int) _).2 hdeep
    · simp
  · have hltError : ord K ((a : K) - 1) <
        (((n + 1 : Nat) : Int) : WithTop Int) := lt_of_not_ge hdeep
    have hfinite : ord K ((a : K) - 1) ≠ ⊤ :=
      ne_top_of_lt (hltError.trans (WithTop.coe_lt_top _))
    obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hdLower : (n : Int) ≤ d := by
      rw [← hd] at hbase
      exact_mod_cast hbase
    have hdUpper : d < (n + 1 : Nat) := by
      rw [← hd] at hltError
      exact_mod_cast hltError
    have hdEq : d = (n : Int) := by omega
    have herrorOrder : ord K ((a : K) - 1) =
        ((n : Int) : WithTop Int) := by rw [← hd, hdEq]
    rcases heven with ⟨k, hk⟩
    have hkPos : 0 < k := by omega
    have hkLtE : k < ramificationIndex K := by omega
    let p : Kˣ := uniformizerPowerUnit K (k : Int)
    have hpOrder : ordUnit K p = (k : Int) := by
      exact ordUnit_uniformizerPowerUnit (K := K) (k : Int)
    have herrorNe : (a : K) - 1 ≠ 0 := by
      apply (ord_eq_top_iff K).not.mp
      rw [herrorOrder]
      exact WithTop.coe_ne_top
    let error : Kˣ := Units.mk0 ((a : K) - 1) herrorNe
    have herrorUnitOrder : ordUnit K error = (n : Int) := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      change ord K ((a : K) - 1) = ((n : Int) : WithTop Int)
      exact herrorOrder
    let epsilon : Kˣ := error / p ^ 2
    have hepsilonOrder : ordUnit K epsilon = 0 := by
      dsimp only [epsilon]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
        herrorUnitOrder, hpOrder]
      omega
    have hepsilonUnit : IsValuationUnit K (epsilon : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K epsilon).2 hepsilonOrder
    obtain ⟨z, hzUnit, hzApprox⟩ :=
      exists_unit_squareRoot_mod_maximal K epsilon hepsilonUnit
    have hzNe : z ≠ 0 := by
      intro hzero
      subst z
      simp [IsValuationUnit] at hzUnit
    let zu : Kˣ := Units.mk0 z hzNe
    have hzuOrder : ordUnit K zu = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K zu).1 (by simpa [zu] using hzUnit)
    let t : Kˣ := p * zu
    have htOrder : ordUnit K t = (k : Int) := by
      dsimp only [t]
      rw [ordUnit_mul, hpOrder, hzuOrder, add_zero]
    have htPos : (0 : WithTop Int) < ord K (t : K) := by
      rw [← coe_ordUnit, htOrder]
      exact_mod_cast (show (0 : Int) < (k : Int) by omega)
    have hsOrder : ord K (1 + (t : K)) = 0 := by
      have hstrict : ord K (1 : K) < ord K (t : K) := by
        simpa only [ord_one] using htPos
      simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hstrict
    have hsNe : 1 + (t : K) ≠ 0 := by
      apply (ord_eq_top_iff K).not.mp
      rw [hsOrder]
      exact WithTop.coe_ne_top
    let s : Kˣ := Units.mk0 (1 + (t : K)) hsNe
    have hsUnit : IsValuationUnit K (s : K) := by
      simpa [s, IsValuationUnit] using hsOrder
    have hmatch : (((n + 1 : Nat) : Int) : WithTop Int) ≤
        ord K (((a : K) - 1) - (t : K) ^ 2) := by
      have hroot : (1 : WithTop Int) ≤
          ord K ((epsilon : K) - z ^ 2) := by
        have hneg : ord K ((epsilon : K) - z ^ 2) =
            ord K (z ^ 2 - (epsilon : K)) := by
          have heq : (epsilon : K) - z ^ 2 =
              -(z ^ 2 - (epsilon : K)) := by ring
          rw [heq, ord_neg]
        rw [hneg]
        exact one_le_ord_of_pos hzApprox
      have hfactor : ((a : K) - 1) - (t : K) ^ 2 =
          (p : K) ^ 2 * ((epsilon : K) - z ^ 2) := by
        have htVal : (t : K) = (p : K) * z := rfl
        have hepsilonVal : (epsilon : K) =
            ((a : K) - 1) / (p : K) ^ 2 := by
          dsimp only [epsilon, error]
          rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
          rfl
        rw [htVal, hepsilonVal]
        field_simp [Units.ne_zero p]
      rw [hfactor, ord_mul]
      have hpSqOrder : ord K ((p : K) ^ 2) =
          ((n : Int) : WithTop Int) := by
        change ord K ((p ^ 2 : Kˣ) : K) =
          ((n : Int) : WithTop Int)
        rw [← coe_ordUnit, ordUnit_pow, hpOrder]
        exact_mod_cast (show (2 : Int) * (k : Int) = (n : Int) by omega)
      rw [hpSqOrder]
      have hcast : (((n + 1 : Nat) : Int) : WithTop Int) ≤
          ((n : Int) : WithTop Int) + 1 := by
        exact_mod_cast (show (n + 1 : Int) ≤ (n : Int) + 1 by omega)
      exact hcast.trans (add_le_add (le_refl _) hroot)
    have htwoT : (((n + 1 : Nat) : Int) : WithTop Int) ≤
        ord K ((2 : K) * (t : K)) := by
      rw [ord_mul, ← coe_ordUnit, htOrder, ← ramificationIndex_spec]
      exact_mod_cast (show (n + 1 : Int) ≤
        (ramificationIndex K : Int) + (k : Int) by omega)
    have hnumerator : (((n + 1 : Nat) : Int) : WithTop Int) ≤
        ord K ((a : K) - (s : K) ^ 2) := by
      have hsumOrder := min_ord_le_ord_add K
        (((a : K) - 1) - (t : K) ^ 2) (-((2 : K) * (t : K)))
      have hmin : (((n + 1 : Nat) : Int) : WithTop Int) ≤
          min (ord K (((a : K) - 1) - (t : K) ^ 2))
            (ord K (-((2 : K) * (t : K)))) := by
        exact le_min hmatch (by simpa only [ord_neg] using htwoT)
      have hfield : (((a : K) - 1) - (t : K) ^ 2) +
          (-((2 : K) * (t : K))) = (a : K) - (s : K) ^ 2 := by
        change (((a : K) - 1) - (t : K) ^ 2) +
          (-((2 : K) * (t : K))) = (a : K) - (1 + (t : K)) ^ 2
        ring
      rw [← hfield]
      exact hmin.trans hsumOrder
    let b : Kˣ := a / s ^ 2
    have hbUnit : IsValuationUnit K (b : K) := by
      apply (valuationUnitSubgroup K).mul_mem ha.1
      apply (valuationUnitSubgroup K).inv_mem
      exact (valuationUnitSubgroup K).pow_mem hsUnit 2
    have hbDeep : (((n + 1 : Nat) : Int) : WithTop Int) ≤
        ord K ((b : K) - 1) := by
      have hfield : (b : K) - 1 =
          ((a : K) - (s : K) ^ 2) / (s : K) ^ 2 := by
        dsimp only [b]
        rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero s]
      rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv]
      have hsSq : ord K ((s : K) ^ 2) = 0 := by
        rw [ord_pow, hsUnit]
        simp
      rw [hsSq, neg_zero, add_zero]
      exact hnumerator
    refine ⟨b, ⟨hbUnit, ?_⟩, s, ?_⟩
    · exact (Lattice.mem_powerIdeal_iff (K := K)
        ((n + 1 : Nat) : Int) _).2 hbDeep
    · dsimp only [b]
      simp

noncomputable instance principalUnitSquareClassFiltrationLawsProved :
    PrincipalUnitSquareClassFiltrationLaws K where
  eq_succ_of_even n hpos hlt heven := by
    apply le_antisymm
    · rintro c ⟨a, ha, rfl⟩
      obtain ⟨b, hb, s, has⟩ :=
        exists_deeper_principal_unit_square_class n hpos hlt heven a ha
      refine ⟨b, hb, ?_⟩
      change squareClass K b = squareClass K a
      rw [has, squareClass_mul_square]
    · exact principalUnitSquareClassSubgroup_anti K (Nat.le_succ n)

/-- Relative quadratic defect depends only on the field square class. -/
theorem quadraticDefect_eq_of_squareClass_eq (a b : Kˣ)
    (h : squareClass K a = squareClass K b) :
    quadraticDefect K a = quadraticDefect K b := by
  change QuotientGroup.mk' (Subgroup.square Kˣ) a =
    QuotientGroup.mk' (Subgroup.square Kˣ) b at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨s, hs, hasb⟩
  change IsSquare s at hs
  rcases hs with ⟨t, ht⟩
  have hproduct : a * t ^ 2 = b := by
    simpa [pow_two, ht] using hasb
  rw [← hproduct, quadraticDefect_mul_square]

/-- Membership in the principal-unit filtration is equivalent, in the
direction needed for Beli's reverse constructions, to the corresponding
lower bound on relative quadratic defect. -/
theorem natCast_le_quadraticDefect_of_unitClass_mem
    (u : valuationUnitSubgroup K) (n : Nat)
    (hmem : valuationUnitClassHom K u ∈
      principalUnitValuationClassSubgroup K n) :
    (n : ℕ∞) ≤ quadraticDefect K (u : Kˣ) := by
  rcases hmem with ⟨v, hv, hclass⟩
  change (v : Kˣ) ∈ principalUnitSubgroup K n at hv
  have herror : ((n : Int) : WithTop Int) ≤
      ord K (((v : Kˣ) : K) - 1) :=
    (Lattice.mem_powerIdeal_iff (K := K) (n : Int) _).1 hv.2
  have happ : IsQuadraticApproximation K (v : Kˣ) n := by
    refine ⟨1, ?_⟩
    have hfield : 1 - (1 : K) ^ 2 / ((v : Kˣ) : K) =
        (((v : Kˣ) : K) - 1) / ((v : Kˣ) : K) := by
      field_simp [Units.ne_zero (v : Kˣ)]
    rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv, v.property]
    simp only [neg_zero, add_zero]
    exact_mod_cast herror
  have hvDefect : (n : ℕ∞) ≤ quadraticDefect K (v : Kˣ) :=
    natCast_le_quadraticDefect K happ
  have hsquareClass : squareClass K (v : Kˣ) = squareClass K (u : Kˣ) := by
    have hmap := congrArg (valuationUnitClassToSquareClass K) hclass
    simpa only [valuationUnitClassToSquareClass_apply] using hmap
  rw [← quadraticDefect_eq_of_squareClass_eq (v : Kˣ) (u : Kˣ) hsquareClass]
  exact hvDefect

/-- Every valuation unit has relative quadratic defect at least one. -/
theorem one_le_quadraticDefect_of_unit (u : Kˣ)
    (hu : IsValuationUnit K (u : K)) :
    (1 : ℕ∞) ≤ quadraticDefect K u := by
  obtain ⟨z, hzUnit, hzApprox⟩ :=
    exists_unit_squareRoot_mod_maximal K u hu
  apply natCast_le_quadraticDefect K
  refine ⟨z, ?_⟩
  have hfield : 1 - z ^ 2 / (u : K) =
      ((u : K) - z ^ 2) / (u : K) := by
    field_simp [Units.ne_zero u]
  rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv, hu]
  simp only [neg_zero, add_zero]
  have hneg : ord K ((u : K) - z ^ 2) =
      ord K (z ^ 2 - (u : K)) := by
    have heq : (u : K) - z ^ 2 = -(z ^ 2 - (u : K)) := by ring
    rw [heq, ord_neg]
  rw [hneg]
  exact one_le_ord_of_pos hzApprox

/-- In residue characteristic two, every valuation-unit square class has a
principal-unit representative of depth one.  Thus the genuine depth-zero
and depth-one square-class layers coincide. -/
theorem principalUnitSquareClassSubgroup_zero_eq_one :
    principalUnitSquareClassSubgroup K 0 =
      principalUnitSquareClassSubgroup K 1 := by
  apply le_antisymm
  · rw [principalUnitSquareClassSubgroup_zero]
    rintro z ⟨u, hu, rfl⟩
    let uu : valuationUnitSubgroup K := ⟨u, hu⟩
    have hdefect : (1 : ℕ∞) ≤ quadraticDefect K (uu : Kˣ) :=
      one_le_quadraticDefect_of_unit (uu : Kˣ) uu.property
    have hunitClass : valuationUnitClassHom K uu ∈
        principalUnitValuationClassSubgroup K 1 :=
      valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
        K uu 1 hdefect
    rw [← valuationUnitClassSubgroupSquareImage_principalUnit K 1]
    exact valuationUnitClassToSquareClass_mem_image K hunitClass
  · exact principalUnitSquareClassSubgroup_anti K (Nat.zero_le 1)

/-- Relative quadratic defect is zero only on odd-valuation square classes.
Together with the converse implication in the common defect-arithmetic
layer, this identifies the zero-defect stratum. -/
theorem odd_ordUnit_of_quadraticDefect_eq_zero
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
    have hone := one_le_quadraticDefect_of_unit u huUnit
    rw [huDefect] at hone
    simp at hone
  · exact hodd

noncomputable instance unitQuadraticDefectParityLawsProved :
    UnitQuadraticDefectParityLaws K where
  odd_toNat_of_lt_two_mul_e u hu hlt := by
    have hfinite : quadraticDefect K u ≠ ⊤ :=
      ne_top_of_lt (hlt.trans (ENat.coe_lt_top _))
    let d := (quadraticDefect K u).toNat
    have hdefect : quadraticDefect K u = (d : ℕ∞) := by
      simpa only [d] using (ENat.coe_toNat hfinite).symm
    have hdPos : 0 < d := by
      have hone := one_le_quadraticDefect_of_unit u hu
      rw [hdefect] at hone
      exact_mod_cast hone
    have hdLt : d < 2 * ramificationIndex K := by
      rw [hdefect] at hlt
      exact_mod_cast hlt
    rcases Nat.even_or_odd d with heven | hodd
    · let uu : valuationUnitSubgroup K := ⟨u, hu⟩
      have hmem : valuationUnitClassHom K uu ∈
          principalUnitValuationClassSubgroup K d :=
        valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
          K uu d (by rw [← hdefect])
      have hnext : valuationUnitClassHom K uu ∈
          principalUnitValuationClassSubgroup K (d + 1) := by
        rw [← principalUnitValuationClassSubgroup_eq_succ_of_even
          K d hdPos hdLt heven]
        exact hmem
      have hlower := natCast_le_quadraticDefect_of_unitClass_mem uu (d + 1) hnext
      rw [hdefect] at hlower
      have hfalse : False := by
        have hnat : d + 1 ≤ d := by exact_mod_cast hlower
        omega
      exact hfalse.elim
    · exact hodd

/-- A square class of even valuation and defect strictly below `2e` has odd
finite defect.  This is the square-normalized form of the unit parity law. -/
theorem quadraticDefect_toNat_odd_of_even_ordUnit_of_lt_two_mul_e
    (x : Kˣ) (hxEven : Even (ordUnit K x))
    (hlt : quadraticDefect K x <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    Odd (quadraticDefect K x).toNat := by
  rcases hxEven with ⟨k, hk⟩
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
  have huDefect : quadraticDefect K u = quadraticDefect K x := by
    calc
      quadraticDefect K u = quadraticDefect K (u * s ^ 2) :=
        (quadraticDefect_mul_square K u s).symm
      _ = quadraticDefect K x := congrArg (quadraticDefect K) hfactor
  have huLt : quadraticDefect K u <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rwa [huDefect]
  have huOdd := quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
    (K := K) u huUnit huLt
  rwa [huDefect] at huOdd

theorem exists_unit_quadraticDefect_eq_odd
    (d : Nat) (hpos : 0 < d) (hodd : Odd d)
    (hlt : d < 2 * ramificationIndex K) :
    ∃ u : Kˣ, IsValuationUnit K (u : K) ∧
      quadraticDefect K u = (d : ℕ∞) := by
  let p : Kˣ := uniformizerPowerUnit K (d : Int)
  have hpOrder : ordUnit K p = (d : Int) :=
    ordUnit_uniformizerPowerUnit (K := K) (d : Int)
  have hpPos : (0 : WithTop Int) < ord K (p : K) := by
    rw [← coe_ordUnit, hpOrder]
    exact_mod_cast (show (0 : Int) < (d : Int) by omega)
  have huOrder : ord K (1 + (p : K)) = 0 := by
    have hstrict : ord K (1 : K) < ord K (p : K) := by
      simpa only [ord_one] using hpPos
    simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hstrict
  have huNe : 1 + (p : K) ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [huOrder]
    exact WithTop.coe_ne_top
  let u : Kˣ := Units.mk0 (1 + (p : K)) huNe
  have huUnit : IsValuationUnit K (u : K) := by
    simpa [u, IsValuationUnit] using huOrder
  have hlower : (d : ℕ∞) ≤ quadraticDefect K u := by
    apply natCast_le_quadraticDefect K
    refine ⟨1, ?_⟩
    have hfield : 1 - (1 : K) ^ 2 / (u : K) =
        (p : K) / (u : K) := by
      have huVal : (u : K) = 1 + (p : K) := rfl
      rw [huVal]
      field_simp [huNe]
      ring
    rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv, huUnit]
    simp only [neg_zero, add_zero, ← coe_ordUnit, hpOrder]
    exact_mod_cast (show (d : Int) ≤ (d : Int) by rfl)
  have hupper : quadraticDefect K u ≤ (d : ℕ∞) := by
    by_contra hnot
    have hstrict : (d : ℕ∞) < quadraticDefect K u := lt_of_not_ge hnot
    have hnext : ((d + 1 : Nat) : ℕ∞) ≤ quadraticDefect K u := by
      have hadd : (d : ℕ∞) + 1 ≤ quadraticDefect K u :=
        (ENat.add_one_le_iff (ENat.coe_ne_top d)).2 hstrict
      simpa only [ENat.coe_add, ENat.coe_one] using hadd
    obtain ⟨y, hy⟩ :=
      (isQuadraticApproximation_iff_le_defect K).2 hnext
    have hdeep : (((d + 1 : Nat) : Int) : WithTop Int) ≤
        ord K ((u : K) - y ^ 2) := by
      have hfield : 1 - y ^ 2 / (u : K) =
          ((u : K) - y ^ 2) / (u : K) := by
        field_simp [Units.ne_zero u]
      rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv, huUnit] at hy
      simp only [neg_zero, add_zero] at hy
      exact_mod_cast hy
    have hpFieldOrder : ord K (p : K) =
        ((d : Int) : WithTop Int) := by
      rw [← coe_ordUnit, hpOrder]
    have hpLt : ord K (p : K) < ord K ((u : K) - y ^ 2) := by
      apply lt_of_lt_of_le _ hdeep
      rw [hpFieldOrder]
      exact_mod_cast (show (d : Int) < (d + 1 : Nat) by omega)
    have horder : ord K (1 - y ^ 2) =
        ((d : Int) : WithTop Int) := by
      have hsub := (ord K).map_sub_eq_of_lt_right hpLt
      have hfield : ((u : K) - y ^ 2) - (p : K) = 1 - y ^ 2 := by
        change (1 + (p : K) - y ^ 2) - (p : K) = 1 - y ^ 2
        ring
      simpa only [hfield, hpFieldOrder] using hsub
    have hevenInt : Even (d : Int) :=
      even_order_one_sub_sq_of_lt_two_mul_e_proved y (d : Int) horder
        (by exact_mod_cast hpos) (by exact_mod_cast hlt)
    have hoddInt : Odd (d : Int) := by exact_mod_cast hodd
    exact (Int.not_odd_iff_even.mpr hevenInt hoddInt).elim
  exact ⟨u, huUnit, le_antisymm hupper hlower⟩

end Bong.Dyadic
