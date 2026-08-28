/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiscriminantClassProof
import Bong.Dyadic.HilbertDefectCriterionProof
import Bong.Dyadic.UnramifiedNorm
import Bong.Dyadic.UnitDefectClassification

/-!
# Direct classification of unramified quadratic norms

For the distinguished dyadic discriminant unit `Delta`, this file proves
directly that the nonzero values of `x^2 - Delta * y^2` are exactly the
elements of even valuation.  The proof uses the concrete discriminant
construction, the dyadic square-difference parity theorem, and the concrete
positive Hilbert-defect criterion.  In particular, it does not assume
bimultiplicativity or nondegeneracy of the Hilbert symbol.
-/

namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [discriminant : DyadicDiscriminantClassLaws K]

local instance directDefectLaws : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

private theorem discriminant_not_square :
    ¬IsSquare discriminant.discriminantUnit := by
  intro hsquare
  have htop := quadraticDefect_eq_top_of_isSquare K hsquare
  rw [discriminant.discriminant_defect] at htop
  exact ENat.coe_ne_top _ htop

private theorem ord_four :
    ord K (4 : K) =
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
  rw [show (4 : K) = 2 * 2 by norm_num, ord_mul,
    ← ramificationIndex_spec]
  norm_cast
  ring

private theorem ord_one_sub_discriminant :
    ord K (1 - (discriminant.discriminantUnit : K)) =
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
  rw [discriminant.discriminant_eq_one_sub_four_mul_rho]
  have hfield : 1 - (1 - 4 * discriminant.rho) =
      (4 : K) * discriminant.rho := by ring
  rw [hfield, ord_mul, ord_four,
    discriminant.rho_isValuationUnit, add_zero]

private theorem even_order_square_sub_discriminant
    (z : Kˣ) (hzUnit : IsValuationUnit K (z : K))
    (hdiffNe : (z : K) ^ 2 -
      (discriminant.discriminantUnit : K) ≠ 0) :
    Even (ordUnit K (Units.mk0
      ((z : K) ^ 2 - (discriminant.discriminantUnit : K)) hdiffNe)) := by
  let error : K :=
    1 - (z : K) ^ 2 / (discriminant.discriminantUnit : K)
  have herrorEq : error =
      -((z : K) ^ 2 - (discriminant.discriminantUnit : K)) /
        (discriminant.discriminantUnit : K) := by
    dsimp only [error]
    field_simp [Units.ne_zero discriminant.discriminantUnit]
    ring
  have herrorNe : error ≠ 0 := by
    rw [herrorEq]
    exact div_ne_zero (neg_ne_zero.mpr hdiffNe)
      (Units.ne_zero discriminant.discriminantUnit)
  have herrorIntegral : 0 ≤ ord K error := by
    have hratioUnit :
        ord K ((z : K) ^ 2 /
          (discriminant.discriminantUnit : K)) = 0 := by
      rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
        ord_pow, hzUnit, discriminant.discriminant_isValuationUnit]
      norm_num
    have hsum := min_ord_le_ord_add K (1 : K)
      (-((z : K) ^ 2 / (discriminant.discriminantUnit : K)))
    change 0 ≤ ord K error
    simpa only [sub_eq_add_neg, ord_one, ord_neg, hratioUnit, min_self,
      error] using hsum
  have herrorFinite : ord K error ≠ ⊤ :=
    (ord_eq_top_iff K).not.mpr herrorNe
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp herrorFinite
  have hnNonneg : 0 ≤ n := by
    rw [← hn] at herrorIntegral
    exact_mod_cast herrorIntegral
  have happ : IsQuadraticApproximation K
      discriminant.discriminantUnit n.toNat := by
    refine ⟨(z : K), ?_⟩
    change ((n.toNat : Nat) : WithTop Int) ≤ ord K error
    rw [← hn]
    exact_mod_cast (show (n.toNat : Int) ≤ n by
      rw [Int.toNat_of_nonneg hnNonneg])
  have hnDefect := natCast_le_quadraticDefect K happ
  have hnUpper : n ≤ 2 * (ramificationIndex K : Int) := by
    rw [discriminant.discriminant_defect] at hnDefect
    have hnatUpper : n.toNat ≤ 2 * ramificationIndex K := by
      exact_mod_cast hnDefect
    rw [← Int.toNat_of_nonneg hnNonneg]
    exact_mod_cast hnatUpper
  have hnEven : Even n := by
    rcases lt_trichotomy n (2 * (ramificationIndex K : Int)) with
      hlt | heq | hgt
    · by_cases hnZero : n = 0
      · subst n
        exact Even.zero
      have hnPos : 0 < n := lt_of_le_of_ne hnNonneg (Ne.symm hnZero)
      have hdiffOrder :
          ord K ((discriminant.discriminantUnit : K) - (z : K) ^ 2) =
            (n : WithTop Int) := by
        have hfield : (discriminant.discriminantUnit : K) - (z : K) ^ 2 =
            (discriminant.discriminantUnit : K) * error := by
          dsimp only [error]
          field_simp [Units.ne_zero discriminant.discriminantUnit]
        rw [hfield, ord_mul,
          discriminant.discriminant_isValuationUnit, zero_add]
        exact hn.symm
      have hdeltaOrder :
          ord K (1 - (discriminant.discriminantUnit : K)) =
            (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) :=
        ord_one_sub_discriminant (K := K)
      have hstrict :
          ord K ((discriminant.discriminantUnit : K) - (z : K) ^ 2) <
            ord K (1 - (discriminant.discriminantUnit : K)) := by
        rw [hdiffOrder, hdeltaOrder]
        exact_mod_cast hlt
      have hadd := (ord K).map_add_eq_of_lt_left hstrict
      have hfield :
          ((discriminant.discriminantUnit : K) - (z : K) ^ 2) +
            (1 - (discriminant.discriminantUnit : K)) =
              1 - (z : K) ^ 2 := by ring
      have honeOrder : ord K (1 - (z : K) ^ 2) =
          (n : WithTop Int) := by
        simpa only [hfield, hdiffOrder] using hadd
      exact even_order_one_sub_sq_of_lt_two_mul_e_proved
        (z : K) n honeOrder hnPos hlt
    · subst n
      refine ⟨ramificationIndex K, ?_⟩
      ring
    · exact (not_le_of_gt hgt hnUpper).elim
  have hunitOrder :
      ordUnit K (Units.mk0
        ((z : K) ^ 2 - (discriminant.discriminantUnit : K)) hdiffNe) = n := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K ((z : K) ^ 2 -
      (discriminant.discriminantUnit : K)) = (n : WithTop Int)
    rw [show (z : K) ^ 2 - (discriminant.discriminantUnit : K) =
      -((discriminant.discriminantUnit : K) * error) by
        dsimp only [error]
        field_simp [Units.ne_zero discriminant.discriminantUnit]
        ring,
      ord_neg, ord_mul, discriminant.discriminant_isValuationUnit,
      zero_add, hn]
  rw [hunitOrder]
  exact hnEven

private theorem ord_sq_unit (u : Kˣ) :
    ord K ((u : K) ^ 2) =
      ((2 * ordUnit K u : Int) : WithTop Int) := by
  change ord K (((u ^ 2 : Kˣ) : K)) =
    ((2 * ordUnit K u : Int) : WithTop Int)
  rw [← coe_ordUnit, ordUnit_pow]
  norm_cast

private theorem ord_discriminant_mul_sq (u : Kˣ) :
    ord K ((discriminant.discriminantUnit : K) * (u : K) ^ 2) =
      ((2 * ordUnit K u : Int) : WithTop Int) := by
  rw [ord_mul, discriminant.discriminant_isValuationUnit, zero_add,
    ord_sq_unit]

private theorem even_order_of_discriminant_norm
    (b : Kˣ) (hb : IsQuadraticNorm K discriminant.discriminantUnit b) :
    Even (ordUnit K b) := by
  rcases hb with ⟨x, y, hxy⟩
  by_cases hxZero : x = 0
  · subst x
    have hyNe : y ≠ 0 := by
      intro hyZero
      subst y
      norm_num at hxy
      exact Units.ne_zero b hxy.symm
    let yu : Kˣ := Units.mk0 y hyNe
    have horder : ordUnit K b = 2 * ordUnit K yu := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      change ord K (b : K) =
        ((2 * ordUnit K yu : Int) : WithTop Int)
      rw [← hxy]
      rw [zero_pow (by omega : 2 ≠ 0), zero_sub, ord_neg]
      exact ord_discriminant_mul_sq yu
    rw [horder]
    refine ⟨ordUnit K yu, by omega⟩
  by_cases hyZero : y = 0
  · subst y
    let xu : Kˣ := Units.mk0 x hxZero
    have horder : ordUnit K b = 2 * ordUnit K xu := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      change ord K (b : K) =
        ((2 * ordUnit K xu : Int) : WithTop Int)
      rw [← hxy]
      rw [zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero]
      exact ord_sq_unit xu
    rw [horder]
    refine ⟨ordUnit K xu, by omega⟩
  let xu : Kˣ := Units.mk0 x hxZero
  let yu : Kˣ := Units.mk0 y hyZero
  rcases lt_trichotomy (ordUnit K xu) (ordUnit K yu) with hlt | heq | hgt
  · have hterm : ord K (x ^ 2) <
        ord K ((discriminant.discriminantUnit : K) * y ^ 2) := by
      change ord K ((xu : K) ^ 2) <
        ord K ((discriminant.discriminantUnit : K) * (yu : K) ^ 2)
      rw [ord_sq_unit, ord_discriminant_mul_sq]
      exact_mod_cast (show 2 * ordUnit K xu < 2 * ordUnit K yu by omega)
    have hvalue := (ord K).map_sub_eq_of_lt_left hterm
    rw [hxy] at hvalue
    change ord K (b : K) = ord K ((xu : K) ^ 2) at hvalue
    have horder : ordUnit K b = 2 * ordUnit K xu := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, hvalue, ord_sq_unit]
    rw [horder]
    refine ⟨ordUnit K xu, by omega⟩
  · let z : Kˣ := xu / yu
    have hzOrder : ordUnit K z = 0 := by
      dsimp only [z]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
      omega
    have hzUnit : IsValuationUnit K (z : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K z).2 hzOrder
    have hdiffNe : (z : K) ^ 2 -
        (discriminant.discriminantUnit : K) ≠ 0 := by
      intro hzero
      apply discriminant_not_square (K := K)
      refine ⟨z, ?_⟩
      apply Units.ext
      change (discriminant.discriminantUnit : K) = (z : K) * (z : K)
      simpa [pow_two] using (sub_eq_zero.mp hzero).symm
    let diff : Kˣ := Units.mk0
      ((z : K) ^ 2 - (discriminant.discriminantUnit : K)) hdiffNe
    have hdiffEven : Even (ordUnit K diff) :=
      even_order_square_sub_discriminant z hzUnit hdiffNe
    have hfactor : x ^ 2 -
        (discriminant.discriminantUnit : K) * y ^ 2 =
          y ^ 2 * (diff : K) := by
      dsimp only [diff, z, xu, yu]
      simp only [Units.val_mk0, Units.val_div_eq_div_val]
      field_simp [hyZero]
    have horder : ordUnit K b =
        2 * ordUnit K yu + ordUnit K diff := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      calc
        ord K (b : K) = ord K (y ^ 2 * (diff : K)) := by
          exact congrArg (ord K) (hxy.symm.trans hfactor)
        _ = ord K (y ^ 2) + ord K (diff : K) := ord_mul K _ _
        _ = ((2 * ordUnit K yu : Int) : WithTop Int) +
            (ordUnit K diff : WithTop Int) := by
          rw [show y ^ 2 = (yu : K) ^ 2 by rfl, ord_sq_unit,
            coe_ordUnit]
        _ = ((2 * ordUnit K yu + ordUnit K diff : Int) :
            WithTop Int) := by norm_cast
    rcases hdiffEven with ⟨k, hk⟩
    rw [horder, hk]
    refine ⟨ordUnit K yu + k, by omega⟩
  · have hterm : ord K ((discriminant.discriminantUnit : K) * y ^ 2) <
        ord K (x ^ 2) := by
      change ord K ((discriminant.discriminantUnit : K) * (yu : K) ^ 2) <
        ord K ((xu : K) ^ 2)
      rw [ord_discriminant_mul_sq, ord_sq_unit]
      exact_mod_cast (show 2 * ordUnit K yu < 2 * ordUnit K xu by omega)
    have hvalue := (ord K).map_sub_eq_of_lt_right hterm
    rw [hxy] at hvalue
    change ord K (b : K) =
      ord K ((discriminant.discriminantUnit : K) * (yu : K) ^ 2) at hvalue
    have horder : ordUnit K b = 2 * ordUnit K yu := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, hvalue, ord_discriminant_mul_sq]
    rw [horder]
    refine ⟨ordUnit K yu, by omega⟩

private theorem quadraticDefect_ne_zero_of_unit
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    quadraticDefect K u ≠ 0 := by
  rcases exists_unit_squareRoot_mod_maximal K u hu with
    ⟨z, _hzUnit, hzError⟩
  have happrox : IsQuadraticApproximation K u 1 := by
    refine ⟨z, ?_⟩
    have hnormalized :
        1 - z ^ 2 / (u : K) = ((u : K) - z ^ 2) / (u : K) := by
      field_simp [Units.ne_zero u]
    rw [hnormalized, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, hu]
    simp only [neg_zero, add_zero]
    have hpositive : 0 < ord K ((u : K) - z ^ 2) := by
      rw [show (u : K) - z ^ 2 = -(z ^ 2 - (u : K)) by ring,
        ord_neg]
      exact hzError
    by_cases htop : ord K ((u : K) - z ^ 2) = ⊤
    · rw [htop]
      exact le_top
    · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hd] at hpositive ⊢
      have hdPositive : (0 : Int) < d := by exact_mod_cast hpositive
      exact_mod_cast (show (1 : Int) ≤ d by omega)
  have hdefect := natCast_le_quadraticDefect K happrox
  intro hzero
  rw [hzero] at hdefect
  simp at hdefect

private theorem discriminant_norm_of_even_order
    (b : Kˣ) (heven : Even (ordUnit K b)) :
    IsQuadraticNorm K discriminant.discriminantUnit b := by
  rcases heven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let unitPart : Kˣ := b / s ^ 2
  have hsOrder : ordUnit K s = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have hunitOrder : ordUnit K unitPart = 0 := by
    dsimp only [unitPart]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow, hsOrder]
    omega
  have hunit : IsValuationUnit K (unitPart : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K unitPart).2 hunitOrder
  have hunitDefectNe : quadraticDefect K unitPart ≠ 0 :=
    quadraticDefect_ne_zero_of_unit unitPart hunit
  have hstrict : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K discriminant.discriminantUnit +
        quadraticDefect K unitPart := by
    rw [discriminant.discriminant_defect]
    have hpositive : (0 : ℕ∞) < quadraticDefect K unitPart :=
      pos_iff_ne_zero.mpr hunitDefectNe
    simpa using
      (ENat.add_lt_add_iff_left (ENat.coe_ne_top
        (2 * ramificationIndex K))).2 hpositive
  have hunitNorm :
      IsQuadraticNorm K discriminant.discriminantUnit unitPart :=
    (hilbertSymbol_eq_one_iff K _ _).mp
      (hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e_proved
        discriminant.discriminantUnit unitPart hstrict)
  have hfactor : unitPart * s ^ 2 = b := by
    dsimp only [unitPart]
    simp
  rw [← hfactor]
  exact IsQuadraticNorm.mul K hunitNorm
    (isQuadraticNorm_of_isSquare_right K ⟨s, by simp [pow_two]⟩)

noncomputable instance dyadicUnramifiedNormLawsProvedDirect :
    DyadicUnramifiedNormLaws K where
  discriminant_norm_iff_even_order b :=
    ⟨even_order_of_discriminant_norm b,
      discriminant_norm_of_even_order b⟩

end Bong.Dyadic
