/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma82Unit

/-!
# Valuation-unit multipliers for even square classes

An even-order field square class has a valuation-unit representative after
removing a uniformizer square.  This elementary normalization converts the
square classes supplied by Lemma 8.2 into the valuation-unit multipliers
used in the equal-outer-order part of Lemma 8.14.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A square class of even valuation cannot have quadratic defect zero. -/
theorem quadraticDefect_ne_zero_of_even_ordUnit
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    (x : Kˣ) (hxEven : Even (ordUnit K x)) :
    quadraticDefect K x ≠ 0 := by
  intro hxZero
  have hxOdd := odd_ordUnit_of_quadraticDefect_eq_zero x hxZero
  rcases hxEven with ⟨k, hk⟩
  rcases hxOdd with ⟨l, hl⟩
  omega

/-- Below the dyadic endpoint, a finite defect carried by an even-order
square class is an odd rational integer. -/
theorem isOddRationalInteger_of_even_ordUnit_of_defectOrder_eq
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    (x : Kˣ) (d : ℚ)
    (hxEven : Even (ordUnit K x))
    (hdefect : GoodBONG.defectOrder (K := K) x = (d : WithTop ℚ))
    (hdLt : d < 2 * (ramificationIndex K : ℚ)) :
    IsOddRationalInteger d := by
  have hxNonzero := quadraticDefect_ne_zero_of_even_ordUnit x hxEven
  rcases exists_valuationUnit_same_defect_same_hilbert
      (1 : Kˣ) x hxNonzero with
    ⟨u, huUnit, huDefect, _⟩
  cases huQuadratic : quadraticDefect K u with
  | top =>
      unfold GoodBONG.defectOrder at hdefect
      rw [← huDefect, huQuadratic] at hdefect
      exact (WithTop.top_ne_coe hdefect).elim
  | coe m =>
      have hmDefect : (m : ℚ) = d := by
        unfold GoodBONG.defectOrder at hdefect
        rw [← huDefect, huQuadratic] at hdefect
        exact WithTop.coe_eq_coe.mp hdefect
      have hmLt : m < 2 * ramificationIndex K := by
        exact_mod_cast (hmDefect.trans_lt hdLt)
      have huLt : quadraticDefect K u <
          ((2 * ramificationIndex K : Nat) : WithTop Nat) := by
        rw [huQuadratic]
        exact WithTop.coe_lt_coe.mpr hmLt
      have hmOdd : Odd m := by
        simpa [huQuadratic] using
          quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
            (K := K) u huUnit huLt
      refine ⟨(m : Int), ?_, ?_⟩
      · exact_mod_cast hmOdd
      · calc
          d = (m : ℚ) := hmDefect.symm
          _ = ((m : Int) : ℚ) := by norm_num

/-- An even-order square class can be killed by a valuation-unit multiplier.
The multiplier has the same quadratic defect as the original class. -/
theorem exists_valuationUnit_multiplier_isSquare
    (x : Kˣ) (hxEven : Even (ordUnit K x)) :
    ∃ η : Kˣ,
      IsValuationUnit K (η : K) ∧
        IsSquare (η * x) ∧
        quadraticDefect K η = quadraticDefect K x := by
  rcases hxEven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let xUnit : Kˣ := x / s ^ 2
  have hsOrder : ordUnit K s = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have hxUnitOrder : ordUnit K xUnit = 0 := by
    dsimp only [xUnit]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder]
    omega
  have hxUnit : IsValuationUnit K (xUnit : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K xUnit).2 hxUnitOrder
  let η : Kˣ := xUnit⁻¹
  have hηUnit : IsValuationUnit K (η : K) := by
    rw [isValuationUnit_iff_ordUnit_eq_zero]
    dsimp only [η]
    rw [ordUnit_inv, hxUnitOrder]
    simp
  have hfactor : xUnit * s ^ 2 = x := by
    dsimp only [xUnit]
    simp
  have hscaled : η * x = s ^ 2 := by
    rw [← hfactor]
    dsimp only [η]
    simp
  have hsquare : IsSquare (η * x) := by
    refine ⟨s, ?_⟩
    simpa [pow_two] using hscaled
  refine ⟨η, hηUnit, hsquare, ?_⟩
  calc
    quadraticDefect K η = quadraticDefect K xUnit := by
      dsimp only [η]
      exact quadraticDefect_inv K xUnit
    _ = quadraticDefect K (xUnit * s ^ 2) :=
      (quadraticDefect_mul_square K xUnit s).symm
    _ = quadraticDefect K x := congrArg (quadraticDefect K) hfactor

/-- If `x` has even order, any nonzero-defect square class `w` can be
written, up to a square, as `ηx` with `η` a valuation unit.  Both its
quadratic defect and its Hilbert pairing with a fixed class are preserved.
-/
theorem exists_valuationUnit_multiplier_same_defect_same_hilbert
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    (z x w : Kˣ)
    (hxEven : Even (ordUnit K x))
    (hwNonzero : quadraticDefect K w ≠ 0) :
    ∃ η : Kˣ,
      IsValuationUnit K (η : K) ∧
        quadraticDefect K (η * x) = quadraticDefect K w ∧
        hilbertSymbol K z (η * x) = hilbertSymbol K z w := by
  rcases exists_valuationUnit_same_defect_same_hilbert
      z w hwNonzero with
    ⟨u, huUnit, huDefect, huHilbert⟩
  rcases hxEven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let xUnit : Kˣ := x / s ^ 2
  have hsOrder : ordUnit K s = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have hxUnitOrder : ordUnit K xUnit = 0 := by
    dsimp only [xUnit]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder]
    omega
  have hxUnit : IsValuationUnit K (xUnit : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K xUnit).2 hxUnitOrder
  let η : Kˣ := u * xUnit⁻¹
  have hηUnit : IsValuationUnit K (η : K) := by
    rw [isValuationUnit_iff_ordUnit_eq_zero]
    dsimp only [η]
    rw [ordUnit_mul, ordUnit_inv,
      (isValuationUnit_iff_ordUnit_eq_zero K u).1 huUnit,
      hxUnitOrder]
    simp
  have hfactor : xUnit * s ^ 2 = x := by
    dsimp only [xUnit]
    simp
  have hscaled : η * x = u * s ^ 2 := by
    rw [← hfactor]
    dsimp only [η]
    simp [mul_assoc]
  refine ⟨η, hηUnit, ?_, ?_⟩
  · rw [hscaled, quadraticDefect_mul_square, huDefect]
  · rw [hscaled, hilbertSymbol_mul_square_right, huHilbert]

/-- Negative-sign form obtained by combining the even-class normalization
with Lemma 8.2(i). -/
theorem exists_valuationUnit_multiplier_hilbert_neg_of_defect_sum
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    (z x reference : Kˣ)
    (hxEven : Even (ordUnit K x))
    (hrefUnit : IsValuationUnit K (reference : K))
    (hsum : quadraticDefect K z + quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : WithTop Nat)) :
    ∃ η : Kˣ,
      IsValuationUnit K (η : K) ∧
        quadraticDefect K (η * x) =
          quadraticDefect K reference ∧
        hilbertSymbol K (η * x) z = -1 := by
  rcases (beli2019Lemma82_i z reference).2 hsum with
    ⟨w, hwDefect, hwHilbert⟩
  have hrefNonzero : quadraticDefect K reference ≠ 0 :=
    quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
  have hwNonzero : quadraticDefect K w ≠ 0 := by
    rw [hwDefect]
    exact hrefNonzero
  rcases exists_valuationUnit_multiplier_same_defect_same_hilbert
      z x w hxEven hwNonzero with
    ⟨η, hηUnit, hηDefect, hηHilbert⟩
  refine ⟨η, hηUnit, hηDefect.trans hwDefect, ?_⟩
  calc
    hilbertSymbol K (η * x) z =
        hilbertSymbol K z (η * x) := hilbertSymbol_comm K _ _
    _ = hilbertSymbol K z w := hηHilbert
    _ = -1 := hwHilbert

end BONG

end Bong
