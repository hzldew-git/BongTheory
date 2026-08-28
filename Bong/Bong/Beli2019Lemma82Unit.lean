/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma82
import Bong.Bong.Beli2009BinaryRemarks
import Bong.Bong.BeliLemma317

/-!
# Unit-valued refinement of Beli (2019), Lemma 8.2

Lemma 8.2 chooses a field square class of prescribed defect and Hilbert sign.
Lemma 8.8 needs a representative in `𝒪ˣ`.  Equality with the defect of a
valuation unit rules out odd valuation; dividing by a uniformizer square then
normalizes the chosen representative without changing either its defect or
its Hilbert pairing.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A valuation unit never has zero relative quadratic defect. -/
theorem quadraticDefect_ne_zero_of_isValuationUnit
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    quadraticDefect K u ≠ 0 := by
  by_cases htop : quadraticDefect K u = ⊤
  · rw [htop]
    exact WithTop.top_ne_zero
  · have hpos := quadraticDefect_toNat_pos_of_unit_of_ne_top
      u hu htop
    intro hzero
    rw [hzero] at hpos
    simp at hpos

/-- Relative quadratic defect zero is equivalent to the odd-valuation
square classes.  The reverse implication normalizes any hypothetical
even-order representative by a uniformizer square and contradicts the
nonzero defect of a valuation unit. -/
theorem odd_ordUnit_of_quadraticDefect_eq_zero
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
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
    have hu : IsValuationUnit K (u : K) :=
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
    exact (quadraticDefect_ne_zero_of_isValuationUnit u hu huDefect).elim
  · exact hodd

/-- A nonzero-defect square class has a valuation-unit representative, and
normalization preserves its Hilbert pairing with any fixed first argument.
-/
theorem exists_valuationUnit_same_defect_same_hilbert
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    (a x : Kˣ) (hx : quadraticDefect K x ≠ 0) :
    ∃ u : Kˣ,
      IsValuationUnit K (u : K) ∧
        quadraticDefect K u = quadraticDefect K x ∧
        hilbertSymbol K a u = hilbertSymbol K a x := by
  have heven : Even (ordUnit K x) := by
    rcases Int.even_or_odd (ordUnit K x) with heven | hodd
    · exact heven
    · exact (hx (quadraticDefect_eq_zero_of_odd_ordUnit x hodd)).elim
  rcases heven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let u : Kˣ := x / s ^ 2
  have hsOrder : ordUnit K s = k := by
    exact ordUnit_uniformizerPowerUnit (K := K) k
  have huOrder : ordUnit K u = 0 := by
    dsimp only [u]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder]
    omega
  have hu : IsValuationUnit K (u : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder
  have hfactor : u * s ^ 2 = x := by
    dsimp only [u]
    simp
  refine ⟨u, hu, ?_, ?_⟩
  · calc
      quadraticDefect K u = quadraticDefect K (u * s ^ 2) :=
        (quadraticDefect_mul_square K u s).symm
      _ = quadraticDefect K x := congrArg (quadraticDefect K) hfactor
  · calc
      hilbertSymbol K a u = hilbertSymbol K a (u * s ^ 2) :=
        (hilbertSymbol_mul_square_right (K := K) a u s).symm
      _ = hilbertSymbol K a x := congrArg (hilbertSymbol K a) hfactor

/-- Refine any positive-sign choice of the same defect as a valuation unit to
a positive-sign valuation-unit choice. -/
theorem exists_valuationUnit_same_defect_hilbert_one
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    (a reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hchoice : ∃ x : Kˣ,
      quadraticDefect K x = quadraticDefect K reference ∧
        hilbertSymbol K a x = 1) :
    ∃ u : Kˣ,
      IsValuationUnit K (u : K) ∧
        quadraticDefect K u = quadraticDefect K reference ∧
        hilbertSymbol K a u = 1 := by
  rcases hchoice with ⟨x, hxDefect, hxHilbert⟩
  have hrefNonzero := quadraticDefect_ne_zero_of_isValuationUnit
    reference hrefUnit
  have hxNonzero : quadraticDefect K x ≠ 0 := by
    rw [hxDefect]
    exact hrefNonzero
  rcases exists_valuationUnit_same_defect_same_hilbert a x hxNonzero with
    ⟨u, hu, huDefect, huHilbert⟩
  exact ⟨u, hu, huDefect.trans hxDefect,
    huHilbert.trans hxHilbert⟩

/-- Unit-valued form of Lemma 8.2(ii). -/
theorem beli2019Lemma82_ii_unit
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hnot : ¬IsZeroTwoEDefectPair (K := K) a reference) :
    ∃ u : Kˣ,
      IsValuationUnit K (u : K) ∧
        quadraticDefect K u = quadraticDefect K reference ∧
        hilbertSymbol K a u = 1 := by
  apply exists_valuationUnit_same_defect_hilbert_one a reference
    hrefUnit
  exact (beli2019Lemma82_ii hres a reference).2 hnot

/-- Unit-valued form of Lemma 8.2(iii). -/
theorem beli2019Lemma82_iii_unit
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    (hres : ¬HasResidueFieldMoreThanTwoElements (K := K))
    (a reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hsum : quadraticDefect K a + quadraticDefect K reference ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ u : Kˣ,
      IsValuationUnit K (u : K) ∧
        quadraticDefect K u = quadraticDefect K reference ∧
        hilbertSymbol K a u = 1 := by
  apply exists_valuationUnit_same_defect_hilbert_one a reference
    hrefUnit
  exact (beli2019Lemma82_iii hres a reference).2 hsum

/-- Equality of quadratic defects in the unit-valued refinements immediately
gives equality of the rationally embedded defect orders. -/
theorem defectOrder_eq_of_quadraticDefect_eq
    (a b : Kˣ) (h : quadraticDefect K a = quadraticDefect K b) :
    GoodBONG.defectOrder (K := K) a =
      GoodBONG.defectOrder (K := K) b := by
  unfold GoodBONG.defectOrder
  rw [h]

end BONG

end Bong
