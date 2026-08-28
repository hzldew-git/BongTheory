/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Choice
import Bong.Bong.BinaryEndpointClass

/-!
# Complementary Hilbert choices

This file packages the local-field choice used in the ternary proof of
Beli (2019), Lemma 8.14.  A finite positive defect `d < 2e` has an odd
integral depth.  The complementary depth `2e - d` is therefore again in the
unit-defect spectrum, and Lemma 8.2(i) supplies a valuation-unit partner with
negative Hilbert symbol.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A positive finite defect below `2e` admits a valuation-unit Hilbert
partner whose defect is the complementary depth `2e - d`. -/
theorem exists_complementaryDefect_hilbert_neg
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    (z : Kˣ) (d : ℚ)
    (hzDefect : GoodBONG.defectOrder (K := K) z = (d : WithTop ℚ))
    (hdPos : 0 < d)
    (hdLt : d < 2 * (ramificationIndex K : ℚ)) :
    ∃ η : Kˣ,
      IsValuationUnit K (η : K) ∧
        GoodBONG.defectOrder (K := K) η =
          ((2 * (ramificationIndex K : ℚ) - d : ℚ) : WithTop ℚ) ∧
        hilbertSymbol K η z = -1 := by
  have hzNonzero : quadraticDefect K z ≠ 0 := by
    intro hzero
    unfold GoodBONG.defectOrder at hzDefect
    rw [hzero] at hzDefect
    have hdZero : d = 0 := by
      exact WithTop.coe_eq_coe.mp hzDefect.symm
    linarith
  rcases exists_valuationUnit_same_defect_same_hilbert
      (1 : Kˣ) z hzNonzero with
    ⟨u, huUnit, huDefect, _⟩
  have huDefectOrder : GoodBONG.defectOrder (K := K) u =
      (d : WithTop ℚ) := by
    calc
      GoodBONG.defectOrder (K := K) u =
          GoodBONG.defectOrder (K := K) z := by
        unfold GoodBONG.defectOrder
        rw [huDefect]
      _ = (d : WithTop ℚ) := hzDefect
  cases huQuadratic : quadraticDefect K u with
  | top =>
      unfold GoodBONG.defectOrder at huDefectOrder
      rw [huQuadratic] at huDefectOrder
      exact (WithTop.top_ne_coe huDefectOrder).elim
  | coe m =>
      have hmDefect : (m : ℚ) = d := by
        unfold GoodBONG.defectOrder at huDefectOrder
        rw [huQuadratic] at huDefectOrder
        exact WithTop.coe_eq_coe.mp huDefectOrder
      have hmLt : m < 2 * ramificationIndex K := by
        have hmLtQ : (m : ℚ) < ((2 * ramificationIndex K : Nat) : ℚ) := by
          push_cast
          exact hmDefect.trans_lt hdLt
        exact_mod_cast hmLtQ
      have huQuadraticLt : quadraticDefect K u <
          ((2 * ramificationIndex K : Nat) : WithTop Nat) := by
        rw [huQuadratic]
        exact WithTop.coe_lt_coe.mpr hmLt
      have hmOdd : Odd m := by
        simpa [huQuadratic] using
          quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
            (K := K) u huUnit huQuadraticLt
      have hdOdd : IsOddRationalInteger d := by
        refine ⟨(m : Int), ?_, ?_⟩
        · exact_mod_cast hmOdd
        · exact hmDefect.symm
      let complement : ℚ := 2 * (ramificationIndex K : ℚ) - d
      have hcomplementOdd : IsOddRationalInteger complement := by
        rcases hdOdd with ⟨k, hkOdd, hdk⟩
        rcases hkOdd with ⟨l, hl⟩
        refine ⟨2 * (ramificationIndex K : Int) - k, ?_, ?_⟩
        · refine ⟨(ramificationIndex K : Int) - l - 1, ?_⟩
          omega
        · dsimp only [complement]
          rw [hdk]
          push_cast
          ring
      have hcomplementNonnegative : 0 ≤ complement := by
        dsimp only [complement]
        linarith
      have hcomplementLt : complement <
          2 * (ramificationIndex K : ℚ) := by
        dsimp only [complement]
        linarith
      rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
          complement hcomplementOdd hcomplementNonnegative hcomplementLt with
        ⟨reference, hrefUnit, hrefDefect⟩
      have hsumDefectOrder :
          GoodBONG.defectOrder (K := K) z +
              GoodBONG.defectOrder (K := K) reference =
            (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
        rw [hzDefect, hrefDefect]
        dsimp only [complement]
        norm_cast
        push_cast
        ring
      have hsumQuadratic :=
        GoodBONG.quadraticDefect_add_eq_twoE_of_defectOrder_add_eq_twoE
          z reference hsumDefectOrder
      rcases (beli2019Lemma82_i z reference).2 hsumQuadratic.le with
        ⟨x, hxDefect, hxHilbert⟩
      have hxNonzero : quadraticDefect K x ≠ 0 := by
        intro hxZero
        have hrefZero : quadraticDefect K reference = 0 := by
          rw [← hxDefect, hxZero]
        unfold GoodBONG.defectOrder at hrefDefect
        rw [hrefZero] at hrefDefect
        have hcomplementZero : complement = 0 :=
          WithTop.coe_eq_coe.mp hrefDefect.symm
        exact (ne_of_gt hcomplementLt)
          (by dsimp only [complement] at hcomplementZero ⊢; linarith)
      rcases exists_valuationUnit_same_defect_same_hilbert
          z x hxNonzero with
        ⟨η, hηUnit, hηDefect, hηHilbert⟩
      refine ⟨η, hηUnit, ?_, ?_⟩
      · unfold GoodBONG.defectOrder
        rw [hηDefect, hxDefect, ← show GoodBONG.defectOrder (K := K)
          reference = (complement : WithTop ℚ) from hrefDefect]
        rfl
      · rw [hilbertSymbol_comm K η z, hηHilbert, hxHilbert]

/-- A zero defect has a valuation-unit Hilbert partner at the discriminant
endpoint `2e`. -/
theorem exists_twoEDefect_hilbert_neg_of_defect_zero
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    (z : Kˣ)
    (hzDefect : GoodBONG.defectOrder (K := K) z =
      (0 : WithTop ℚ)) :
    ∃ η : Kˣ,
      IsValuationUnit K (η : K) ∧
        GoodBONG.defectOrder (K := K) η =
          ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ∧
        hilbertSymbol K η z = -1 := by
  let reference : Kˣ := laws.discriminantUnit
  have hrefUnit : IsValuationUnit K (reference : K) := by
    exact laws.discriminant_isValuationUnit
  have hrefDefect : GoodBONG.defectOrder (K := K) reference =
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    dsimp only [reference]
    unfold GoodBONG.defectOrder
    rw [laws.discriminant_defect]
    norm_cast
  have hsumDefectOrder :
      GoodBONG.defectOrder (K := K) z +
          GoodBONG.defectOrder (K := K) reference =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hzDefect, hrefDefect]
    norm_cast
    simp
  have hsumQuadratic :=
    GoodBONG.quadraticDefect_add_eq_twoE_of_defectOrder_add_eq_twoE
      z reference hsumDefectOrder
  rcases (beli2019Lemma82_i z reference).2 hsumQuadratic.le with
    ⟨x, hxDefect, hxHilbert⟩
  have hrefNonzero : quadraticDefect K reference ≠ 0 :=
    quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
  have hxNonzero : quadraticDefect K x ≠ 0 := by
    rw [hxDefect]
    exact hrefNonzero
  rcases exists_valuationUnit_same_defect_same_hilbert
      z x hxNonzero with
    ⟨η, hηUnit, hηDefect, hηHilbert⟩
  refine ⟨η, hηUnit, ?_, ?_⟩
  · calc
      GoodBONG.defectOrder (K := K) η =
          GoodBONG.defectOrder (K := K) reference := by
        unfold GoodBONG.defectOrder
        rw [hηDefect, hxDefect]
      _ = ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
        hrefDefect
  · rw [hilbertSymbol_comm K η z, hηHilbert, hxHilbert]

/-- Uniform complementary Hilbert choice for every nonnegative finite defect
strictly below `2e`, including the zero-defect endpoint. -/
theorem exists_complementaryDefect_hilbert_neg_of_nonnegative
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    (z : Kˣ) (d : ℚ)
    (hzDefect : GoodBONG.defectOrder (K := K) z =
      (d : WithTop ℚ))
    (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : ℚ)) :
    ∃ η : Kˣ,
      IsValuationUnit K (η : K) ∧
        GoodBONG.defectOrder (K := K) η =
          ((2 * (ramificationIndex K : ℚ) - d : ℚ) : WithTop ℚ) ∧
        hilbertSymbol K η z = -1 := by
  by_cases hdZero : d = 0
  · subst d
    simpa using
      exists_twoEDefect_hilbert_neg_of_defect_zero (K := K) z hzDefect
  · have hdPos : 0 < d :=
      lt_of_le_of_ne hdNonnegative (Ne.symm hdZero)
    exact exists_complementaryDefect_hilbert_neg
      (K := K) z d hzDefect hdPos hdLt

end BONG

end Bong
