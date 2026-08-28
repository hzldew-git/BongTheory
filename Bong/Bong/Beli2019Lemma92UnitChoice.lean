/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92RankFiveRealization
import Bong.Bong.Beli2019Lemma88Choice

/-!
# Beli (2019), Lemma 9.2: the two auxiliary units

The rank-four and rank-five proofs use the same ternary calculation.  First
choose `ε` with the preceding alpha defect.  Because the final old adjacent
defect is strictly larger, `ε` times that adjacent product still has the
defect of `ε`.  Lemma 8.2 then chooses `η`, of the final alpha defect, with
the Hilbert sign needed to preserve the ternary Hasse invariant.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Strict defect-sum inequality permits either requested Hilbert sign while
keeping the second defect and choosing a valuation-unit representative. -/
theorem exists_valuationUnit_same_defect_hilbert_eq_of_defectOrder_add_lt_twoE
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    (a reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (s : ℤˣ)
    (hsum : GoodBONG.defectOrder (K := K) a +
        GoodBONG.defectOrder (K := K) reference <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    ∃ u : Kˣ,
      IsValuationUnit K (u : K) ∧
        quadraticDefect K u = quadraticDefect K reference ∧
        hilbertSymbol K a u = s := by
  rcases Int.units_eq_one_or s with hs | hs
  · rcases
        exists_valuationUnit_same_defect_hilbert_one_of_defectOrder_add_ne_twoE
          a reference hrefUnit (ne_of_lt hsum) with
      ⟨u, hu, huDefect, huHilbert⟩
    exact ⟨u, hu, huDefect, huHilbert.trans hs.symm⟩
  · have hraw :=
      quadraticDefect_add_lt_twoE_of_defectOrder_add_lt_twoE
        a reference hsum
    rcases (beli2019Lemma82_i a reference).2 hraw.le with
      ⟨x, hxDefect, hxHilbert⟩
    have hrefNonzero := quadraticDefect_ne_zero_of_isValuationUnit
      reference hrefUnit
    have hxNonzero : quadraticDefect K x ≠ 0 := by
      rw [hxDefect]
      exact hrefNonzero
    rcases exists_valuationUnit_same_defect_same_hilbert
        a x hxNonzero with ⟨u, hu, huDefect, huHilbert⟩
    exact ⟨u, hu, huDefect.trans hxDefect,
      (huHilbert.trans hxHilbert).trans hs.symm⟩

namespace GoodBONG

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The Hilbert sign prescribed in the printed proof is exactly sufficient
for the scaled ternary Hasse identity. -/
theorem ternaryScaled_adjacentHilbert_eq_of_choice
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hchoice :
      hilbertSymbol K (ε * a.adjacentProduct (1 : Fin 2)) η =
        hilbertSymbol K ε (a.adjacentProduct (0 : Fin 2))) :
    hilbertSymbol K
        (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
        (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
      hilbertSymbol K
        (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
        (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) := by
  have hfirst :
      -(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)) =
        η * a.adjacentProduct (0 : Fin 2) := by
    unfold adjacentProduct
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    simp
    ring
  have hsecond :
      -(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3)) =
        ε * a.adjacentProduct (1 : Fin 2) := by
    unfold adjacentProduct
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    simp
    ring
  rw [hfirst, hsecond]
  change
    hilbertSymbol K (η * a.adjacentProduct (0 : Fin 2))
        (ε * a.adjacentProduct (1 : Fin 2)) =
      hilbertSymbol K (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2))
  have hpair :
      hilbertSymbol K η (ε * a.adjacentProduct (1 : Fin 2)) =
        hilbertSymbol K (a.adjacentProduct (0 : Fin 2)) ε := by
    calc
      hilbertSymbol K η (ε * a.adjacentProduct (1 : Fin 2)) =
          hilbertSymbol K (ε * a.adjacentProduct (1 : Fin 2)) η :=
        hilbertSymbol_comm K _ _
      _ = hilbertSymbol K ε (a.adjacentProduct (0 : Fin 2)) := hchoice
      _ = hilbertSymbol K (a.adjacentProduct (0 : Fin 2)) ε :=
        hilbertSymbol_comm K _ _
  rw [hilbertSymbol_mul_left, hpair, hilbertSymbol_mul_right]
  rcases Int.units_eq_one_or
      (hilbertSymbol K (a.adjacentProduct (0 : Fin 2)) ε) with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- Reusable unit-choice certificate for the ternary tail common to both
low-rank branches of Lemma 9.2. -/
structure Lemma92TernaryUnitChoiceData
    (a : GoodBONG q L 3) (previousDepth finalDepth : ℚ) where
  epsilon : Kˣ
  eta : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  eta_isValuationUnit : IsValuationUnit K (eta : K)
  epsilon_defect : defectOrder (K := K) epsilon =
    (previousDepth : WithTop ℚ)
  eta_defect : defectOrder (K := K) eta =
    (finalDepth : WithTop ℚ)
  scaledLastAdjacent_defect :
    defectOrder (K := K)
        (epsilon * a.adjacentProduct (1 : Fin 2)) =
      (previousDepth : WithTop ℚ)
  hilbert_choice :
    hilbertSymbol K (epsilon * a.adjacentProduct (1 : Fin 2)) eta =
      hilbertSymbol K epsilon (a.adjacentProduct (0 : Fin 2))
  adjacent_hilbert :
    hilbertSymbol K
        (-(eta * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
        (-(epsilon * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
      hilbertSymbol K
        (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
        (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3)))

/-- Lemma 8.2 and the unit-defect spectrum construct the common ternary unit
certificate. -/
theorem exists_lemma92TernaryUnitChoiceData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L 3) (previousDepth finalDepth : ℚ)
    (hpreviousOdd : IsOddRationalInteger previousDepth)
    (hpreviousNonnegative : 0 ≤ previousDepth)
    (hpreviousLt :
      previousDepth < 2 * (ramificationIndex K : ℚ))
    (hfinalOdd : IsOddRationalInteger finalDepth)
    (hfinalNonnegative : 0 ≤ finalDepth)
    (hfinalLt : finalDepth < 2 * (ramificationIndex K : ℚ))
    (hlastAdjacent : (previousDepth : WithTop ℚ) <
      a.adjacentDefect (1 : Fin 2))
    (hsum : previousDepth + finalDepth <
      2 * (ramificationIndex K : ℚ)) :
    Nonempty (Lemma92TernaryUnitChoiceData a previousDepth finalDepth) := by
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      previousDepth hpreviousOdd hpreviousNonnegative hpreviousLt with
    ⟨ε, hεUnit, hεDefect⟩
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      finalDepth hfinalOdd hfinalNonnegative hfinalLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hεLt : defectOrder (K := K) ε <
      defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) := by
    rw [hεDefect]
    simpa only [adjacentDefect] using hlastAdjacent
  have hscaled :
      defectOrder (K := K) (ε * a.adjacentProduct (1 : Fin 2)) =
        (previousDepth : WithTop ℚ) := by
    rw [defectOrder_mul_eq_left_of_lt_right hεLt, hεDefect]
  have hsumTop :
      defectOrder (K := K) (ε * a.adjacentProduct (1 : Fin 2)) +
          defectOrder (K := K) reference <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hscaled, hrefDefect]
    norm_cast
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsum
  let requested := hilbertSymbol K ε (a.adjacentProduct (0 : Fin 2))
  rcases
      exists_valuationUnit_same_defect_hilbert_eq_of_defectOrder_add_lt_twoE
        (ε * a.adjacentProduct (1 : Fin 2)) reference hrefUnit
          requested hsumTop with
    ⟨η, hηUnit, hηRawDefect, hηHilbert⟩
  have hηDefect : defectOrder (K := K) η =
      (finalDepth : WithTop ℚ) :=
    (defectOrder_eq_of_quadraticDefect_eq η reference hηRawDefect).trans
      hrefDefect
  have hadjacent :=
    a.ternaryScaled_adjacentHilbert_eq_of_choice ε η hηHilbert
  exact ⟨{
    epsilon := ε
    eta := η
    epsilon_isValuationUnit := hεUnit
    eta_isValuationUnit := hηUnit
    epsilon_defect := hεDefect
    eta_defect := hηDefect
    scaledLastAdjacent_defect := hscaled
    hilbert_choice := hηHilbert
    adjacent_hilbert := hadjacent
  }⟩

end GoodBONG

end BONG

end Bong
