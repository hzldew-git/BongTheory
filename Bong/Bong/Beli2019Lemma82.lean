/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma81
import Bong.Bong.HilbertDefectChoice
import Bong.Dyadic.HilbertSymbol

/-!
# Beli (2019), Lemma 8.2

The lemma classifies which Hilbert-symbol sign can occur among square classes
of a prescribed quadratic defect.  Its genuinely local existence input is
separated below.  The residue-cardinality dichotomy, including the strict
exclusion at `d+d'=2e` over the two-element residue field, is derived from
Lemma 8.1 and multiplicativity of the Hilbert symbol.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [QuadraticDefectLaws K]
  [HilbertSymbolLaws K]
  [DyadicResidueDefectProductLaws K]
  [DyadicHilbertDefectChoiceLaws K]

/-- The exceptional unordered pair of prescribed defects in Lemma 8.2(ii).
-/
def IsZeroTwoEDefectPair (a b : Kˣ) : Prop :=
  (quadraticDefect K a = 0 ∧
      quadraticDefect K b =
        ((2 * ramificationIndex K : Nat) : ℕ∞)) ∨
    (quadraticDefect K a =
        ((2 * ramificationIndex K : Nat) : ℕ∞) ∧
      quadraticDefect K b = 0)

/-- A strict defect-sum inequality permits either Hilbert sign while keeping
the second defect fixed.  For the positive sign, multiply by a higher-defect
negative partner when the reference itself has negative sign. -/
private theorem exists_same_defect_hilbert_one_of_sum_lt
    (a reference : Kˣ)
    (h : quadraticDefect K a + quadraticDefect K reference <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ b : Kˣ,
      quadraticDefect K b = quadraticDefect K reference ∧
        hilbertSymbol K a b = 1 := by
  by_cases href : hilbertSymbol K a reference = 1
  · exact ⟨reference, rfl, href⟩
  · have hrefNeg : hilbertSymbol K a reference = -1 :=
      (Int.units_eq_one_or (hilbertSymbol K a reference)).resolve_left href
    rcases
        DyadicHilbertDefectChoiceLaws.exists_higher_defect_negative_of_sum_lt
          a reference h with
      ⟨c, hcDefect, hcNeg⟩
    refine ⟨reference * c, ?_, ?_⟩
    · exact quadraticDefect_mul_eq_left_of_lt_right (K := K) hcDefect
    · rw [hilbertSymbol_mul_right, hrefNeg, hcNeg]
      norm_num

/-- Lemma 8.2(i): a negative Hilbert partner of the prescribed defect exists
exactly when the two defects have sum at most `2e`. -/
theorem beli2019Lemma82_i (a reference : Kˣ) :
    (∃ b : Kˣ,
        quadraticDefect K b = quadraticDefect K reference ∧
          hilbertSymbol K a b = -1) ↔
      quadraticDefect K a + quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  constructor
  · rintro ⟨b, hbDefect, hbNeg⟩
    by_contra hnot
    have hgt : ((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K a + quadraticDefect K b := by
      rw [hbDefect]
      exact lt_of_not_ge hnot
    have hone := hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e
      (K := K) (a := a) (b := b) hgt
    exact (by norm_num : (1 : ℤˣ) ≠ -1) (hone.symm.trans hbNeg)
  · exact
      DyadicHilbertDefectChoiceLaws.exists_negative_same_defect_of_sum_le
        a reference

/-- At the boundary sum `2e`, neither prescribed defect is `0` or `2e`
unless the pair is the exceptional unordered pair. -/
private theorem boundary_reference_ne_zero_twoE
    (a reference : Kˣ)
    (hsum : quadraticDefect K a + quadraticDefect K reference =
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hnot : ¬IsZeroTwoEDefectPair (K := K) a reference) :
    quadraticDefect K reference ≠ 0 ∧
      quadraticDefect K reference ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  constructor
  · intro hrefZero
    apply hnot
    right
    refine ⟨?_, hrefZero⟩
    simpa [hrefZero] using hsum
  · intro hrefTwoE
    apply hnot
    left
    refine ⟨?_, hrefTwoE⟩
    let twoE : ℕ∞ := ((2 * ramificationIndex K : Nat) : ℕ∞)
    have htwoFinite : twoE ≠ ⊤ := WithTop.coe_ne_top
    have hcancel : twoE + quadraticDefect K a = twoE + 0 := by
      calc
        twoE + quadraticDefect K a =
            quadraticDefect K a + twoE := add_comm _ _
        _ = twoE := by simpa [twoE, hrefTwoE] using hsum
        _ = twoE + 0 := by simp
    exact WithTop.add_left_cancel htwoFinite hcancel

/-- Lemma 8.2(ii): over a residue field with more than two elements, a
positive Hilbert partner exists precisely away from the unordered pair
`{0,2e}`. -/
theorem beli2019Lemma82_ii
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a reference : Kˣ) :
    (∃ b : Kˣ,
        quadraticDefect K b = quadraticDefect K reference ∧
          hilbertSymbol K a b = 1) ↔
      ¬IsZeroTwoEDefectPair (K := K) a reference := by
  constructor
  · rintro ⟨b, hbDefect, hbOne⟩ hboundary
    have hbNeg :=
      DyadicHilbertDefectChoiceLaws.hilbert_eq_neg_one_of_zero_twoE
        a b (by simpa [IsZeroTwoEDefectPair, hbDefect] using hboundary)
    exact (by norm_num : (1 : ℤˣ) ≠ -1) (hbOne.symm.trans hbNeg)
  · intro hnot
    let twoE : ℕ∞ := ((2 * ramificationIndex K : Nat) : ℕ∞)
    rcases lt_trichotomy
        (quadraticDefect K a + quadraticDefect K reference) twoE with
      hlt | heq | hgt
    · exact exists_same_defect_hilbert_one_of_sum_lt a reference hlt
    · have href := boundary_reference_ne_zero_twoE a reference heq hnot
      rcases beli2019Lemma81_i hres reference href.1 href.2 with
        ⟨c, hcDefect, hproductDefect⟩
      by_cases hrefOne : hilbertSymbol K a reference = 1
      · exact ⟨reference, rfl, hrefOne⟩
      by_cases hcOne : hilbertSymbol K a c = 1
      · exact ⟨c, hcDefect, hcOne⟩
      have hrefNeg : hilbertSymbol K a reference = -1 :=
        (Int.units_eq_one_or
          (hilbertSymbol K a reference)).resolve_left hrefOne
      have hcNeg : hilbertSymbol K a c = -1 :=
        (Int.units_eq_one_or (hilbertSymbol K a c)).resolve_left hcOne
      refine ⟨reference * c, hproductDefect, ?_⟩
      rw [hilbertSymbol_mul_right, hrefNeg, hcNeg]
      norm_num
    · refine ⟨reference, rfl, ?_⟩
      exact hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e
        (K := K) hgt

/-- Lemma 8.2(iii): over the two-element residue field, a positive partner
of the prescribed defect exists exactly off the boundary `d+d'=2e`. -/
theorem beli2019Lemma82_iii
    (hres : ¬HasResidueFieldMoreThanTwoElements (K := K))
    (a reference : Kˣ) :
    (∃ b : Kˣ,
        quadraticDefect K b = quadraticDefect K reference ∧
          hilbertSymbol K a b = 1) ↔
      quadraticDefect K a + quadraticDefect K reference ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  constructor
  · rintro ⟨b, hbDefect, hbOne⟩ hsum
    have hle : quadraticDefect K a + quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := hsum.le
    rcases
        DyadicHilbertDefectChoiceLaws.exists_negative_same_defect_of_sum_le
          a reference hle with
      ⟨c, hcDefect, hcNeg⟩
    have hbFinite : quadraticDefect K b ≠ ⊤ := by
      intro hbTop
      have : quadraticDefect K a + quadraticDefect K reference = ⊤ := by
        rw [← hbDefect, hbTop]
        simp
      rw [this] at hsum
      exact WithTop.top_ne_coe hsum
    have hstrict : quadraticDefect K b < quadraticDefect K (b * c) :=
      beli2019Lemma81_ii_strict hres b c (hbDefect.trans hcDefect.symm)
        hbFinite
    have haFinite : quadraticDefect K a ≠ ⊤ := by
      intro haTop
      have : quadraticDefect K a + quadraticDefect K reference = ⊤ := by
        rw [haTop]
        simp
      rw [this] at hsum
      exact WithTop.top_ne_coe hsum
    have hsumStrict :
        ((2 * ramificationIndex K : Nat) : ℕ∞) <
          quadraticDefect K a + quadraticDefect K (b * c) := by
      calc
        ((2 * ramificationIndex K : Nat) : ℕ∞) =
            quadraticDefect K a + quadraticDefect K b := by
          rw [hbDefect]
          exact hsum.symm
        _ < quadraticDefect K a + quadraticDefect K (b * c) :=
          (ENat.add_lt_add_iff_left haFinite).2 hstrict
    have hproductOne := hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e
      (K := K) (a := a) (b := b * c) hsumStrict
    have hproductNeg : hilbertSymbol K a (b * c) = -1 := by
      rw [hilbertSymbol_mul_right, hbOne, hcNeg]
      norm_num
    exact (by norm_num : (1 : ℤˣ) ≠ -1)
      (hproductOne.symm.trans hproductNeg)
  · intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact exists_same_defect_hilbert_one_of_sum_lt a reference hlt
    · exact ⟨reference, rfl,
        hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e (K := K) hgt⟩

end BONG

end Bong
