/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma82Unit
import Bong.Bong.Beli2019Lemma88Tail
import Bong.Bong.Beli2019Lemma88Necessity
import Bong.Bong.Beli2009AlphaArithmetic

/-!
# Beli (2019), Lemma 8.8: numerical Hilbert choice

This file formalizes the nonexceptional numerical choice used before the
induction starts.  The only new local-field input is the familiar description
of the unit-defect spectrum: every nonnegative odd integral depth below `2e`
occurs as the quadratic defect of a valuation unit.

Everything after that input is proved here: strictness below the half-gap
forces the first alpha to have the required arithmetic shape, the first
binary defect sum is strictly below `2e`, Lemma 8.2 supplies a Hilbert-positive
unit of that defect, and the already verified binary replacement theorem
produces the required good BONG.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

/-- The interior part of the classical unit-defect spectrum of a dyadic
local field.  This is a field-level statement and contains no lattice or BONG
data. -/
class DyadicUnitDefectSpectrumLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  exists_unit_of_odd_rational_defect
      (d : ℚ) (hodd : IsOddRationalInteger d)
      (hnonnegative : 0 ≤ d)
      (hlt : d < 2 * (ramificationIndex K : ℚ)) :
      ∃ u : Kˣ,
        IsValuationUnit K (u : K) ∧
          GoodBONG.defectOrder (K := K) u = (d : WithTop ℚ)

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Strict comparison of embedded defect sums reflects to the underlying
extended-natural quadratic defects. -/
theorem quadraticDefect_add_lt_twoE_of_defectOrder_add_lt_twoE
    (a b : Kˣ)
    (h : GoodBONG.defectOrder (K := K) a +
        GoodBONG.defectOrder (K := K) b <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    quadraticDefect K a + quadraticDefect K b <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  cases ha : quadraticDefect K a with
  | top =>
      unfold GoodBONG.defectOrder at h
      rw [ha] at h
      change (⊤ : WithTop ℚ) + _ < _ at h
      exact (not_lt_of_ge le_top h).elim
  | coe m =>
      cases hb : quadraticDefect K b with
      | top =>
          unfold GoodBONG.defectOrder at h
          rw [hb] at h
          change _ + (⊤ : WithTop ℚ) < _ at h
          have htop : (⊤ : WithTop ℚ) <
              (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
            simpa only [add_top] using h
          exact (not_lt_of_ge le_top htop).elim
      | coe n =>
          have hmn : (m : ℚ) + (n : ℚ) <
              (2 * ramificationIndex K : Nat) := by
            unfold GoodBONG.defectOrder at h
            rw [ha, hb] at h
            change ((m : ℚ) : WithTop ℚ) + (n : ℚ) < _ at h
            norm_cast at h
            exact_mod_cast h
          change (m : ℕ∞) + (n : ℕ∞) <
            ((2 * ramificationIndex K : Nat) : ℕ∞)
          exact_mod_cast hmn

/-- A strict rational defect-order sum cannot be the exceptional unordered
pair `{0, 2e}` from Lemma 8.2(ii). -/
theorem not_zero_twoEDefectPair_of_defectOrder_add_lt_twoE
    [QuadraticDefectLaws K]
    (a reference : Kˣ)
    (h : GoodBONG.defectOrder (K := K) a +
        GoodBONG.defectOrder (K := K) reference <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    ¬IsZeroTwoEDefectPair (K := K) a reference := by
  have hraw := quadraticDefect_add_lt_twoE_of_defectOrder_add_lt_twoE
    a reference h
  rintro (hpair | hpair)
  · rcases hpair with ⟨ha, href⟩
    rw [ha, href] at hraw
    apply (lt_irrefl
      (((2 * ramificationIndex K : Nat) : ℕ∞)))
    simpa only [zero_add] using hraw
  · rcases hpair with ⟨ha, href⟩
    rw [ha, href] at hraw
    apply (lt_irrefl
      (((2 * ramificationIndex K : Nat) : ℕ∞)))
    simpa only [add_zero] using hraw

/-- Equality of an extended-natural defect sum with `2e` maps to equality of
the corresponding rational defect-order sum. -/
theorem defectOrder_add_eq_twoE_of_quadraticDefect_add_eq_twoE
    (a b : Kˣ)
    (hraw : quadraticDefect K a + quadraticDefect K b =
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    GoodBONG.defectOrder (K := K) a +
        GoodBONG.defectOrder (K := K) b =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  cases ha : quadraticDefect K a with
  | top =>
      rw [ha] at hraw
      have hfalse : (⊤ : ℕ∞) =
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        simpa only [top_add] using hraw
      exact (ENat.top_ne_coe _ hfalse).elim
  | coe m =>
      cases hb : quadraticDefect K b with
      | top =>
          rw [hb] at hraw
          have hfalse : (⊤ : ℕ∞) =
              ((2 * ramificationIndex K : Nat) : ℕ∞) := by
            simpa only [add_top] using hraw
          exact (ENat.top_ne_coe _ hfalse).elim
      | coe n =>
          have hmn : m + n = 2 * ramificationIndex K := by
            rw [ha, hb] at hraw
            exact_mod_cast hraw
          unfold GoodBONG.defectOrder
          rw [ha, hb]
          change ((m : ℚ) : WithTop ℚ) + (n : ℚ) = _
          norm_cast

/-- A nonboundary rational defect-order sum remains nonboundary before
embedding from `ℕ∞`. -/
theorem quadraticDefect_add_ne_twoE_of_defectOrder_add_ne_twoE
    (a b : Kˣ)
    (h : GoodBONG.defectOrder (K := K) a +
        GoodBONG.defectOrder (K := K) b ≠
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    quadraticDefect K a + quadraticDefect K b ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  intro hraw
  exact h (defectOrder_add_eq_twoE_of_quadraticDefect_add_eq_twoE
    a b hraw)

/-- A nonboundary defect-order sum rules out the exceptional unordered pair
`{0, 2e}`. -/
theorem not_zero_twoEDefectPair_of_defectOrder_add_ne_twoE
    (a reference : Kˣ)
    (h : GoodBONG.defectOrder (K := K) a +
        GoodBONG.defectOrder (K := K) reference ≠
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    ¬IsZeroTwoEDefectPair (K := K) a reference := by
  rintro (hpair | hpair)
  · rcases hpair with ⟨ha, href⟩
    apply h
    apply defectOrder_add_eq_twoE_of_quadraticDefect_add_eq_twoE
    rw [ha, href]
    simp
  · rcases hpair with ⟨ha, href⟩
    apply h
    apply defectOrder_add_eq_twoE_of_quadraticDefect_add_eq_twoE
    rw [ha, href]
    simp

/-- Unit-valued Hilbert-positive choice whenever the prescribed and fixed
defects do not have boundary sum `2e`.  Lemma 8.2(ii) handles residue degree
greater than one and Lemma 8.2(iii) handles residue degree one. -/
theorem exists_valuationUnit_same_defect_hilbert_one_of_defectOrder_add_ne_twoE
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    (a reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hsum : GoodBONG.defectOrder (K := K) a +
        GoodBONG.defectOrder (K := K) reference ≠
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    ∃ u : Kˣ,
      IsValuationUnit K (u : K) ∧
        quadraticDefect K u = quadraticDefect K reference ∧
        hilbertSymbol K a u = 1 := by
  obtain hres | hres := Classical.em
    (HasResidueFieldMoreThanTwoElements (K := K))
  · exact beli2019Lemma82_ii_unit hres a reference hrefUnit
      (not_zero_twoEDefectPair_of_defectOrder_add_ne_twoE
        a reference hsum)
  · exact beli2019Lemma82_iii_unit hres a reference hrefUnit
      (quadraticDefect_add_ne_twoE_of_defectOrder_add_ne_twoE
        a reference hsum)

namespace GoodBONG

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- Below the half-gap, Lemma 2.7(iv) and Corollary 2.8 show that the first
alpha is a nonnegative odd integral depth below `2e`; the unit-defect spectrum
therefore realizes it. -/
theorem exists_firstAlphaUnit_of_lt_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (b : GoodBONG q L (N + 2))
    (hstrict : b.alphaValue (0 : Fin (N + 1)) <
      b.halfGapValue (0 : Fin (N + 1))) :
    ∃ u : Kˣ,
      IsValuationUnit K (u : K) ∧
        defectOrder (K := K) u =
          (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
  let first : Fin (N + 1) := ⟨0, by omega⟩
  have hne : b.alphaValue first ≠ b.halfGapValue first :=
    ne_of_lt hstrict
  have hodd : IsOddRationalInteger (b.alphaValue first) :=
    b.beli2009Lemma27_iv first hne
  have hnonnegative : 0 ≤ b.alphaValue first :=
    (b.beli2009Lemma27_i first).1
  have hgaplt : b.orderGap first <
      2 * (ramificationIndex K : Int) := by
    by_contra hnot
    have hge : 2 * (ramificationIndex K : Int) ≤ b.orderGap first :=
      le_of_not_gt hnot
    exact hne (b.beli2009Lemma27_ii first hge)
  have halphalt : b.alphaValue first <
      2 * (ramificationIndex K : ℚ) :=
    (b.beli2009Corollary28_ii first).1.mpr hgaplt
  exact DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
    (b.alphaValue first) hodd hnonnegative halphalt

/-- If the global first alpha is already the alpha of the first binary
segment and is strictly below the half-gap, then its defect together with the
first adjacent defect has sum strictly below `2e`. -/
theorem firstAdjacent_defectOrder_add_alpha_lt_twoE_of_strict_binary
    (b : GoodBONG q L (N + 2))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hstrict : b.alphaValue (0 : Fin (N + 1)) <
      b.halfGapValue (0 : Fin (N + 1))) :
    defectOrder (K := K) (b.adjacentProduct (0 : Fin (N + 1))) +
        (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  have hstrictTop :
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
        b.halfGapCandidate (0 : Fin (N + 1)) := by
    rw [← b.coe_halfGapValue]
    exact_mod_cast hstrict
  have hleftlt :
      b.leftDefectCandidate (0 : Fin (N + 1)) (0 : Fin (N + 1)) <
        b.halfGapCandidate (0 : Fin (N + 1)) := by
    by_contra hnot
    have hhalfLe : b.halfGapCandidate (0 : Fin (N + 1)) ≤
        b.leftDefectCandidate (0 : Fin (N + 1)) (0 : Fin (N + 1)) :=
      le_of_not_gt hnot
    have hmin := hbinary
    unfold firstBinaryAlpha at hmin
    rw [min_eq_left hhalfLe] at hmin
    exact (ne_of_lt hstrictTop) hmin.symm
  have hleft :
      b.leftDefectCandidate (0 : Fin (N + 1)) (0 : Fin (N + 1)) =
        (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    have hmin := hbinary
    unfold firstBinaryAlpha at hmin
    rw [min_eq_right hleftlt.le] at hmin
    exact hmin
  cases hadjacent : b.adjacentDefect (0 : Fin (N + 1)) with
  | top =>
      unfold leftDefectCandidate at hleft
      rw [hadjacent] at hleft
      exact (WithTop.top_ne_coe hleft).elim
  | coe d =>
      have hleftTop :
          ((b.orderGap (0 : Fin (N + 1)) : ℚ) : WithTop ℚ) +
              (d : WithTop ℚ) =
            (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
        simpa only [leftDefectCandidate, orderGap, hadjacent] using hleft
      have hleftTop' :
          (((b.orderGap (0 : Fin (N + 1)) : ℚ) + d : ℚ) : WithTop ℚ) =
            (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
        rw [WithTop.coe_add]
        exact hleftTop
      have hleftQ :
          (b.orderGap (0 : Fin (N + 1)) : ℚ) + d =
            b.alphaValue (0 : Fin (N + 1)) := by
        exact WithTop.coe_eq_coe.mp hleftTop'
      have hsumQ : d + b.alphaValue (0 : Fin (N + 1)) <
          2 * (ramificationIndex K : ℚ) := by
        unfold orderGap at hleftQ
        unfold halfGapValue orderGap at hstrict
        push_cast at hstrict hleftQ
        rw [← hleftQ]
        linarith
      change b.adjacentDefect (0 : Fin (N + 1)) +
          (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) < _
      rw [hadjacent]
      exact_mod_cast hsumQ

/-- The complete strict binary-prefix branch of Lemma 8.8.  The residue-field
case split is discharged by the unit-valued forms of Lemma 8.2(ii)--(iii). -/
theorem beli2019Lemma88_strict_binary
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hstrict : b.alphaValue (0 : Fin (N + 1)) <
      b.halfGapValue (0 : Fin (N + 1))) :
    Nonempty b.Beli2019FirstValueTransform := by
  rcases b.exists_firstAlphaUnit_of_lt_halfGap hstrict with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hsum := b.firstAdjacent_defectOrder_add_alpha_lt_twoE_of_strict_binary
    hbinary hstrict
  have hsumReference :
      defectOrder (K := K) (b.adjacentProduct 0) +
          defectOrder (K := K) reference <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect]
    exact hsum
  have hnotPair := not_zero_twoEDefectPair_of_defectOrder_add_lt_twoE
    (b.adjacentProduct 0) reference hsumReference
  obtain hres | hres := Classical.em
    (HasResidueFieldMoreThanTwoElements (K := K))
  · rcases beli2019Lemma82_ii_unit hres (b.adjacentProduct 0) reference
        hrefUnit hnotPair with ⟨ε, hεUnit, hεDefectRaw, hεHilbert⟩
    have hεDefect : defectOrder (K := K) ε =
        (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
      exact (defectOrder_eq_of_quadraticDefect_eq ε reference
        hεDefectRaw).trans hrefDefect
    apply b.firstValueTransform_of_firstBinaryAlpha ε hεUnit hεDefect
      hbinary
    rw [hilbertSymbol_comm]
    exact hεHilbert
  · have hsumRaw := quadraticDefect_add_lt_twoE_of_defectOrder_add_lt_twoE
      (b.adjacentProduct 0) reference hsumReference
    have hsumNe : quadraticDefect K (b.adjacentProduct 0) +
        quadraticDefect K reference ≠
          ((2 * ramificationIndex K : Nat) : WithTop Nat) :=
      ne_of_lt hsumRaw
    rcases beli2019Lemma82_iii_unit hres (b.adjacentProduct 0) reference
        hrefUnit hsumNe with ⟨ε, hεUnit, hεDefectRaw, hεHilbert⟩
    have hεDefect : defectOrder (K := K) ε =
        (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
      exact (defectOrder_eq_of_quadraticDefect_eq ε reference
        hεDefectRaw).trans hrefDefect
    apply b.firstValueTransform_of_firstBinaryAlpha ε hεUnit hεDefect
      hbinary
    rw [hilbertSymbol_comm]
    exact hεHilbert

/-- Binary replacement from a realized unit defect whenever its sum with the
first adjacent defect is not the residue-two boundary `2e`. -/
theorem beli2019Lemma88_binary_of_unit_sum_ne_twoE
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hrefDefect : defectOrder (K := K) reference =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hsum : defectOrder (K := K) (b.adjacentProduct 0) +
        defectOrder (K := K) reference ≠
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    Nonempty b.Beli2019FirstValueTransform := by
  rcases
      exists_valuationUnit_same_defect_hilbert_one_of_defectOrder_add_ne_twoE
        (b.adjacentProduct 0) reference hrefUnit hsum with
    ⟨ε, hεUnit, hεDefectRaw, hεHilbert⟩
  have hεDefect : defectOrder (K := K) ε =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    exact (defectOrder_eq_of_quadraticDefect_eq ε reference
      hεDefectRaw).trans hrefDefect
  apply b.firstValueTransform_of_firstBinaryAlpha ε hεUnit hεDefect
    hbinary
  rw [hilbertSymbol_comm]
  exact hεHilbert

/-- At the half-gap, failure of the first adjacent defect to equal the
complementary value is exactly failure of the Hilbert-choice defect sum to be
`2e`. -/
theorem firstAdjacent_defectOrder_add_unitDefect_ne_twoE_of_halfGap
    (b : GoodBONG q L (N + 2))
    (reference : Kˣ)
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1)))
    (hrefDefect : defectOrder (K := K) reference =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 1)) ≠
      (b.lemma88ComplementaryDefect : WithTop ℚ)) :
    defectOrder (K := K) (b.adjacentProduct 0) +
        defectOrder (K := K) reference ≠
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  intro hsum
  apply hadjacent
  have hhalfTop :
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) =
        (b.halfGapValue (0 : Fin (N + 1)) : WithTop ℚ) :=
    congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf
  have hsum' :
      b.adjacentDefect (0 : Fin (N + 1)) +
          (b.halfGapValue (0 : Fin (N + 1)) : WithTop ℚ) =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    unfold adjacentDefect
    rw [← hhalfTop, ← hrefDefect]
    exact hsum
  have hcompTop :
      (b.lemma88ComplementaryDefect : WithTop ℚ) +
          (b.halfGapValue (0 : Fin (N + 1)) : WithTop ℚ) =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    exact_mod_cast b.lemma88ComplementaryDefect_add_halfGap
  apply WithTop.add_left_cancel WithTop.coe_ne_top
  calc
    (b.halfGapValue (0 : Fin (N + 1)) : WithTop ℚ) +
          b.adjacentDefect (0 : Fin (N + 1)) =
        b.adjacentDefect (0 : Fin (N + 1)) +
          (b.halfGapValue (0 : Fin (N + 1)) : WithTop ℚ) := add_comm _ _
    _ = (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := hsum'
    _ = (b.lemma88ComplementaryDefect : WithTop ℚ) +
          (b.halfGapValue (0 : Fin (N + 1)) : WithTop ℚ) := hcompTop.symm
    _ = (b.halfGapValue (0 : Fin (N + 1)) : WithTop ℚ) +
          (b.lemma88ComplementaryDefect : WithTop ℚ) := add_comm _ _

/-- The direct half-gap binary branch: a realized unit alpha and a
noncomplementary first adjacent defect give the desired transform. -/
theorem beli2019Lemma88_halfGap_binary_of_adjacent_ne_complementary
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hrefDefect : defectOrder (K := K) reference =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1)))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 1)) ≠
      (b.lemma88ComplementaryDefect : WithTop ℚ)) :
    Nonempty b.Beli2019FirstValueTransform := by
  apply b.beli2019Lemma88_binary_of_unit_sum_ne_twoE reference hrefUnit
    hrefDefect hbinary
  exact b.firstAdjacent_defectOrder_add_unitDefect_ne_twoE_of_halfGap
    reference hhalf hrefDefect hadjacent

/-- Exact nonexceptional form of the direct half-gap binary branch.  The
negation of exception (a) supplies the unit-defect witness. -/
theorem beli2019Lemma88_halfGap_binary_of_notExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1)))
    (hnotExceptional : ¬b.Beli2019Lemma88Exceptional)
    (hadjacent : b.adjacentDefect (0 : Fin (N + 1)) ≠
      (b.lemma88ComplementaryDefect : WithTop ℚ)) :
    Nonempty b.Beli2019FirstValueTransform := by
  have hrealized : IsValuationUnitDefect (K := K)
      (b.alphaValue (0 : Fin (N + 1))) := by
    by_contra hnot
    apply hnotExceptional
    exact ⟨hhalf, Or.inl hnot⟩
  rcases hrealized with ⟨reference, hrefUnit, hrefDefect⟩
  exact b.beli2019Lemma88_halfGap_binary_of_adjacent_ne_complementary
    reference hrefUnit hrefDefect hbinary hhalf hadjacent

end GoodBONG

end BONG

end Bong
