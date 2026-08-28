/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88ExceptionA

/-!
# Beli (2019), Lemma 8.8: sufficiency and the completed induction

This file assembles the strict binary branch, recursive tail replacement,
and the three critical exceptional-tail branches into the induction on the
rank of a good BONG.  It also closes the rank-two boundary case.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- In the strict recursive branch, the projected-tail alpha is itself
strictly below its half-gap. -/
theorem tailAlpha_lt_halfGap_of_global_strict
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (htail :
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
        b.adjacentDefect (0 : Fin (N + 2)))
    (hstrict : b.alphaValue (0 : Fin (N + 2)) <
      b.halfGapValue (0 : Fin (N + 2))) :
    b.tail.alphaValue (0 : Fin (N + 1)) <
      b.tail.halfGapValue (0 : Fin (N + 1)) := by
  have hle := b.tail.alphaValue_le_halfGapValue (0 : Fin (N + 1))
  apply lt_of_le_of_ne hle
  intro heq
  have hglobalTop :=
    b.alpha_zero_eq_orderGap_add_tailAlpha_of_tailAlpha_lt_adjacentDefect
      htail hstrict
  have hglobal : b.alphaValue (0 : Fin (N + 2)) =
      (b.orderGap (0 : Fin (N + 2)) : ℚ) +
        b.tail.alphaValue (0 : Fin (N + 1)) := by
    apply WithTop.coe_eq_coe.mp
    simpa only [WithTop.coe_add] using hglobalTop
  have hgood : b.order (0 : Fin (N + 3)) ≤
      b.order (2 : Fin (N + 3)) := by
    have hraw := b.good (0 : Fin (N + 3))
      (show (0 : Nat) + 2 < N + 3 by omega)
    convert hraw using 1 <;> congr 1
  have hgoodQ : (b.order (0 : Fin (N + 3)) : ℚ) ≤
      (b.order (2 : Fin (N + 3)) : ℚ) := by
    exact_mod_cast hgood
  unfold halfGapValue orderGap at heq hstrict hglobal
  simp only [b.order_goodTail] at heq
  change b.tail.alphaValue (0 : Fin (N + 1)) =
      ((b.order (2 : Fin (N + 3)) -
        b.order (1 : Fin (N + 3)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) at heq
  change b.alphaValue (0 : Fin (N + 2)) <
      ((b.order (1 : Fin (N + 3)) -
        b.order (0 : Fin (N + 3)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) at hstrict
  change b.alphaValue (0 : Fin (N + 2)) =
      (b.order (1 : Fin (N + 3)) -
        b.order (0 : Fin (N + 3)) : Int) +
        b.tail.alphaValue (0 : Fin (N + 1)) at hglobal
  push_cast at heq hstrict hglobal
  linarith [hgoodQ]

/-- At the half-gap, a valuation-unit representative of the first alpha
cannot form the exceptional unordered defect pair `{0, 2e}` with the first
adjacent product. -/
theorem not_zero_twoEDefectPair_of_halfGap_unit
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    (b : GoodBONG q L (N + 2))
    (reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hrefDefect : defectOrder (K := K) reference =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1))) :
    ¬IsZeroTwoEDefectPair (K := K)
      (b.adjacentProduct (0 : Fin (N + 1))) reference := by
  rintro (⟨hadjacentZero, hrefTwoE⟩ | ⟨_, hrefZero⟩)
  · have hreferenceOrder : defectOrder (K := K) reference =
        ((((2 * ramificationIndex K : Nat) : ℚ)) : WithTop ℚ) := by
      unfold defectOrder
      rw [hrefTwoE]
      norm_cast
    have halphaNat : b.alphaValue (0 : Fin (N + 1)) =
        ((2 * ramificationIndex K : Nat) : ℚ) := by
      apply WithTop.coe_eq_coe.mp
      exact hrefDefect.symm.trans hreferenceOrder
    have halpha : b.alphaValue (0 : Fin (N + 1)) =
        2 * (ramificationIndex K : ℚ) := by
      norm_num at halphaNat ⊢
      exact halphaNat
    have hadjacentOdd := odd_ordUnit_of_quadraticDefect_eq_zero
      (b.adjacentProduct (0 : Fin (N + 1))) hadjacentZero
    have hadjacentEven :=
      b.firstAdjacentOrder_even_of_halfGap_alpha_eq_twoE hhalf halpha
    exact (Int.not_even_iff_odd.mpr hadjacentOdd) hadjacentEven
  · exact quadraticDefect_ne_zero_of_isValuationUnit
      reference hrefUnit hrefZero

/-- The residue-cardinality-greater-than-two half-gap branch of the binary
argument, including the boundary defect sum `2e`. -/
theorem beli2019Lemma88_halfGap_binary_of_residueMore
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
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty b.Beli2019FirstValueTransform := by
  have hnotPair := b.not_zero_twoEDefectPair_of_halfGap_unit
    reference hrefUnit hrefDefect hhalf
  rcases beli2019Lemma82_ii_unit hresidueMore
      (b.adjacentProduct (0 : Fin (N + 1))) reference hrefUnit hnotPair with
    ⟨ε, hεUnit, hεDefectRaw, hεHilbert⟩
  have hεDefect : defectOrder (K := K) ε =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    exact (defectOrder_eq_of_quadraticDefect_eq ε reference
      hεDefectRaw).trans hrefDefect
  apply b.firstValueTransform_of_firstBinaryAlpha
    ε hεUnit hεDefect hbinary
  rw [hilbertSymbol_comm]
  exact hεHilbert

/-- In rank two the right prefix-alpha cap is terminal, so the bracketed
first defect is exactly the raw first adjacent defect. -/
theorem lemma88FirstCappedDefect_eq_adjacent_rankTwo
    (b : GoodBONG q L 2) :
    b.lemma88FirstCappedDefect =
      b.adjacentDefect (0 : Fin 1) := by
  rw [lemma88FirstCappedDefect, truncatedPrefixDefect]
  have hraw :
      defectOrder (K := K)
          ((-1) * b.prefixProduct 0 * b.prefixProduct 2) =
        b.adjacentDefect (0 : Fin 1) := by
    simpa using
      b.defectOrder_prefixPair_eq_adjacentDefect (0 : Fin 1)
  rw [hraw, b.prefixAlphaCap_zero]
  simp

/-- Rank-two sufficiency for Lemma 8.8(i), including the terminal form of
exception (b). -/
theorem beli2019Lemma88_rankTwo_sufficiency
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
    (b : GoodBONG q L 2)
    (hnotExceptional : ¬b.Beli2019Lemma88Exceptional) :
    Nonempty b.Beli2019FirstValueTransform := by
  have hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin 1) : WithTop ℚ) := by
    unfold firstBinaryAlpha
    exact b.binary_alpha_eq_min_candidates.symm
  by_cases hhalf : b.AttainsHalfGap (0 : Fin 1)
  · have hnotA : ¬b.Beli2019Lemma88ExceptionA := by
      intro hA
      exact hnotExceptional ⟨hhalf, Or.inl hA⟩
    have hrealized : IsValuationUnitDefect (K := K)
        (b.alphaValue (0 : Fin 1)) := by
      by_contra hnot
      exact hnotA hnot
    rcases hrealized with ⟨reference, hrefUnit, hrefDefect⟩
    obtain hresidueMore | hresidueTwo := Classical.em
      (HasResidueFieldMoreThanTwoElements (K := K))
    · exact b.beli2019Lemma88_halfGap_binary_of_residueMore
        reference hrefUnit hrefDefect hbinary hhalf hresidueMore
    · by_cases hadjacent : b.adjacentDefect (0 : Fin 1) =
          (b.lemma88ComplementaryDefect : WithTop ℚ)
      · have hcapped : b.lemma88FirstCappedDefect =
            (b.lemma88ComplementaryDefect : WithTop ℚ) :=
          b.lemma88FirstCappedDefect_eq_adjacent_rankTwo.trans hadjacent
        let B : b.Beli2019Lemma88ExceptionB := {
          residueTwo := hresidueTwo
          cappedDefect_eq := hcapped
          nextAlpha_strict := by
            intro hthree
            omega
        }
        exact (hnotExceptional
          ⟨hhalf, Or.inr (Or.inl ⟨B⟩)⟩).elim
      · exact b.beli2019Lemma88_halfGap_binary_of_adjacent_ne_complementary
          reference hrefUnit hrefDefect hbinary hhalf hadjacent
  · have hstrict : b.alphaValue (0 : Fin 1) <
        b.halfGapValue (0 : Fin 1) :=
      lt_of_le_of_ne (b.alphaValue_le_halfGapValue 0) hhalf
    exact b.beli2019Lemma88_strict_binary hbinary hstrict

/-- Sufficiency direction of Beli (2019), Lemma 8.8(i), proved by induction
on the excess rank over two. -/
theorem beli2019Lemma88_sufficiency
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [discriminant : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (hnotExceptional : ¬b.Beli2019Lemma88Exceptional) :
    Nonempty b.Beli2019FirstValueTransform := by
  induction N generalizing V with
  | zero =>
      exact b.beli2019Lemma88_rankTwo_sufficiency hnotExceptional
  | succ N ih =>
      by_cases hhalf : b.AttainsHalfGap (0 : Fin (N + 2))
      · have hbinary := b.firstBinaryAlpha_eq_alpha_of_halfGap hhalf
        have hnotA : ¬b.Beli2019Lemma88ExceptionA := by
          intro hA
          exact hnotExceptional ⟨hhalf, Or.inl hA⟩
        have hnotB : ¬Nonempty b.Beli2019Lemma88ExceptionB := by
          intro hB
          exact hnotExceptional ⟨hhalf, Or.inr (Or.inl hB)⟩
        have hnotC : ¬Nonempty b.Beli2019Lemma88ExceptionC := by
          intro hC
          exact hnotExceptional ⟨hhalf, Or.inr (Or.inr hC)⟩
        by_cases hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
            (b.lemma88ComplementaryDefect : WithTop ℚ)
        · obtain hresidueMore | hresidueTwo := Classical.em
            (HasResidueFieldMoreThanTwoElements (K := K))
          · have hrealized : IsValuationUnitDefect (K := K)
                (b.alphaValue (0 : Fin (N + 2))) := by
              by_contra hnot
              exact hnotA hnot
            rcases hrealized with ⟨reference, hrefUnit, hrefDefect⟩
            exact b.beli2019Lemma88_halfGap_binary_of_residueMore
              reference hrefUnit hrefDefect hbinary hhalf hresidueMore
          · have htailAlpha :=
              b.tailAlpha_zero_eq_complementary_of_not_exceptionB
                hhalf hresidueTwo hadjacent hnotB
            by_cases htailExceptional :
                b.tail.Beli2019Lemma88Exceptional
            · rcases htailExceptional.2 with
                Atail | Btail | Ctail
              · exact b.beli2019Lemma88_critical_of_tailExceptionA
                  hhalf hnotA htailAlpha Atail
              · rcases Btail with ⟨B⟩
                have hglobalC := b.tailExceptionB_implies_exceptionC
                  hadjacent htailAlpha htailExceptional B
                exact (hnotC hglobalC).elim
              · rcases Ctail with ⟨C⟩
                cases N with
                | zero =>
                    exact (not_lemma88ExceptionC_of_rank_two
                      b.tail ⟨C⟩).elim
                | succ M =>
                    exact b.beli2019Lemma88_critical_of_tailExceptionC
                      hhalf hnotA htailAlpha htailExceptional C
            · rcases ih b.tail htailExceptional with ⟨T⟩
              exact b.beli2019Lemma88_critical_of_tailTransform
                hhalf hresidueTwo hadjacent hnotA hnotB T
        · exact b.beli2019Lemma88_halfGap_binary_of_notExceptional
            hbinary hhalf hnotExceptional hadjacent
      · have hstrict : b.alphaValue (0 : Fin (N + 2)) <
            b.halfGapValue (0 : Fin (N + 2)) :=
          lt_of_le_of_ne (b.alphaValue_le_halfGapValue 0) hhalf
        by_cases hle : b.adjacentDefect (0 : Fin (N + 2)) ≤
            (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ)
        · exact b.beli2019Lemma88_strict_of_adjacentDefect_le_tailAlpha
            hle hstrict
        · have htail :
              (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
                b.adjacentDefect (0 : Fin (N + 2)) := lt_of_not_ge hle
          have htailStrict :=
            b.tailAlpha_lt_halfGap_of_global_strict htail hstrict
          have htailNotExceptional :
              ¬b.tail.Beli2019Lemma88Exceptional := by
            rintro ⟨htailHalf, _⟩
            exact (ne_of_lt htailStrict) htailHalf
          rcases ih b.tail htailNotExceptional with ⟨T⟩
          exact b.beli2019Lemma88_strict_tail_of_tailTransform
            htail hstrict T

/-- Beli (2019), Lemma 8.8(i), in its exact formalized form. -/
theorem beli2019Lemma88_i
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (b : GoodBONG q L (N + 2)) :
    b.Beli2019Lemma88Claim := by
  unfold Beli2019Lemma88Claim
  constructor
  · exact b.beli2019Lemma88_necessity
  · exact b.beli2019Lemma88_sufficiency

end BONG.GoodBONG

end Bong
