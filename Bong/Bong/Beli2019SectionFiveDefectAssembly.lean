/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveWeakUnaryShift
import Bong.Bong.Beli2019SectionFiveUnaryProper
import Bong.Bong.Beli2019SectionFiveUnaryImproperApproximation
import Bong.Bong.Beli2019SectionFiveDual

/-!
# Direct-range assembly for Beli (2019), condition 2.1(ii)

This module combines the aligned and unary-transposition calculations on
the full direct reduced range.  The only exposed continuation is the
rank-two selected gap-two endpoint, which Section 5.11 explicitly transfers
to the swapped reverse-dual inclusion.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- When the selected weak components occupy the same position, the direct
reduced cutoff is exactly the literal Lemma 5.17 cutoff. -/
theorem lemma517Range_of_defectReducedRange_of_selectedPositions_eq
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.DefectReducedRange i) : D.Lemma517Range i := by
  have hstart := D.weakAligned_largeSelectedStart_eq_smallSelectedStart
    hselected
  change D.largeSelectedStart = D.smallSelectedStart at hstart
  change i.val ≤ D.smallSelectedStart +
    finrank K
      (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
    at hi
  change i.val ≤ D.largeSelectedStart +
    finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
  rw [D.smallAlmostJordan_finrank_selected] at hi
  rw [D.largeAlmostJordan_finrank_selected, hstart]
  exact hi

/-- In an aligned rank-one case the comparison coordinate is strictly
before the selected component throughout the reduced range. -/
theorem weakAligned_rankOne_alphaCoordinate_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i) :
    ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  have hiStart : i.val ≤ D.largeSelectedStart := by
    change i.val ≤ D.largeSelectedStart +
      finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
      at hi
    rw [D.largeAlmostJordan_finrank_selected, hfin] at hi
    exact hi
  have hgIndex : g.val < D.largeSelectedStart := by
    change i.val - 1 < D.largeSelectedStart
    have hipos := i.pos
    omega
  apply D.weakUnaryShift_component_before_of_index_lt_start a g.castSucc
  change i.val - 1 <
    ∑ p ∈ Finset.Iio D.largeSelectedPosition,
      finrank K (D.largeAlmostJordan.component p).carrier
  change i.val - 1 < D.largeSelectedStart at hgIndex
  simpa only [largeSelectedStart] using hgIndex

/-- Complete direct reduced-range certificate in the aligned rank-one
case. -/
theorem weakAligned_rankOne_defectCertificate_reduced
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.DefectReducedRange i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  have hi517 :=
    D.lemma517Range_of_defectReducedRange_of_selectedPositions_eq
      hselected i hi
  have hbefore := D.weakAligned_rankOne_alphaCoordinate_before_selected
    hfin a i hi517
  exact D.weakAligned_defectCertificate_before_selected
    hselected a b i hi517 hbefore

/-- Complete the aligned rank-two direct range, except for the single
selected gap-two branch explicitly sent to reverse duality in Section
5.11. -/
theorem weakAligned_rankTwo_defectCertificate_reduced
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.DefectReducedRange i)
    (gapTwo :
      ((D.largeWeakProfileWitness a).indexEquiv
          (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
          D.largeSelectedPosition →
        ((D.largeWeakProfileWitness a).indexEquiv
          (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0 →
        b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc =
          a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 2 →
        BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  have hi517 :=
    D.lemma517Range_of_defectReducedRange_of_selectedPositions_eq
      hselected i hi
  rcases D.weakAligned_reducedRange_coordinate hselected a i hi with
    hbefore | ⟨hposition, hlocal⟩
  · exact D.weakAligned_defectCertificate_before_selected
      hselected a b i hi517 hbefore
  · have hle : a.order g.castSucc ≤ b.order g.castSucc :=
      D.weakAligned_selected_order_le hselected a b g.castSucc hposition
    have horders := D.weakAligned_selected_current_orders
      hselected a b g.castSucc hposition hlocal
    have heLargeSmall := D.largeSelected_effectiveNormOrder_le_smallSelected
    have heSmallLarge :=
      D.smallSelected_effectiveNormOrder_le_largeSelected_add_two_of_rank_two
        hfin
    have hupp : b.order g.castSucc ≤ a.order g.castSucc + 2 := by
      rw [horders.1, horders.2]
      exact heSmallLarge
    have hcases : b.order g.castSucc = a.order g.castSucc ∨
        b.order g.castSucc = a.order g.castSucc + 1 ∨
        b.order g.castSucc = a.order g.castSucc + 2 := by
      omega
    rcases hcases with heq | hone | htwo
    · let localData := D.weakAligned_lemma513LocalData hselected a b
      have hentryEq : a.orderSequence.entryOrZero (i.val - 1) =
          b.orderSequence.entryOrZero (i.val - 1) := by
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (by have := i.lt_large; omega),
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (by have := i.lt_large; omega)]
        simp only [BONG.GoodBONG.orderSequence_at]
        have hindex :
            (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) =
              g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact heq.symm
      exact localData.equalCertificate a b D.smallLattice_le_large
        (D.lemma517Data_proved a b) i hi517 hentryEq
    · exact D.weakAligned_selectedBinary_oddCertificate
        hselected hfin a b i hi517 hposition hlocal hone
    · exact gapTwo hposition hlocal htwo

/-- Complete direct reduced-range certificate for a unary adjacent
transposition, including its proper and improper exceptional intervals. -/
theorem weakUnaryShift_defectCertificate_reduced
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.DefectReducedRange i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  by_cases hi517 : D.Lemma517Range i
  · exact D.weakUnaryDirect_defectCertificate_lemma517Range
      hfin i₀ hi₀ a b i hi517
  · rcases D.unaryShift_commonEffectiveNormOrder_cases hfin i₀ hi₀ with
      hproper | himproper
    · exact D.weakUnaryShift_proper_defectCertificate
        hfin i₀ hi₀ hproper a b i hi hi517
    · exact D.weakUnaryShift_improper_defectCertificate
        hfin i₀ hi₀ himproper a b i hi hi517

/-- Complete the direct reduced range in every selected-rank case, with the
single Section 5.11 binary gap-two endpoint exposed as an explicit handler
for reverse duality. -/
theorem defectCertificate_reduced
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.DefectReducedRange i)
    (gapTwo : ∀
      (hfin : finrank K D.input.block.component.carrier = 2)
      (hselected : D.smallSelectedPosition = D.largeSelectedPosition),
      ((D.largeWeakProfileWitness a).indexEquiv
          (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
          D.largeSelectedPosition →
        ((D.largeWeakProfileWitness a).indexEquiv
          (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0 →
        b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc =
          a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 2 →
        BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  rcases D.rank_one_or_two with hOne | hTwo
  · rcases D.selectedPositions_unary_alternative hOne with
      hselected | ⟨i₀, ⟨hi₀, _hadjacent⟩, _hunique⟩
    · exact D.weakAligned_rankOne_defectCertificate_reduced
        hselected hOne a b i hi
    · exact D.weakUnaryShift_defectCertificate_reduced
        hOne i₀ hi₀ a b i hi
  · have hselected := D.selectedPositions_eq_of_rank_two hTwo
    apply D.weakAligned_rankTwo_defectCertificate_reduced
      hselected hTwo a b i hi
    exact gapTwo hTwo hselected

end Lattice.Beli2019Lemma51Data

end Bong
