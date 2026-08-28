/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCutoffGeometry
import Bong.Bong.Beli2019SectionFiveDefectAssembly

/-!
# The complete defect calculation in Beli (2019), Section 5

This file closes condition 2.1(ii).  It treats the selected binary gap-two
endpoint by passing to the swapped reverse-dual calculation, proves the
converse endpoint reduction, and assembles a certificate at every boundary.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- The second coordinate of the selected binary component on the smaller
side has the complementary local order. -/
theorem selectedBinary_targetNext_order
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0) :
    b.order ⟨i.val, i.lt_large⟩ =
      2 * ordUnit K D.input.block.scaleGenerator -
        D.smallAlmostJordan.effectiveNormOrderAt
          D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) := by
  let I : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  change (x.indexEquiv I).1 = D.largeSelectedPosition at hposition
  change (x.indexEquiv I).2.val = 0 at hlocal
  have hxy := D.weakProfile_coordinates_eq hselected a b I
  have hsmallPosition : (y.indexEquiv I).1 =
      D.smallSelectedPosition := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hxy.1.symm
      _ = D.largeSelectedPosition := hposition
      _ = D.smallSelectedPosition := hselected.symm
  have hsmallLocal : (y.indexEquiv I).2.val = 0 :=
    hxy.2.symm.trans hlocal
  have hrank : finrank K
      (D.smallAlmostJordan.component (y.indexEquiv I).1).carrier = 2 := by
    rw [hsmallPosition, D.smallAlmostJordan_finrank_selected, hfin]
  have hlocalSucc : (y.indexEquiv I).2.val + 1 <
      finrank K
        (D.smallAlmostJordan.component (y.indexEquiv I).1).carrier := by
    have hbound := (y.indexEquiv I).2.isLt
    omega
  have hIVal : I.val = i.val - 1 := rfl
  have hIValSucc : I.val + 1 = i.val := by
    have := i.pos
    omega
  have hglobal : I.val + 1 < n + 2 := by
    rw [hIValSucc]
    exact i.lt_large
  have hraw := y.order_succ_eq_weakJordanExpectedOrder_of_local_succ
    I hglobal hlocalSucc
  have hscale := D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
    D.smallSelectedPosition
      (ordUnit K D.input.block.scaleGenerator)
  have hodd : ¬Even ((y.indexEquiv I).2.val + 1) := by
    rw [hsmallLocal]
    decide
  have hexpected : BONG.weakJordanExpectedOrder D.smallAlmostJordan
      (y.indexEquiv I).1
      ⟨(y.indexEquiv I).2.val + 1, hlocalSucc⟩ =
        2 * ordUnit K D.input.block.scaleGenerator -
          D.smallAlmostJordan.effectiveNormOrderAt
            D.smallSelectedPosition
            (ordUnit K D.input.block.scaleGenerator) := by
    change JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K
          (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      ((y.indexEquiv I).2.val + 1) = _
    simpa only [hsmallPosition,
      D.smallAlmostJordan_scaleGenerator_selected] using
      JordanProfileOrder.localOrder_odd_of_scale_le hscale hodd
  have hindex : (⟨I.val + 1, hglobal⟩ : Fin (n + 2)) =
      ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    exact hIValSucc
  calc
    b.order ⟨i.val, i.lt_large⟩ =
        b.toBONG.order ⟨I.val + 1, hglobal⟩ := by
      rw [hindex]
      rfl
    _ = BONG.weakJordanExpectedOrder D.smallAlmostJordan
        (y.indexEquiv I).1
        ⟨(y.indexEquiv I).2.val + 1, hlocalSucc⟩ := hraw
    _ = _ := hexpected

/-- A rank-two selected local-zero boundary is exactly the reduced cutoff. -/
theorem selectedBinary_boundary_eq_defectReducedCutoff
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0) :
    i.val = D.defectReducedCutoff := by
  let I : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  let x := D.largeWeakProfileWitness a
  change (x.indexEquiv I).1 = D.largeSelectedPosition at hposition
  change (x.indexEquiv I).2.val = 0 at hlocal
  have hindex := x.index_val_eq_componentStart_add_local I
  change I.val =
    (∑ p ∈ Finset.Iio (x.indexEquiv I).1,
      finrank K (D.largeAlmostJordan.component p).carrier) +
        (x.indexEquiv I).2.val at hindex
  have hsum :
      (∑ p ∈ Finset.Iio (x.indexEquiv I).1,
        finrank K (D.largeAlmostJordan.component p).carrier) =
          D.largeSelectedStart := by
    rw [hposition]
    rfl
  have hstart : I.val = D.largeSelectedStart := by
    calc
      I.val =
          (∑ p ∈ Finset.Iio (x.indexEquiv I).1,
            finrank K (D.largeAlmostJordan.component p).carrier) +
              (x.indexEquiv I).2.val := hindex
      _ = D.largeSelectedStart := by rw [hsum, hlocal, Nat.add_zero]
  have haligned := D.weakAligned_largeSelectedStart_eq_smallSelectedStart
    hselected
  change D.largeSelectedStart = D.smallSelectedStart at haligned
  change i.val = D.smallSelectedStart +
    finrank K (D.smallAlmostJordan.component
      D.smallSelectedPosition).carrier - 1
  rw [D.smallAlmostJordan_finrank_selected, hfin]
  have hIVal : I.val = i.val - 1 := rfl
  have hiStart : i.val - 1 = D.smallSelectedStart := by
    calc
      i.val - 1 = I.val := hIVal.symm
      _ = D.largeSelectedStart := hstart
      _ = D.smallSelectedStart := haligned
  have hipos := i.pos
  omega

/-- A two-step rise at the first selected binary coordinate forces equality
of the two second-coordinate orders. -/
theorem selectedBinary_next_orders_eq_of_current_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 2) :
    a.order ⟨i.val, i.lt_large⟩ = b.order ⟨i.val, i.lt_large⟩ := by
  let I : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  have horders := D.weakAligned_selected_current_orders
    hselected a b I hposition hlocal
  have hsource := D.selectedBinary_sourceNext_order
    hfin a i hposition hlocal
  have htarget := D.selectedBinary_targetNext_order
    hselected hfin a b i hposition hlocal
  have hscale : ordUnit K D.input.block.scaleGenerator =
      ordUnit K D.input.block.enlargedScaleGenerator + 1 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · omega
    · omega
  change b.order I = a.order I + 2 at hcurrent
  omega

/-- The complementary boundary of a selected binary gap-two endpoint lies
in the direct reduced range of every reverse-dual Lemma 5.1 datum. -/
theorem reverseDual_defectReducedRange_of_selectedBinary
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M))
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0) :
    E.DefectReducedRange i.reverse := by
  have hboundary := D.selectedBinary_boundary_eq_defectReducedCutoff
    hselected hfin a i hposition hlocal
  have hcover :=
    D.defectReducedCutoff_add_reverseDual_ge_rank_add_selected_sub_two E
  have hrank : n + 2 = finrank K V := a.toBONG.length_eq_finrank
  change i.reverse.val ≤ E.defectReducedCutoff
  rw [RepresentationIndex.reverse_val]
  have hfinInt : (finrank K D.input.block.component.carrier : Int) = 2 := by
    exact_mod_cast hfin
  omega

end Lattice.Beli2019Lemma51Data

namespace BONG.GoodBONG.Beli2019SectionFiveReverseDualData

variable {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- A certificate for the original inclusion transports to the
complementary boundary of the swapped reverse-dual inclusion. -/
theorem reverseCertificate_of_original
    [Beli2006AlphaLaws.{u, v} K]
    {a : BONG.GoodBONG q M (n + 1)}
    {b : BONG.GoodBONG q N (n + 1)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (D : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (i : RepresentationIndex (n + 1) (n + 1))
    (C : BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate
      D.sourceDual D.targetDual i.reverse := by
  apply BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.direct
  have hOriginal := C.discharge
  have hAlpha := a.representationAlphaValue_reverseDual_swap b
    D.targetDual D.sourceDual D.targetOrder D.sourceOrder
      D.truncatedPrefixDefect i
  have hComparison := D.truncatedPrefixDefect
    i.reverse.val i.reverse.val
      (Nat.le_of_lt i.reverse.lt_large)
      (Nat.le_of_lt i.reverse.lt_large) 1
  have hBoundary : n + 1 - i.reverse.val = i.val := by
    simp only [RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  rw [hBoundary] at hComparison
  calc
    (D.sourceDual.representationAlphaValue D.targetDual i.reverse :
        WithTop ℚ) =
        (a.representationAlphaValue b i : WithTop ℚ) :=
      congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hAlpha
    _ ≤ a.truncatedPrefixDefect b 1 i.val i.val := hOriginal
    _ = D.sourceDual.truncatedPrefixDefect D.targetDual
        1 i.reverse.val i.reverse.val := hComparison.symm

/-- At the complementary reverse-dual boundary of an original selected
binary gap-two endpoint, the two current dual orders are equal. -/
theorem currentOrders_eq_of_original_selectedBinary_gapTwo
    [BeliLemma47Laws.{u, v} K]
    {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (D : Lattice.Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 2) :
    R.sourceDual.order
        (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc =
      R.targetDual.order
        (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc := by
  let gDual : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc
  let next : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  change R.sourceDual.order gDual = R.targetDual.order gDual
  have hindex : Fin.rev gDual = next := by
    apply Fin.ext
    simp only [gDual, next, BONG.GoodBONG.representationAlphaIndex,
      Fin.val_castSucc, RepresentationIndex.reverse_val, Fin.rev]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have hnext := D.selectedBinary_next_orders_eq_of_current_add_two
    hselected hfin a b i hposition hlocal hcurrent
  have hsource := R.sourceOrder gDual
  have htarget := R.targetOrder gDual
  rw [hindex] at hsource htarget
  change a.order next = b.order next at hnext
  omega

/-- If the swapped reverse-dual calculation reaches its selected binary
gap-two endpoint, then the two original orders at the complementary
boundary are equal. -/
theorem originalCurrentOrders_eq_of_reverse_selectedBinary_gapTwo
    [BeliLemma47Laws.{u, v} K]
    {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hselected :
      R.lemma51.smallSelectedPosition = R.lemma51.largeSelectedPosition)
    (hfin : finrank K R.lemma51.input.block.component.carrier = 2)
    (hposition : ((R.lemma51.largeWeakProfileWitness R.sourceDual).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc).1 =
        R.lemma51.largeSelectedPosition)
    (hlocal : ((R.lemma51.largeWeakProfileWitness R.sourceDual).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc).2.val = 0)
    (hcurrent : R.targetDual.order
        (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc =
      R.sourceDual.order
        (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc + 2) :
    a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc := by
  let nextDual : Fin (n + 2) := ⟨i.reverse.val, i.reverse.lt_large⟩
  let current : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  have hindex : Fin.rev nextDual = current := by
    apply Fin.ext
    simp only [nextDual, current, BONG.GoodBONG.representationAlphaIndex,
      Fin.val_castSucc, RepresentationIndex.reverse_val, Fin.rev]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have hnext :=
    R.lemma51.selectedBinary_next_orders_eq_of_current_add_two
      hselected hfin R.sourceDual R.targetDual i.reverse
        hposition hlocal hcurrent
  have hsource := R.sourceOrder nextDual
  have htarget := R.targetOrder nextDual
  rw [hindex] at hsource htarget
  change R.sourceDual.order nextDual = R.targetDual.order nextDual at hnext
  change a.order current = b.order current
  omega

end BONG.GoodBONG.Beli2019SectionFiveReverseDualData

namespace Lattice.Beli2019Lemma51Data

/-- A selected binary endpoint in the swapped reverse-dual calculation has
its complementary original boundary in the direct reduced range. -/
theorem defectReducedRange_of_reverseDual_selectedBinary
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hselected :
      R.lemma51.smallSelectedPosition = R.lemma51.largeSelectedPosition)
    (hfin : finrank K R.lemma51.input.block.component.carrier = 2)
    (hposition : ((R.lemma51.largeWeakProfileWitness R.sourceDual).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc).1 =
        R.lemma51.largeSelectedPosition)
    (hlocal : ((R.lemma51.largeWeakProfileWitness R.sourceDual).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc).2.val = 0) :
    D.DefectReducedRange i := by
  have hboundary :=
    R.lemma51.selectedBinary_boundary_eq_defectReducedCutoff
      hselected hfin R.sourceDual i.reverse hposition hlocal
  have hcover :=
    D.defectReducedCutoff_add_reverseDual_ge_rank_add_selected_sub_two
      R.lemma51
  have hrank : n + 2 = finrank K V := a.toBONG.length_eq_finrank
  have hselectedRank := D.reverseDual_selectedRank R.lemma51
  have hfinD : finrank K D.input.block.component.carrier = 2 := by omega
  change i.val ≤ D.defectReducedCutoff
  have hreverse := i.reverse_val
  have hfinInt : (finrank K D.input.block.component.carrier : Int) = 2 := by
    exact_mod_cast hfinD
  have hpos := i.pos
  have hlt := i.lt_large
  omega

/-- Close the original selected-binary gap-two endpoint by applying the
direct calculation to the complementary reverse-dual boundary. -/
theorem selectedBinary_gapTwo_defectCertificate_via_reverseDual
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
    {n : Nat} {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 2) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  have hrange := D.reverseDual_defectReducedRange_of_selectedBinary
    R.lemma51 hselected hfin a i hposition hlocal
  have hequal :=
    R.currentOrders_eq_of_original_selectedBinary_gapTwo D hselected hfin
      i hposition hlocal hcurrent
  have Cdual := R.lemma51.defectCertificate_reduced
    R.sourceDual R.targetDual i.reverse hrange (by
      intro _hfinDual _hselectedDual _hpositionDual _hlocalDual htwoDual
      let gDual :=
        (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc
      change R.targetDual.order gDual =
        R.sourceDual.order gDual + 2 at htwoDual
      change R.sourceDual.order gDual = R.targetDual.order gDual at hequal
      omega)
  exact R.originalCertificate_of_reverse i Cdual

/-- The full direct reduced range, now including the Section 5.11
selected-binary endpoint. -/
theorem defectCertificate_reduced_complete
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
    {n : Nat} {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.DefectReducedRange i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  apply D.defectCertificate_reduced a b i hi
  intro hfin hselected hposition hlocal hcurrent
  exact D.selectedBinary_gapTwo_defectCertificate_via_reverseDual
    R i hfin hselected hposition hlocal hcurrent

/-- Close a selected-binary gap-two endpoint in the swapped reverse-dual
calculation by returning to the complementary original boundary. -/
theorem reverseDual_selectedBinary_gapTwo_defectCertificate_via_original
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
    {n : Nat} {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hfin : finrank K R.lemma51.input.block.component.carrier = 2)
    (hselected :
      R.lemma51.smallSelectedPosition = R.lemma51.largeSelectedPosition)
    (hposition : ((R.lemma51.largeWeakProfileWitness R.sourceDual).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc).1 =
        R.lemma51.largeSelectedPosition)
    (hlocal : ((R.lemma51.largeWeakProfileWitness R.sourceDual).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc).2.val = 0)
    (_hcurrent : R.targetDual.order
        (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc =
      R.sourceDual.order
        (BONG.GoodBONG.representationAlphaIndex i.reverse).castSucc + 2) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate
      R.sourceDual R.targetDual i.reverse := by
  have hrange := D.defectReducedRange_of_reverseDual_selectedBinary
    R i hselected hfin hposition hlocal
  have C := D.defectCertificate_reduced_complete R i hrange
  exact R.reverseCertificate_of_original i C

/-- The complete pointwise Section 5 defect certificate, obtained by the
direct reduced calculation or by the complementary reverse-dual one. -/
theorem defectCertificate_complete
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
    {n : Nat} {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (i : RepresentationIndex (n + 2) (n + 2)) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  rcases D.defectReducedRange_or_reverseRange i with hi | hreverse
  · exact D.defectCertificate_reduced_complete R i hi
  · have hdualRange :=
      D.defectReducedRange_reverseDual_of_reverseRange
        R.lemma51 i.reverse a.toBONG.length_eq_finrank hreverse
    have Cdual := R.lemma51.defectCertificate_reduced
      R.sourceDual R.targetDual i.reverse hdualRange (by
        intro hfin hselected hposition hlocal hcurrent
        exact D.reverseDual_selectedBinary_gapTwo_defectCertificate_via_original
          R i hfin hselected hposition hlocal hcurrent)
    exact R.originalCertificate_of_reverse i Cdual

/-- Condition 2.1(ii) of Beli 2019, with every Section 5 boundary supplied
by the direct/reverse-dual calculation. -/
theorem sectionFiveDefectData
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
    {n : Nat} {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion) :
    BONG.GoodBONG.Beli2019SectionFiveDefectData a b where
  certificate := D.defectCertificate_complete R

end Lattice.Beli2019Lemma51Data

end Bong
