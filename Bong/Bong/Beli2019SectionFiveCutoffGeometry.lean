/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularDecompositionInvariants
import Bong.Bong.Beli2019SectionFiveReducedRange
import Bong.Bong.Beli2019Lemma516

/-!
# Intrinsic and reverse-dual cutoffs in Beli (2019), Section 5

The common-complement data of Lemma 5.1 is noncanonical.  This file proves
that its selected rank, selected scales, and reduced cutoff are nevertheless
intrinsic.  It then computes their transformation under swapped reverse
duality and proves that the original and dual reduced ranges cover every
equal-rank boundary.  Repeated modular scales are handled by the intrinsic
scale-rank multiplicity from `ModularDecompositionInvariants`.
-/

open scoped BigOperators

namespace Bong

open Dyadic Module

universe u v

namespace Lattice.Beli2019Lemma51Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- Intrinsic scale-rank difference between the smaller and larger
members of a Lemma 5.1 pair. -/
noncomputable def scaleRankDifference
    (D : Beli2019Lemma51Data q M N) (r : Int) : Int :=
  D.smallModularDecomposition.scaleRankMultiplicity r -
    D.largeModularDecomposition.scaleRankMultiplicity r

theorem scaleRankDifference_eq_selected
    (D : Beli2019Lemma51Data q M N) (r : Int) :
    D.scaleRankDifference r =
      (finrank K D.input.block.component.carrier : Int) *
          (if ordUnit K D.input.block.scaleGenerator = r then 1 else 0) -
        (finrank K D.input.block.component.carrier : Int) *
          (if ordUnit K D.input.block.enlargedScaleGenerator = r then 1 else 0) := by
  classical
  unfold scaleRankDifference
    Lattice.ModularDecomposition.scaleRankMultiplicity
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [D.smallModularDecomposition_scaleGenerator_zero,
    D.largeModularDecomposition_scaleGenerator_zero,
    D.smallModularDecomposition_scaleGenerator_succ,
    D.largeModularDecomposition_scaleGenerator_succ]
  have hsmallZero : finrank K
      (D.smallModularDecomposition.component 0).carrier =
        finrank K D.input.block.component.carrier := by
    rw [D.smallModularDecomposition_component_zero]
  have hlargeZero : finrank K
      (D.largeModularDecomposition.component 0).carrier =
        finrank K D.input.block.component.carrier := by
    rw [D.largeModularDecomposition_component_zero]
    rfl
  have hsmallSucc (x : Fin D.complementComponentCount) : finrank K
      (D.smallModularDecomposition.component x.succ).carrier =
        finrank K (D.complementStrictWeak.component x).carrier := by
    rw [D.smallModularDecomposition_component_succ,
      D.complement.finrank_liftNested]
  have hlargeSucc (x : Fin D.complementComponentCount) : finrank K
      (D.largeModularDecomposition.component x.succ).carrier =
        finrank K (D.complementStrictWeak.component x).carrier := by
    rw [D.largeModularDecomposition_component_succ,
      D.complement.finrank_liftNested]
  simp_rw [hsmallZero, hlargeZero, hsmallSucc, hlargeSucc]
  ring

/-- The scale-rank difference is intrinsic to the ordered inclusion, not
to the choice made in Lemma 5.1. -/
theorem scaleRankDifference_eq
    (D E : Beli2019Lemma51Data q M N) (r : Int) :
    D.scaleRankDifference r = E.scaleRankDifference r := by
  unfold scaleRankDifference
  rw [D.smallModularDecomposition.scaleRankMultiplicity_eq
      E.smallModularDecomposition r,
    D.largeModularDecomposition.scaleRankMultiplicity_eq
      E.largeModularDecomposition r]

/-- The scale of the smaller selected block is uniquely determined by the
index-uniformizer inclusion. -/
theorem selectedScaleOrder_eq
    (D E : Beli2019Lemma51Data q M N) :
    ordUnit K D.input.block.scaleGenerator =
      ordUnit K E.input.block.scaleGenerator := by
  have hdelta := D.scaleRankDifference_eq E
    (ordUnit K D.input.block.scaleGenerator)
  rw [D.scaleRankDifference_eq_selected,
    E.scaleRankDifference_eq_selected] at hdelta
  have hDne : ordUnit K D.input.block.enlargedScaleGenerator ≠
      ordUnit K D.input.block.scaleGenerator := by
    exact ne_of_lt D.enlargedScaleOrder_lt_smallScaleOrder
  have hDpos : 0 < finrank K D.input.block.component.carrier := by
    rcases D.rank_one_or_two with h | h <;> omega
  have hEpos : 0 < finrank K E.input.block.component.carrier := by
    rcases E.rank_one_or_two with h | h <;> omega
  by_contra hsmall
  have hsmall' : ordUnit K E.input.block.scaleGenerator ≠
      ordUnit K D.input.block.scaleGenerator := Ne.symm hsmall
  by_cases henlarged :
      ordUnit K E.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator
  · simp [hDne, hsmall', henlarged] at hdelta
    omega
  · simp [hDne, hsmall', henlarged] at hdelta
    omega

/-- The rank of the selected unary-or-binary block is likewise intrinsic. -/
theorem selectedRank_eq
    (D E : Beli2019Lemma51Data q M N) :
    finrank K D.input.block.component.carrier =
      finrank K E.input.block.component.carrier := by
  have hscale := D.selectedScaleOrder_eq E
  have hdelta := D.scaleRankDifference_eq E
    (ordUnit K D.input.block.scaleGenerator)
  rw [D.scaleRankDifference_eq_selected,
    E.scaleRankDifference_eq_selected] at hdelta
  have hDne : ordUnit K D.input.block.enlargedScaleGenerator ≠
      ordUnit K D.input.block.scaleGenerator := by
    exact ne_of_lt D.enlargedScaleOrder_lt_smallScaleOrder
  have hEne : ordUnit K E.input.block.enlargedScaleGenerator ≠
      ordUnit K D.input.block.scaleGenerator := by
    intro h
    have hlt := E.enlargedScaleOrder_lt_smallScaleOrder
    rw [h, ← hscale] at hlt
    exact (lt_irrefl _ hlt).elim
  simp [hDne, hscale.symm, hEne] at hdelta
  exact_mod_cast hdelta

/-- The enlarged selected scale is determined once the selected rank and
smaller selected scale are fixed. -/
theorem enlargedSelectedScaleOrder_eq
    (D E : Beli2019Lemma51Data q M N) :
    ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K E.input.block.enlargedScaleGenerator := by
  have hrank := D.selectedRank_eq E
  have hscale := D.selectedScaleOrder_eq E
  rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hDone | hDtwo
  · rcases E.input.block.componentRank_and_enlargedScaleOrder with
        hEone | hEtwo
    · omega
    · omega
  · rcases E.input.block.componentRank_and_enlargedScaleOrder with
        hEone | hEtwo
    · omega
    · omega

/-- The coordinates preceding the selected smaller block are exactly the
common components of strictly smaller scale. -/
noncomputable def smallPrefixCommonEquiv
    (D : Beli2019Lemma51Data q M N) :
    {p : Fin (D.complementComponentCount + 1) //
        p < D.smallSelectedPosition} ≃
      {i : Fin D.complementComponentCount //
        ordUnit K (D.complementStrictWeak.scaleGenerator i) <
          ordUnit K D.input.block.scaleGenerator} where
  toFun p := by
    let z : {p : Fin (D.complementComponentCount + 1) //
        p ≠ D.smallSelectedPosition} := ⟨p.1, ne_of_lt p.2⟩
    let i : Fin D.complementComponentCount :=
      D.smallCommonPositionOrderIso.symm z
    have hposition : D.smallCommonPosition i = p.1 := by
      have h := congrArg Subtype.val
        (D.smallCommonPositionOrderIso.apply_symm_apply z)
      simpa only [smallCommonPositionOrderIso_apply, z, i] using h
    refine ⟨i, ?_⟩
    apply (D.smallCommon_key_lt_selected_iff i).mp
    apply (ModularDecomposition.SortedReindex.oldPosition_lt_iff
      D.smallModularDecomposition D.smallSort i.succ 0).mp
    change D.smallCommonPosition i < D.smallSelectedPosition
    rw [hposition]
    exact p.2
  invFun i := ⟨D.smallCommonPosition i.1, by
    apply (ModularDecomposition.SortedReindex.oldPosition_lt_iff
      D.smallModularDecomposition D.smallSort i.1.succ 0).mpr
    exact (D.smallCommon_key_lt_selected_iff i.1).mpr i.2⟩
  left_inv p := by
    apply Subtype.ext
    let z : {p : Fin (D.complementComponentCount + 1) //
        p ≠ D.smallSelectedPosition} := ⟨p.1, ne_of_lt p.2⟩
    have h := congrArg Subtype.val
      (D.smallCommonPositionOrderIso.apply_symm_apply z)
    simpa only [smallCommonPositionOrderIso_apply, z] using h
  right_inv i := by
    apply Subtype.ext
    let z : {p : Fin (D.complementComponentCount + 1) //
        p ≠ D.smallSelectedPosition} :=
      ⟨D.smallCommonPosition i.1,
        (D.smallSelectedPosition_ne_common i.1).symm⟩
    have hz : z = D.smallCommonPositionOrderIso i.1 := by
      apply Subtype.ext
      rfl
    have h := D.smallCommonPositionOrderIso.symm_apply_apply i.1
    simpa only [z, hz] using h

@[simp]
theorem smallPrefixCommonEquiv_symm_apply
    (D : Beli2019Lemma51Data q M N)
    (i : {i : Fin D.complementComponentCount //
      ordUnit K (D.complementStrictWeak.scaleGenerator i) <
        ordUnit K D.input.block.scaleGenerator}) :
    (D.smallPrefixCommonEquiv.symm i).1 = D.smallCommonPosition i.1 := by
  rfl

/-- The smaller selected start is the rank of all common components below
the selected scale. -/
theorem smallSelectedStart_eq_sum_common_lt
    (D : Beli2019Lemma51Data q M N) :
    D.smallSelectedStart =
      ∑ i ∈ (Finset.univ : Finset (Fin D.complementComponentCount)).filter
          (fun i ↦ ordUnit K (D.complementStrictWeak.scaleGenerator i) <
            ordUnit K D.input.block.scaleGenerator),
        finrank K (D.complementStrictWeak.component i).carrier := by
  classical
  change (∑ p ∈ Finset.Iio D.smallSelectedPosition,
      finrank K (D.smallAlmostJordan.component p).carrier) = _
  rw [Finset.sum_subtype (Finset.Iio D.smallSelectedPosition) (by
    intro p
    simp only [Finset.mem_Iio]
    rfl) (fun p ↦ finrank K (D.smallAlmostJordan.component p).carrier)]
  rw [Finset.sum_subtype (p := fun i ↦
      ordUnit K (D.complementStrictWeak.scaleGenerator i) <
        ordUnit K D.input.block.scaleGenerator)
    ((Finset.univ : Finset (Fin D.complementComponentCount)).filter
      (fun i ↦ ordUnit K (D.complementStrictWeak.scaleGenerator i) <
        ordUnit K D.input.block.scaleGenerator)) (by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun i ↦ finrank K
        (D.complementStrictWeak.component i).carrier)]
  symm
  apply Fintype.sum_equiv D.smallPrefixCommonEquiv.symm
  intro i
  rw [D.smallPrefixCommonEquiv_symm_apply,
    D.smallAlmostJordan_finrank_common]

/-- In intrinsic form, the smaller selected start is the total modular
rank strictly below its selected scale. -/
theorem intCast_smallSelectedStart_eq_scaleRankBelow
    (D : Beli2019Lemma51Data q M N) :
    (D.smallSelectedStart : Int) =
      D.smallModularDecomposition.scaleRankBelow
        (ordUnit K D.input.block.scaleGenerator) := by
  classical
  rw [D.smallSelectedStart_eq_sum_common_lt]
  unfold ModularDecomposition.scaleRankBelow
  rw [Fin.sum_univ_succ]
  simp only [D.smallModularDecomposition_scaleGenerator_zero,
    D.smallModularDecomposition_scaleGenerator_succ]
  have hsmallSucc (x : Fin D.complementComponentCount) : finrank K
      (D.smallModularDecomposition.component x.succ).carrier =
        finrank K (D.complementStrictWeak.component x).carrier := by
    rw [D.smallModularDecomposition_component_succ,
      D.complement.finrank_liftNested]
  simp_rw [hsmallSucc]
  simp only [lt_self_iff_false, if_false, mul_zero, zero_add]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hscale : ordUnit K (D.complementStrictWeak.scaleGenerator i) <
      ordUnit K D.input.block.scaleGenerator <;> simp [hscale]

/-- Consequently the reduced defect cutoff is intrinsic to the inclusion
and does not depend on the chosen Lemma 5.1 data. -/
theorem defectReducedCutoff_eq
    (D E : Beli2019Lemma51Data q M N) :
    D.defectReducedCutoff = E.defectReducedCutoff := by
  have hstartD := D.intCast_smallSelectedStart_eq_scaleRankBelow
  have hstartE := E.intCast_smallSelectedStart_eq_scaleRankBelow
  have hscale := D.selectedScaleOrder_eq E
  have hbelow := D.smallModularDecomposition.scaleRankBelow_eq
    E.smallModularDecomposition
      (ordUnit K D.input.block.scaleGenerator)
  have hrank := D.selectedRank_eq E
  change D.smallSelectedStart +
      finrank K (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1 =
    E.smallSelectedStart +
      finrank K (E.smallAlmostJordan.component E.smallSelectedPosition).carrier - 1
  rw [D.smallAlmostJordan_finrank_selected,
    E.smallAlmostJordan_finrank_selected]
  have hstart : D.smallSelectedStart = E.smallSelectedStart := by
    exact_mod_cast hstartD.trans (hbelow.trans (hscale ▸ hstartE.symm))
  omega

/-! ## Reverse-dual selected parameters -/

/-- The scale-rank difference for the swapped reverse-dual inclusion is
the negative reflected difference of the original inclusion. -/
theorem reverseDual_scaleRankDifference
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M))
    (r : Int) :
    E.scaleRankDifference r = -D.scaleRankDifference (-r) := by
  unfold scaleRankDifference
  rw [E.smallModularDecomposition.scaleRankMultiplicity_eq
      D.largeModularDecomposition.reverseDual r,
    E.largeModularDecomposition.scaleRankMultiplicity_eq
      D.smallModularDecomposition.reverseDual r,
    D.largeModularDecomposition.reverseDual_scaleRankMultiplicity,
    D.smallModularDecomposition.reverseDual_scaleRankMultiplicity]
  ring

/-- The selected smaller scale in the reverse-dual Lemma 5.1 data is the
negative of the original enlarged selected scale. -/
theorem reverseDual_selectedScaleOrder
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M)) :
    ordUnit K E.input.block.scaleGenerator =
      -ordUnit K D.input.block.enlargedScaleGenerator := by
  let r := -ordUnit K D.input.block.enlargedScaleGenerator
  have hdelta := D.reverseDual_scaleRankDifference E r
  rw [E.scaleRankDifference_eq_selected,
    D.scaleRankDifference_eq_selected] at hdelta
  have hDne : ordUnit K D.input.block.scaleGenerator ≠
      ordUnit K D.input.block.enlargedScaleGenerator :=
    ne_of_gt D.enlargedScaleOrder_lt_smallScaleOrder
  have hDpos : 0 < finrank K D.input.block.component.carrier := by
    rcases D.rank_one_or_two with h | h <;> omega
  have hEpos : 0 < finrank K E.input.block.component.carrier := by
    rcases E.rank_one_or_two with h | h <;> omega
  have hdelta' :
      (finrank K E.input.block.component.carrier : Int) *
          (if ordUnit K E.input.block.scaleGenerator = r then 1 else 0) -
        (finrank K E.input.block.component.carrier : Int) *
          (if ordUnit K E.input.block.enlargedScaleGenerator = r then 1 else 0) =
        (finrank K D.input.block.component.carrier : Int) := by
    simpa [r, hDne] using hdelta
  by_contra hsmall
  by_cases henlarged :
      ordUnit K E.input.block.enlargedScaleGenerator = r
  · simp [henlarged] at hdelta'
    omega
  · simp [henlarged] at hdelta'
    omega

/-- Reverse duality preserves the selected unary-or-binary rank. -/
theorem reverseDual_selectedRank
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M)) :
    finrank K E.input.block.component.carrier =
      finrank K D.input.block.component.carrier := by
  let r := -ordUnit K D.input.block.enlargedScaleGenerator
  have hscale := D.reverseDual_selectedScaleOrder E
  have hdelta := D.reverseDual_scaleRankDifference E r
  rw [E.scaleRankDifference_eq_selected,
    D.scaleRankDifference_eq_selected] at hdelta
  have hDne : ordUnit K D.input.block.scaleGenerator ≠
      ordUnit K D.input.block.enlargedScaleGenerator :=
    ne_of_gt D.enlargedScaleOrder_lt_smallScaleOrder
  have hEne : ordUnit K E.input.block.enlargedScaleGenerator ≠ r := by
    intro h
    have hlt := E.enlargedScaleOrder_lt_smallScaleOrder
    rw [h, hscale] at hlt
    exact (lt_irrefl _ hlt).elim
  have hdelta' :
      (finrank K E.input.block.component.carrier : Int) =
        (finrank K D.input.block.component.carrier : Int) := by
    simpa [r, hscale, hEne, hDne] using hdelta
  exact_mod_cast hdelta'

/-- The enlarged selected scale in the reverse-dual data is the negative
of the original smaller selected scale. -/
theorem reverseDual_enlargedSelectedScaleOrder
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M)) :
    ordUnit K E.input.block.enlargedScaleGenerator =
      -ordUnit K D.input.block.scaleGenerator := by
  have hscale := D.reverseDual_selectedScaleOrder E
  have hrank := D.reverseDual_selectedRank E
  rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hDone | hDtwo
  · rcases E.input.block.componentRank_and_enlargedScaleOrder with
        hEone | hEtwo
    · omega
    · omega
  · rcases E.input.block.componentRank_and_enlargedScaleOrder with
        hEone | hEtwo
    · omega
    · omega

/-- Up to the selected rank, the large-side rank below the successor of
its selected scale is bounded by the smaller-side rank below its selected
scale.  This is the sole numerical estimate needed for dual cutoff cover. -/
theorem largeScaleRankBelow_le_small_add_selectedRank
    (D : Beli2019Lemma51Data q M N) :
    D.largeModularDecomposition.scaleRankBelow
        (ordUnit K D.input.block.enlargedScaleGenerator + 1) ≤
      D.smallModularDecomposition.scaleRankBelow
          (ordUnit K D.input.block.scaleGenerator) +
        finrank K D.input.block.component.carrier := by
  classical
  have hthreshold :
      ordUnit K D.input.block.enlargedScaleGenerator + 1 ≤
        ordUnit K D.input.block.scaleGenerator := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo <;> omega
  unfold ModularDecomposition.scaleRankBelow
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [D.largeModularDecomposition_scaleGenerator_zero,
    D.smallModularDecomposition_scaleGenerator_zero,
    D.largeModularDecomposition_scaleGenerator_succ,
    D.smallModularDecomposition_scaleGenerator_succ]
  have hlargeZero : finrank K
      (D.largeModularDecomposition.component 0).carrier =
        finrank K D.input.block.component.carrier := by
    rw [D.largeModularDecomposition_component_zero]
    rfl
  have hsmallZero : finrank K
      (D.smallModularDecomposition.component 0).carrier =
        finrank K D.input.block.component.carrier := by
    rw [D.smallModularDecomposition_component_zero]
  have hlargeSucc (x : Fin D.complementComponentCount) : finrank K
      (D.largeModularDecomposition.component x.succ).carrier =
        finrank K (D.complementStrictWeak.component x).carrier := by
    rw [D.largeModularDecomposition_component_succ,
      D.complement.finrank_liftNested]
  have hsmallSucc (x : Fin D.complementComponentCount) : finrank K
      (D.smallModularDecomposition.component x.succ).carrier =
        finrank K (D.complementStrictWeak.component x).carrier := by
    rw [D.smallModularDecomposition_component_succ,
      D.complement.finrank_liftNested]
  simp_rw [hlargeZero, hsmallZero, hlargeSucc, hsmallSucc]
  have hselectedLarge : ordUnit K D.input.block.enlargedScaleGenerator <
      ordUnit K D.input.block.enlargedScaleGenerator + 1 := by omega
  have hselectedSmall : ¬ ordUnit K D.input.block.scaleGenerator <
      ordUnit K D.input.block.scaleGenerator := lt_irrefl _
  simp only [if_pos hselectedLarge, if_neg hselectedSmall,
    mul_one, mul_zero, zero_add]
  have hsum :
      (∑ x, (finrank K (D.complementStrictWeak.component x).carrier : Int) *
        if ordUnit K (D.complementStrictWeak.scaleGenerator x) <
            ordUnit K D.input.block.enlargedScaleGenerator + 1
          then 1 else 0) ≤
      ∑ x, (finrank K (D.complementStrictWeak.component x).carrier : Int) *
        if ordUnit K (D.complementStrictWeak.scaleGenerator x) <
            ordUnit K D.input.block.scaleGenerator
          then 1 else 0 := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hlarge : ordUnit K
        (D.complementStrictWeak.scaleGenerator i) <
          ordUnit K D.input.block.enlargedScaleGenerator + 1
    · have hsmall := hlarge.trans_le hthreshold
      simp [hlarge, hsmall]
    · by_cases hsmall : ordUnit K
          (D.complementStrictWeak.scaleGenerator i) <
            ordUnit K D.input.block.scaleGenerator
      · simp [hlarge, hsmall]
      · simp [hlarge, hsmall]
  omega

/-- The sum of the original and reverse-dual reduced cutoffs is at least
the ambient rank plus the selected rank minus two.  The binary case is
therefore stronger by one than the general boundary cover. -/
theorem defectReducedCutoff_add_reverseDual_ge_rank_add_selected_sub_two
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M)) :
    (finrank K V : Int) +
        finrank K D.input.block.component.carrier - 2 ≤
      (D.defectReducedCutoff : Int) +
        (E.defectReducedCutoff : Int) := by
  have hDstart := D.intCast_smallSelectedStart_eq_scaleRankBelow
  have hEstart := E.intCast_smallSelectedStart_eq_scaleRankBelow
  have hscale := D.reverseDual_selectedScaleOrder E
  have hrank := D.reverseDual_selectedRank E
  have hEbelow := E.smallModularDecomposition.scaleRankBelow_eq
    D.largeModularDecomposition.reverseDual
      (ordUnit K E.input.block.scaleGenerator)
  have hdual := D.largeModularDecomposition.reverseDual_scaleRankBelow
    (ordUnit K D.input.block.enlargedScaleGenerator)
  have hEstartValue :
      (E.smallSelectedStart : Int) = (finrank K V : Int) -
        D.largeModularDecomposition.scaleRankBelow
          (ordUnit K D.input.block.enlargedScaleGenerator + 1) := by
    calc
      (E.smallSelectedStart : Int) =
          E.smallModularDecomposition.scaleRankBelow
            (ordUnit K E.input.block.scaleGenerator) := hEstart
      _ = D.largeModularDecomposition.reverseDual.scaleRankBelow
            (ordUnit K E.input.block.scaleGenerator) := hEbelow
      _ = D.largeModularDecomposition.reverseDual.scaleRankBelow
            (-ordUnit K D.input.block.enlargedScaleGenerator) := by rw [hscale]
      _ = (finrank K V : Int) -
          D.largeModularDecomposition.scaleRankBelow
            (ordUnit K D.input.block.enlargedScaleGenerator + 1) := hdual
  have hbelow := D.largeScaleRankBelow_le_small_add_selectedRank
  have hrankPos : 0 < finrank K D.input.block.component.carrier := by
    rcases D.rank_one_or_two with h | h <;> omega
  have hDcut : (D.defectReducedCutoff : Int) =
      (D.smallSelectedStart : Int) +
        finrank K D.input.block.component.carrier - 1 := by
    change ((D.smallSelectedStart +
      finrank K (D.smallAlmostJordan.component
        D.smallSelectedPosition).carrier - 1 : Nat) : Int) = _
    rw [D.smallAlmostJordan_finrank_selected, Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hEcut : (E.defectReducedCutoff : Int) =
      (E.smallSelectedStart : Int) +
        finrank K E.input.block.component.carrier - 1 := by
    have hrankEPos : 0 < finrank K E.input.block.component.carrier := by omega
    change ((E.smallSelectedStart +
      finrank K (E.smallAlmostJordan.component
        E.smallSelectedPosition).carrier - 1 : Nat) : Int) = _
    rw [E.smallAlmostJordan_finrank_selected, Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [hDcut, hEcut, hEstartValue]
  have hrankInt : (finrank K E.input.block.component.carrier : Int) =
      (finrank K D.input.block.component.carrier : Int) := by
    exact_mod_cast hrank
  omega

/-- Original and swapped reverse-dual reduced cutoffs cover every boundary
of the ambient rank. -/
theorem defectReducedCutoff_add_reverseDual_ge
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M)) :
    (finrank K V : Int) - 1 ≤
      (D.defectReducedCutoff : Int) +
        (E.defectReducedCutoff : Int) := by
  have hstrong :=
    D.defectReducedCutoff_add_reverseDual_ge_rank_add_selected_sub_two E
  have hrankPos : 0 < finrank K D.input.block.component.carrier := by
    rcases D.rank_one_or_two with h | h <;> omega
  omega

/-- A boundary in the original complementary range belongs to the direct
reduced range for every Lemma 5.1 datum on the swapped reverse-dual pair. -/
theorem defectReducedRange_reverseDual_of_reverseRange
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M))
    {rank : Nat} (j : RepresentationIndex rank rank)
    (hrank : rank = finrank K V)
    (hj : D.DefectReverseRange j) : E.DefectReducedRange j := by
  have hcover := D.defectReducedCutoff_add_reverseDual_ge E
  change j.val + D.defectReducedCutoff < rank at hj
  change j.val ≤ E.defectReducedCutoff
  omega

end Lattice.Beli2019Lemma51Data

end Bong
