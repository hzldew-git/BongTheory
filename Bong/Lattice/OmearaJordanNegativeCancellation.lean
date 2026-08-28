/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaGeneralModularCancellation
import Bong.Lattice.OmearaNormGroupShift
import Bong.Lattice.OmearaModularDecompositionTruncation
import Bong.Lattice.OrthogonalSumRescale
import Bong.Lattice.OmearaSaturatedJordan
import Bong.Lattice.BlockOrthogonalPairDistribution

/-!
# Cancelling the negative of a saturated Jordan lattice

O'Meara 93:28, Step 2 adjoins the negative of the source lattice to both
the source and target.  Corollary 93:14a then cancels the source Jordan
components one at a time.  This file implements that iteration on the
explicit block-product presentation.

The recursive theorem is deliberately stated with arbitrary complements.
At every stage the still-present positive source or target lattice contains
the norm group of the modular component being cancelled at the appropriate
scale truncation.  Thus the recursion exactly records the two containment
hypotheses of 93:14a and does not hide a cancellation axiom.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v x y

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Iterated 93:14a cancellation for the negative of a finite block product.

The source family supplies the common modular summands on both sides.  The
two containment hypotheses say that every such summand occurs in the scale
truncation of the corresponding positive complement. -/
noncomputable def cancelNegativeBlockProduct :
    (n : Nat) →
    (C : Fin (n + 1) → Type v) →
    [(∀ i, AddCommGroup (C i))] → [(∀ i, Module K (C i))] →
    (qs : ∀ i, QuadraticSpace K (C i)) →
    (Ls : ∀ i, Lattice K (C i)) →
    (scale : Fin (n + 1) → Kˣ) →
    (hmodular : ∀ i, IsModular (qs i) (Ls i) (scale i)) →
    {X : Type x} → [AddCommGroup X] → [Module K X] →
    {Y : Type y} → [AddCommGroup Y] → [Module K Y] →
    (q : QuadraticSpace K X) → (r : QuadraticSpace K Y) →
    (L : Lattice K X) → (M : Lattice K Y) →
    (hsource : ∀ i, normGroupSet (qs i) (Ls i) ⊆
      normGroupSet q (omearaScaleTruncation q L (scale i))) →
    (htarget : ∀ i, normGroupSet (qs i) (Ls i) ⊆
      normGroupSet r (omearaScaleTruncation r M (scale i))) →
    Isometry
      ((BONG.blockOrthogonalForm n C qs).rescaleUnit
        (-1 : Kˣ) |>.orthogonalSum q)
      ((BONG.blockOrthogonalForm n C qs).rescaleUnit
        (-1 : Kˣ) |>.orthogonalSum r)
      (product (BONG.blockProductLattice n C Ls) L)
      (product (BONG.blockProductLattice n C Ls) M) →
    Isometry q r L M
  | 0, C, _, _, qs, Ls, scale, hmodular,
      X, _, _, Y, _, _, q, r, L, M, hsource, htarget, f => by
      let blockForm := BONG.blockOrthogonalForm 0 C qs
      let blockLattice := BONG.blockProductLattice 0 C Ls
      let singleton := BONG.blockOrthogonalSingletonLatticeIsometry C qs Ls
      let negativeSingleton := singleton.rescaleUnitBoth (-1 : Kˣ)
      let sourcePresentation : Isometry
          (blockForm.rescaleUnit (-1 : Kˣ) |>.orthogonalSum q)
          ((qs 0).rescaleUnit (-1 : Kˣ) |>.orthogonalSum q)
          (product blockLattice L) (product (Ls 0) L) :=
        negativeSingleton.orthogonalProductBasic (Isometry.refl q L)
      let targetPresentation : Isometry
          (blockForm.rescaleUnit (-1 : Kˣ) |>.orthogonalSum r)
          ((qs 0).rescaleUnit (-1 : Kˣ) |>.orthogonalSum r)
          (product blockLattice M) (product (Ls 0) M) :=
        negativeSingleton.orthogonalProductBasic (Isometry.refl r M)
      let displayed : Isometry
          ((qs 0).rescaleUnit (-1 : Kˣ) |>.orthogonalSum q)
          ((qs 0).rescaleUnit (-1 : Kˣ) |>.orthogonalSum r)
          (product (Ls 0) L) (product (Ls 0) M) :=
        sourcePresentation.symm.trans (f.trans targetPresentation)
      have hnegative : IsModular ((qs 0).rescaleUnit (-1 : Kˣ))
          (Ls 0) (scale 0) :=
        (hmodular 0).rescaleUnit_neg_one_general
      have hsourceNegative :
          normGroupSet ((qs 0).rescaleUnit (-1 : Kˣ)) (Ls 0) ⊆
            normGroupSet q (omearaScaleTruncation q L (scale 0)) := by
        rw [normGroupSet_rescaleUnit_neg_one]
        exact hsource 0
      have htargetNegative :
          normGroupSet ((qs 0).rescaleUnit (-1 : Kˣ)) (Ls 0) ⊆
            normGroupSet r (omearaScaleTruncation r M (scale 0)) := by
        rw [normGroupSet_rescaleUnit_neg_one]
        exact htarget 0
      exact omeara9314a_general (scale 0) hnegative hnegative
        (Isometry.refl ((qs 0).rescaleUnit (-1 : Kˣ)) (Ls 0))
        hsourceNegative htargetNegative displayed
  | n + 1, C, _, _, qs, Ls, scale, hmodular,
      X, _, _, Y, _, _, q, r, L, M, hsource, htarget, f => by
      let tailC : Fin (n + 1) → Type v := fun i ↦ C i.succ
      let tailQ : ∀ i, QuadraticSpace K (tailC i) := fun i ↦ qs i.succ
      let tailL : ∀ i, Lattice K (tailC i) := fun i ↦ Ls i.succ
      let tailScale : Fin (n + 1) → Kˣ := fun i ↦ scale i.succ
      let blockForm := BONG.blockOrthogonalForm (n + 1) C qs
      let blockLattice := BONG.blockProductLattice (n + 1) C Ls
      let tailForm := BONG.blockOrthogonalForm n tailC tailQ
      let tailLattice := BONG.blockProductLattice n tailC tailL
      let split := BONG.blockOrthogonalSplitLatticeIsometry
        n C qs Ls
      let splitNegative := split.rescaleUnitBoth (-1 : Kˣ)
      let distributeNegative := rescaleUnitOrthogonalProductIsometry
        (qs 0) tailForm (Ls 0) tailLattice (-1 : Kˣ)
      let negativeSplit : Isometry
          (blockForm.rescaleUnit (-1 : Kˣ))
          (((qs 0).rescaleUnit (-1 : Kˣ)).orthogonalSum
            (tailForm.rescaleUnit (-1 : Kˣ)))
          blockLattice (product (Ls 0) tailLattice) :=
        splitNegative.trans distributeNegative
      let sourcePresentation : Isometry
          (blockForm.rescaleUnit (-1 : Kˣ) |>.orthogonalSum q)
          (((qs 0).rescaleUnit (-1 : Kˣ)).orthogonalSum
            ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum q))
          (product blockLattice L)
          (product (Ls 0) (product tailLattice L)) :=
        (negativeSplit.orthogonalProductBasic (Isometry.refl q L)).trans
          orthogonalProductAssoc
      let targetPresentation : Isometry
          (blockForm.rescaleUnit (-1 : Kˣ) |>.orthogonalSum r)
          (((qs 0).rescaleUnit (-1 : Kˣ)).orthogonalSum
            ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum r))
          (product blockLattice M)
          (product (Ls 0) (product tailLattice M)) :=
        (negativeSplit.orthogonalProductBasic (Isometry.refl r M)).trans
          orthogonalProductAssoc
      let displayed : Isometry
          (((qs 0).rescaleUnit (-1 : Kˣ)).orthogonalSum
            ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum q))
          (((qs 0).rescaleUnit (-1 : Kˣ)).orthogonalSum
            ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum r))
          (product (Ls 0) (product tailLattice L))
          (product (Ls 0) (product tailLattice M)) :=
        sourcePresentation.symm.trans (f.trans targetPresentation)
      have hnegative : IsModular ((qs 0).rescaleUnit (-1 : Kˣ))
          (Ls 0) (scale 0) :=
        (hmodular 0).rescaleUnit_neg_one_general
      have hsourceNegative :
          normGroupSet ((qs 0).rescaleUnit (-1 : Kˣ)) (Ls 0) ⊆
            normGroupSet
              ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
              (omearaScaleTruncation
                ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
                (product tailLattice L) (scale 0)) := by
        intro z hz
        have hzSource : z ∈ normGroupSet (qs 0) (Ls 0) := by
          rw [← normGroupSet_rescaleUnit_neg_one (qs 0) (Ls 0)]
          exact hz
        exact normGroupSet_omearaScaleTruncation_subset_orthogonalProduct_right
          (tailForm.rescaleUnit (-1 : Kˣ)) tailLattice q L (scale 0)
            (hsource 0 hzSource)
      have htargetNegative :
          normGroupSet ((qs 0).rescaleUnit (-1 : Kˣ)) (Ls 0) ⊆
            normGroupSet
              ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum r)
              (omearaScaleTruncation
                ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum r)
                (product tailLattice M) (scale 0)) := by
        intro z hz
        have hzSource : z ∈ normGroupSet (qs 0) (Ls 0) := by
          rw [← normGroupSet_rescaleUnit_neg_one (qs 0) (Ls 0)]
          exact hz
        exact normGroupSet_omearaScaleTruncation_subset_orthogonalProduct_right
          (tailForm.rescaleUnit (-1 : Kˣ)) tailLattice r M (scale 0)
            (htarget 0 hzSource)
      let tailTotal : Isometry
          ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
          ((tailForm.rescaleUnit (-1 : Kˣ)).orthogonalSum r)
          (product tailLattice L) (product tailLattice M) :=
        omeara9314a_general (scale 0) hnegative hnegative
          (Isometry.refl ((qs 0).rescaleUnit (-1 : Kˣ)) (Ls 0))
          hsourceNegative htargetNegative displayed
      exact cancelNegativeBlockProduct n tailC tailQ tailL tailScale
        (fun i ↦ hmodular i.succ) q r L M
        (fun i ↦ hsource i.succ) (fun i ↦ htarget i.succ) tailTotal

namespace JordanDecomposition

universe w

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- A saturated source component occurs, with its complete norm group, in
the scale truncation of the full source lattice at its own Jordan scale. -/
theorem IsSaturated.componentNormGroup_subset_sourceTruncation
    (J : JordanDecomposition q L (n + 1)) (hJ : J.IsSaturated)
    (i : Fin (n + 1)) :
    normGroupSet (J.component i).space (J.component i).lattice ⊆
      normGroupSet q
        (omearaScaleTruncation q L (J.scaleGenerator i)) := by
  have h := hJ i
  unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder at h
  rw [omearaScaleTruncation_eq_scaleTruncation]
  rw [← h]

/-- Corresponding saturated components occur in the target truncations as
well, after equality of fundamental type identifies their scale orders and
norm groups. -/
theorem IsSaturated.componentNormGroup_subset_targetTruncation
    (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H) (i : Fin (n + 1)) :
    normGroupSet (J.component i).space (J.component i).lattice ⊆
      normGroupSet r
        (omearaScaleTruncation r M (J.scaleGenerator i)) := by
  have hscaleOrder := F.scaleOrder_eq i
  rw [F.indexEquiv_apply_eq_self] at hscaleOrder
  have hscaleOrder' : ordUnit K (H.scaleGenerator i) =
      ordUnit K (J.scaleGenerator i) := by
    simpa only [fundamentalScaleOrder] using hscaleOrder
  have htrunc : omearaScaleTruncation r M (H.scaleGenerator i) =
      omearaScaleTruncation r M (J.scaleGenerator i) :=
    by
      rw [omearaScaleTruncation_eq_scaleTruncation,
        omearaScaleTruncation_eq_scaleTruncation, hscaleOrder']
  rw [← htrunc]
  have hcomponent := hJ.componentNormGroup_eq hH F i
  rw [← hcomponent]
  exact hH.componentNormGroup_subset_sourceTruncation H i

/-- Corollary 93:14a, iterated over all source Jordan components.

An isometry after adjoining the negative source lattice to both sides
therefore descends to an isometry of the original saturated lattices. -/
noncomputable def cancelNegativeAdjunction
    (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H)
    (f : Isometry
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum r)
      (product L L) (product L M)) :
    Isometry q r L M := by
  let C : Fin (n + 1) → Type v := fun i ↦ (J.component i).carrier
  let qs : ∀ i, QuadraticSpace K (C i) := fun i ↦ (J.component i).space
  let Ls : ∀ i, Lattice K (C i) := fun i ↦ (J.component i).lattice
  let blockForm := BONG.blockOrthogonalForm n C qs
  let blockLattice := BONG.blockProductLattice n C Ls
  let present :=
    BONG.orthogonalDecompositionProductIsometry J.toOrthogonalDecomposition
  let blockTotal : Isometry
      ((blockForm.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
      ((blockForm.rescaleUnit (-1 : Kˣ)).orthogonalSum r)
      (product blockLattice L) (product blockLattice M) :=
    (present.rescaleUnitBoth (-1 : Kˣ)).orthogonalProductBasic
        (Isometry.refl q L) |>.trans <|
      f.trans <|
        ((present.rescaleUnitBoth (-1 : Kˣ)).orthogonalProductBasic
          (Isometry.refl r M)).symm
  exact cancelNegativeBlockProduct n C qs Ls J.scaleGenerator
    J.modular q r L M
    (fun i ↦ hJ.componentNormGroup_subset_sourceTruncation J i)
    (fun i ↦ hJ.componentNormGroup_subset_targetTruncation J H hH F i)
    blockTotal

end JordanDecomposition

end Lattice

end Bong
