/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaCommonAdjunctionConditions
import Bong.Lattice.OmearaGeneralModularCancellation
import Bong.Lattice.OmearaModularDecompositionTruncation

/-!
# Cancelling O'Meara's common adjunction

Corollary 93:14a cancels one modular component at a time.  Iterating it over
the block presentation of a saturated common Jordan splitting removes the
common adjunction used in O'Meara 93:28, Step 2.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v x y

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Iterated 93:14a cancellation for a finite common modular block product.
The containment hypotheses are measured in the two remaining complements
at the scale of each common block. -/
noncomputable def cancelCommonBlockProduct :
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
      ((BONG.blockOrthogonalForm n C qs).orthogonalSum q)
      ((BONG.blockOrthogonalForm n C qs).orthogonalSum r)
      (product (BONG.blockProductLattice n C Ls) L)
      (product (BONG.blockProductLattice n C Ls) M) →
    Isometry q r L M
  | 0, C, _, _, qs, Ls, scale, hmodular,
      X, _, _, Y, _, _, q, r, L, M, hsource, htarget, f => by
      let blockForm := BONG.blockOrthogonalForm 0 C qs
      let blockLattice := BONG.blockProductLattice 0 C Ls
      let singleton := BONG.blockOrthogonalSingletonLatticeIsometry C qs Ls
      let sourcePresentation : Isometry
          (blockForm.orthogonalSum q) ((qs 0).orthogonalSum q)
          (product blockLattice L) (product (Ls 0) L) :=
        singleton.orthogonalProductBasic (Isometry.refl q L)
      let targetPresentation : Isometry
          (blockForm.orthogonalSum r) ((qs 0).orthogonalSum r)
          (product blockLattice M) (product (Ls 0) M) :=
        singleton.orthogonalProductBasic (Isometry.refl r M)
      let displayed : Isometry
          ((qs 0).orthogonalSum q) ((qs 0).orthogonalSum r)
          (product (Ls 0) L) (product (Ls 0) M) :=
        sourcePresentation.symm.trans (f.trans targetPresentation)
      exact omeara9314a_general (scale 0) (hmodular 0) (hmodular 0)
        (Isometry.refl (qs 0) (Ls 0)) (hsource 0) (htarget 0) displayed
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
      let split := BONG.blockOrthogonalSplitLatticeIsometry n C qs Ls
      let sourcePresentation : Isometry
          (blockForm.orthogonalSum q)
          ((qs 0).orthogonalSum (tailForm.orthogonalSum q))
          (product blockLattice L)
          (product (Ls 0) (product tailLattice L)) :=
        (split.orthogonalProductBasic (Isometry.refl q L)).trans
          orthogonalProductAssoc
      let targetPresentation : Isometry
          (blockForm.orthogonalSum r)
          ((qs 0).orthogonalSum (tailForm.orthogonalSum r))
          (product blockLattice M)
          (product (Ls 0) (product tailLattice M)) :=
        (split.orthogonalProductBasic (Isometry.refl r M)).trans
          orthogonalProductAssoc
      let displayed : Isometry
          ((qs 0).orthogonalSum (tailForm.orthogonalSum q))
          ((qs 0).orthogonalSum (tailForm.orthogonalSum r))
          (product (Ls 0) (product tailLattice L))
          (product (Ls 0) (product tailLattice M)) :=
        sourcePresentation.symm.trans (f.trans targetPresentation)
      have hsourceHead : normGroupSet (qs 0) (Ls 0) ⊆
          normGroupSet (tailForm.orthogonalSum q)
            (omearaScaleTruncation (tailForm.orthogonalSum q)
              (product tailLattice L) (scale 0)) := by
        intro z hz
        exact normGroupSet_omearaScaleTruncation_subset_orthogonalProduct_right
          tailForm tailLattice q L (scale 0) (hsource 0 hz)
      have htargetHead : normGroupSet (qs 0) (Ls 0) ⊆
          normGroupSet (tailForm.orthogonalSum r)
            (omearaScaleTruncation (tailForm.orthogonalSum r)
              (product tailLattice M) (scale 0)) := by
        intro z hz
        exact normGroupSet_omearaScaleTruncation_subset_orthogonalProduct_right
          tailForm tailLattice r M (scale 0) (htarget 0 hz)
      let tailTotal : Isometry
          (tailForm.orthogonalSum q) (tailForm.orthogonalSum r)
          (product tailLattice L) (product tailLattice M) :=
        omeara9314a_general (scale 0) (hmodular 0) (hmodular 0)
          (Isometry.refl (qs 0) (Ls 0)) hsourceHead htargetHead displayed
      exact cancelCommonBlockProduct n tailC tailQ tailL tailScale
        (fun i ↦ hmodular i.succ) q r L M
        (fun i ↦ hsource i.succ) (fun i ↦ htarget i.succ) tailTotal

namespace JordanDecomposition

universe w

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- A saturated component of one decomposition occurs in the scale
truncation of every decomposition of the same fundamental type. -/
theorem IsSaturated.componentNormGroup_subset_sameTypeTruncation
    (P : JordanDecomposition q L (n + 2)) (hP : P.IsSaturated)
    (J : JordanDecomposition r M (n + 2))
    (F : SameFundamentalType P J) (i : Fin (n + 2)) :
    normGroupSet (P.component i).space (P.component i).lattice ⊆
      normGroupSet r
        (omearaScaleTruncation r M (P.scaleGenerator i)) := by
  have hscale := F.scaleGenerator_order_eq_sameIndex i
  have hgroup := F.normGroup_eq i
  rw [F.indexEquiv_apply_eq_self] at hgroup
  have htarget : normGroupSet r
      (omearaScaleTruncation r M (P.scaleGenerator i)) =
        J.fundamentalNormGroup i := by
    rw [omearaScaleTruncation_eq_scaleTruncation]
    unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
    rw [hscale]
  rw [hP i, htarget, hgroup]

/-- Iterated 93:14a cancels the saturated common splitting from an
isometry of two componentwise common adjunctions. -/
noncomputable def cancelCommonAdjunction
    {X : Type x} [AddCommGroup X] [Module K X]
    (P : JordanDecomposition q L (n + 2))
    (J : JordanDecomposition r M (n + 2))
    {s : QuadraticSpace K X} {N : Lattice K X}
    (H : JordanDecomposition s N (n + 2))
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (hP : P.IsSaturated)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) (P.commonAdjunctionCarrier J)
        (P.commonAdjunctionForm J))
      (BONG.blockOrthogonalForm (n + 1) (P.commonAdjunctionCarrier H)
        (P.commonAdjunctionForm H))
      (BONG.blockProductLattice (n + 1) (P.commonAdjunctionCarrier J)
        (P.commonAdjunctionLattice J))
      (BONG.blockProductLattice (n + 1) (P.commonAdjunctionCarrier H)
        (P.commonAdjunctionLattice H))) :
    Isometry r s M N := by
  let sourceGather := P.commonAdjunctionProductIsometry J
  let targetGather := P.commonAdjunctionProductIsometry H
  let totalProduct : Isometry (q.orthogonalSum r) (q.orthogonalSum s)
      (product L M) (product L N) :=
    sourceGather.symm.trans (f.trans targetGather)
  let C : Fin (n + 2) → Type v := fun i ↦ (P.component i).carrier
  let qs : ∀ i, QuadraticSpace K (C i) := fun i ↦ (P.component i).space
  let Ls : ∀ i, Lattice K (C i) := fun i ↦ (P.component i).lattice
  let blockForm := BONG.blockOrthogonalForm (n + 1) C qs
  let blockLattice := BONG.blockProductLattice (n + 1) C Ls
  let present :=
    BONG.orthogonalDecompositionProductIsometry P.toOrthogonalDecomposition
  let blockTotal : Isometry
      (blockForm.orthogonalSum r) (blockForm.orthogonalSum s)
      (product blockLattice M) (product blockLattice N) :=
    (present.orthogonalProductBasic (Isometry.refl r M)).trans <|
      totalProduct.trans <|
        (present.orthogonalProductBasic (Isometry.refl s N)).symm
  exact cancelCommonBlockProduct (n + 1) C qs Ls P.scaleGenerator P.modular
    r s M N
    (fun i ↦ hP.componentNormGroup_subset_sameTypeTruncation P J FPJ i)
    (fun i ↦ hP.componentNormGroup_subset_sameTypeTruncation P H FPH i)
    blockTotal

end JordanDecomposition
end Lattice

end Bong
