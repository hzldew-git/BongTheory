/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NormIdealOrthogonalProduct
import Bong.Lattice.OmearaBinaryModularSplitting
import Bong.Lattice.OrthogonalDecompositionIdeals
import Bong.Lattice.RankOneNormScale

/-!
# A binary modular splitting with norm-preserving complement

O'Meara 93:18(ii) starts with a binary modular summand whose orthogonal
complement has the same norm ideal as the original modular lattice.  An
arbitrary binary summand need not have this property.  The construction below
uses two binary splittings: if the first complement does not retain the norm,
then the first plane itself carries the total norm, so a binary plane is split
from its complement and moved in front of the first plane.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Norm ideals of positive-dimensional quadratic lattices over a discretely
valued field are comparable. -/
theorem normIdeal_le_total_of_finrank_pos
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (r : QuadraticSpace K W) (M : Lattice K W)
    (hL : 0 < finrank K V) (hM : 0 < finrank K W) :
    normIdeal q L ≤ normIdeal r M ∨ normIdeal r M ≤ normIdeal q L := by
  let hxExists := exists_isNormGenerator_of_finrank_pos q L hL
  let x := Classical.choose hxExists
  have hxGenerator : IsNormGenerator q L x :=
    (Classical.choose_spec hxExists).1
  have hxNe : q.quadratic x ≠ 0 :=
    (Classical.choose_spec hxExists).2
  let hyExists := exists_isNormGenerator_of_finrank_pos r M hM
  let y := Classical.choose hyExists
  have hyGenerator : IsNormGenerator r M y :=
    (Classical.choose_spec hyExists).1
  have hyNe : r.quadratic y ≠ 0 :=
    (Classical.choose_spec hyExists).2
  let ux : Kˣ := Units.mk0 (q.quadratic x) hxNe
  let uy : Kˣ := Units.mk0 (r.quadratic y) hyNe
  have hxIdeal : normIdeal q L = principalIdeal (K := K) (ux : K) := by
    simpa only [ux, Units.val_mk0] using hxGenerator.normIdeal_eq
  have hyIdeal : normIdeal r M = principalIdeal (K := K) (uy : K) := by
    simpa only [uy, Units.val_mk0] using hyGenerator.normIdeal_eq
  rcases le_total (ordUnit K ux) (ordUnit K uy) with hxy | hyx
  · right
    rw [hxIdeal, hyIdeal]
    exact (principalIdeal_le_iff_ord_ge
      (Units.ne_zero uy) (Units.ne_zero ux)).2 (by
        simpa only [← coe_ordUnit K ux, ← coe_ordUnit K uy] using
          WithTop.coe_le_coe.mpr hxy)
  · left
    rw [hxIdeal, hyIdeal]
    exact (principalIdeal_le_iff_ord_ge
      (Units.ne_zero ux) (Units.ne_zero uy)).2 (by
        simpa only [← coe_ordUnit K uy, ← coe_ordUnit K ux] using
          WithTop.coe_le_coe.mpr hyx)

/-- A binary modular splitting whose complement retains the norm ideal of
the ambient lattice. -/
structure NormPreservingBinaryModularSplittingData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    extends BinaryModularSplittingData q L a where
  complement_normIdeal_eq :
    normIdeal (decomposition.component 1).space
        (decomposition.component 1).lattice = normIdeal q L

namespace NormPreservingBinaryModularSplittingData

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}

/-- The norm ideal of a two-component orthogonal decomposition is the
supremum of the two component norm ideals. -/
theorem normIdeal_eq_sup_components
    (D : OrthogonalDecomposition q L 2) :
    normIdeal q L =
      normIdeal (D.component 0).space (D.component 0).lattice ⊔
        normIdeal (D.component 1).space (D.component 1).lattice := by
  rw [D.normIdeal_eq_iSup_component]
  apply le_antisymm
  · apply iSup_le
    intro i
    fin_cases i
    · exact _root_.le_sup_left
    · exact _root_.le_sup_right
  · exact _root_.sup_le
      (le_iSup (fun i : Fin 2 ↦
        normIdeal (D.component i).space (D.component i).lattice) 0)
      (le_iSup (fun i : Fin 2 ↦
        normIdeal (D.component i).space (D.component i).lattice) 1)

/-- The second component's norm ideal is contained in the ambient norm
ideal. -/
theorem componentOne_normIdeal_le
    (D : OrthogonalDecomposition q L 2) :
    normIdeal (D.component 1).space (D.component 1).lattice ≤
      normIdeal q L := by
  rw [D.normIdeal_eq_iSup_component]
  exact le_iSup (fun i : Fin 2 ↦
    normIdeal (D.component i).space (D.component i).lattice) 1

/-- The first component's norm ideal is contained in the ambient norm
ideal. -/
theorem componentZero_normIdeal_le
    (D : OrthogonalDecomposition q L 2) :
    normIdeal (D.component 0).space (D.component 0).lattice ≤
      normIdeal q L := by
  rw [D.normIdeal_eq_iSup_component]
  exact le_iSup (fun i : Fin 2 ↦
    normIdeal (D.component i).space (D.component i).lattice) 0

/-- Every modular lattice of rank at least three has a binary modular
summand whose modular orthogonal complement has the same norm ideal as the
ambient lattice.  This is the opening splitting in O'Meara 93:18(ii). -/
noncomputable def normPreservingBinaryModularSplittingData
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hmodular : IsModular q L a)
    (hrank : 3 ≤ finrank K V) :
    NormPreservingBinaryModularSplittingData q L a := by
  letI : Module.Finite K V := L.moduleFinite
  let D₁ := binaryModularSplittingData q L a hmodular (by omega)
  let J := D₁.decomposition.component 0
  let C := D₁.decomposition.component 1
  letI : Module.Finite K J.carrier := J.lattice.moduleFinite
  letI : Module.Finite K C.carrier := C.lattice.moduleFinite
  have htotalRank := D₁.decomposition.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
  have hCrankPos : 0 < finrank K C.carrier := by
    change finrank K (J.carrier × C.carrier) = finrank K V at htotalRank
    rw [Module.finrank_prod, D₁.first_rank] at htotalRank
    omega
  by_cases hCnorm : normIdeal C.space C.lattice = normIdeal q L
  · exact
      { toBinaryModularSplittingData := D₁
        complement_normIdeal_eq := hCnorm }
  · have hCrank : 2 ≤ finrank K C.carrier := by
      by_contra hnot
      have hCrankOne : finrank K C.carrier = 1 := by omega
      have hnormScale : normIdeal C.space C.lattice =
          scaleIdeal C.space C.lattice :=
        normIdeal_eq_scaleIdeal_of_finrank_eq_one
          C.space C.lattice hCrankOne
      have hscaleAmbient : scaleIdeal C.space C.lattice =
          scaleIdeal q L := by
        rw [D₁.complement_modular.scaleIdeal_eq_principal hCrankPos,
          hmodular.scaleIdeal_eq_principal (by omega)]
      have hCle : normIdeal C.space C.lattice ≤ normIdeal q L :=
        componentOne_normIdeal_le D₁.decomposition
      have hLeC : normIdeal q L ≤ normIdeal C.space C.lattice := by
        rw [hnormScale, hscaleAmbient]
        exact normIdeal_le_scaleIdeal q L
      exact hCnorm (le_antisymm hCle hLeC)
    let D₂ := binaryModularSplittingData C.space C.lattice a
      D₁.complement_modular hCrank
    let H := D₂.decomposition.component 0
    let R := D₂.decomposition.component 1
    letI : Module.Finite K H.carrier := H.lattice.moduleFinite
    letI : Module.Finite K R.carrier := R.lattice.moduleFinite
    have hJnorm : normIdeal J.space J.lattice = normIdeal q L := by
      have htotal := normIdeal_eq_sup_components D₁.decomposition
      rcases normIdeal_le_total_of_finrank_pos J.space J.lattice
          C.space C.lattice (by rw [D₁.first_rank]; omega) hCrankPos with
        hJleC | hCleJ
      · have hL_eq_C : normIdeal q L = normIdeal C.space C.lattice :=
          htotal.trans (sup_eq_right.mpr hJleC)
        exact (hCnorm hL_eq_C.symm).elim
      · exact (htotal.trans (sup_eq_left.mpr hCleJ)).symm
    have hRleJ : normIdeal R.space R.lattice ≤
        normIdeal J.space J.lattice := by
      have hRleC : normIdeal R.space R.lattice ≤
          normIdeal C.space C.lattice :=
        componentOne_normIdeal_le D₂.decomposition
      have hCleL : normIdeal C.space C.lattice ≤ normIdeal q L :=
        componentOne_normIdeal_le D₁.decomposition
      rw [hJnorm]
      exact hRleC.trans hCleL
    let expose₁ : Isometry q (J.space.orthogonalSum C.space) L
        (product J.lattice C.lattice) :=
      D₁.decomposition.pairProductLatticeIsometry.symm
    let expose₂ : Isometry C.space (H.space.orthogonalSum R.space)
        C.lattice (product H.lattice R.lattice) :=
      D₂.decomposition.pairProductLatticeIsometry.symm
    let nested : Isometry q
        (J.space.orthogonalSum (H.space.orthogonalSum R.space)) L
        (product J.lattice (product H.lattice R.lattice)) :=
      expose₁.trans
        ((Isometry.refl J.space J.lattice).orthogonalProductBasic expose₂)
    let rotate : Isometry
        (J.space.orthogonalSum (H.space.orthogonalSum R.space))
        ((H.space.orthogonalSum J.space).orthogonalSum R.space)
        (product J.lattice (product H.lattice R.lattice))
        (product (product H.lattice J.lattice) R.lattice) :=
      orthogonalProductRotateLeft
    let regroup : Isometry
        ((H.space.orthogonalSum J.space).orthogonalSum R.space)
        (H.space.orthogonalSum (J.space.orthogonalSum R.space))
        (product (product H.lattice J.lattice) R.lattice)
        (product H.lattice (product J.lattice R.lattice)) :=
      orthogonalProductAssoc
    let displayed := nested.trans (rotate.trans regroup)
    let T : OrthogonalDecomposition
        (H.space.orthogonalSum (J.space.orthogonalSum R.space))
        (product H.lattice (product J.lattice R.lattice)) 2 :=
      orthogonalProductDecomposition H.space
        (J.space.orthogonalSum R.space) H.lattice
        (product J.lattice R.lattice)
    let pulled : OrthogonalDecomposition q L 2 :=
      T.mapIsometry displayed.symm
    let standardToLeft : Isometry H.space (T.component 0).space H.lattice
        (T.component 0).lattice :=
      orthogonalProductLeftComponentIsometry H.space
        (J.space.orthogonalSum R.space) H.lattice
    let leftToPulled := (T.component 0).mapLatticeIsometry displayed.symm
    let standardToRight : Isometry (J.space.orthogonalSum R.space)
        (T.component 1).space (product J.lattice R.lattice)
        (T.component 1).lattice :=
      orthogonalProductRightComponentIsometry H.space
        (J.space.orthogonalSum R.space) (product J.lattice R.lattice)
    let rightToPulled := (T.component 1).mapLatticeIsometry displayed.symm
    let complementIsometry := standardToRight.trans rightToPulled
    have hfirstRank : finrank K (pulled.component 0).carrier = 2 := by
      have h := (standardToLeft.trans leftToPulled).toLinearEquiv.finrank_eq
      change finrank K ((T.component 0).mapIsometry displayed.symm).carrier = 2
      calc
        finrank K ((T.component 0).mapIsometry displayed.symm).carrier =
            finrank K H.carrier := h.symm
        _ = 2 := D₂.first_rank
    have hcomplementNorm :
        normIdeal (pulled.component 1).space
            (pulled.component 1).lattice = normIdeal q L := by
      change normIdeal ((T.component 1).mapIsometry displayed.symm).space
          ((T.component 1).mapIsometry displayed.symm).lattice =
        normIdeal q L
      calc
        normIdeal ((T.component 1).mapIsometry displayed.symm).space
            ((T.component 1).mapIsometry displayed.symm).lattice =
            normIdeal (J.space.orthogonalSum R.space)
              (product J.lattice R.lattice) := by
          rw [← complementIsometry.map_eq]
          exact normIdeal_map_isometry
            complementIsometry.toQuadraticSpaceIsometry
              (product J.lattice R.lattice)
        _ = normIdeal J.space J.lattice ⊔
              normIdeal R.space R.lattice := normIdeal_orthogonalProduct
        _ = normIdeal J.space J.lattice := sup_eq_left.mpr hRleJ
        _ = normIdeal q L := hJnorm
    exact
      { toBinaryModularSplittingData :=
          { decomposition := pulled
            first_rank := hfirstRank
            first_modular := pulled.component_modular_of_ambient hmodular 0
            complement_modular := pulled.component_modular_of_ambient hmodular 1 }
        complement_normIdeal_eq := hcomplementNorm }

end NormPreservingBinaryModularSplittingData

end Lattice

end Bong
