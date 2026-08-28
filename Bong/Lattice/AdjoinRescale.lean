/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.AdjoinVector
import Bong.Lattice.BasisUnits
import Bong.Lattice.DeterminantBasis
import Bong.Lattice.DVRFactorization
import Bong.Lattice.Modular

/-!
# Rescaling a one-vector lattice enlargement

This file records the elementary lattice sandwich used in Beli (2019),
Lemma 5.1.  If `x` is integral, adjoining `π⁻¹x` enlarges a lattice by at
most one residue-field coordinate, and multiplication by `π` returns to the
original lattice.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Coordinate multipliers that divide one chosen basis vector by the
uniformizer. -/
noncomputable def uniformizerInvScaleUnitsAt
    {ι : Type w} [DecidableEq ι] (i : ι) : ι → Kˣ :=
  Function.update (fun _ ↦ 1) i (uniformizerUnit K)⁻¹

/-- Divide one vector of an arbitrarily indexed finite basis by the
uniformizer. -/
noncomputable def uniformizerInvScaleBasisAt
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (b : Basis ι K V) (i : ι) : Basis ι K V :=
  b.unitsSMul (uniformizerInvScaleUnitsAt (K := K) i)

@[simp]
theorem uniformizerInvScaleBasisAt_apply_same
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (b : Basis ι K V) (i : ι) :
    uniformizerInvScaleBasisAt b i i =
      (((uniformizerUnit K)⁻¹ : Kˣ) : K) • b i := by
  rw [uniformizerInvScaleBasisAt, Basis.unitsSMul_apply]
  simp [uniformizerInvScaleUnitsAt, Function.update, Units.smul_def]

@[simp]
theorem uniformizerInvScaleBasisAt_apply_of_ne
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (b : Basis ι K V) {i j : ι} (hji : j ≠ i) :
    uniformizerInvScaleBasisAt b i j = b j := by
  rw [uniformizerInvScaleBasisAt, Basis.unitsSMul_apply]
  simp [uniformizerInvScaleUnitsAt, Function.update, hji]

/-- Dividing one vector of any finite basis by the uniformizer gives exactly
the corresponding one-vector lattice enlargement. -/
theorem adjoin_basisLattice_uniformizerInv_eq
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (b : Basis ι K V) (i : ι) :
    adjoinVector (basisLattice b)
        ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b i) =
      basisLattice (uniformizerInvScaleBasisAt b i) := by
  classical
  apply Lattice.ext
  apply le_antisymm
  · apply adjoinVector_le
    · change Submodule.span (IntegerRing K) (Set.range b) ≤
        Submodule.span (IntegerRing K)
          (Set.range (uniformizerInvScaleBasisAt b i))
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hji : j = i
      · subst j
        have hmem := (Submodule.span (IntegerRing K)
          (Set.range (uniformizerInvScaleBasisAt b i))).smul_mem
            (uniformizerInteger K) (Submodule.subset_span ⟨i, rfl⟩)
        rw [uniformizerInvScaleBasisAt_apply_same] at hmem
        change uniformizer K •
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b i) ∈ _ at hmem
        simpa [smul_smul, uniformizer_ne_zero K] using hmem
      · rw [← uniformizerInvScaleBasisAt_apply_of_ne b hji]
        exact Submodule.subset_span ⟨j, rfl⟩
    · rw [← uniformizerInvScaleBasisAt_apply_same b i]
      exact Submodule.subset_span ⟨i, rfl⟩
  · change Submodule.span (IntegerRing K)
        (Set.range (uniformizerInvScaleBasisAt b i)) ≤
      (adjoinVector (basisLattice b)
        ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b i)).toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      rw [uniformizerInvScaleBasisAt_apply_same]
      exact mem_adjoinVector _ _
    · rw [uniformizerInvScaleBasisAt_apply_of_ne _ hji]
      exact le_adjoinVector _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- In rank one, adjoining the divided basis vector is exactly global inverse
uniformizer rescaling. -/
theorem adjoin_basisLattice_uniformizerInv_fin_one_eq_rescale
    (b : Basis (Fin 1) K V) :
    adjoinVector (basisLattice b)
        ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b 0) =
      rescale (uniformizerUnit K)⁻¹ (basisLattice b) := by
  rw [adjoin_basisLattice_uniformizerInv_eq,
    rescale_basisLattice]
  congr 1
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rw [uniformizerInvScaleBasisAt_apply_same, Basis.smul_apply]
  rfl

/-- Dividing one coordinate of any finite basis lowers the volume order by
exactly two. -/
theorem volumeOrder_basisLattice_uniformizerInvScaleBasisAt
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V) (i : ι) :
    volumeOrder q (basisLattice (uniformizerInvScaleBasisAt b i)) =
      volumeOrder q (basisLattice b) - 2 := by
  let e : ι ≃ Fin (finrank K V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  let bFin : Basis (Fin (finrank K V)) K V := b.reindex e
  let cFin : Basis (Fin (finrank K V)) K V :=
    (uniformizerInvScaleBasisAt b i).reindex e
  have hb : basisLattice bFin = basisLattice b := basisLattice_reindex b e
  have hc : basisLattice cFin =
      basisLattice (uniformizerInvScaleBasisAt b i) :=
    basisLattice_reindex (uniformizerInvScaleBasisAt b i) e
  have hdet := basisGramDeterminant_changeBasis q bFin cFin
  have hmatrix : Matrix.det (bFin.toMatrix cFin) =
      (((uniformizerUnit K)⁻¹ : Kˣ) : K) := by
    rw [← Basis.det_apply]
    let a := uniformizerInvScaleUnitsAt (K := K) i
    have hcb : cFin = (b.unitsSMul a).reindex e := rfl
    have hreindex : (b.unitsSMul a).reindex e =
        bFin.unitsSMul (a ∘ e.symm) := by
      ext j
      simp [bFin, Basis.unitsSMul_apply]
    rw [hcb, hreindex]
    have hprod := bFin.det_unitsSMul_self (a ∘ e.symm)
    rw [hprod]
    change ∏ j, (((a (e.symm j) : Kˣ) : K)) =
      (((uniformizerUnit K)⁻¹ : Kˣ) : K)
    have hprodReindex :
        (∏ j : Fin (finrank K V), (((a (e.symm j) : Kˣ) : K))) =
          ∏ j : ι, (((a j : Kˣ) : K)) := by
      exact Equiv.prod_comp e.symm (fun j : ι ↦ ((a j : Kˣ) : K))
    rw [hprodReindex]
    have ha : (fun j ↦ ((a j : Kˣ) : K)) =
        Function.update (fun _ ↦ (1 : K)) i
          (((uniformizerUnit K)⁻¹ : Kˣ) : K) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [a, uniformizerInvScaleUnitsAt, Function.update]
      · simp [a, uniformizerInvScaleUnitsAt, Function.update, hji]
    rw [ha, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  apply WithTop.coe_injective
  rw [← hc, ← hb]
  have hleft := coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant q cFin
  have hright := coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant q bFin
  have hsub :
      ((volumeOrder q (basisLattice bFin) - 2 : Int) : WithTop Int) =
        (volumeOrder q (basisLattice bFin) : WithTop Int) -
          ((2 : Int) : WithTop Int) :=
    rfl
  have hinv : ord K (((uniformizerUnit K)⁻¹ : Kˣ) : K) =
      ((-1 : Int) : WithTop Int) := by
    rw [← coe_ordUnit, ordUnit_inv]
    have hpi : ordUnit K (uniformizerUnit K) = 1 := by
      simpa [uniformizerPowerUnit] using
        (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
    rw [hpi]
  rw [hleft, hsub, hright, hdet, hmatrix, ord_mul, ord_pow, hinv]
  rw [sub_eq_add_neg]
  norm_num

/-- If an integral vector is divided by the uniformizer and adjoined, then
rescaling the enlarged lattice by the uniformizer lands back in the original
lattice. -/
theorem rescale_uniformizer_adjoin_uniformizerInv_smul_le
    (L : Lattice K V) {x : V} (hx : x ∈ L) :
    rescale (uniformizerUnit K)
        (adjoinVector L ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • x)) ≤ L := by
  intro z hz
  change z ∈ rescale (uniformizerUnit K)
      (adjoinVector L ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • x)) at hz
  rw [mem_rescale_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [mem_adjoinVector_iff] at hy
  obtain ⟨w, hw, c, rfl⟩ := hy
  have hwScaled : ((uniformizerUnit K : Kˣ) : K) • w ∈ L := by
    have hmem := L.smul_mem (uniformizerInteger K) hw
    have heq : (uniformizerInteger K) • w =
        ((uniformizerUnit K : Kˣ) : K) • w := by
      rw [← IsScalarTower.algebraMap_smul K (uniformizerInteger K) w]
      change uniformizer K • w = uniformizer K • w
      rfl
    rwa [heq] at hmem
  have hcx : c • x ∈ L := L.smul_mem c hx
  have hscalar :
      ((uniformizerUnit K : Kˣ) : K) •
          (c • ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • x)) = c • x := by
    rw [← IsScalarTower.algebraMap_smul K c]
    change uniformizer K •
        ((c : K) • ((uniformizer K)⁻¹ • x)) = (c : K) • x
    rw [smul_smul, mul_comm (uniformizer K) (c : K),
      smul_smul, mul_assoc]
    simp [uniformizer_ne_zero K]
  rw [smul_add, hscalar]
  exact L.add_mem hwScaled hcx

end Lattice

end Bong
