/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DeterminantBasis
import Bong.Lattice.SmithPowerBasis
import Bong.Bong.Beli2019SectionFive

/-!
# Coordinate construction of index-uniformizer inclusions

Multiplying one vector of an ambient basis by the selected uniformizer gives
a sublattice of index `\mathfrak p`.  The determinant calculation below proves
directly that its volume order rises by two, so the construction produces the
literal `Beli2019IndexPInclusion` required by Section 5.
-/

namespace Bong.Lattice

open Module
open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The coordinatewise units that multiply only coordinate `i` by the
selected uniformizer. -/
noncomputable def coordinateScaleUnits
    (i : Fin (finrank K V)) : Fin (finrank K V) → Kˣ :=
  Function.update (fun _ => 1) i (uniformizerUnit K)

/-- Multiply one vector of a field basis by the selected uniformizer. -/
noncomputable def coordinateScaleBasis
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    Basis (Fin (finrank K V)) K V :=
  b.unitsSMul (coordinateScaleUnits (K := K) i)

@[simp]
theorem coordinateScaleBasis_apply_same
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    coordinateScaleBasis b i i = uniformizer K • b i := by
  rw [coordinateScaleBasis, Basis.unitsSMul_apply]
  simp [coordinateScaleUnits, Function.update, Units.smul_def,
    coe_uniformizerUnit]

@[simp]
theorem coordinateScaleBasis_apply_of_ne
    (b : Basis (Fin (finrank K V)) K V) {i j : Fin (finrank K V)}
    (hji : j ≠ i) :
    coordinateScaleBasis b i j = b j := by
  rw [coordinateScaleBasis, Basis.unitsSMul_apply]
  simp [coordinateScaleUnits, Function.update, hji]

/-- Scaling one coordinate by the uniformizer gives a sublattice. -/
theorem basisLattice_coordinateScaleBasis_le
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    basisLattice (coordinateScaleBasis b i) ≤ basisLattice b := by
  classical
  change Submodule.span (IntegerRing K)
      (Set.range (coordinateScaleBasis b i)) ≤
    Submodule.span (IntegerRing K) (Set.range b)
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  by_cases hji : j = i
  · subst j
    rw [coordinateScaleBasis_apply_same]
    have hmem := (Submodule.span (IntegerRing K) (Set.range b)).smul_mem
      (uniformizerInteger K) (Submodule.subset_span ⟨i, rfl⟩)
    change uniformizer K • b i ∈
      Submodule.span (IntegerRing K) (Set.range b) at hmem
    exact hmem
  · rw [coordinateScaleBasis_apply_of_ne b hji]
    exact Submodule.subset_span ⟨j, rfl⟩

/-- The one-coordinate operation multiplies the Gram determinant by the
square of the uniformizer. -/
theorem basisGramDeterminant_coordinateScaleBasis
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    basisGramDeterminant q (coordinateScaleBasis b i) =
      basisGramDeterminant q b * uniformizer K ^ 2 := by
  rw [basisGramDeterminant_changeBasis q b]
  congr 2
  have hdet := b.det_unitsSMul_self (coordinateScaleUnits (K := K) i)
  change Matrix.det (b.toMatrix (coordinateScaleBasis b i)) =
    uniformizer K
  rw [← Basis.det_apply]
  rw [show coordinateScaleBasis b i =
      b.unitsSMul (coordinateScaleUnits (K := K) i) by rfl]
  rw [hdet]
  change ∏ j, ((coordinateScaleUnits (K := K) i j : Kˣ) : K) =
    uniformizer K
  have hfun :
      (fun j => ((coordinateScaleUnits (K := K) i j : Kˣ) : K)) =
        Function.update (fun _ => (1 : K)) i (uniformizer K) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [coordinateScaleUnits, Function.update,
        coe_uniformizerUnit]
    · simp [coordinateScaleUnits, Function.update, hji]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

/-- A coordinate scaling raises the lattice volume order by exactly two. -/
theorem volumeOrder_basisLattice_coordinateScaleBasis
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    volumeOrder q (basisLattice (coordinateScaleBasis b i)) =
      volumeOrder q (basisLattice b) + 2 := by
  apply WithTop.coe_injective
  change (volumeOrder q
      (basisLattice (coordinateScaleBasis b i)) : WithTop Int) =
    (volumeOrder q (basisLattice b) : WithTop Int) + 2
  rw [coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant,
    coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant,
    basisGramDeterminant_coordinateScaleBasis, ord_mul, ord_pow,
    ord_uniformizer]
  norm_num

/-- The one-coordinate basis operation is a literal Section 5
index-`\mathfrak p` inclusion. -/
theorem indexPInclusion_coordinateScaleBasis
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    Beli2019IndexPInclusion q (basisLattice b)
      (basisLattice (coordinateScaleBasis b i)) where
  lattice_le := basisLattice_coordinateScaleBasis_le b i
  volumeOrder_eq := volumeOrder_basisLattice_coordinateScaleBasis q b i

end Bong.Lattice
