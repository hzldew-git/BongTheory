/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714NonNormProduct
import Bong.Lattice.NormGeneratorIsometry

/-!
# Beli (2019), Lemma 7.14(ii): transport back to the original lattice

The split-model calculation `M' = \mathfrak pJ ⊥ T` is invariant under the
actual two-block lattice isometry.  This file packages the resulting literal
isometry from the rescaled product to the non-norm-generator lattice in the
original ambient quadratic space.
-/

namespace Bong

open Dyadic

universe u v w z

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K Z}
  {J : Lattice K V} {T : Lattice K W} {M : Lattice K Z}

/-- The norm ideal `p^R` of the split product transports to the original
target lattice. -/
theorem normIdeal_eq_powerIdeal_of_orthogonalProduct_isometry
    (R : Int) (hnormJ : normIdeal q J = powerIdeal (K := K) R)
    (hnormT : normIdeal r T ≤ powerIdeal (K := K) (R + 1))
    (f : Isometry (q.orthogonalSum r) s (product J T) M) :
    normIdeal s M = powerIdeal (K := K) R := by
  calc
    normIdeal s M =
        normIdeal s (map f.toLinearEquiv (product J T)) :=
      congrArg (normIdeal s) f.map_eq.symm
    _ = normIdeal (q.orthogonalSum r) (product J T) :=
      normIdeal_map_isometry f.toQuadraticSpaceIsometry (product J T)
    _ = powerIdeal (K := K) R :=
      normIdeal_orthogonalProduct_eq_powerIdeal R hnormJ hnormT

/-- The actual isometry `J ⊥ T ≃ M` restricts to an isometry
`pJ ⊥ T ≃ M'`, where `M'` is the concrete non-norm-generator lattice. -/
noncomputable def rescaledLeftProductToNonNormIsometry
    (R : Int) (hnormJ : normIdeal q J = powerIdeal (K := K) R)
    (hnormT : normIdeal r T ≤ powerIdeal (K := K) (R + 1))
    (hprimitive : EveryPrimitiveIsNormGenerator q J)
    (f : Isometry (q.orthogonalSum r) s (product J T) M)
    (hscale : scaleIdeal s M ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1)) :
    Isometry (q.orthogonalSum r) s
      (product (rescale (uniformizerUnit K) J) T)
      (nonNormGeneratorLattice R
        (normIdeal_eq_powerIdeal_of_orthogonalProduct_isometry
          R hnormJ hnormT f) hscale) where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := f.map_bilin
  map_mem z := by
    let hnormM :=
      normIdeal_eq_powerIdeal_of_orthogonalProduct_isometry
        R hnormJ hnormT f
    have hpiLe : rescale (uniformizerUnit K) J ≤ J := by
      apply rescale_le_self_of_mem_integerRing
      rw [coe_uniformizerUnit, mem_integerRing_iff, Dyadic.IsIntegral,
        ord_uniformizer]
      norm_num
    constructor
    · intro hzScaled
      have hzScaled' := mem_product_iff.mp hzScaled
      have hzProduct : z ∈ product J T :=
        mem_product_iff.mpr ⟨hpiLe hzScaled'.1, hzScaled'.2⟩
      rw [mem_nonNormGeneratorLattice_iff]
      refine ⟨(f.map_mem z).1 hzProduct, ?_⟩
      intro htargetGenerator
      have hproductGenerator :
          IsNormGenerator (q.orthogonalSum r) (product J T) z :=
        (isNormGenerator_map_iff f z).1 htargetGenerator
      exact
        (not_isNormGenerator_orthogonalProduct_iff_left_mem_rescale
          R hnormJ hnormT hprimitive z hzProduct).2 hzScaled'.1
          hproductGenerator
    · intro htarget
      rw [mem_nonNormGeneratorLattice_iff] at htarget
      have hzProduct : z ∈ product J T :=
        (f.map_mem z).2 htarget.1
      have hproductNotGenerator :
          ¬IsNormGenerator (q.orthogonalSum r) (product J T) z := by
        intro hproductGenerator
        exact htarget.2 ((isNormGenerator_map_iff f z).2 hproductGenerator)
      have hxScaled :=
        (not_isNormGenerator_orthogonalProduct_iff_left_mem_rescale
          R hnormJ hnormT hprimitive z hzProduct).1
          hproductNotGenerator
      exact mem_product_iff.mpr
        ⟨hxScaled, (mem_product_iff.mp hzProduct).2⟩

end Lattice

end Bong
