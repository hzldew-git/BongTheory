/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionScale
import Bong.Lattice.OrthogonalDecompositionMerge

/-!
# Scale ideals of orthogonal products and amalgamated components

Orthogonality kills the mixed pairings, so the scale ideal of a product is
the supremum of the two scale ideals.  Transporting across the canonical
addition isometry gives the same formula for `orthogonalSup`.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The scale ideal of an orthogonal product is the supremum of the factor
scale ideals. -/
theorem scaleIdeal_orthogonalProduct :
    scaleIdeal (q.orthogonalSum r) (product L M) =
      scaleIdeal q L ⊔ scaleIdeal r M := by
  apply le_antisymm
  · apply scaleIdeal_le_of_bilin_mem (q.orthogonalSum r) (product L M)
    intro x y hx hy
    have hx' := mem_product_iff.mp hx
    have hy' := mem_product_iff.mp hy
    rw [QuadraticSpace.orthogonalSum_bilin_apply]
    exact (scaleIdeal q L ⊔ scaleIdeal r M).add_mem
      ((_root_.le_sup_left : scaleIdeal q L ≤
        scaleIdeal q L ⊔ scaleIdeal r M)
        (bilin_mem_scaleIdeal_of_mem q L hx'.1 hy'.1))
      ((_root_.le_sup_right : scaleIdeal r M ≤
        scaleIdeal q L ⊔ scaleIdeal r M)
        (bilin_mem_scaleIdeal_of_mem r M hx'.2 hy'.2))
  · apply _root_.sup_le
    · apply scaleIdeal_le_of_bilin_mem q L
      intro x y hx hy
      have hxProduct : (x, (0 : W)) ∈ product L M :=
        inl_mem_product_iff.mpr hx
      have hyProduct : (y, (0 : W)) ∈ product L M :=
        inl_mem_product_iff.mpr hy
      have hpair := bilin_mem_scaleIdeal_of_mem
        (q.orthogonalSum r) (product L M) hxProduct hyProduct
      simpa using hpair
    · apply scaleIdeal_le_of_bilin_mem r M
      intro x y hx hy
      have hxProduct : ((0 : V), x) ∈ product L M :=
        inr_mem_product_iff.mpr hx
      have hyProduct : ((0 : V), y) ∈ product L M :=
        inr_mem_product_iff.mpr hy
      have hpair := bilin_mem_scaleIdeal_of_mem
        (q.orthogonalSum r) (product L M) hxProduct hyProduct
      simpa using hpair

namespace OrthogonalDecomposition

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The scale ideal of two amalgamated orthogonal components is the supremum
of their scale ideals. -/
theorem scaleIdeal_orthogonalSup
    (D : OrthogonalDecomposition q L t) {i j : Fin t} (hij : i ≠ j) :
    scaleIdeal (D.orthogonalSup hij).space
        (D.orthogonalSup hij).lattice =
      scaleIdeal (D.component i).space (D.component i).lattice ⊔
        scaleIdeal (D.component j).space (D.component j).lattice := by
  let f := D.orthogonalSupLatticeIsometry hij
  calc
    scaleIdeal (D.orthogonalSup hij).space
        (D.orthogonalSup hij).lattice =
        scaleIdeal
          ((D.component i).space.orthogonalSum (D.component j).space)
          (product (D.component i).lattice (D.component j).lattice) := by
      exact scaleIdeal_map_isometry f.toQuadraticSpaceIsometry
        (product (D.component i).lattice (D.component j).lattice)
    _ = scaleIdeal (D.component i).space (D.component i).lattice ⊔
        scaleIdeal (D.component j).space (D.component j).lattice :=
      scaleIdeal_orthogonalProduct

/-- The scale ideal of a three-component orthogonal decomposition is the
iterated supremum of the component scale ideals. -/
theorem scaleIdeal_eq_sup_components_fin_three
    (D : OrthogonalDecomposition q L 3) :
    scaleIdeal q L =
      scaleIdeal (D.component 0).space (D.component 0).lattice ⊔
        scaleIdeal (D.component 1).space (D.component 1).lattice ⊔
          scaleIdeal (D.component 2).space (D.component 2).lattice := by
  let E := D.mergeAdjacent (0 : Fin 2)
  have h := E.scaleIdeal_eq_sup_components_fin_two
  change scaleIdeal q L =
      scaleIdeal (D.orthogonalSup (by decide : (0 : Fin 3) ≠ 1)).space
          (D.orthogonalSup (by decide : (0 : Fin 3) ≠ 1)).lattice ⊔
        scaleIdeal (D.component 2).space (D.component 2).lattice at h
  rw [D.scaleIdeal_orthogonalSup] at h
  exact h

end OrthogonalDecomposition

end Lattice

end Bong
