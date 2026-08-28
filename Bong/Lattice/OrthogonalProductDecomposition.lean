/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanIsometry
import Bong.Lattice.Product
import Bong.Lattice.ModularSplitting
import Bong.QuadraticSpace.OrthogonalSum

/-!
# The coordinate decomposition of an orthogonal product lattice

The product lattice `L × M` has its canonical two-component orthogonal
decomposition by the left and right coordinate axes.  Both components are
bundled together with their exact integral isometries to the original
factors.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  (q : QuadraticSpace K V) (r : QuadraticSpace K W)
  (L : Lattice K V) (M : Lattice K W)

/-- The left coordinate axis in a product space. -/
def orthogonalProductLeftCarrier : Submodule K (V × W) :=
  { carrier := {z | z.2 = 0}
    zero_mem' := rfl
    add_mem' := by
      intro x y hx hy
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hx hy ⊢
      rw [hx, hy, add_zero]
    smul_mem' := by
      intro a x hx
      simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd] at hx ⊢
      rw [hx, smul_zero] }

/-- The right coordinate axis in a product space. -/
def orthogonalProductRightCarrier : Submodule K (V × W) :=
  { carrier := {z | z.1 = 0}
    zero_mem' := rfl
    add_mem' := by
      intro x y hx hy
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hx hy ⊢
      rw [hx, hy, add_zero]
    smul_mem' := by
      intro a x hx
      simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd] at hx ⊢
      rw [hx, smul_zero] }

/-- The left factor is linearly equivalent to the left coordinate axis. -/
def orthogonalProductLeftCarrierEquiv :
    V ≃ₗ[K] orthogonalProductLeftCarrier (K := K) (V := V) (W := W) where
  toFun x := ⟨(x, 0), rfl⟩
  invFun z := (z : V × W).1
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact z.property.symm
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp
  map_smul' a x := by
    apply Subtype.ext
    ext <;> simp

/-- The right factor is linearly equivalent to the right coordinate axis. -/
def orthogonalProductRightCarrierEquiv :
    W ≃ₗ[K] orthogonalProductRightCarrier (K := K) (V := V) (W := W) where
  toFun y := ⟨(0, y), rfl⟩
  invFun z := (z : V × W).2
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.property.symm
    · rfl
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp
  map_smul' a x := by
    apply Subtype.ext
    ext <;> simp

private theorem orthogonalProductLeftCarrier_nondegenerate :
    ((q.orthogonalSum r).bilin.restrict
      (orthogonalProductLeftCarrier (K := K) (V := V) (W := W))).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    apply Prod.ext
    · apply q.nondegenerate.1 (x : V × W).1
      intro y
      have h := hx ⟨(y, 0), rfl⟩
      change q.bilin (x : V × W).1 y +
        r.bilin (x : V × W).2 0 = 0 at h
      simpa using h
    · exact x.property
  · intro x hx
    apply Subtype.ext
    apply Prod.ext
    · apply q.nondegenerate.2 (x : V × W).1
      intro y
      have h := hx ⟨(y, 0), rfl⟩
      change q.bilin y (x : V × W).1 +
        r.bilin 0 (x : V × W).2 = 0 at h
      simpa using h
    · exact x.property

private theorem orthogonalProductRightCarrier_nondegenerate :
    ((q.orthogonalSum r).bilin.restrict
      (orthogonalProductRightCarrier (K := K) (V := V) (W := W))).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    apply Prod.ext
    · exact x.property
    · apply r.nondegenerate.1 (x : V × W).2
      intro y
      have h := hx ⟨(0, y), rfl⟩
      change q.bilin (x : V × W).1 0 +
        r.bilin (x : V × W).2 y = 0 at h
      simpa using h
  · intro x hx
    apply Subtype.ext
    apply Prod.ext
    · exact x.property
    · apply r.nondegenerate.2 (x : V × W).2
      intro y
      have h := hx ⟨(0, y), rfl⟩
      change q.bilin 0 (x : V × W).1 +
        r.bilin y (x : V × W).2 = 0 at h
      simpa using h

/-- The left coordinate quadratic sublattice. -/
noncomputable def orthogonalProductLeftComponent :
    QuadraticSublattice (q.orthogonalSum r) where
  carrier := orthogonalProductLeftCarrier (K := K) (V := V) (W := W)
  nondegenerate := orthogonalProductLeftCarrier_nondegenerate q r
  lattice := map (orthogonalProductLeftCarrierEquiv
    (K := K) (V := V) (W := W)) L

/-- The right coordinate quadratic sublattice. -/
noncomputable def orthogonalProductRightComponent :
    QuadraticSublattice (q.orthogonalSum r) where
  carrier := orthogonalProductRightCarrier (K := K) (V := V) (W := W)
  nondegenerate := orthogonalProductRightCarrier_nondegenerate q r
  lattice := map (orthogonalProductRightCarrierEquiv
    (K := K) (V := V) (W := W)) M

/-- The left coordinate component is exactly the original left lattice. -/
noncomputable def orthogonalProductLeftComponentIsometry :
    Isometry q (orthogonalProductLeftComponent q r L).space L
      (orthogonalProductLeftComponent q r L).lattice where
  toLinearEquiv := by
    change V ≃ₗ[K] orthogonalProductLeftCarrier
      (K := K) (V := V) (W := W)
    exact orthogonalProductLeftCarrierEquiv
      (K := K) (V := V) (W := W)
  map_bilin x y := by
    change (q.orthogonalSum r).bilin
        (((orthogonalProductLeftCarrierEquiv
          (K := K) (V := V) (W := W)) x :
            orthogonalProductLeftCarrier) : V × W)
        (((orthogonalProductLeftCarrierEquiv
          (K := K) (V := V) (W := W)) y :
            orthogonalProductLeftCarrier) : V × W) = q.bilin x y
    change q.bilin x y + r.bilin 0 0 = q.bilin x y
    simp [QuadraticSpace.orthogonalSum_bilin_apply]
  map_mem x := by
    change x ∈ L ↔
      orthogonalProductLeftCarrierEquiv
        (K := K) (V := V) (W := W) x ∈
          map (orthogonalProductLeftCarrierEquiv
            (K := K) (V := V) (W := W)) L
    exact (map_mem_map_iff
      (orthogonalProductLeftCarrierEquiv
        (K := K) (V := V) (W := W)) L x).symm

/-- The right coordinate component is exactly the original right lattice. -/
noncomputable def orthogonalProductRightComponentIsometry :
    Isometry r (orthogonalProductRightComponent q r M).space M
      (orthogonalProductRightComponent q r M).lattice where
  toLinearEquiv := by
    change W ≃ₗ[K] orthogonalProductRightCarrier
      (K := K) (V := V) (W := W)
    exact orthogonalProductRightCarrierEquiv
      (K := K) (V := V) (W := W)
  map_bilin x y := by
    change (q.orthogonalSum r).bilin
        (((orthogonalProductRightCarrierEquiv
          (K := K) (V := V) (W := W)) x :
            orthogonalProductRightCarrier) : V × W)
        (((orthogonalProductRightCarrierEquiv
          (K := K) (V := V) (W := W)) y :
            orthogonalProductRightCarrier) : V × W) = r.bilin x y
    change q.bilin 0 0 + r.bilin x y = r.bilin x y
    simp [QuadraticSpace.orthogonalSum_bilin_apply]
  map_mem x := by
    change x ∈ M ↔
      orthogonalProductRightCarrierEquiv
        (K := K) (V := V) (W := W) x ∈
          map (orthogonalProductRightCarrierEquiv
            (K := K) (V := V) (W := W)) M
    exact (map_mem_map_iff
      (orthogonalProductRightCarrierEquiv
        (K := K) (V := V) (W := W)) M x).symm

/-- The canonical two-axis orthogonal decomposition of a product lattice. -/
noncomputable def orthogonalProductDecomposition :
    OrthogonalDecomposition (q.orthogonalSum r) (product L M) 2 := by
  let components : Fin 2 → QuadraticSublattice (q.orthogonalSum r) :=
    Fin.cases (orthogonalProductLeftComponent q r L)
      (fun _ ↦ orthogonalProductRightComponent q r M)
  exact {
    component := components
    orthogonal := by
      intro i j hij x y
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · change q.bilin (x : V × W).1 (y : V × W).1 +
          r.bilin (x : V × W).2 (y : V × W).2 = 0
        have hx : (x : V × W).2 = 0 := by
          have h := x.property
          change (x : V × W).2 = 0 at h
          exact h
        have hy : (y : V × W).1 = 0 := by
          have h := y.property
          change (y : V × W).1 = 0 at h
          exact h
        rw [hx, hy]
        simp
      · change q.bilin (x : V × W).1 (y : V × W).1 +
          r.bilin (x : V × W).2 (y : V × W).2 = 0
        have hx : (x : V × W).1 = 0 := by
          have h := x.property
          change (x : V × W).1 = 0 at h
          exact h
        have hy : (y : V × W).2 = 0 := by
          have h := y.property
          change (y : V × W).2 = 0 at h
          exact h
        rw [hx, hy]
        simp
      · exact (hij rfl).elim
    sum_eq := by
      apply le_antisymm
      · apply iSup_le
        rw [Fin.forall_fin_two]
        constructor
        · intro z hz
          rcases hz with ⟨x, hx, rfl⟩
          have hx' :
              (orthogonalProductLeftCarrierEquiv
                (K := K) (V := V) (W := W)).symm x ∈ L := by
            have hx0 := hx
            change x ∈ map (orthogonalProductLeftCarrierEquiv
              (K := K) (V := V) (W := W)) L at hx0
            exact (mem_map_iff
              (orthogonalProductLeftCarrierEquiv
                (K := K) (V := V) (W := W)) L x).1 hx0
          apply mem_product_iff.2
          constructor
          · simpa [orthogonalProductLeftCarrierEquiv] using hx'
          · let second : W :=
              (((Submodule.subtype (components 0).carrier).restrictScalars
                (IntegerRing K)) x).2
            change second ∈ M
            have hsecond : second = 0 := by
              change (x : V × W).2 = 0
              exact x.property
            rw [hsecond]
            exact M.zero_mem
        · intro z hz
          rcases hz with ⟨y, hy, rfl⟩
          have hy' :
              (orthogonalProductRightCarrierEquiv
                (K := K) (V := V) (W := W)).symm y ∈ M := by
            have hy0 := hy
            change y ∈ map (orthogonalProductRightCarrierEquiv
              (K := K) (V := V) (W := W)) M at hy0
            exact (mem_map_iff
              (orthogonalProductRightCarrierEquiv
                (K := K) (V := V) (W := W)) M y).1 hy0
          apply mem_product_iff.2
          constructor
          · let first : V :=
              (((Submodule.subtype (components 1).carrier).restrictScalars
                (IntegerRing K)) y).1
            change first ∈ L
            have hfirst : first = 0 := by
              change (y : V × W).1 = 0
              exact y.property
            rw [hfirst]
            exact L.zero_mem
          · simpa [orthogonalProductRightCarrierEquiv] using hy'
      · intro z hz
        have hz' := mem_product_iff.1 hz
        have hleft : (z.1, 0) ∈
            (orthogonalProductLeftComponent q r L).ambientSubmodule := by
          refine ⟨orthogonalProductLeftCarrierEquiv
            (K := K) (V := V) (W := W) z.1, ?_, ?_⟩
          · exact (map_mem_map_iff
            (orthogonalProductLeftCarrierEquiv
              (K := K) (V := V) (W := W)) L z.1).2 hz'.1
          · change
              ((orthogonalProductLeftCarrierEquiv
                (K := K) (V := V) (W := W) z.1 :
                  orthogonalProductLeftCarrier) : V × W) = (z.1, 0)
            rfl
        have hright : (0, z.2) ∈
            (orthogonalProductRightComponent q r M).ambientSubmodule := by
          refine ⟨orthogonalProductRightCarrierEquiv
            (K := K) (V := V) (W := W) z.2, ?_, ?_⟩
          · exact (map_mem_map_iff
            (orthogonalProductRightCarrierEquiv
              (K := K) (V := V) (W := W)) M z.2).2 hz'.2
          · change
              ((orthogonalProductRightCarrierEquiv
                (K := K) (V := V) (W := W) z.2 :
                  orthogonalProductRightCarrier) : V × W) = (0, z.2)
            rfl
        have hleft' : (z.1, 0) ∈ ⨆ i, (components i).ambientSubmodule :=
          (le_iSup (fun i : Fin 2 ↦ (components i).ambientSubmodule) 0) hleft
        have hright' : (0, z.2) ∈ ⨆ i, (components i).ambientSubmodule :=
          (le_iSup (fun i : Fin 2 ↦ (components i).ambientSubmodule) 1) hright
        convert Submodule.add_mem _ hleft' hright' using 1 <;> ext <;> simp }

@[simp]
theorem orthogonalProductDecomposition_component_zero :
    (orthogonalProductDecomposition q r L M).component 0 =
      orthogonalProductLeftComponent q r L :=
  rfl

@[simp]
theorem orthogonalProductDecomposition_component_one :
    (orthogonalProductDecomposition q r L M).component 1 =
      orthogonalProductRightComponent q r M :=
  rfl

end Lattice

end Bong
