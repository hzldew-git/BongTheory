/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NormGroupRepresentation
import Bong.Lattice.OmearaSaturatedJordan

/-!
# Tails of saturated Jordan splittings

For a saturated splitting, deleting the first Jordan component shifts the
fundamental norm groups exactly by one index.  This is the invariant
inheritance used after the first components have been aligned in O'Meara
93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace JordanDecomposition

variable (J : JordanDecomposition q L (n + 1))

@[simp]
theorem tail_fundamentalScaleOrder (i : Fin n) :
    J.tail.fundamentalScaleOrder i = J.fundamentalScaleOrder i.succ :=
  rfl

/-- The intrinsic scale layer of the exact suffix embeds into the
corresponding intrinsic scale layer of the original lattice. -/
theorem coe_mem_fundamentalLattice_of_mem_tail
    (i : Fin n)
    (x : J.toOrthogonalDecomposition.suffixCarrier 1)
    (hx : x ∈ J.tail.fundamentalLattice i) :
    (x : V) ∈ J.fundamentalLattice i.succ := by
  let order := J.fundamentalScaleOrder i.succ
  let tailLayer := J.tail.scaleTruncationDecomposition order
  let fullLayer := J.scaleTruncationDecomposition order
  have hxLayer : x ∈ Lattice.scaleTruncation
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice
      order := by
    simpa only [fundamentalLattice, tail_fundamentalScaleOrder, order] using hx
  have hxSum : x ∈ ⨆ j : Fin n,
      (tailLayer.component j).ambientSubmodule := by
    rw [tailLayer.sum_eq]
    exact hxLayer
  have hxFull : (x : V) ∈ ⨆ k : Fin (n + 1),
      (fullLayer.component k).ambientSubmodule := by
    refine Submodule.iSup_induction
      (p := fun j : Fin n => (tailLayer.component j).ambientSubmodule)
      (motive := fun z => (z : V) ∈ ⨆ k : Fin (n + 1),
        (fullLayer.component k).ambientSubmodule)
      hxSum ?_ ?_ ?_
    · intro j z hz
      apply le_iSup
        (fun k : Fin (n + 1) => (fullLayer.component k).ambientSubmodule)
        j.succ
      have hfactor :
          J.tail.scaleTruncationFactor order j =
            J.scaleTruncationFactor order j.succ := rfl
      dsimp only [tailLayer] at hz
      rw [J.tail.scaleTruncationDecomposition_component, hfactor] at hz
      dsimp only [fullLayer]
      rw [J.scaleTruncationDecomposition_component]
      have hzNormalized : z ∈
          ((J.toOrthogonalDecomposition.tailComponent j).rescaleLattice
            (J.scaleTruncationFactor order j.succ)).ambientSubmodule := by
        simpa only [JordanDecomposition.tail_component] using hz
      simp only [QuadraticSublattice.mem_ambientSubmodule_iff,
        QuadraticSublattice.rescaleLattice_carrier,
        QuadraticSublattice.rescaleLattice_lattice] at hzNormalized
      rcases hzNormalized with ⟨z', hz', rfl⟩
      let g₀ := J.toOrthogonalDecomposition.tailComponentIsometry j
      let g := g₀.rescaleLattices (J.scaleTruncationFactor order j.succ)
      let y := g.toLinearEquiv.symm z'
      have hy : y ∈ Lattice.rescale
          (J.scaleTruncationFactor order j.succ)
          (J.component j.succ).lattice := by
        apply (g.map_mem (g.toLinearEquiv.symm z')).mpr
        rw [g.toLinearEquiv.apply_symm_apply]
        exact hz'
      refine ⟨y, hy, ?_⟩
      have hgy : g.toLinearEquiv y = z' :=
        g.toLinearEquiv.apply_symm_apply z'
      have hcoe := congrArg
        (fun z : J.toOrthogonalDecomposition.tailComponentCarrier j =>
          ((z.1 : J.toOrthogonalDecomposition.suffixCarrier 1) : V)) hgy
      exact
        (J.toOrthogonalDecomposition.coe_tailComponentEquiv j y).symm.trans hcoe
    · simp
    · intro y z hy hz
      simpa only [Submodule.coe_add] using
        (⨆ k : Fin (n + 1),
          (fullLayer.component k).ambientSubmodule).add_mem hy hz
  have hxTarget : (x : V) ∈ Lattice.scaleTruncation q L order := by
    change (x : V) ∈ (Lattice.scaleTruncation q L order).toSubmodule
    rw [← fullLayer.sum_eq]
    exact hxFull
  simpa only [fundamentalLattice, order] using hxTarget

/-- Integral inclusion of a suffix fundamental layer into the corresponding
fundamental layer of the full lattice. -/
noncomputable def tailFundamentalLatticeRepresentation (i : Fin n) :
    Representation
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space q
      (J.tail.fundamentalLattice i) (J.fundamentalLattice i.succ) :=
  QuadraticSublattice.inclusionRepresentation
    (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1)
    (J.tail.fundamentalLattice i) (J.fundamentalLattice i.succ)
    (fun x hx => J.coe_mem_fundamentalLattice_of_mem_tail i x hx)

/-- Therefore every suffix fundamental norm group is contained in the
corresponding full fundamental norm group. -/
theorem tail_fundamentalNormGroup_subset (i : Fin n) :
    J.tail.fundamentalNormGroup i ⊆ J.fundamentalNormGroup i.succ :=
  (J.tailFundamentalLatticeRepresentation i).normGroupSet_subset

/-- A displayed tail component embeds integrally into the intrinsic scale
layer in which it occurs without rescaling. -/
noncomputable def tailComponentFundamentalRepresentation (i : Fin n) :
    Representation (J.tail.component i).space
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
      (J.tail.component i).lattice (J.tail.fundamentalLattice i) := by
  apply QuadraticSublattice.inclusionRepresentation
    (J.tail.component i) (J.tail.component i).lattice
      (J.tail.fundamentalLattice i)
  intro x hx
  let layer := J.tail.scaleTruncationDecomposition
    (J.tail.fundamentalScaleOrder i)
  have hxComponent : (x.1 :
      J.toOrthogonalDecomposition.suffixCarrier 1) ∈
      (layer.component i).ambientSubmodule := by
    have hcomponent : layer.component i = J.tail.component i := by
      simpa only [layer, fundamentalScaleOrder] using
        J.tail.scaleTruncationDecomposition_component_self i
    rw [hcomponent]
    exact ⟨x, hx, rfl⟩
  have hxSum : (x.1 :
      J.toOrthogonalDecomposition.suffixCarrier 1) ∈
      ⨆ j, (layer.component j).ambientSubmodule :=
    le_iSup (fun j => (layer.component j).ambientSubmodule) i hxComponent
  change (x.1 :
      J.toOrthogonalDecomposition.suffixCarrier 1) ∈
    (Lattice.scaleTruncation
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice
      (J.tail.fundamentalScaleOrder i)).toSubmodule
  rw [← layer.sum_eq]
  exact hxSum

theorem tail_componentNormGroup_subset_fundamental (i : Fin n) :
    normGroupSet (J.tail.component i).space (J.tail.component i).lattice ⊆
      J.tail.fundamentalNormGroup i :=
  (J.tailComponentFundamentalRepresentation i).normGroupSet_subset

namespace IsSaturated

/-- Saturation is inherited by the exact suffix Jordan splitting. -/
theorem tail (hJ : J.IsSaturated) : J.tail.IsSaturated := by
  intro i
  apply Set.Subset.antisymm
  · exact J.tail_componentNormGroup_subset_fundamental i
  · intro z hz
    have hzFull : z ∈ J.fundamentalNormGroup i.succ :=
      J.tail_fundamentalNormGroup_subset i hz
    have hzComponent : z ∈
        normGroupSet (J.component i.succ).space
          (J.component i.succ).lattice := by
      rw [hJ i.succ]
      exact hzFull
    let g := J.toOrthogonalDecomposition.tailComponentIsometry i
    have hgroup := normGroupSet_eq_of_latticeIsometry g
    change z ∈ normGroupSet
      (J.toOrthogonalDecomposition.tailComponent i).space
      (J.toOrthogonalDecomposition.tailComponent i).lattice
    rw [hgroup]
    exact hzComponent

/-- In a saturated splitting, deleting the head shifts each fundamental
norm group literally by one index. -/
theorem tail_fundamentalNormGroup_eq (hJ : J.IsSaturated) (i : Fin n) :
    J.tail.fundamentalNormGroup i = J.fundamentalNormGroup i.succ := by
  calc
    J.tail.fundamentalNormGroup i =
        normGroupSet (J.tail.component i).space
          (J.tail.component i).lattice := (tail J hJ i).symm
    _ = normGroupSet (J.component i.succ).space
          (J.component i.succ).lattice :=
      normGroupSet_eq_of_latticeIsometry
        (J.toOrthogonalDecomposition.tailComponentIsometry i)
    _ = J.fundamentalNormGroup i.succ := hJ i.succ

end IsSaturated

namespace SameFundamentalType

variable {r : QuadraticSpace K W} {M : Lattice K W}
  {J : JordanDecomposition q L (n + 1)}
  {H : JordanDecomposition r M (n + 1)}

/-- Equal fundamental type passes to exact suffixes of saturated Jordan
splittings.  The index equivalence is the literal identity after the common
head has been deleted. -/
noncomputable def tail (F : SameFundamentalType J H)
    (hJ : J.IsSaturated) (hH : H.IsSaturated) :
    SameFundamentalType J.tail H.tail where
  indexEquiv := Equiv.refl (Fin n)
  index_val := fun _ => rfl
  componentRank_eq := by
    intro i
    rw [J.tail_componentRank, H.tail_componentRank]
    have h := F.componentRank_eq i.succ
    rw [F.indexEquiv_apply_eq_self] at h
    exact h
  scaleOrder_eq := by
    intro i
    rw [J.tail_fundamentalScaleOrder, H.tail_fundamentalScaleOrder]
    have h := F.scaleOrder_eq i.succ
    rw [F.indexEquiv_apply_eq_self] at h
    exact h
  normGroup_eq := by
    intro i
    calc
      H.tail.fundamentalNormGroup i =
          H.fundamentalNormGroup i.succ :=
        IsSaturated.tail_fundamentalNormGroup_eq H hH i
      _ = J.fundamentalNormGroup i.succ := by
        have h := F.normGroup_eq i.succ
        rw [F.indexEquiv_apply_eq_self] at h
        exact h
      _ = J.tail.fundamentalNormGroup i :=
        (IsSaturated.tail_fundamentalNormGroup_eq J hJ i).symm

end SameFundamentalType

end JordanDecomposition

end Lattice

end Bong
