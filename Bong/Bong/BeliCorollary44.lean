/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma43
import Bong.Bong.SegmentTransport

/-!
# Beli (2003), Corollary 4.4

The lattice equalities in Corollary 4.4 are represented by actual two- and
three-component orthogonal decompositions whose components are consecutive
BONG segment witnesses.  The scale formula is stated using twice the scale
order, so the displayed half-sum is encoded exactly over `Int`.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace BONG.SegmentWitness

variable {b : BONG V q L n} {start length : Nat}
  {bound : start + length ≤ n}

/-- A segment witness regarded as a quadratic sublattice of the ambient space. -/
noncomputable def toQuadraticSublattice
    (w : BONG.SegmentWitness b start length bound) :
    Lattice.QuadraticSublattice q where
  carrier := w.carrier
  nondegenerate := w.nondegenerate
  lattice := w.lattice

@[simp]
theorem toQuadraticSublattice_carrier
    (w : BONG.SegmentWitness b start length bound) :
    w.toQuadraticSublattice.carrier = w.carrier :=
  rfl

end BONG.SegmentWitness

namespace BONG

/-- A split of a BONG lattice into its first `cut` and remaining vectors. -/
structure TwoBlockSplitWitness (b : BONG V q L n) (cut : Nat)
    (hcut : cut ≤ n) where
  /-- The initial consecutive segment. -/
  left : SegmentWitness b 0 cut (by omega)
  /-- The remaining consecutive segment. -/
  right : SegmentWitness b cut (n - cut) (by omega)
  /-- The corresponding two-component orthogonal decomposition of `L`. -/
  decomposition : Lattice.OrthogonalDecomposition q L 2
  /-- Its first component is the initial segment lattice. -/
  component_zero :
    decomposition.component 0 = left.toQuadraticSublattice
  /-- Its second component is the remaining segment lattice. -/
  component_one :
    decomposition.component 1 = right.toQuadraticSublattice

/-- The canonical two-block split at cut zero.  Its first component is the
zero-dimensional segment and its second component is the entire BONG
lattice.  This boundary constructor is unconditional: no order comparison
or Corollary 4.4 hypothesis is needed. -/
noncomputable def zeroTwoBlockSplitWitness (b : BONG V q L n) :
    TwoBlockSplitWitness b 0 (Nat.zero_le n) := by
  let left := b.segmentWitness 0 0 (by omega)
  let right := SegmentWitness.whole b
  let leftComponent := left.toQuadraticSublattice
  let rightComponent := right.toQuadraticSublattice
  let component : Fin 2 → Lattice.QuadraticSublattice q :=
    fun i ↦ Fin.cases leftComponent (fun _ ↦ rightComponent) i
  have hleftCarrier : left.carrier = ⊥ := by
    rw [left.carrier_eq_segmentCarrier]
    simp [BONG.segmentCarrier]
  have hrightAmbient : rightComponent.ambientSubmodule = L.toSubmodule := by
    change (SegmentWitness.whole b).toQuadraticSublattice.ambientSubmodule =
      L.toSubmodule
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      let f := SegmentWitness.wholeLatticeIsometry b
      have hy' : y ∈ (SegmentWitness.whole b).lattice := hy
      have hmem : f.toLinearEquiv.symm y ∈ L :=
        (f.map_mem (f.toLinearEquiv.symm y)).2 (by simpa using hy')
      have hcoe : f.toLinearEquiv.symm y = (y : V) := rfl
      rwa [hcoe] at hmem
    · intro x hx
      let f := SegmentWitness.wholeLatticeIsometry b
      refine ⟨f.toLinearEquiv x, (f.map_mem x).1 hx, ?_⟩
      rfl
  let decomposition : Lattice.OrthogonalDecomposition q L 2 := {
    component := component
    orthogonal := by
      intro i j hij x y
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · have hxmem : (x : V) ∈ left.carrier := x.property
        have hx : (x : V) = 0 := by
          rw [hleftCarrier] at hxmem
          simpa using hxmem
        rw [hx]
        simp
      · have hymem : (y : V) ∈ left.carrier := y.property
        have hyzero : (y : V) = 0 := by
          rw [hleftCarrier] at hymem
          simpa using hymem
        rw [hyzero]
        simp
      · exact (hij rfl).elim
    sum_eq := by
      apply le_antisymm
      · apply iSup_le
        intro i
        fin_cases i
        · change leftComponent.ambientSubmodule ≤ L.toSubmodule
          intro x hx
          rcases hx with ⟨y, hy, rfl⟩
          have hymem : (y : V) ∈ left.carrier := y.property
          have hyzero : (y : V) = 0 := by
            rw [hleftCarrier] at hymem
            simpa using hymem
          change (y : V) ∈ L
          rw [hyzero]
          exact L.zero_mem
        · change rightComponent.ambientSubmodule ≤ L.toSubmodule
          exact le_of_eq hrightAmbient
      · calc
          L.toSubmodule = rightComponent.ambientSubmodule := hrightAmbient.symm
          _ ≤ ⨆ i, (component i).ambientSubmodule :=
            le_iSup (fun i ↦ (component i).ambientSubmodule) (1 : Fin 2)
  }
  exact {
    left := left
    right := right
    decomposition := decomposition
    component_zero := rfl
    component_one := rfl }

/-- The lattice splits orthogonally at the specified BONG cut. -/
def HasTwoBlockSplit (b : BONG V q L n) (cut : Nat)
    (hcut : cut ≤ n) : Prop :=
  Nonempty (TwoBlockSplitWitness b cut hcut)

/-- A split into the prefix, one adjacent binary pair, and the suffix. -/
structure ThreeBlockSplitWitness (b : BONG V q L n)
    (i : Fin n) (hi : i.1 + 1 < n) where
  /-- Vectors strictly before the selected pair. -/
  leftBlock : SegmentWitness b 0 i.1 (by omega)
  /-- The selected adjacent binary pair. -/
  pairBlock : SegmentWitness b i.1 2 (by omega)
  /-- Vectors strictly after the selected pair. -/
  rightBlock : SegmentWitness b (i.1 + 2) (n - (i.1 + 2)) (by omega)
  /-- The corresponding three-component orthogonal decomposition. -/
  decomposition : Lattice.OrthogonalDecomposition q L 3
  /-- The first component is the prefix lattice. -/
  component_zero :
    decomposition.component 0 = leftBlock.toQuadraticSublattice
  /-- The middle component is the selected binary lattice. -/
  component_one :
    decomposition.component 1 = pairBlock.toQuadraticSublattice
  /-- The last component is the suffix lattice. -/
  component_two :
    decomposition.component 2 = rightBlock.toQuadraticSublattice

/-- The lattice admits the three-block split centered on an adjacent pair. -/
def HasThreeBlockSplit (b : BONG V q L n)
    (i : Fin n) (hi : i.1 + 1 < n) : Prop :=
  Nonempty (ThreeBlockSplitWitness b i hi)

/-- The two adjacent positions belong to one component BONG. -/
def AdjacentPairIsOneComponent (b : BONG V q L n)
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (i : Fin n) (hi : i.1 + 1 < n) : Prop :=
  ∃ w : PutTogetherWitness b M.toOrthogonalDecomposition c,
    (w.indexEquiv i).1 =
      (w.indexEquiv ⟨i.1 + 1, hi⟩).1

/-- Good segment BONGs exist on both sides of a cut. -/
def HasGoodSegmentsAroundCut (b : BONG V q L n)
    (cut : Nat) (hcut : cut ≤ n) : Prop :=
  (∃ left : SegmentWitness b 0 cut (by omega), left.bong.IsGood) ∧
    ∃ right : SegmentWitness b cut (n - cut) (by omega),
      right.bong.IsGood

/-- The three boundary inequalities in Corollary 4.4(v), in zero-based form. -/
def BoundaryGoodConditions (b : BONG V q L n) (cut : Nat)
    (hleft : 2 ≤ cut) (hright : cut + 1 < n) : Prop :=
  b.order ⟨cut - 2, by omega⟩ ≤ b.order ⟨cut, by omega⟩ ∧
    b.order ⟨cut - 1, by omega⟩ ≤ b.order ⟨cut + 1, by omega⟩ ∧
      b.order ⟨cut - 1, by omega⟩ ≤ b.order ⟨cut, by omega⟩

end BONG

namespace Lattice

/-- The scale ideal has the specified doubled valuation order. -/
def HasDoubledScaleOrder (q : QuadraticSpace K V) (L : Lattice K V)
    (r₂ : Int) : Prop :=
  ∃ s : Kˣ,
    scaleIdeal q L = principalIdeal (K := K) (s : K) ∧
      2 * ordUnit K s = r₂

end Lattice

/-- The five decomposition assertions of Beli (2003), Corollary 4.4. -/
class BeliCorollary44Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  /-- Corollary 4.4(i). -/
  split_of_adjacentOrder_le
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n) :
    b.order i ≤ b.order ⟨i.1 + 1, hi⟩ →
      b.HasTwoBlockSplit (i.1 + 1) (by omega)
  /-- Corollary 4.4(ii). -/
  split_around_adjacentOrder_gt
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n) :
    b.order ⟨i.1 + 1, hi⟩ < b.order i →
      b.HasThreeBlockSplit i hi
  /-- Corollary 4.4(iii). -/
  adjacentOrder_gt_sameComponent
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}
    (b : BONG V q L n)
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (hconcat : b.IsPutTogether M.toOrthogonalDecomposition c)
    (i : Fin n) (hi : i.1 + 1 < n) :
    b.order ⟨i.1 + 1, hi⟩ < b.order i →
      b.AdjacentPairIsOneComponent M c i hi
  /-- Corollary 4.4(iv), without division by two in `Int`. -/
  firstScaleOrder
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 2)) (hgood : b.IsGood) :
    Lattice.HasDoubledScaleOrder q L
      (min (2 * b.order 0) (b.order 0 + b.order 1))
  /-- Corollary 4.4(v). -/
  glue_good_iff_boundary
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n cut : Nat}
    (b : BONG V q L n) (hleft : 2 ≤ cut)
    (hright : cut + 1 < n)
    (hsegments : b.HasGoodSegmentsAroundCut cut (by omega)) :
    (b.IsGood ∧ b.HasTwoBlockSplit cut (by omega)) ↔
      b.BoundaryGoodConditions cut hleft hright

namespace BONG

variable [BeliCorollary44Laws.{u, v} K]

/-- Beli (2003), Corollary 4.4(i). -/
theorem beliCorollary44_i (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n)
    (horder : b.order i ≤ b.order ⟨i.1 + 1, hi⟩) :
    b.HasTwoBlockSplit (i.1 + 1) (by omega) :=
  BeliCorollary44Laws.split_of_adjacentOrder_le b hgood i hi horder

/-- Beli (2003), Corollary 4.4(ii). -/
theorem beliCorollary44_ii (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n)
    (horder : b.order ⟨i.1 + 1, hi⟩ < b.order i) :
    b.HasThreeBlockSplit i hi :=
  BeliCorollary44Laws.split_around_adjacentOrder_gt b hgood i hi horder

/-- Beli (2003), Corollary 4.4(iii). -/
theorem beliCorollary44_iii (b : BONG V q L n)
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (hconcat : b.IsPutTogether M.toOrthogonalDecomposition c)
    (i : Fin n) (hi : i.1 + 1 < n)
    (horder : b.order ⟨i.1 + 1, hi⟩ < b.order i) :
    b.AdjacentPairIsOneComponent M c i hi :=
  BeliCorollary44Laws.adjacentOrder_gt_sameComponent
    b M c hconcat i hi horder

/-- Beli (2003), Corollary 4.4(iv). -/
theorem beliCorollary44_iv (b : BONG V q L (n + 2)) (hgood : b.IsGood) :
    Lattice.HasDoubledScaleOrder q L
      (min (2 * b.order 0) (b.order 0 + b.order 1)) :=
  BeliCorollary44Laws.firstScaleOrder b hgood

/-- Beli (2003), Corollary 4.4(v). -/
theorem beliCorollary44_v (b : BONG V q L n) (cut : Nat)
    (hleft : 2 ≤ cut) (hright : cut + 1 < n)
    (hsegments : b.HasGoodSegmentsAroundCut cut (by omega)) :
    (b.IsGood ∧ b.HasTwoBlockSplit cut (by omega)) ↔
      b.BoundaryGoodConditions cut hleft hright :=
  BeliCorollary44Laws.glue_good_iff_boundary
    b hleft hright hsegments

end BONG

end Bong
