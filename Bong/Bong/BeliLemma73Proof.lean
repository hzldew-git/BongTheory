/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma73
import Bong.Bong.BeliLemma73AdaptedVector
import Bong.Bong.BeliCorollary44Proof
import Bong.Bong.BeliCorollary44GlueProof
import Bong.Bong.BeliCorollary44ScaleProof
import Bong.Bong.BeliLemma319
import Bong.Bong.BeliLemma71Proof
import Bong.Bong.BeliLemma72Proof
import Bong.Bong.BeliLemmas48To410
import Bong.Bong.StructuralProof
import Bong.Lattice.AsymmetricBinaryModular
import Bong.Lattice.HyperbolicLatticeModular
import Bong.Lattice.HyperbolicLatticeInvariants
import Bong.Lattice.ModularSplitting
import Bong.Lattice.ModularVolume
import Bong.Lattice.NestedSublattice
import Bong.Lattice.OrthogonalDecompositionDeterminant
import Bong.Lattice.OrthogonalDecompositionCons
import Bong.Lattice.OrthogonalDecompositionMerge
import Bong.Lattice.OrthogonalSup
import Bong.Lattice.ScaledHyperbolicMaximalProof
import Bong.Bong.Beli2019VolumeOrders

/-!
# Proof of Beli (2003), Lemma 7.3

This file constructs the hyperbolic-plane splitting in both adjacent-order
branches, transports the construction to an arbitrary position, and supplies
the unconditional `BeliLemma73Laws` instance.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

noncomputable def lemma73InitialBinarySegment
    (b : BONG V q L 3) : SegmentWitness b 0 2 (by omega) :=
  b.segmentWitness 0 2 (by omega)

noncomputable def lemma73InitialBinary
    (b : BONG V q L 3) :
    BONG (b.lemma73InitialBinarySegment.carrier)
      (q.restrict b.lemma73InitialBinarySegment.carrier
        b.lemma73InitialBinarySegment.nondegenerate)
      b.lemma73InitialBinarySegment.lattice 2 :=
  b.lemma73InitialBinarySegment.bong

@[simp]
theorem lemma73InitialBinary_order_zero (b : BONG V q L 3) :
    b.lemma73InitialBinary.order 0 = b.order 0 := by
  change b.lemma73InitialBinarySegment.bong.order 0 = _
  rw [SegmentWitness.order_eq]
  congr 1

@[simp]
theorem lemma73InitialBinary_order_one (b : BONG V q L 3) :
    b.lemma73InitialBinary.order 1 = b.order 1 := by
  change b.lemma73InitialBinarySegment.bong.order 1 = _
  rw [SegmentWitness.order_eq]
  congr 1

@[simp]
theorem lemma73InitialBinary_binaryOrderGap (b : BONG V q L 3) :
    b.lemma73InitialBinary.binaryOrderGap = b.order 1 - b.order 0 := by
  unfold binaryOrderGap
  rw [b.lemma73InitialBinary_order_zero,
    b.lemma73InitialBinary_order_one]

@[simp]
theorem lemma73InitialBinary_binaryParameter (b : BONG V q L 3) :
    b.lemma73InitialBinary.binaryParameter =
      b.adjacentParameter 0 (by omega) := by
  unfold lemma73InitialBinary binaryParameter adjacentParameter
  apply congrArg₂ (fun x y : Kˣ ↦ x / y)
  · rw [SegmentWitness.valueUnit_eq]
    congr 1
  · rw [SegmentWitness.valueUnit_eq]
    congr 1

noncomputable def lemma73AdaptedVector
    (b : BONG V q L 3)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) : V :=
  (b.lemma73InitialBinary.binaryAdaptedShearAmbientVector D.coefficient :
    b.lemma73InitialBinarySegment.carrier)

/-- The order `R` to which the asymmetric Lemma 3.19 is applied. -/
noncomputable def lemma73PolarizationOrder
    (b : BONG V q L 3) : Int :=
  b.order 0 +
    (lemma73CentralDepth (K := K) (b.order 1 - b.order 0) : Nat)

theorem lemma73PolarizationOrder_eq
    (b : BONG V q L 3)
    (hEven : Even (b.order 1 - b.order 0))
    (hlower : -(2 * (ramificationIndex K : Int)) ≤
      b.order 1 - b.order 0) :
    b.lemma73PolarizationOrder =
      (b.order 0 + b.order 1) / 2 + ramificationIndex K := by
  rw [lemma73PolarizationOrder,
    lemma73CentralDepth_cast (K := K)
      (b.order 1 - b.order 0) hlower]
  rcases hEven with ⟨r, hr⟩
  omega

theorem lemma73PolarizationOrder_sub_e_eq
    (b : BONG V q L 3)
    (hEven : Even (b.order 1 - b.order 0))
    (hlower : -(2 * (ramificationIndex K : Int)) ≤
      b.order 1 - b.order 0) :
    b.lemma73PolarizationOrder - ramificationIndex K =
      (b.order 0 + b.order 1) / 2 := by
  rw [b.lemma73PolarizationOrder_eq hEven hlower]
  omega

theorem lemma73AdaptedVector_mixed_ne
    (b : BONG V q L 3)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) :
    q.bilin (b.ambientVector 0) (b.lemma73AdaptedVector D) ≠ 0 := by
  have hhead := b.lemma73InitialBinarySegment.ambientVector_eq (0 : Fin 2)
  change (b.lemma73InitialBinary.ambientVector 0 : V) =
    b.ambientVector 0 at hhead
  rw [← hhead, b.lemma73InitialBinary.ambientVector_zero_eq_head]
  exact D.mixed_ne

theorem lemma73AdaptedVector_mixed_order
    (b : BONG V q L 3)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) :
    ordUnit K (Units.mk0
      (q.bilin (b.ambientVector 0) (b.lemma73AdaptedVector D))
      (b.lemma73AdaptedVector_mixed_ne D)) =
      b.order 0 + (b.order 1 - b.order 0) / 2 := by
  have hhead := b.lemma73InitialBinarySegment.ambientVector_eq (0 : Fin 2)
  change (b.lemma73InitialBinary.ambientVector 0 : V) =
    b.ambientVector 0 at hhead
  have hfield :
      q.bilin (b.ambientVector 0) (b.lemma73AdaptedVector D) =
        (q.restrict b.lemma73InitialBinarySegment.carrier
          b.lemma73InitialBinarySegment.nondegenerate).bilin
          b.lemma73InitialBinary.head
          (b.lemma73InitialBinary.binaryAdaptedShearAmbientVector
            D.coefficient) := by
    rw [← hhead, b.lemma73InitialBinary.ambientVector_zero_eq_head]
    rfl
  let U : Kˣ := Units.mk0
    (q.bilin (b.ambientVector 0) (b.lemma73AdaptedVector D))
    (b.lemma73AdaptedVector_mixed_ne D)
  let W : Kˣ := Units.mk0
    ((q.restrict b.lemma73InitialBinarySegment.carrier
      b.lemma73InitialBinarySegment.nondegenerate).bilin
      b.lemma73InitialBinary.head
      (b.lemma73InitialBinary.binaryAdaptedShearAmbientVector
        D.coefficient)) D.mixed_ne
  have hUW : U = W := by
    apply Units.ext
    exact hfield
  change ordUnit K U = _
  rw [hUW]
  change ordUnit K W = _
  rw [show ordUnit K W =
      b.lemma73InitialBinary.order 0 +
        b.lemma73InitialBinary.binaryOrderGap / 2 from D.mixed_order]
  rw [b.lemma73InitialBinary_order_zero,
    b.lemma73InitialBinary_binaryOrderGap]

@[simp]
theorem quadratic_lemma73AdaptedVector
    (b : BONG V q L 3)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) :
    q.quadratic (b.lemma73AdaptedVector D) =
      (q.restrict b.lemma73InitialBinarySegment.carrier
        b.lemma73InitialBinarySegment.nondegenerate).quadratic
        (b.lemma73InitialBinary.binaryAdaptedShearAmbientVector
          D.coefficient) :=
  rfl

theorem ord_quadratic_lemma73AdaptedVector_ge
    (b : BONG V q L 3)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) :
    (b.lemma73PolarizationOrder : WithTop Int) ≤
      ord K (q.quadratic (b.lemma73AdaptedVector D)) := by
  rw [b.quadratic_lemma73AdaptedVector]
  have h := D.norm_order_ge
  rw [b.lemma73InitialBinary_order_zero,
    b.lemma73InitialBinary_binaryOrderGap] at h
  exact h

theorem ord_quadratic_lemma73AdaptedVector_gt_of_gap_zero
    (b : BONG V q L 3)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary)
    (hzero : b.order 1 - b.order 0 = 0) :
    (b.lemma73PolarizationOrder : WithTop Int) <
      ord K (q.quadratic (b.lemma73AdaptedVector D)) := by
  rw [b.quadratic_lemma73AdaptedVector]
  have hzero' : b.lemma73InitialBinary.binaryOrderGap = 0 := by
    rw [b.lemma73InitialBinary_binaryOrderGap, hzero]
  have h := D.norm_order_gt_of_gap_zero hzero'
  rw [b.lemma73InitialBinary_order_zero,
    b.lemma73InitialBinary_binaryOrderGap] at h
  exact h

/-- The endpoint approximation vector and its weak/strict norm bounds. -/
structure Lemma73EndpointVectorData (b : BONG V q L 3) where
  multiplier : Kˣ
  multiplier_order : ordUnit K multiplier = 0
  norm_order_ge :
    (b.lemma73PolarizationOrder : WithTop Int) ≤
      ord K (q.quadratic (b.lemma73EndpointVector multiplier))
  norm_order_gt_of_gap_neg : b.order 1 - b.order 0 < 0 →
    (b.lemma73PolarizationOrder : WithTop Int) <
      ord K (q.quadratic (b.lemma73EndpointVector multiplier))

/-- The two adjacent Lemma 7.2 criteria give the endpoint vector used in
the local ternary argument. -/
theorem exists_lemma73EndpointVectorData
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 - b.order 0 ≤ 0)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 0 (by omega)))
    (h₁ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 1 (by omega))) :
    Nonempty (Lemma73EndpointVectorData b) := by
  let p₀ := b.adjacentParameter 0 (by omega)
  let p₁ := b.adjacentParameter 1 (by omega)
  let G := b.order 1 - b.order 0
  have hG₀ : ordUnit K p₀ = G := by
    have h := b.ordUnit_adjacentParameter 0 (by omega)
    change ordUnit K p₀ = b.order 1 - b.order 0 at h
    exact h
  have hG₁ : ordUnit K p₁ = -G := by
    have h := b.ordUnit_adjacentParameter 1 (by omega)
    change ordUnit K p₁ = b.order 2 - b.order 1 at h
    rw [h, ← hendpoint]
    dsimp only [G]
    omega
  have hEven : Even G := by
    rw [← hG₀]
    exact h₀.1
  have hlower : -(2 * (ramificationIndex K : Int)) ≤ G := by
    have h := (b.adjacentParameter_isBinaryParameterAdmissible
      0 (by omega)).ordUnit_ge_neg_two_mul_e
    rw [hG₀] at h
    exact h
  rcases exists_lemma73EndpointMultiplier
      (K := K) p₀ p₁ G hG₀ hG₁ hEven hlower hupper h₀ h₁ with
    ⟨s, hsOrder, herror, herrorStrict⟩
  have hnorm :
      (b.lemma73PolarizationOrder : WithTop Int) ≤
        ord K (q.quadratic (b.lemma73EndpointVector s)) := by
    have h := b.ord_quadratic_lemma73EndpointVector_ge s
      (b.order 2)
      (lemma73CentralDepth (K := K) G : Nat)
      rfl herror
    rw [← hendpoint] at h
    exact h
  have hnormStrict : b.order 1 - b.order 0 < 0 →
      (b.lemma73PolarizationOrder : WithTop Int) <
        ord K (q.quadratic (b.lemma73EndpointVector s)) := by
    intro hneg
    have h := b.ord_quadratic_lemma73EndpointVector_gt s
      (b.order 2)
      (lemma73CentralDepth (K := K) G : Nat)
      rfl (herrorStrict hneg)
    rw [← hendpoint] at h
    exact h
  exact ⟨{
    multiplier := s
    multiplier_order := hsOrder
    norm_order_ge := hnorm
    norm_order_gt_of_gap_neg := hnormStrict }⟩

theorem bilin_last_lemma73AdaptedVector
    (b : BONG V q L 3)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) :
    q.bilin (b.ambientVector 2) (b.lemma73AdaptedVector D) = 0 := by
  let right := b.segmentWitness 2 1 (by omega)
  let z : right.carrier := right.bong.head
  have hz := right.ambientVector_eq (0 : Fin 1)
  change (right.bong.ambientVector 0 : V) = b.ambientVector 2 at hz
  rw [right.bong.ambientVector_zero_eq_head] at hz
  have horth := b.segmentCarriers_orthogonal 2 (by omega)
    (b.lemma73InitialBinary.binaryAdaptedShearAmbientVector D.coefficient) z
  rw [q.isSymm.eq]
  rw [← hz]
  exact horth

theorem bilin_lemma73EndpointVector_lemma73AdaptedVector
    (b : BONG V q L 3) (s : Kˣ)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) :
    q.bilin (b.lemma73EndpointVector s) (b.lemma73AdaptedVector D) =
      (s : K) *
        q.bilin (b.ambientVector 0) (b.lemma73AdaptedVector D) := by
  rw [lemma73EndpointVector, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.smul_left,
    b.bilin_last_lemma73AdaptedVector D, add_zero]

theorem bilin_lemma73EndpointVector_lemma73AdaptedVector_ne
    (b : BONG V q L 3) (s : Kˣ)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) :
    q.bilin (b.lemma73EndpointVector s) (b.lemma73AdaptedVector D) ≠ 0 := by
  rw [b.bilin_lemma73EndpointVector_lemma73AdaptedVector s D]
  exact mul_ne_zero (Units.ne_zero s)
    (b.lemma73AdaptedVector_mixed_ne D)

theorem lemma73AdaptedMixedOrder_eq_polarization_sub_e
    (b : BONG V q L 3)
    (hlower : -(2 * (ramificationIndex K : Int)) ≤
      b.order 1 - b.order 0) :
    b.order 0 + (b.order 1 - b.order 0) / 2 =
      b.lemma73PolarizationOrder - ramificationIndex K := by
  rw [lemma73PolarizationOrder,
    lemma73CentralDepth_cast (K := K)
      (b.order 1 - b.order 0) hlower]
  omega

theorem ordUnit_lemma73EndpointVector_lemma73AdaptedVector
    (b : BONG V q L 3)
    (E : Lemma73EndpointVectorData b)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary)
    (hlower : -(2 * (ramificationIndex K : Int)) ≤
      b.order 1 - b.order 0) :
    ordUnit K (Units.mk0
      (q.bilin (b.lemma73EndpointVector E.multiplier)
        (b.lemma73AdaptedVector D))
      (b.bilin_lemma73EndpointVector_lemma73AdaptedVector_ne
        E.multiplier D)) =
      b.lemma73PolarizationOrder - ramificationIndex K := by
  let base : Kˣ := Units.mk0
    (q.bilin (b.ambientVector 0) (b.lemma73AdaptedVector D))
    (b.lemma73AdaptedVector_mixed_ne D)
  let mixed : Kˣ := Units.mk0
    (q.bilin (b.lemma73EndpointVector E.multiplier)
      (b.lemma73AdaptedVector D))
    (b.bilin_lemma73EndpointVector_lemma73AdaptedVector_ne
      E.multiplier D)
  have hmixed : mixed = E.multiplier * base := by
    apply Units.ext
    exact b.bilin_lemma73EndpointVector_lemma73AdaptedVector
      E.multiplier D
  change ordUnit K mixed = _
  rw [hmixed, ordUnit_mul, E.multiplier_order, zero_add]
  change ordUnit K base = _
  rw [show ordUnit K base =
      b.order 0 + (b.order 1 - b.order 0) / 2 from
    b.lemma73AdaptedVector_mixed_order D]
  exact b.lemma73AdaptedMixedOrder_eq_polarization_sub_e hlower

/-- Either order of the endpoint and adapted vectors may be used in the
asymmetric Lemma 3.19; this predicate records that no third vector occurs. -/
def IsLemma73EndpointAdaptedOrdering
    (b : BONG V q L 3)
    (E : Lemma73EndpointVectorData b)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary)
    (x y : V) : Prop :=
  (x = b.lemma73EndpointVector E.multiplier ∧
      y = b.lemma73AdaptedVector D) ∨
    (x = b.lemma73AdaptedVector D ∧
      y = b.lemma73EndpointVector E.multiplier)

/-- Local ternary core of Beli (2003), Lemma 7.3 when the middle order is
not larger than the equal endpoint orders. -/
theorem exists_lemma73LocalHyperbolicPair_of_middle_le
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 0 (by omega)))
    (h₁ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 1 (by omega))) :
    ∃ (E : Lemma73EndpointVectorData b)
      (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary)
      (x y : V),
      IsLemma73EndpointAdaptedOrdering b E D x y ∧
      IsScaledHyperbolicPair q x y
        ((b.order 0 + b.order 1) / 2) := by
  let G := b.order 1 - b.order 0
  have hGupper : G ≤ 0 := by
    dsimp only [G]
    omega
  have hcriterionLeft :
      SatisfiesLemma72UnitCriterion (K := K)
        b.lemma73InitialBinary.binaryParameter := by
    rw [b.lemma73InitialBinary_binaryParameter]
    exact h₀
  have hleftUpper : b.lemma73InitialBinary.binaryOrderGap ≤ 0 := by
    rw [b.lemma73InitialBinary_binaryOrderGap]
    exact hGupper
  rcases b.lemma73InitialBinary.exists_lemma73AdaptedBinaryVectorData
      hcriterionLeft hleftUpper with ⟨D⟩
  rcases b.exists_lemma73EndpointVectorData
      hendpoint hGupper h₀ h₁ with ⟨E⟩
  have hEven : Even G := by
    have hpOrder := b.ordUnit_adjacentParameter 0 (by omega)
    change ordUnit K (b.adjacentParameter 0 (by omega)) = G at hpOrder
    rw [← hpOrder]
    exact h₀.1
  have hlower : -(2 * (ramificationIndex K : Int)) ≤ G := by
    have h := (b.adjacentParameter_isBinaryParameterAdmissible
      0 (by omega)).ordUnit_ge_neg_two_mul_e
    have hpOrder := b.ordUnit_adjacentParameter 0 (by omega)
    change ordUnit K (b.adjacentParameter 0 (by omega)) = G at hpOrder
    rw [hpOrder] at h
    exact h
  have hmixedNe :=
    b.bilin_lemma73EndpointVector_lemma73AdaptedVector_ne
      E.multiplier D
  have hmixedOrder :=
    b.ordUnit_lemma73EndpointVector_lemma73AdaptedVector E D hlower
  by_cases hneg : G < 0
  · let x := b.lemma73EndpointVector E.multiplier
    let y := b.lemma73AdaptedVector D
    have hpair := beliLemma319_of_mixedPairing x y
      b.lemma73PolarizationOrder hmixedNe hmixedOrder
      (E.norm_order_gt_of_gap_neg hneg)
      (b.ord_quadratic_lemma73AdaptedVector_ge D)
    rw [b.lemma73PolarizationOrder_sub_e_eq hEven hlower] at hpair
    exact ⟨E, D, x, y, Or.inl ⟨rfl, rfl⟩, hpair⟩
  · have hzero : G = 0 := by omega
    let x := b.lemma73AdaptedVector D
    let y := b.lemma73EndpointVector E.multiplier
    have hmixedNe' : q.bilin x y ≠ 0 := by
      rw [q.isSymm.eq]
      exact hmixedNe
    have hmixedOrder' :
        ordUnit K (Units.mk0 (q.bilin x y) hmixedNe') =
          b.lemma73PolarizationOrder - ramificationIndex K := by
      let U : Kˣ := Units.mk0 (q.bilin x y) hmixedNe'
      let W : Kˣ := Units.mk0
        (q.bilin (b.lemma73EndpointVector E.multiplier)
          (b.lemma73AdaptedVector D)) hmixedNe
      have hUW : U = W := by
        apply Units.ext
        exact q.isSymm.eq x y
      change ordUnit K U = _
      rw [hUW]
      exact hmixedOrder
    have hpair := beliLemma319_of_mixedPairing x y
      b.lemma73PolarizationOrder hmixedNe' hmixedOrder'
      (b.ord_quadratic_lemma73AdaptedVector_gt_of_gap_zero D hzero)
      E.norm_order_ge
    rw [b.lemma73PolarizationOrder_sub_e_eq hEven hlower] at hpair
    exact ⟨E, D, x, y, Or.inr ⟨rfl, rfl⟩, hpair⟩

/-- The canonical split of the initial binary segment from the final unary
segment under the middle-order inequality. -/
noncomputable def lemma73InitialTwoBlockSplit
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0) :
    TwoBlockSplitWitness b 2 (by omega) :=
  b.twoBlockSplitOfLeftOrdersLeRightHead 2 (by omega) (by omega) (by
    intro i
    rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
    fin_cases i
    · simpa [SegmentWitness.sourceIndex] using hendpoint.le
    · have h := hupper.trans_eq hendpoint
      simpa [SegmentWitness.sourceIndex] using h)

@[simp]
theorem lemma73InitialTwoBlockSplit_left
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0) :
    (b.lemma73InitialTwoBlockSplit hendpoint hupper).left =
      b.lemma73InitialBinarySegment :=
  rfl

theorem lemma73AdaptedVector_mem
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0)
    (D : Lemma73AdaptedBinaryVectorData b.lemma73InitialBinary) :
    b.lemma73AdaptedVector D ∈ L := by
  let S := b.lemma73InitialTwoBlockSplit hendpoint hupper
  apply S.decomposition.component_ambientSubmodule_le 0
  rw [S.component_zero]
  exact ⟨b.lemma73InitialBinary.binaryAdaptedShearAmbientVector
    D.coefficient, D.vector_mem, rfl⟩

theorem lemma73AmbientVector_zero_mem
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0) :
    b.ambientVector 0 ∈ L := by
  let S := b.lemma73InitialTwoBlockSplit hendpoint hupper
  apply S.decomposition.component_ambientSubmodule_le 0
  rw [S.component_zero]
  let x : S.left.carrier := S.left.bong.head
  refine ⟨x, S.left.bong.head_isNormGenerator.mem, ?_⟩
  change (S.left.bong.head : S.left.carrier) = b.ambientVector 0
  rw [← S.left.bong.ambientVector_zero_eq_head,
    S.left.ambientVector_eq]
  congr 1

theorem lemma73AmbientVector_two_mem
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0) :
    b.ambientVector 2 ∈ L := by
  let S := b.lemma73InitialTwoBlockSplit hendpoint hupper
  apply S.decomposition.component_ambientSubmodule_le 1
  rw [S.component_one]
  let z : S.right.carrier := S.right.bong.head
  refine ⟨z, S.right.bong.head_isNormGenerator.mem, ?_⟩
  change (S.right.bong.head : S.right.carrier) = b.ambientVector 2
  rw [← S.right.bong.ambientVector_zero_eq_head,
    S.right.ambientVector_eq]
  congr 1

theorem lemma73EndpointVector_mem
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0)
    (E : Lemma73EndpointVectorData b) :
    b.lemma73EndpointVector E.multiplier ∈ L := by
  rw [lemma73EndpointVector]
  apply L.add_mem
  · have hsIntegral : (E.multiplier : K) ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, ← coe_ordUnit, E.multiplier_order]
      rfl
    exact L.smul_mem ⟨E.multiplier, hsIntegral⟩
      (b.lemma73AmbientVector_zero_mem hendpoint hupper)
  · exact b.lemma73AmbientVector_two_mem hendpoint hupper

/-- The local ternary lattice splits off the hyperbolic plane constructed
above.  This is the lattice-theoretic `H ⊥ K` part of Lemma 7.3. -/
theorem exists_lemma73LocalHyperbolicDecomposition_of_middle_le
    (b : BONG V q L 3) (hgood : b.IsGood)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 0 (by omega)))
    (h₁ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 1 (by omega))) :
    ∃ decomposition : Lattice.OrthogonalDecomposition q L 2,
      Lattice.IsIsometric (decomposition.component 0).space
        (QuadraticSpace.hyperbolicPlane
          (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
        (decomposition.component 0).lattice
        (Lattice.hyperbolicPlaneLattice (K := K)) := by
  rcases b.exists_lemma73LocalHyperbolicPair_of_middle_le
      hendpoint hupper h₀ h₁ with
    ⟨E, D, x, y, hordering, hpair⟩
  have hxL : x ∈ L := by
    rcases hordering with h | h
    · rw [h.1]
      exact b.lemma73EndpointVector_mem hendpoint hupper E
    · rw [h.1]
      exact b.lemma73AdaptedVector_mem hendpoint hupper D
  have hyL : y ∈ L := by
    rcases hordering with h | h
    · rw [h.2]
      exact b.lemma73AdaptedVector_mem hendpoint hupper D
    · rw [h.2]
      exact b.lemma73EndpointVector_mem hendpoint hupper E
  rcases hpair with ⟨hli, hnondeg, hisometric⟩
  let C : Lattice.QuadraticSublattice q :=
    Lattice.basisQuadraticSublattice
      (binaryPairSpan (K := K) x y) hnondeg
      (binaryPairBasis (K := K) x y hli)
  have hCL : C.ambientSubmodule ≤ L.toSubmodule := by
    apply Lattice.basisQuadraticSublattice_ambientSubmodule_le
    intro i
    rw [coe_binaryPairBasis]
    fin_cases i
    · exact hxL
    · exact hyL
  let scale := uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)
  have hmodular : Lattice.IsModular C.space C.lattice scale := by
    rcases hisometric with ⟨f⟩
    have hstandard :=
      Lattice.hyperbolicPlaneLattice_isModular scale
    have hmapped := hstandard.mapLatticeIsometry f.symm
    exact hmapped
  have hEven : Even (b.order 1 - b.order 0) := by
    have hpOrder := b.ordUnit_adjacentParameter 0 (by omega)
    change ordUnit K (b.adjacentParameter 0 (by omega)) =
      b.order 1 - b.order 0 at hpOrder
    rw [← hpOrder]
    exact h₀.1
  have hsumEven : Even (b.order 0 + b.order 1) := by
    rcases hEven with ⟨r, hr⟩
    refine ⟨b.order 0 + r, ?_⟩
    omega
  have hscaleIdeal : Lattice.scaleIdeal q L ≤
      Lattice.principalIdeal (K := K) (scale : K) := by
    rcases b.beliCorollary44_iv_unconditional hgood with
      ⟨a, haScale, haOrder⟩
    have hmin :
        min (2 * b.order 0) (b.order 0 + b.order 1) =
          b.order 0 + b.order 1 := by
      rw [min_eq_right]
      omega
    rw [hmin] at haOrder
    have haOrder' : ordUnit K a = (b.order 0 + b.order 1) / 2 := by
      rcases hsumEven with ⟨r, hr⟩
      omega
    have hprincipal :
        Lattice.principalIdeal (K := K) (a : K) =
          Lattice.principalIdeal (K := K) (scale : K) := by
      apply (Lattice.principalIdeal_eq_iff_ordUnit_eq a scale).2
      rw [haOrder', ordUnit_uniformizerPowerUnit]
    rw [haScale, hprincipal]
  let decomposition := Lattice.omearaModularSplittingOfScaleIdealLe
    C hCL hmodular hscaleIdeal
  refine ⟨decomposition, ?_⟩
  rcases hisometric with ⟨f⟩
  exact ⟨f⟩

theorem lemma73LocalHyperbolicComponent_finrank
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K))) :
    Module.finrank K (decomposition.component 0).carrier = 2 := by
  rcases hyperbolic with ⟨f⟩
  have h := f.toLinearEquiv.finrank_eq
  simpa using h

theorem lemma73LocalRemainderComponent_finrank
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K))) :
    Module.finrank K (decomposition.component 1).carrier = 1 := by
  letI : Module.Finite K (decomposition.component 0).carrier :=
    (decomposition.component 0).lattice.moduleFinite
  letI : Module.Finite K (decomposition.component 1).carrier :=
    (decomposition.component 1).lattice.moduleFinite
  have htotal := decomposition.pairToAmbientLinearEquiv.finrank_eq
  rw [Module.finrank_prod, ← b.length_eq_finrank] at htotal
  have hzero := b.lemma73LocalHyperbolicComponent_finrank
    decomposition hyperbolic
  omega

noncomputable def lemma73LocalRemainderBONG
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K))) :
    BONG (decomposition.component 1).carrier
      (decomposition.component 1).space
      (decomposition.component 1).lattice 1 :=
  (BONG.ofLattice (decomposition.component 1).space
      (decomposition.component 1).lattice).castLength
    (b.lemma73LocalRemainderComponent_finrank decomposition hyperbolic)

theorem lemma73LocalHyperbolicComponent_volumeOrder
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K))) :
    Lattice.volumeOrder (decomposition.component 0).space
        (decomposition.component 0).lattice =
      2 * ((b.order 0 + b.order 1) / 2) := by
  let scale := uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)
  rcases hyperbolic with ⟨f⟩
  rw [Lattice.volumeOrder_eq_of_isometry f]
  have hvolume := (Lattice.hyperbolicPlaneLattice_isModular scale).volumeOrder_eq
  change Lattice.volumeOrder (QuadraticSpace.hyperbolicPlane scale)
      (Lattice.hyperbolicPlaneLattice (K := K)) = _
  rw [hvolume]
  rw [Module.finrank_fin_fun K]
  change (2 : Int) * ordUnit K scale =
    2 * ((b.order 0 + b.order 1) / 2)
  rw [show ordUnit K scale = (b.order 0 + b.order 1) / 2 by
    exact ordUnit_uniformizerPowerUnit
      (K := K) ((b.order 0 + b.order 1) / 2)]

theorem lemma73LocalRemainderComponent_volumeOrder
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K)))
    (hendpoint : b.order 0 = b.order 2)
    (hEven : Even (b.order 1 - b.order 0)) :
    Lattice.volumeOrder (decomposition.component 1).space
        (decomposition.component 1).lattice = b.order 0 := by
  have hambient := b.volumeOrder_eq_sum_order
  have hsplit := decomposition.volumeOrder_eq_add_components
  have hhyperbolic := b.lemma73LocalHyperbolicComponent_volumeOrder
    decomposition hyperbolic
  have hsum : ∑ i : Fin 3, b.order i =
      b.order 0 + b.order 1 + b.order 2 := by
    rw [Fin.sum_univ_three]
  rw [hsum] at hambient
  rcases hEven with ⟨r, hr⟩
  omega

@[simp]
theorem lemma73LocalRemainderBONG_order_zero
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K)))
    (hendpoint : b.order 0 = b.order 2)
    (hEven : Even (b.order 1 - b.order 0)) :
    (b.lemma73LocalRemainderBONG decomposition hyperbolic).order 0 =
      b.order 0 := by
  let c := b.lemma73LocalRemainderBONG decomposition hyperbolic
  have hc := c.volumeOrder_eq_sum_order
  have hrem := b.lemma73LocalRemainderComponent_volumeOrder
    decomposition hyperbolic hendpoint hEven
  change c.order 0 = b.order 0
  rw [show (∑ i : Fin 1, c.order i) = c.order 0 by simp] at hc
  omega

theorem lemma73_valueProduct_eq_hyperbolic_mul_residual
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hEven : Even (b.order 1 - b.order 0)) :
    b.valueProduct =
      ((-1 : Kˣ) *
          uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2) ^ 2) *
        b.lemma73ResidualValue (0 : Fin 1) := by
  have hproduct : b.valueProduct =
      b.valueUnit 0 * b.valueUnit 1 * b.valueUnit 2 := by
    apply Units.ext
    simp [Fin.prod_univ_three]
  have hvalue (i : Fin 3) :
      uniformizerPowerUnit K (b.order i) * b.normalizedValue i =
        b.valueUnit i := by
    simpa [uniformizerPowerUnit] using
      b.uniformizer_zpow_mul_normalizedValue i
  rw [hproduct, ← hvalue 0, ← hvalue 1, ← hvalue 2]
  unfold lemma73ResidualValue
  change
    (uniformizerPowerUnit K (b.order 0) * b.normalizedValue 0) *
        (uniformizerPowerUnit K (b.order 1) * b.normalizedValue 1) *
        (uniformizerPowerUnit K (b.order 2) * b.normalizedValue 2) =
      ((-1 : Kˣ) *
          uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2) ^ 2) *
        -(uniformizerPowerUnit K (b.order 0) * b.normalizedValue 0 *
          b.normalizedValue 1 * b.normalizedValue 2)
  rcases hEven with ⟨r, hr⟩
  have hexponent :
      b.order 0 + b.order 1 + b.order 2 =
        2 * ((b.order 0 + b.order 1) / 2) + b.order 0 := by
    omega
  have hpower :
      uniformizerPowerUnit K (b.order 0) *
          uniformizerPowerUnit K (b.order 1) *
          uniformizerPowerUnit K (b.order 2) =
        uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2) ^ 2 *
          uniformizerPowerUnit K (b.order 0) := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add,
      ← zpow_add, ← zpow_add]
    rw [hexponent]
    congr 1
    omega
  rw [neg_one_mul, neg_mul_neg]
  calc
    _ = (uniformizerPowerUnit K (b.order 0) *
          uniformizerPowerUnit K (b.order 1) *
          uniformizerPowerUnit K (b.order 2)) *
        (b.normalizedValue 0 * b.normalizedValue 1 *
          b.normalizedValue 2) := by ac_rfl
    _ = (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2) ^ 2 *
          uniformizerPowerUnit K (b.order 0)) *
        (b.normalizedValue 0 * b.normalizedValue 1 *
          b.normalizedValue 2) := by rw [hpower]
    _ = _ := by ac_rfl

theorem lemma73LocalRemainderBONG_squareClass_valueProduct
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K)))
    (hendpoint : b.order 0 = b.order 2)
    (hEven : Even (b.order 1 - b.order 0)) :
    squareClass K
        (b.lemma73LocalRemainderBONG decomposition hyperbolic).valueProduct =
      squareClass K (b.lemma73ResidualValue (0 : Fin 1)) := by
  let c := b.lemma73LocalRemainderBONG decomposition hyperbolic
  have hdet := decomposition.determinantClass_eq_mul_components
  have hsquare := congrArg (unitSquareClassToSquareClass K) hdet
  rw [map_mul] at hsquare
  rw [Lattice.determinantClass_toSquareClass_eq_valueProduct b] at hsquare
  rw [Lattice.determinantClass_toSquareClass_eq_valueProduct c] at hsquare
  rcases hyperbolic with ⟨f⟩
  have hdetZero := Lattice.determinantClass_eq_of_isometry f
  rw [Lattice.determinantClass_hyperbolicPlaneLattice] at hdetZero
  rw [hdetZero, unitSquareClassToSquareClass_apply] at hsquare
  have hproduct := b.lemma73_valueProduct_eq_hyperbolic_mul_residual
    hendpoint hEven
  have hproductClass := congrArg (squareClass K) hproduct
  change squareClass K c.valueProduct = _
  rw [hproduct] at hsquare
  change
    squareClass K
        (((-1 : Kˣ) *
          uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2) ^ 2) *
          b.lemma73ResidualValue (0 : Fin 1)) =
      squareClass K
          ((-1 : Kˣ) *
            uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2) ^ 2) *
        squareClass K c.valueProduct at hsquare
  change
    squareClass K
        ((-1 : Kˣ) *
          uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2) ^ 2) *
        squareClass K (b.lemma73ResidualValue (0 : Fin 1)) =
      squareClass K
          ((-1 : Kˣ) *
            uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2) ^ 2) *
        squareClass K c.valueProduct at hsquare
  exact (mul_left_cancel hsquare).symm

noncomputable def ofNormGeneratorUnary
    {W : Type v} [AddCommGroup W] [Module K W]
    (p : QuadraticSpace K W) (M : Lattice K W) (x : W)
    (generator : Lattice.IsNormGenerator p M x)
    (anisotropic : p.IsAnisotropic x)
    (hfin : Module.finrank K W = 1) : BONG W p M 1 := by
  letI : Module.Finite K W := M.moduleFinite
  have horth : Module.finrank K (p.vectorOrthogonal x) = 0 := by
    have hdim := p.finrank_vectorOrthogonal anisotropic
    omega
  haveI hsub : Subsingleton (p.vectorOrthogonal x) :=
    Module.finrank_zero_iff.mp horth
  exact BONG.cons x generator anisotropic
    (BONG.nil (p.orthogonalSpace x anisotropic)
      (M.projectedLattice p x anisotropic) hsub)

@[simp]
theorem head_ofNormGeneratorUnary
    {W : Type v} [AddCommGroup W] [Module K W]
    (p : QuadraticSpace K W) (M : Lattice K W) (x : W)
    (generator : Lattice.IsNormGenerator p M x)
    (anisotropic : p.IsAnisotropic x)
    (hfin : Module.finrank K W = 1) :
    (ofNormGeneratorUnary p M x generator anisotropic hfin).head = x :=
  rfl

theorem exists_lemma73LocalRemainderSquareMultiplier
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K)))
    (hendpoint : b.order 0 = b.order 2)
    (hEven : Even (b.order 1 - b.order 0)) :
    ∃ t : Kˣ, ordUnit K t = 0 ∧
      t ^ 2 *
          (b.lemma73LocalRemainderBONG decomposition hyperbolic).valueUnit 0 =
        b.lemma73ResidualValue (0 : Fin 1) := by
  let c := b.lemma73LocalRemainderBONG decomposition hyperbolic
  have hclass := b.lemma73LocalRemainderBONG_squareClass_valueProduct
    decomposition hyperbolic hendpoint hEven
  have hcProduct : c.valueProduct = c.valueUnit 0 := by
    apply Units.ext
    simp [Fin.prod_univ_one]
  change squareClass K c.valueProduct = _ at hclass
  rw [hcProduct] at hclass
  change QuotientGroup.mk' (Subgroup.square Kˣ) (c.valueUnit 0) =
      QuotientGroup.mk' (Subgroup.square Kˣ)
        (b.lemma73ResidualValue (0 : Fin 1)) at hclass
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  rcases hclass with ⟨s, hs, hsc⟩
  change IsSquare s at hs
  rcases hs with ⟨t, rfl⟩
  have horder := congrArg (ordUnit K) hsc
  have hcOrder := b.lemma73LocalRemainderBONG_order_zero
    decomposition hyperbolic hendpoint hEven
  have hresOrder := b.ordUnit_lemma73ResidualValue (0 : Fin 1)
  change c.order 0 = b.order 0 at hcOrder
  change ordUnit K (b.lemma73ResidualValue (0 : Fin 1)) =
      b.order 0 at hresOrder
  have hcValueOrder : ordUnit K (c.valueUnit 0) = b.order 0 := by
    rw [← c.order_eq_ordUnit]
    exact hcOrder
  refine ⟨t, ?_, ?_⟩
  · rw [ordUnit_mul, ordUnit_mul, hcValueOrder, hresOrder] at horder
    omega
  · change t ^ 2 * c.valueUnit 0 = _
    simpa [pow_two, mul_comm] using hsc

theorem exists_lemma73LocalExactRemainderBONG
    (b : BONG V q L 3)
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K)))
    (hendpoint : b.order 0 = b.order 2)
    (hEven : Even (b.order 1 - b.order 0)) :
    ∃ c : BONG (decomposition.component 1).carrier
        (decomposition.component 1).space
        (decomposition.component 1).lattice 1,
      c.value 0 = (b.lemma73ResidualValue (0 : Fin 1) : K) := by
  let raw := b.lemma73LocalRemainderBONG decomposition hyperbolic
  rcases b.exists_lemma73LocalRemainderSquareMultiplier decomposition
      hyperbolic hendpoint hEven with ⟨t, htOrder, htValue⟩
  have htUnit : IsValuationUnit K (t : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K t).2 htOrder
  let x : (decomposition.component 1).carrier := (t : K) • raw.head
  have hxGenerator : Lattice.IsNormGenerator
      (decomposition.component 1).space
      (decomposition.component 1).lattice x :=
    raw.head_isNormGenerator.smul_valuationUnit t htUnit
  have hxAnisotropic :
      (decomposition.component 1).space.IsAnisotropic x :=
    (decomposition.component 1).space.isAnisotropic_smul
      raw.head_isAnisotropic (Units.ne_zero t)
  have hfin := b.lemma73LocalRemainderComponent_finrank
    decomposition hyperbolic
  let c := ofNormGeneratorUnary
    (decomposition.component 1).space
    (decomposition.component 1).lattice x hxGenerator hxAnisotropic hfin
  refine ⟨c, ?_⟩
  rw [c.value_zero_eq_quadratic_head,
    head_ofNormGeneratorUnary,
    (decomposition.component 1).space.quadratic_smul,
    ← raw.value_zero_eq_quadratic_head]
  change t ^ 2 * raw.valueUnit 0 = _ at htValue
  have htValueField := congrArg Units.val htValue
  change (t : K) ^ 2 * raw.value 0 =
    (b.lemma73ResidualValue (0 : Fin 1) : K) at htValueField
  exact htValueField

theorem exists_lemma73LocalSplittingWitness_of_decomposition
    (b : BONG V q L 3)
    (hendpoint : b.order 0 = b.order 2)
    (hEven : Even (b.order 1 - b.order 0))
    (decomposition : Lattice.OrthogonalDecomposition q L 2)
    (hyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K))) :
    Nonempty (b.Lemma73SplittingWitness (0 : Fin 1)) := by
  rcases b.exists_lemma73LocalExactRemainderBONG decomposition
      hyperbolic hendpoint hEven with ⟨c, hcValue⟩
  let remainderNorm : Lattice.NormOrderDatum
      (decomposition.component 1).space
      (decomposition.component 1).lattice := {
    generator := c.valueUnit 0
    normIdeal_eq := by
      simpa [c.value_zero_eq_quadratic_head] using
        c.head_isNormGenerator.normIdeal_eq }
  let splitting : Lattice.HyperbolicPlaneSplitting q L := {
    decomposition := decomposition
    scaleOrder := (b.order 0 + b.order 1) / 2
    hyperbolic := hyperbolic
    remainderNorm := remainderNorm }
  have hcOrder : c.order 0 = b.order 0 := by
    apply WithTop.coe_injective
    rw [c.coe_order, b.coe_order, hcValue]
    rw [← coe_ordUnit, b.ordUnit_lemma73ResidualValue (0 : Fin 1)]
    simpa [lemma73FirstIndex] using b.coe_order (0 : Fin 3)
  refine ⟨{
    decomposition := decomposition
    hyperbolic := ?_
    remainderBONG := c
    value_before := ?_
    replacement_value := ?_
    value_after := ?_
    componentNormData := splitting.componentNormData
    hyperbolicNorm_order := ?_
    remainderNorm_order := ?_
    good := ?_ }⟩
  · simpa [lemma73HyperbolicScaleOrder, lemma73FirstIndex,
      lemma73MiddleIndex] using hyperbolic
  · intro j hj
    fin_cases j
    omega
  · simpa [lemma73FirstIndex, lemma73MiddleIndex,
      lemma73LastIndex] using hcValue
  · intro j hj
    fin_cases j
    omega
  · change splitting.hyperbolicNorm.order = _
    rw [Lattice.HyperbolicPlaneSplitting.hyperbolicNorm_order]
    rfl
  · change remainderNorm.order = b.order 0
    change ordUnit K (c.valueUnit 0) = b.order 0
    rw [← c.order_eq_ordUnit]
    exact hcOrder
  · intro j hj
    omega

theorem exists_lemma73LocalSplittingWitness_of_middle_le
    (b : BONG V q L 3) (hgood : b.IsGood)
    (hendpoint : b.order 0 = b.order 2)
    (hupper : b.order 1 ≤ b.order 0)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 0 (by omega)))
    (h₁ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 1 (by omega))) :
    Nonempty (b.Lemma73SplittingWitness (0 : Fin 1)) := by
  rcases b.exists_lemma73LocalHyperbolicDecomposition_of_middle_le
      hgood hendpoint hupper h₀ h₁ with ⟨decomposition, hyperbolic⟩
  have hEven : Even (b.order 1 - b.order 0) := by
    have hpOrder := b.ordUnit_adjacentParameter 0 (by omega)
    change ordUnit K (b.adjacentParameter 0 (by omega)) =
      b.order 1 - b.order 0 at hpOrder
    rw [← hpOrder]
    exact h₀.1
  exact b.exists_lemma73LocalSplittingWitness_of_decomposition
    hendpoint hEven decomposition hyperbolic

/-- Under reverse duality the two adjacent ternary parameters are exchanged. -/
theorem lemma73ReverseDual_adjacentParameter_zero
    (b : BONG V q L 3)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (hvalues : ∀ i, d.value i = ((b.valueUnit (Fin.rev i))⁻¹ : K)) :
    d.adjacentParameter 0 (by omega) =
      b.adjacentParameter 1 (by omega) := by
  have hvalueUnit : ∀ i,
      d.valueUnit i = (b.valueUnit (Fin.rev i))⁻¹ := by
    intro i
    apply Units.ext
    exact hvalues i
  unfold adjacentParameter
  change d.valueUnit 1 / d.valueUnit 0 =
    b.valueUnit 2 / b.valueUnit 1
  rw [hvalueUnit 0, hvalueUnit 1]
  simp [div_eq_mul_inv, mul_comm]

/-- The second reverse-dual ternary parameter is the first original one. -/
theorem lemma73ReverseDual_adjacentParameter_one
    (b : BONG V q L 3)
    (d : BONG V q (Lattice.dualLattice q L) 3)
    (hvalues : ∀ i, d.value i = ((b.valueUnit (Fin.rev i))⁻¹ : K)) :
    d.adjacentParameter 1 (by omega) =
      b.adjacentParameter 0 (by omega) := by
  have hvalueUnit : ∀ i,
      d.valueUnit i = (b.valueUnit (Fin.rev i))⁻¹ := by
    intro i
    apply Units.ext
    exact hvalues i
  unfold adjacentParameter
  change d.valueUnit 2 / d.valueUnit 1 =
    b.valueUnit 1 / b.valueUnit 0
  rw [hvalueUnit 1, hvalueUnit 2]
  simp [div_eq_mul_inv, mul_comm]

/-- The opposite ternary order inequality is reduced to the preceding case
by reverse duality.  We dualize the resulting two-component decomposition
componentwise, retaining the component order. -/
theorem exists_lemma73LocalHyperbolicDecomposition_of_endpoint_le_middle
    (b : BONG V q L 3) (hgood : b.IsGood)
    (hendpoint : b.order 0 = b.order 2)
    (hlower : b.order 0 ≤ b.order 1)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 0 (by omega)))
    (h₁ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 1 (by omega))) :
    ∃ decomposition : Lattice.OrthogonalDecomposition q L 2,
      Lattice.IsIsometric (decomposition.component 0).space
        (QuadraticSpace.hyperbolicPlane
          (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
        (decomposition.component 0).lattice
        (Lattice.hyperbolicPlaneLattice (K := K)) := by
  let source : GoodBONG q L 3 := ⟨b, hgood⟩
  rcases source.exists_reverseDual_with_values with
    ⟨dual, _hdualVectors, hdualValues, hdualOrders⟩
  have hrev₀ : Fin.rev (0 : Fin 3) = 2 := by decide
  have hrev₁ : Fin.rev (1 : Fin 3) = 1 := by decide
  have hrev₂ : Fin.rev (2 : Fin 3) = 0 := by decide
  have hdualEndpoint : dual.order 0 = dual.order 2 := by
    have hzero : dual.order 0 = -b.order 2 := by
      have h := hdualOrders 0
      change dual.toBONG.order 0 = -b.order (Fin.rev (0 : Fin 3)) at h
      rwa [hrev₀] at h
    have htwo : dual.order 2 = -b.order 0 := by
      have h := hdualOrders 2
      change dual.toBONG.order 2 = -b.order (Fin.rev (2 : Fin 3)) at h
      rwa [hrev₂] at h
    rw [hzero, htwo, hendpoint]
  have hdualUpper : dual.order 1 ≤ dual.order 0 := by
    have hzero : dual.order 0 = -b.order 2 := by
      have h := hdualOrders 0
      change dual.toBONG.order 0 = -b.order (Fin.rev (0 : Fin 3)) at h
      rwa [hrev₀] at h
    have hone : dual.order 1 = -b.order 1 := by
      have h := hdualOrders 1
      change dual.toBONG.order 1 = -b.order (Fin.rev (1 : Fin 3)) at h
      rwa [hrev₁] at h
    rw [hzero, hone, ← hendpoint]
    exact neg_le_neg hlower
  have hdual₀ : SatisfiesLemma72UnitCriterion (K := K)
      (dual.toBONG.adjacentParameter 0 (by omega)) := by
    rw [lemma73ReverseDual_adjacentParameter_zero b dual.toBONG hdualValues]
    exact h₁
  have hdual₁ : SatisfiesLemma72UnitCriterion (K := K)
      (dual.toBONG.adjacentParameter 1 (by omega)) := by
    rw [lemma73ReverseDual_adjacentParameter_one b dual.toBONG hdualValues]
    exact h₀
  rcases dual.toBONG.exists_lemma73LocalHyperbolicDecomposition_of_middle_le
      dual.good hdualEndpoint hdualUpper hdual₀ hdual₁ with
    ⟨dualDecomposition, dualHyperbolic⟩
  let componentwiseDual :=
    dualDecomposition.reverseDual.reindex Fin.revPerm
  let decomposition : Lattice.OrthogonalDecomposition q L 2 := {
    component := componentwiseDual.component
    orthogonal := componentwiseDual.orthogonal
    sum_eq := by
      simpa only [Lattice.dualLattice_dualLattice] using
        componentwiseDual.sum_eq }
  have hcomponent : decomposition.component 0 =
      (dualDecomposition.component 0).dual := by
    simp [decomposition, componentwiseDual,
      Lattice.OrthogonalDecomposition.reverseDualComponent]
  have hparameterEven : Even (b.order 1 - b.order 0) := by
    have hparameterOrder := b.ordUnit_adjacentParameter 0 (by omega)
    change ordUnit K (b.adjacentParameter 0 (by omega)) =
      b.order 1 - b.order 0 at hparameterOrder
    rw [← hparameterOrder]
    exact h₀.1
  have hsumEven : Even (b.order 0 + b.order 1) := by
    rcases hparameterEven with ⟨r, hr⟩
    refine ⟨b.order 0 + r, ?_⟩
    omega
  have hdualScaleOrder :
      (dual.order 0 + dual.order 1) / 2 =
        -((b.order 0 + b.order 1) / 2) := by
    have hzero : dual.order 0 = -b.order 2 := by
      have h := hdualOrders 0
      change dual.toBONG.order 0 = -b.order (Fin.rev (0 : Fin 3)) at h
      rwa [hrev₀] at h
    have hone : dual.order 1 = -b.order 1 := by
      have h := hdualOrders 1
      change dual.toBONG.order 1 = -b.order (Fin.rev (1 : Fin 3)) at h
      rwa [hrev₁] at h
    rw [hzero, hone, ← hendpoint]
    rcases hsumEven with ⟨r, hr⟩
    omega
  rcases dualHyperbolic with ⟨f⟩
  let dualScale : Kˣ := uniformizerPowerUnit K
    ((dual.order 0 + dual.order 1) / 2)
  let transported := f.dual.trans
    (Lattice.dualHyperbolicPlaneLatticeIsometry dualScale)
  refine ⟨decomposition, ?_⟩
  rw [hcomponent]
  change Lattice.IsIsometric
    (dualDecomposition.component 0).space
    (QuadraticSpace.hyperbolicPlane
      (uniformizerPowerUnit K ((b.order 0 + b.order 1) / 2)))
    (Lattice.dualLattice (dualDecomposition.component 0).space
      (dualDecomposition.component 0).lattice)
    (Lattice.hyperbolicPlaneLattice (K := K))
  exact ⟨by
    simpa [Lattice.QuadraticSublattice.dual,
      transported, dualScale, hdualScaleOrder,
      uniformizerPowerUnit, zpow_neg] using transported⟩

/-- The reverse-dual decomposition supplies the exact local splitting
witness in the remaining order branch. -/
theorem exists_lemma73LocalSplittingWitness_of_endpoint_le_middle
    (b : BONG V q L 3) (hgood : b.IsGood)
    (hendpoint : b.order 0 = b.order 2)
    (hlower : b.order 0 ≤ b.order 1)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 0 (by omega)))
    (h₁ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 1 (by omega))) :
    Nonempty (b.Lemma73SplittingWitness (0 : Fin 1)) := by
  rcases b.exists_lemma73LocalHyperbolicDecomposition_of_endpoint_le_middle
      hgood hendpoint hlower h₀ h₁ with ⟨decomposition, hyperbolic⟩
  have hEven : Even (b.order 1 - b.order 0) := by
    have hpOrder := b.ordUnit_adjacentParameter 0 (by omega)
    change ordUnit K (b.adjacentParameter 0 (by omega)) =
      b.order 1 - b.order 0 at hpOrder
    rw [← hpOrder]
    exact h₀.1
  exact b.exists_lemma73LocalSplittingWitness_of_decomposition
    hendpoint hEven decomposition hyperbolic

/-- Complete ternary form of Beli's Lemma 7.3 after splitting on the two
possible comparisons between the middle order and the common endpoint
order. -/
theorem exists_lemma73LocalSplittingWitness
    (b : BONG V q L 3) (hgood : b.IsGood)
    (hendpoint : b.order 0 = b.order 2)
    (h₀ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 0 (by omega)))
    (h₁ : SatisfiesLemma72UnitCriterion (K := K)
      (b.adjacentParameter 1 (by omega))) :
    Nonempty (b.Lemma73SplittingWitness (0 : Fin 1)) := by
  rcases le_total (b.order 1) (b.order 0) with hupper | hlower
  · exact b.exists_lemma73LocalSplittingWitness_of_middle_le
      hgood hendpoint hupper h₀ h₁
  · exact b.exists_lemma73LocalSplittingWitness_of_endpoint_le_middle
      hgood hendpoint hlower h₀ h₁

/-- The published spinor-group hypotheses imply the two explicit Lemma 7.2
criteria used by the local construction. -/
theorem exists_lemma73LocalSplittingWitness_of_hypotheses
    (b : BONG V q L 3) (hgood : b.IsGood)
    (h : b.Lemma73Hypotheses (0 : Fin 1)) :
    Nonempty (b.Lemma73SplittingWitness (0 : Fin 1)) := by
  have hendpoint : b.order 0 = b.order 2 := by
    simpa [Lemma73Hypotheses, lemma73FirstIndex,
      lemma73LastIndex] using h.1
  have hunit₀ : beliSpinorGroupRepresentative K
        (b.adjacentParameter 0 (by omega)) ≤
      valuationUnitSquareClassSubgroup K := by
    have hclass := h.2.1
    change beliSpinorGroup K
        (b.adjacentUnitSquareClass 0 (by omega)) ≤
      valuationUnitSquareClassSubgroup K at hclass
    simpa only [adjacentUnitSquareClass,
      beliSpinorGroup_unitSquareClass] using hclass
  have hunit₁ : beliSpinorGroupRepresentative K
        (b.adjacentParameter 1 (by omega)) ≤
      valuationUnitSquareClassSubgroup K := by
    have hclass := h.2.2
    change beliSpinorGroup K
        (b.adjacentUnitSquareClass 1 (by omega)) ≤
      valuationUnitSquareClassSubgroup K at hclass
    simpa only [adjacentUnitSquareClass,
      beliSpinorGroup_unitSquareClass] using hclass
  have h₀ := (Dyadic.beliLemma72_i (K := K)
    (b.adjacentParameter 0 (by omega))
    (b.adjacentParameter_isBinaryParameterAdmissible 0 (by omega))).1 hunit₀
  have h₁ := (Dyadic.beliLemma72_i (K := K)
    (b.adjacentParameter 1 (by omega))
    (b.adjacentParameter_isBinaryParameterAdmissible 1 (by omega))).1 hunit₁
  exact b.exists_lemma73LocalSplittingWitness
    hgood hendpoint h₀ h₁

/-- The hypotheses of Lemma 7.3 restrict exactly to the selected ternary
coordinate block.  This isolates all index arithmetic needed by the global
reconstruction argument. -/
theorem lemma73Segment_hypotheses
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (h : b.Lemma73Hypotheses i) :
    let block := b.segmentWitness i.val 3 (by omega)
    block.bong.Lemma73Hypotheses (0 : Fin 1) := by
  let block := b.segmentWitness i.val 3 (by omega)
  have hfirst : block.bong.order 0 =
      b.order (lemma73FirstIndex i) := by
    rw [SegmentWitness.order_eq]
    congr 1
  have hmiddle : block.bong.order 1 =
      b.order (lemma73MiddleIndex i) := by
    rw [SegmentWitness.order_eq]
    congr 1
  have hlast : block.bong.order 2 =
      b.order (lemma73LastIndex i) := by
    rw [SegmentWitness.order_eq]
    congr 1
  have hparameter₀ : block.bong.adjacentParameter 0 (by omega) =
      b.adjacentParameter (lemma73FirstIndex i) (by
        simp only [lemma73FirstIndex]
        omega) := by
    unfold adjacentParameter
    rw [block.valueUnit_eq, block.valueUnit_eq]
    congr 2 <;> apply Fin.ext <;> simp [block, SegmentWitness.sourceIndex,
      lemma73FirstIndex]
  have hparameter₁ : block.bong.adjacentParameter 1 (by omega) =
      b.adjacentParameter (lemma73MiddleIndex i) (by
        simp only [lemma73MiddleIndex]
        omega) := by
    unfold adjacentParameter
    rw [block.valueUnit_eq, block.valueUnit_eq]
    congr 2 <;> apply Fin.ext <;> simp [block, SegmentWitness.sourceIndex,
      lemma73MiddleIndex]
  unfold Lemma73Hypotheses at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · change block.bong.order 0 = block.bong.order 2
    rw [hfirst, hlast]
    exact h.1
  · change beliSpinorGroup K
        (block.bong.adjacentUnitSquareClass 0 (by omega)) ≤
      valuationUnitSquareClassSubgroup K
    rw [adjacentUnitSquareClass, hparameter₀]
    exact h.2.1
  · change beliSpinorGroup K
        (block.bong.adjacentUnitSquareClass 1 (by omega)) ≤
      valuationUnitSquareClassSubgroup K
    rw [adjacentUnitSquareClass, hparameter₁]
    exact h.2.2

/-- The preceding restriction calculation is independent of the chosen
realization of the consecutive block. -/
theorem SegmentWitness.lemma73Hypotheses
    {n : Nat} {b : BONG V q L (n + 3)} (i : Fin (n + 1))
    (block : SegmentWitness b i.val 3 (by omega))
    (h : b.Lemma73Hypotheses i) :
    block.bong.Lemma73Hypotheses (0 : Fin 1) := by
  have hfirst : block.bong.order 0 =
      b.order (lemma73FirstIndex i) := by
    rw [block.order_eq]
    congr 1
  have hlast : block.bong.order 2 =
      b.order (lemma73LastIndex i) := by
    rw [block.order_eq]
    congr 1
  have hparameter₀ : block.bong.adjacentParameter 0 (by omega) =
      b.adjacentParameter (lemma73FirstIndex i) (by
        simp only [lemma73FirstIndex]
        omega) := by
    unfold adjacentParameter
    rw [block.valueUnit_eq, block.valueUnit_eq]
    congr 2
  have hparameter₁ : block.bong.adjacentParameter 1 (by omega) =
      b.adjacentParameter (lemma73MiddleIndex i) (by
        simp only [lemma73MiddleIndex]
        omega) := by
    unfold adjacentParameter
    rw [block.valueUnit_eq, block.valueUnit_eq]
    congr 2
  unfold Lemma73Hypotheses at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · change block.bong.order 0 = block.bong.order 2
    rw [hfirst, hlast]
    exact h.1
  · change beliSpinorGroup K
        (block.bong.adjacentUnitSquareClass 0 (by omega)) ≤
      valuationUnitSquareClassSubgroup K
    rw [adjacentUnitSquareClass, hparameter₀]
    exact h.2.1
  · change beliSpinorGroup K
        (block.bong.adjacentUnitSquareClass 1 (by omega)) ≤
      valuationUnitSquareClassSubgroup K
    rw [adjacentUnitSquareClass, hparameter₁]
    exact h.2.2

/-- Every selected ternary block therefore carries the unconditional local
splitting witness proved above. -/
theorem exists_lemma73SegmentLocalSplittingWitness
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hgood : b.IsGood) (h : b.Lemma73Hypotheses i) :
    let block := b.segmentWitness i.val 3 (by omega)
    Nonempty (block.bong.Lemma73SplittingWitness (0 : Fin 1)) := by
  let block := b.segmentWitness i.val 3 (by omega)
  exact block.bong.exists_lemma73LocalSplittingWitness_of_hypotheses
    (block.isGood hgood) (b.lemma73Segment_hypotheses i h)

/-- The complete geometric data obtained when the initial ternary block is
globalized in the branch `R₁ ≤ R₀`.  Retaining the local witness is
essential for constructing the exact residual BONG. -/
structure Lemma73HeadMiddleLeData
    {n : Nat} (b : BONG V q L (n + 3)) where
  pref : PrefixWitness b 3 (by omega)
  localWitness : pref.toSegmentWitness.bong.Lemma73SplittingWitness
    (0 : Fin 1)
  decomposition : Lattice.OrthogonalDecomposition q L 2
  component_zero : decomposition.component 0 =
    pref.toSegmentWitness.toQuadraticSublattice.liftNested
      (localWitness.decomposition.component 0)
  component_one_carrier : (decomposition.component 1).carrier =
    (pref.toSegmentWitness.toQuadraticSublattice.liftNested
      (localWitness.decomposition.component 0)).orthogonalCarrier
  component_one_mem_iff : ∀ y : (decomposition.component 1).carrier,
    y ∈ (decomposition.component 1).lattice ↔ (y : V) ∈ L
  residual : (decomposition.component 1).carrier
  residual_ambient_eq : (residual : V) =
    (localWitness.remainderBONG.head : V)
  residual_mem : residual ∈ (decomposition.component 1).lattice
  residual_value : (decomposition.component 1).space.quadratic residual =
    (b.lemma73ResidualValue (0 : Fin (n + 1)) : K)
  residual_generator : Lattice.IsNormGenerator
    (decomposition.component 1).space
    (decomposition.component 1).lattice residual
  hyperbolic : Lattice.IsIsometric (decomposition.component 0).space
    (QuadraticSpace.hyperbolicPlane
      (uniformizerPowerUnit K
        (b.lemma73HyperbolicScaleOrder (0 : Fin (n + 1)))))
    (decomposition.component 0).lattice
    (Lattice.hyperbolicPlaneLattice (K := K))

namespace Lemma73HeadMiddleLeData

/-- In a two-component orthogonal decomposition, the second carrier is the
full orthogonal complement of the first. -/
theorem pair_component_one_carrier_eq_orthogonalCarrier
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (E : Lattice.OrthogonalDecomposition r M 2) :
    (E.component 1).carrier = (E.component 0).orthogonalCarrier := by
  apply le_antisymm
  · intro z hz y hy
    exact E.orthogonal 0 1 (by decide) ⟨y, hy⟩ ⟨z, hz⟩
  · intro z hz
    let p := E.pairToAmbientLinearEquiv.symm z
    have hsum : (p.1 : W) + (p.2 : W) = z := by
      exact E.pairToAmbientLinearEquiv.apply_symm_apply z
    have hpzero : p.1 = 0 := by
      apply (E.component 0).nondegenerate.1
      intro y
      change r.bilin (p.1 : W) (y : W) = 0
      rw [r.isSymm.eq]
      have hzorth : r.bilin (y : W) z = 0 := hz (y : W) y.property
      rw [← hsum, LinearMap.BilinForm.add_right,
        E.orthogonal 0 1 (by decide) y p.2, add_zero] at hzorth
      exact hzorth
    have hzEq : z = (p.2 : W) := by
      rw [← hsum, hpzero]
      simp
    rw [hzEq]
    exact p.2.property

/-- Ambient vector space after removing the first three BONG vectors. -/
noncomputable abbrev thirdTailCarrier
    {n : Nat} (b : BONG V q L (n + 3)) :=
  (((q.orthogonalSpace b.head b.head_isAnisotropic).orthogonalSpace
    b.tail.head b.tail.head_isAnisotropic).vectorOrthogonal
      b.tail.tail.head)

/-- Restricted quadratic space after the first three BONG projections. -/
noncomputable abbrev thirdTailQuadraticSpace
    {n : Nat} (b : BONG V q L (n + 3)) :
    QuadraticSpace K (thirdTailCarrier b) :=
  ((q.orthogonalSpace b.head b.head_isAnisotropic).orthogonalSpace
    b.tail.head b.tail.head_isAnisotropic).orthogonalSpace
      b.tail.tail.head b.tail.tail.head_isAnisotropic

/-- Recursive projected lattice after the first three BONG vectors. -/
noncomputable abbrev thirdTailLattice
    {n : Nat} (b : BONG V q L (n + 3)) :
    Lattice K (thirdTailCarrier b) :=
  (((L.projectedLattice q b.head b.head_isAnisotropic).projectedLattice
    (q.orthogonalSpace b.head b.head_isAnisotropic)
    b.tail.head b.tail.head_isAnisotropic).projectedLattice
      ((q.orthogonalSpace b.head b.head_isAnisotropic).orthogonalSpace
        b.tail.head b.tail.head_isAnisotropic)
      b.tail.tail.head b.tail.tail.head_isAnisotropic)

/-- Literal inclusion of the third recursive tail into the original ambient
space. -/
def thirdTailAmbientLinearMap
    {n : Nat} (b : BONG V q L (n + 3)) :
    thirdTailCarrier b →ₗ[K] V where
  toFun z := (z : V)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem thirdTailAmbientLinearMap_apply
    {n : Nat} (b : BONG V q L (n + 3))
    (z : thirdTailCarrier b) :
    thirdTailAmbientLinearMap b z = (z : V) :=
  rfl

/-- Every vector of the third recursive tail lies in the coordinate suffix
spanned by the fourth through final ambient BONG vectors. -/
theorem thirdTail_mem_segmentCarrier
    {n : Nat} (b : BONG V q L (n + 3))
    (z : thirdTailCarrier b) :
    (z : V) ∈ b.segmentCarrier 3 n (by omega) := by
  have hzSpan : z ∈ Submodule.span K
      (Set.range b.tail.tail.tail.ambientVector) := by
    rw [b.tail.tail.tail.span_ambientVector_eq_top]
    trivial
  have hzMap : (z : V) ∈ Submodule.span K
      (thirdTailAmbientLinearMap b ''
        Set.range b.tail.tail.tail.ambientVector) :=
    Submodule.apply_mem_span_image_of_mem_span
      (thirdTailAmbientLinearMap b) hzSpan
  rw [segmentCarrier]
  apply (Submodule.span_mono ?_) hzMap
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  refine ⟨i, ?_⟩
  change b.ambientVector (segmentIndex 3 n (by omega) i) =
    (b.tail.tail.tail.ambientVector i : V)
  calc
    b.ambientVector (segmentIndex 3 n (by omega) i) =
        b.ambientVector i.succ.succ.succ := by
      congr 1
      apply Fin.ext
      simp [segmentIndex]
      omega
    _ = (b.tail.tail.tail.ambientVector i : V) := by
      simp only [BONG.coe_ambientVector_tail]

/-- The unchanged suffix beginning with the fourth BONG vector, embedded back
into the original ambient quadratic space by the three canonical tail lifts. -/
noncomputable def thirdTailSegment
    {n : Nat} (b : BONG V q L (n + 3)) :
    SegmentWitness b 3 n (by omega) := by
  cases b with
  | @cons _ _ _ _ _ _ x₀ generator₀ anisotropic₀ tail₀ =>
      cases tail₀ with
      | @cons _ _ _ _ _ _ x₁ generator₁ anisotropic₁ tail₁ =>
          cases tail₁ with
          | @cons _ _ _ _ _ _ x₂ generator₂ anisotropic₂ tail₂ =>
              let w₀ := SegmentWitness.whole tail₂
              let w₁ := w₀.liftTail (generator := generator₂)
              let w₂ := w₁.liftTail (generator := generator₁)
              let w₃ := w₂.liftTail (generator := generator₀)
              simpa only [Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] using w₃

/-- The unchanged suffix is orthogonal to the initial ternary prefix. -/
theorem thirdTailSegment_bilin_pref_eq_zero
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (y : D.pref.carrier) (z : (thirdTailSegment b).carrier) :
    q.bilin (y : V) (z : V) = 0 := by
  let left := b.segmentWitness 0 3 (by omega)
  let right := b.segmentWitness 3 n (by omega)
  let y' : left.carrier := ⟨y, by
    rw [left.carrier_eq_segmentCarrier,
      ← D.pref.toSegmentWitness.carrier_eq_segmentCarrier]
    exact y.property⟩
  let z' : right.carrier := ⟨z, by
    rw [right.carrier_eq_segmentCarrier,
      ← (thirdTailSegment b).carrier_eq_segmentCarrier]
    exact z.property⟩
  exact b.segmentCarriers_orthogonal 3 (by omega) y' z'

/-- The residual vector is still carried by the initial ternary prefix. -/
theorem residual_mem_pref_carrier
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (D.residual : V) ∈ D.pref.carrier := by
  rw [D.residual_ambient_eq]
  exact (D.localWitness.remainderBONG.head : D.pref.carrier).property

/-- Every unchanged suffix vector belongs to the global complement carrier. -/
theorem thirdTailSegment_mem_component_one
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (z : (thirdTailSegment b).carrier) :
    (z : V) ∈ (D.decomposition.component 1).carrier := by
  rw [D.component_one_carrier]
  intro y hy
  let outer := D.pref.toSegmentWitness.toQuadraticSublattice
  let localHyperbolic := D.localWitness.decomposition.component 0
  let y' : D.pref.carrier := ⟨y,
    outer.nestedCarrier_le localHyperbolic hy⟩
  exact D.thirdTailSegment_bilin_pref_eq_zero y' z

/-- The unchanged suffix is also orthogonal to the residual generator. -/
theorem residual_bilin_thirdTailSegment_eq_zero
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (z : (thirdTailSegment b).carrier) :
    q.bilin (D.residual : V) (z : V) = 0 :=
  D.thirdTailSegment_bilin_pref_eq_zero
    ⟨D.residual, D.residual_mem_pref_carrier⟩ z

/-- Direct recursive-tail version of prefix--suffix orthogonality. -/
theorem thirdTail_bilin_pref_eq_zero
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (y : D.pref.carrier) (z : thirdTailCarrier b) :
    q.bilin (y : V) (z : V) = 0 := by
  let left := b.segmentWitness 0 3 (by omega)
  let right := b.segmentWitness 3 n (by omega)
  let y' : left.carrier := ⟨y, by
    rw [left.carrier_eq_segmentCarrier,
      ← D.pref.toSegmentWitness.carrier_eq_segmentCarrier]
    exact y.property⟩
  let z' : right.carrier := ⟨z, by
    rw [right.carrier_eq_segmentCarrier]
    exact thirdTail_mem_segmentCarrier b z⟩
  exact b.segmentCarriers_orthogonal 3 (by omega) y' z'

/-- Direct third-tail vectors lie in the global remainder carrier. -/
theorem thirdTail_mem_component_one
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (z : thirdTailCarrier b) :
    (z : V) ∈ (D.decomposition.component 1).carrier := by
  rw [D.component_one_carrier]
  intro y hy
  let outer := D.pref.toSegmentWitness.toQuadraticSublattice
  let localHyperbolic := D.localWitness.decomposition.component 0
  let y' : D.pref.carrier := ⟨y,
    outer.nestedCarrier_le localHyperbolic hy⟩
  exact D.thirdTail_bilin_pref_eq_zero y' z

/-- Direct third-tail vectors are orthogonal to the residual generator. -/
theorem residual_bilin_thirdTail_eq_zero
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (z : thirdTailCarrier b) :
    q.bilin (D.residual : V) (z : V) = 0 :=
  D.thirdTail_bilin_pref_eq_zero
    ⟨D.residual, D.residual_mem_pref_carrier⟩ z

/-- The retained hyperbolic component has field rank two. -/
theorem component_zero_finrank
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Module.finrank K (D.decomposition.component 0).carrier = 2 := by
  rcases D.hyperbolic with ⟨f⟩
  have hfin := f.toLinearEquiv.finrank_eq
  simpa only [Module.finrank_fin_fun] using hfin

/-- Removing the hyperbolic plane leaves the expected rank. -/
theorem component_one_finrank
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Module.finrank K (D.decomposition.component 1).carrier = n + 1 := by
  letI : Module.Finite K V := L.moduleFinite
  letI (i : Fin 2) : Module.Finite K
      (D.decomposition.component i).carrier :=
    (D.decomposition.component i).lattice.moduleFinite
  have hsum := D.decomposition.carrierDirectSumEquiv.finrank_eq
  rw [Module.finrank_directSum] at hsum
  have hsum' :
      Module.finrank K (D.decomposition.component 0).carrier +
          Module.finrank K (D.decomposition.component 1).carrier =
        Module.finrank K V := by
    simpa only [Fin.sum_univ_two] using hsum
  have hambient := b.length_eq_finrank
  rw [D.component_zero_finrank] at hsum'
  omega

/-- The exact residual value is nonzero, so the retained norm generator is
anisotropic in the global complement. -/
theorem residual_isAnisotropic
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (D.decomposition.component 1).space.IsAnisotropic D.residual := by
  change (D.decomposition.component 1).space.quadratic D.residual ≠ 0
  rw [D.residual_value]
  exact Units.ne_zero _

/-- Any of the first three ambient vectors belongs to the ternary prefix. -/
theorem initialAmbientVector_mem_pref_carrier
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (j : Fin (n + 3))
    (hj : j.val < 3) : b.ambientVector j ∈ D.pref.carrier := by
  rw [D.pref.toSegmentWitness.carrier_eq_segmentCarrier, segmentCarrier]
  apply Submodule.subset_span
  let i : Fin 3 := ⟨j.val, hj⟩
  refine ⟨i, ?_⟩
  apply congrArg b.ambientVector
  apply Fin.ext
  simp [i, segmentIndex]

/-- The first recursive BONG head belongs to the ternary prefix. -/
theorem head_mem_pref_carrier
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) : b.head ∈ D.pref.carrier := by
  let j₀ : Fin (n + 3) := ⟨0, by omega⟩
  simpa [j₀, BONG.ambientVector_zero_eq_head] using
    D.initialAmbientVector_mem_pref_carrier j₀ (by simp [j₀])

/-- The second recursive BONG head belongs to the ternary prefix. -/
theorem tail_head_mem_pref_carrier
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (b.tail.head : V) ∈ D.pref.carrier := by
  let j₁ : Fin (n + 3) := ⟨1, by omega⟩
  have heq : (b.tail.head : V) = b.ambientVector j₁ := by
    calc
      (b.tail.head : V) =
          (b.tail.ambientVector (0 : Fin (n + 2)) : V) := by
        rw [b.tail.ambientVector_zero_eq_head]
      _ = b.ambientVector (0 : Fin (n + 2)).succ :=
        b.coe_ambientVector_tail 0
      _ = b.ambientVector j₁ := by
        congr 1
  rw [heq]
  exact D.initialAmbientVector_mem_pref_carrier j₁ (by simp [j₁])

/-- The third recursive BONG head belongs to the ternary prefix. -/
theorem tail_tail_head_mem_pref_carrier
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (b.tail.tail.head : V) ∈ D.pref.carrier := by
  let j₂ : Fin (n + 3) := ⟨2, by omega⟩
  have heq : (b.tail.tail.head : V) = b.ambientVector j₂ := by
    calc
      (b.tail.tail.head : V) =
          (b.tail.tail.ambientVector (0 : Fin (n + 1)) : V) := by
        rw [b.tail.tail.ambientVector_zero_eq_head]
      _ = (b.tail.ambientVector (0 : Fin (n + 1)).succ : V) := by
        exact congrArg Subtype.val (b.tail.coe_ambientVector_tail 0)
      _ = b.ambientVector ((0 : Fin (n + 1)).succ.succ) :=
        b.coe_ambientVector_tail (0 : Fin (n + 1)).succ
      _ = b.ambientVector j₂ := by
        congr 1
  rw [heq]
  exact D.initialAmbientVector_mem_pref_carrier j₂ (by simp [j₂])

/-- The local one-dimensional remainder is spanned by its exact BONG head. -/
theorem localRemainder_mem_span_head
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (z : (D.localWitness.decomposition.component 1).carrier) :
    z ∈ K ∙ D.localWitness.remainderBONG.head := by
  have htopLe :
      (⊤ : Submodule K (D.localWitness.decomposition.component 1).carrier) ≤
        K ∙ D.localWitness.remainderBONG.head := by
    rw [← D.localWitness.remainderBONG.span_ambientVector_eq_top,
      Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [D.localWitness.remainderBONG.ambientVector_zero_eq_head]
    exact Submodule.mem_span_singleton_self _
  exact htopLe Submodule.mem_top

/-- A vector in the residual orthogonal space is orthogonal to the entire
initial ternary prefix. -/
theorem pref_bilin_residualOrthogonal_eq_zero
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (p : D.pref.carrier)
    (y : (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
    q.bilin (p : V) (y : V) = 0 := by
  let outer := D.pref.toSegmentWitness.toQuadraticSublattice
  let localHyperbolic := D.localWitness.decomposition.component 0
  let localRemainder := D.localWitness.decomposition.component 1
  let pair := D.localWitness.decomposition.pairToAmbientLinearEquiv.symm p
  have hsum : (pair.1 : D.pref.carrier) +
      (pair.2 : D.pref.carrier) = p :=
    D.localWitness.decomposition.pairToAmbientLinearEquiv.apply_symm_apply p
  have hyGlobalOrth : (y : V) ∈
      (outer.liftNested localHyperbolic).orthogonalCarrier := by
    rw [← D.component_one_carrier]
    exact (y : (D.decomposition.component 1).carrier).property
  have hhyperbolic : q.bilin (pair.1 : V) (y : V) = 0 := by
    exact hyGlobalOrth
      (outer.nestedCarrierEquiv localHyperbolic pair.1 : V)
      (outer.nestedCarrierEquiv localHyperbolic pair.1).property
  have hremainder : q.bilin (pair.2 : V) (y : V) = 0 := by
    rcases Submodule.mem_span_singleton.mp
        (D.localRemainder_mem_span_head pair.2) with ⟨a, ha⟩
    have haV := congrArg (fun z : localRemainder.carrier ↦ (z : V)) ha
    have hvalue : (pair.2 : V) = a • (D.residual : V) := by
      rw [D.residual_ambient_eq]
      exact haV.symm
    have hyResidual : q.bilin (D.residual : V) (y : V) = 0 := by
      exact ((D.decomposition.component 1).space.mem_vectorOrthogonal_iff
        D.residual y).1 y.property
    rw [hvalue, LinearMap.BilinForm.smul_left, hyResidual, mul_zero]
  have hsumV := congrArg (fun z : D.pref.carrier ↦ (z : V)) hsum
  rw [← hsumV]
  change q.bilin ((pair.1 : V) + (pair.2 : V)) (y : V) = 0
  rw [LinearMap.BilinForm.add_left, hhyperbolic, hremainder, add_zero]

/-- Literal inclusion of the recursive third tail into the residual
orthogonal space. -/
def recursiveThirdTailLinearMap
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    thirdTailCarrier b →ₗ[K]
      (D.decomposition.component 1).space.vectorOrthogonal D.residual where
  toFun z := ⟨⟨z, D.thirdTail_mem_component_one z⟩, by
    rw [(D.decomposition.component 1).space.mem_vectorOrthogonal_iff]
    exact D.residual_bilin_thirdTail_eq_zero z⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem recursiveThirdTailLinearMap_injective
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Function.Injective D.recursiveThirdTailLinearMap := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have h₁ :
      (D.recursiveThirdTailLinearMap z :
          (D.decomposition.component 1).carrier) =
        (D.recursiveThirdTailLinearMap w :
          (D.decomposition.component 1).carrier) :=
    congrArg (fun y :
      (D.decomposition.component 1).space.vectorOrthogonal D.residual ↦
        (y : (D.decomposition.component 1).carrier)) hzw
  exact congrArg (fun y : (D.decomposition.component 1).carrier ↦
    (y : V)) h₁

theorem recursiveThirdTail_finrank_eq
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Module.finrank K (thirdTailCarrier b) =
      Module.finrank K
        ((D.decomposition.component 1).space.vectorOrthogonal D.residual) := by
  letI : Module.Finite K (thirdTailCarrier b) :=
    (thirdTailLattice b).moduleFinite
  letI : Module.Finite K (D.decomposition.component 1).carrier :=
    (D.decomposition.component 1).lattice.moduleFinite
  have hsource := b.tail.tail.tail.length_eq_finrank
  change n = Module.finrank K (thirdTailCarrier b) at hsource
  have htarget := (D.decomposition.component 1).space.finrank_vectorOrthogonal
    D.residual_isAnisotropic
  rw [D.component_one_finrank] at htarget
  omega

/-- Explicit inverse on vectors: a residual-orthogonal remainder vector is
orthogonal to the first three BONG heads and hence belongs to the third
recursive tail carrier. -/
def residualOrthogonalToRecursiveThirdTail
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (y : (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
    thirdTailCarrier b := by
  let y₀ : q.vectorOrthogonal b.head := ⟨(y : V), by
    rw [q.mem_vectorOrthogonal_iff]
    exact D.pref_bilin_residualOrthogonal_eq_zero
      ⟨b.head, D.head_mem_pref_carrier⟩ y⟩
  let q₁ := q.orthogonalSpace b.head b.head_isAnisotropic
  let y₁ : q₁.vectorOrthogonal b.tail.head := ⟨y₀, by
    rw [q₁.mem_vectorOrthogonal_iff]
    change q.bilin (b.tail.head : V) (y : V) = 0
    exact D.pref_bilin_residualOrthogonal_eq_zero
      ⟨(b.tail.head : V), D.tail_head_mem_pref_carrier⟩ y⟩
  refine ⟨y₁, ?_⟩
  let q₂ := q₁.orthogonalSpace b.tail.head b.tail.head_isAnisotropic
  rw [q₂.mem_vectorOrthogonal_iff]
  change q.bilin (b.tail.tail.head : V) (y : V) = 0
  exact D.pref_bilin_residualOrthogonal_eq_zero
    ⟨(b.tail.tail.head : V), D.tail_tail_head_mem_pref_carrier⟩ y

/-- Linear form of the explicit inverse inclusion. -/
def residualOrthogonalToRecursiveThirdTailLinearMap
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (D.decomposition.component 1).space.vectorOrthogonal D.residual →ₗ[K]
      thirdTailCarrier b where
  toFun := D.residualOrthogonalToRecursiveThirdTail
  map_add' y z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' a y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The direct recursive third tail is exactly the residual orthogonal
space. -/
noncomputable def recursiveThirdTailLinearEquiv
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    thirdTailCarrier b ≃ₗ[K]
      (D.decomposition.component 1).space.vectorOrthogonal D.residual := by
  exact
    { toFun := D.recursiveThirdTailLinearMap
      invFun := D.residualOrthogonalToRecursiveThirdTailLinearMap
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl
      map_add' := D.recursiveThirdTailLinearMap.map_add
      map_smul' := D.recursiveThirdTailLinearMap.map_smul }

@[simp]
theorem recursiveThirdTailLinearEquiv_coe
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (z : thirdTailCarrier b) :
    (((D.recursiveThirdTailLinearEquiv z :
        (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
      (D.decomposition.component 1).carrier) : V) = (z : V) := by
  dsimp only [recursiveThirdTailLinearEquiv]
  rfl

/-- The direct tail equivalence is a quadratic isometry. -/
noncomputable def recursiveThirdTailIsometry
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (thirdTailQuadraticSpace b).Isometry
      ((D.decomposition.component 1).space.orthogonalSpace D.residual
        D.residual_isAnisotropic) where
  toLinearEquiv := D.recursiveThirdTailLinearEquiv
  map_bilin z w := by
    change q.bilin
      (((D.recursiveThirdTailLinearEquiv z :
          (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
        (D.decomposition.component 1).carrier) : V)
      (((D.recursiveThirdTailLinearEquiv w :
          (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
        (D.decomposition.component 1).carrier) : V) =
      q.bilin (z : V) (w : V)
    rw [D.recursiveThirdTailLinearEquiv_coe,
      D.recursiveThirdTailLinearEquiv_coe]

/-- Direct image of the recursive third-tail lattice. -/
noncomputable def recursiveThirdTailMappedLattice
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Lattice K
      ((D.decomposition.component 1).space.vectorOrthogonal D.residual) :=
  Lattice.map D.recursiveThirdTailIsometry.toLinearEquiv
    (thirdTailLattice b)

/-- Directly transported unchanged suffix BONG. -/
noncomputable def recursiveThirdTailMappedBONG
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    BONG ((D.decomposition.component 1).space.vectorOrthogonal D.residual)
      ((D.decomposition.component 1).space.orthogonalSpace D.residual
        D.residual_isAnisotropic)
      D.recursiveThirdTailMappedLattice n :=
  b.tail.tail.tail.map D.recursiveThirdTailIsometry

@[simp]
theorem recursiveThirdTailMappedBONG_value
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (j : Fin n) :
    D.recursiveThirdTailMappedBONG.value j =
      b.value ⟨j.val + 3, by omega⟩ := by
  calc
    D.recursiveThirdTailMappedBONG.value j =
        b.tail.tail.tail.value j := by
      simpa only [recursiveThirdTailMappedBONG,
        recursiveThirdTailMappedLattice, thirdTailLattice] using
        BONG.value_map D.recursiveThirdTailIsometry b.tail.tail.tail j
    _ = b.value j.succ.succ.succ := by
      simp only [BONG.value_tail]
    _ = b.value ⟨j.val + 3, by omega⟩ := by
      congr 1

/-- Every vector in the recursive third-tail lattice is obtained from a
vector of the original lattice by the first three orthogonal projections;
their ambient difference belongs to the ternary prefix. -/
theorem exists_parent_sub_mem_pref_of_mem_recursiveThirdTail
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (z : thirdTailCarrier b) (hz : z ∈ thirdTailLattice b) :
    ∃ y : V, y ∈ L ∧ y - (z : V) ∈ D.pref.carrier := by
  let q₁ := q.orthogonalSpace b.head b.head_isAnisotropic
  let L₁ := L.projectedLattice q b.head b.head_isAnisotropic
  let q₂ := q₁.orthogonalSpace b.tail.head b.tail.head_isAnisotropic
  let L₂ := L₁.projectedLattice q₁ b.tail.head
    b.tail.head_isAnisotropic
  rcases (Lattice.mem_projectedLattice_iff q₂ L₂ b.tail.tail.head
      b.tail.tail.head_isAnisotropic z).1 hz with
    ⟨y₂, hy₂, hproj₂⟩
  rcases (Lattice.mem_projectedLattice_iff q₁ L₁ b.tail.head
      b.tail.head_isAnisotropic y₂).1 hy₂ with
    ⟨y₁, hy₁, hproj₁⟩
  rcases (Lattice.mem_projectedLattice_iff q L b.head
      b.head_isAnisotropic y₁).1 hy₁ with
    ⟨y₀, hy₀, hproj₀⟩
  refine ⟨y₀, hy₀, ?_⟩
  have hdiff₀ : y₀ - (y₁ : V) ∈ D.pref.carrier := by
    have hp := congrArg Subtype.val hproj₀
    rw [QuadraticSpace.projectionToOrthogonal_coe] at hp
    have hd := q.lineProjection_add_orthogonalProjection b.head y₀
    rw [hp] at hd
    have heq : y₀ - (y₁ : V) = q.lineProjection b.head y₀ := by
      calc
        y₀ - (y₁ : V) =
            (q.lineProjection b.head y₀ + (y₁ : V)) - (y₁ : V) :=
          congrArg (fun t : V ↦ t - (y₁ : V)) hd.symm
        _ = q.lineProjection b.head y₀ := by abel
    rw [heq, q.lineProjection_apply]
    exact D.pref.carrier.smul_mem _ D.head_mem_pref_carrier
  have hdiff₁ : (y₁ : V) - (y₂ : V) ∈ D.pref.carrier := by
    have hp := congrArg Subtype.val hproj₁
    rw [QuadraticSpace.projectionToOrthogonal_coe] at hp
    have hd := q₁.lineProjection_add_orthogonalProjection b.tail.head y₁
    rw [hp] at hd
    have heq : y₁ - (y₂ : _) = q₁.lineProjection b.tail.head y₁ := by
      calc
        y₁ - (y₂ : _) =
            (q₁.lineProjection b.tail.head y₁ + (y₂ : _)) - (y₂ : _) :=
          congrArg (fun t : q.vectorOrthogonal b.head ↦ t - (y₂ : _))
            hd.symm
        _ = q₁.lineProjection b.tail.head y₁ := by abel
    have heqV := congrArg
      (fun t : q.vectorOrthogonal b.head ↦ (t : V)) heq
    simp only [Submodule.coe_sub] at heqV
    change (y₁ : V) - (y₂ : V) ∈ D.pref.carrier
    rw [heqV, q₁.lineProjection_apply]
    exact D.pref.carrier.smul_mem _ D.tail_head_mem_pref_carrier
  have hdiff₂ : (y₂ : V) - (z : V) ∈ D.pref.carrier := by
    have hp := congrArg Subtype.val hproj₂
    rw [QuadraticSpace.projectionToOrthogonal_coe] at hp
    have hd := q₂.lineProjection_add_orthogonalProjection
      b.tail.tail.head y₂
    rw [hp] at hd
    have heq : y₂ - (z : _) =
        q₂.lineProjection b.tail.tail.head y₂ := by
      calc
        y₂ - (z : _) =
            (q₂.lineProjection b.tail.tail.head y₂ + (z : _)) - (z : _) :=
          congrArg
            (fun t : q₁.vectorOrthogonal b.tail.head ↦ t - (z : _)) hd.symm
        _ = q₂.lineProjection b.tail.tail.head y₂ := by abel
    have heqV := congrArg
      (fun t : q₁.vectorOrthogonal b.tail.head ↦ (t : V)) heq
    simp only [Submodule.coe_sub] at heqV
    change (y₂ : V) - (z : V) ∈ D.pref.carrier
    rw [heqV, q₂.lineProjection_apply]
    exact D.pref.carrier.smul_mem _ D.tail_tail_head_mem_pref_carrier
  have hsum : y₀ - (z : V) =
      (y₀ - (y₁ : V)) + ((y₁ : V) - (y₂ : V)) +
        ((y₂ : V) - (z : V)) := by
    abel
  rw [hsum]
  exact D.pref.carrier.add_mem
    (D.pref.carrier.add_mem hdiff₀ hdiff₁) hdiff₂

/-- Inside the ternary prefix, the part orthogonal to the split hyperbolic
plane is precisely the residual line. -/
theorem mem_span_residual_of_mem_pref_of_mem_component_one
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) {x : V}
    (hxPref : x ∈ D.pref.carrier)
    (hxRemainder : x ∈ (D.decomposition.component 1).carrier) :
    x ∈ K ∙ (D.residual : V) := by
  let outer := D.pref.toSegmentWitness.toQuadraticSublattice
  let localHyperbolic := D.localWitness.decomposition.component 0
  let localRemainder := D.localWitness.decomposition.component 1
  let xPref : outer.carrier := ⟨x, hxPref⟩
  have hxGlobalOrth : x ∈
      (outer.liftNested localHyperbolic).orthogonalCarrier := by
    rw [← D.component_one_carrier]
    exact hxRemainder
  have hxLocalOrth : xPref ∈ localHyperbolic.orthogonalCarrier := by
    intro y hy
    let yLocal : localHyperbolic.carrier := ⟨y, hy⟩
    change q.bilin (y : V) x = 0
    exact hxGlobalOrth
      (outer.nestedCarrierEquiv localHyperbolic yLocal : V)
      (outer.nestedCarrierEquiv localHyperbolic yLocal).property
  have hxLocalRemainder : xPref ∈ localRemainder.carrier := by
    rw [pair_component_one_carrier_eq_orthogonalCarrier
      D.localWitness.decomposition]
    exact hxLocalOrth
  let xr : localRemainder.carrier := ⟨xPref, hxLocalRemainder⟩
  have htopLe : (⊤ : Submodule K localRemainder.carrier) ≤
      K ∙ D.localWitness.remainderBONG.head := by
    rw [← D.localWitness.remainderBONG.span_ambientVector_eq_top,
      Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [D.localWitness.remainderBONG.ambientVector_zero_eq_head]
    exact Submodule.mem_span_singleton_self _
  have hxr : xr ∈ K ∙ D.localWitness.remainderBONG.head :=
    htopLe (Submodule.mem_top)
  rcases Submodule.mem_span_singleton.mp hxr with ⟨a, ha⟩
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a, ?_⟩
  rw [D.residual_ambient_eq]
  have haV := congrArg
    (fun z : localRemainder.carrier ↦ (z : V)) ha
  simpa only [SetLike.val_smul] using haV

/-- The unchanged recursive suffix embeds integrally into the projection of
the global remainder lattice along the new residual generator. -/
theorem recursiveThirdTailMappedLattice_le_projectedLattice
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    D.recursiveThirdTailMappedLattice ≤
      (D.decomposition.component 1).lattice.projectedLattice
        (D.decomposition.component 1).space D.residual
        D.residual_isAnisotropic := by
  intro w hw
  rcases hw with ⟨z, hz, rfl⟩
  have hwAmbient : (z : V) =
      (((D.recursiveThirdTailLinearEquiv z :
          (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
        (D.decomposition.component 1).carrier) : V) :=
    (D.recursiveThirdTailLinearEquiv_coe z).symm
  rcases D.exists_parent_sub_mem_pref_of_mem_recursiveThirdTail z hz with
    ⟨y, hy, hyz⟩
  let p := D.decomposition.pairToAmbientLinearEquiv.symm y
  have hpMem :
      p.1 ∈ (D.decomposition.component 0).lattice ∧
        p.2 ∈ (D.decomposition.component 1).lattice := by
    rw [← Lattice.mem_product_iff]
    apply (D.decomposition.pairProductLatticeIsometry.map_mem p).2
    change D.decomposition.pairToAmbientLinearEquiv p ∈ L
    simpa only [p, LinearEquiv.apply_symm_apply] using hy
  have hpDecomp : (p.1 : V) + (p.2 : V) = y := by
    change D.decomposition.pairToAmbientLinearEquiv p = y
    exact D.decomposition.pairToAmbientLinearEquiv.apply_symm_apply y
  have hp₁Pref : (p.1 : V) ∈ D.pref.carrier := by
    let outer := D.pref.toSegmentWitness.toQuadraticSublattice
    let localHyperbolic := D.localWitness.decomposition.component 0
    have hcarrier : (D.decomposition.component 0).carrier =
        (outer.liftNested localHyperbolic).carrier :=
      congrArg Lattice.QuadraticSublattice.carrier D.component_zero
    have hp₁Lifted : (p.1 : V) ∈
        (outer.liftNested localHyperbolic).carrier := by
      rw [← hcarrier]
      exact p.1.property
    exact outer.nestedCarrier_le localHyperbolic hp₁Lifted
  let w₁ : (D.decomposition.component 1).carrier :=
    (D.recursiveThirdTailLinearEquiv z :
      (D.decomposition.component 1).carrier)
  have hyw : y - (w₁ : V) ∈ D.pref.carrier := by
    dsimp only [w₁]
    rw [← hwAmbient]
    exact hyz
  have hdiffPref : (p.2 : V) - (w₁ : V) ∈ D.pref.carrier := by
    have heq : (p.2 : V) - (w₁ : V) =
        (y - (w₁ : V)) - (p.1 : V) := by
      calc
        (p.2 : V) - (w₁ : V) =
            (((p.1 : V) + (p.2 : V)) - (w₁ : V)) - (p.1 : V) := by
          abel
        _ = (y - (w₁ : V)) - (p.1 : V) := by rw [hpDecomp]
    rw [heq]
    exact D.pref.carrier.sub_mem hyw hp₁Pref
  have hdiffRemainder : (p.2 : V) - (w₁ : V) ∈
      (D.decomposition.component 1).carrier :=
    (D.decomposition.component 1).carrier.sub_mem p.2.property w₁.property
  have hspan : (p.2 : V) - (w₁ : V) ∈ K ∙ (D.residual : V) :=
    D.mem_span_residual_of_mem_pref_of_mem_component_one
      hdiffPref hdiffRemainder
  rcases Submodule.mem_span_singleton.mp hspan with ⟨a, ha⟩
  have hp₂Eq : p.2 = w₁ + a • D.residual := by
    apply Subtype.ext
    change (p.2 : V) = (w₁ : V) + a • (D.residual : V)
    calc
      (p.2 : V) = ((p.2 : V) - (w₁ : V)) + (w₁ : V) := by abel
      _ = a • (D.residual : V) + (w₁ : V) := by rw [← ha]
      _ = (w₁ : V) + a • (D.residual : V) := add_comm _ _
  refine (Lattice.mem_projectedLattice_iff
    (D.decomposition.component 1).space
    (D.decomposition.component 1).lattice D.residual
    D.residual_isAnisotropic
    (D.recursiveThirdTailLinearEquiv z)).2 ⟨p.2, hpMem.2, ?_⟩
  apply Subtype.ext
  rw [QuadraticSpace.projectionToOrthogonal_coe, hp₂Eq, map_add, map_smul,
    (D.decomposition.component 1).space.orthogonalProjection_eq_self
      (D.recursiveThirdTailLinearEquiv z).property,
    (D.decomposition.component 1).space.orthogonalProjection_self
      D.residual_isAnisotropic]
  simp [w₁]

/-- Conversely, projection of the global remainder along the residual line
is the iterated projection along the first three original BONG vectors. -/
theorem projectedLattice_le_recursiveThirdTailMappedLattice
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (D.decomposition.component 1).lattice.projectedLattice
        (D.decomposition.component 1).space D.residual
        D.residual_isAnisotropic ≤
      D.recursiveThirdTailMappedLattice := by
  intro w hw
  rcases (Lattice.mem_projectedLattice_iff
      (D.decomposition.component 1).space
      (D.decomposition.component 1).lattice D.residual
      D.residual_isAnisotropic w).1 hw with ⟨y, hy, hprojResidual⟩
  have hyL : (y : V) ∈ L := (D.component_one_mem_iff y).1 hy
  let q₁ := q.orthogonalSpace b.head b.head_isAnisotropic
  let L₁ := L.projectedLattice q b.head b.head_isAnisotropic
  let y₁ : q.vectorOrthogonal b.head :=
    q.projectionToOrthogonal b.head b.head_isAnisotropic (y : V)
  have hy₁ : y₁ ∈ L₁ :=
    Lattice.projection_mem_projectedLattice q L b.head
      b.head_isAnisotropic hyL
  let q₂ := q₁.orthogonalSpace b.tail.head b.tail.head_isAnisotropic
  let L₂ := L₁.projectedLattice q₁ b.tail.head
    b.tail.head_isAnisotropic
  let y₂ : q₁.vectorOrthogonal b.tail.head :=
    q₁.projectionToOrthogonal b.tail.head
      b.tail.head_isAnisotropic y₁
  have hy₂ : y₂ ∈ L₂ :=
    Lattice.projection_mem_projectedLattice q₁ L₁ b.tail.head
      b.tail.head_isAnisotropic hy₁
  let z : q₂.vectorOrthogonal b.tail.tail.head :=
    q₂.projectionToOrthogonal b.tail.tail.head
      b.tail.tail.head_isAnisotropic y₂
  have hz : z ∈ thirdTailLattice b :=
    Lattice.projection_mem_projectedLattice q₂ L₂ b.tail.tail.head
      b.tail.tail.head_isAnisotropic hy₂
  have hdiff₀ : (y : V) - (y₁ : V) ∈ D.pref.carrier := by
    have hp : q.orthogonalProjection b.head (y : V) = (y₁ : V) := rfl
    have hd := q.lineProjection_add_orthogonalProjection b.head (y : V)
    rw [hp] at hd
    have heq : (y : V) - (y₁ : V) =
        q.lineProjection b.head (y : V) := by
      calc
        (y : V) - (y₁ : V) =
            (q.lineProjection b.head (y : V) + (y₁ : V)) - (y₁ : V) :=
          congrArg (fun t : V ↦ t - (y₁ : V)) hd.symm
        _ = q.lineProjection b.head (y : V) := by abel
    rw [heq, q.lineProjection_apply]
    exact D.pref.carrier.smul_mem _ D.head_mem_pref_carrier
  have hdiff₁ : (y₁ : V) - (y₂ : V) ∈ D.pref.carrier := by
    have hp : q₁.orthogonalProjection b.tail.head y₁ = (y₂ : _) := rfl
    have hd := q₁.lineProjection_add_orthogonalProjection b.tail.head y₁
    rw [hp] at hd
    have heq : y₁ - (y₂ : _) = q₁.lineProjection b.tail.head y₁ := by
      calc
        y₁ - (y₂ : _) =
            (q₁.lineProjection b.tail.head y₁ + (y₂ : _)) - (y₂ : _) :=
          congrArg (fun t : q.vectorOrthogonal b.head ↦ t - (y₂ : _))
            hd.symm
        _ = q₁.lineProjection b.tail.head y₁ := by abel
    have heqV := congrArg
      (fun t : q.vectorOrthogonal b.head ↦ (t : V)) heq
    simp only [Submodule.coe_sub] at heqV
    change (y₁ : V) - (y₂ : V) ∈ D.pref.carrier
    rw [heqV, q₁.lineProjection_apply]
    exact D.pref.carrier.smul_mem _ D.tail_head_mem_pref_carrier
  have hdiff₂ : (y₂ : V) - (z : V) ∈ D.pref.carrier := by
    have hp : q₂.orthogonalProjection b.tail.tail.head y₂ = (z : _) := rfl
    have hd := q₂.lineProjection_add_orthogonalProjection
      b.tail.tail.head y₂
    rw [hp] at hd
    have heq : y₂ - (z : _) =
        q₂.lineProjection b.tail.tail.head y₂ := by
      calc
        y₂ - (z : _) =
            (q₂.lineProjection b.tail.tail.head y₂ + (z : _)) - (z : _) :=
          congrArg
            (fun t : q₁.vectorOrthogonal b.tail.head ↦ t - (z : _)) hd.symm
        _ = q₂.lineProjection b.tail.tail.head y₂ := by abel
    have heqV := congrArg
      (fun t : q₁.vectorOrthogonal b.tail.head ↦ (t : V)) heq
    simp only [Submodule.coe_sub] at heqV
    change (y₂ : V) - (z : V) ∈ D.pref.carrier
    rw [heqV, q₂.lineProjection_apply]
    exact D.pref.carrier.smul_mem _ D.tail_tail_head_mem_pref_carrier
  have hyz : (y : V) - (z : V) ∈ D.pref.carrier := by
    have heq : (y : V) - (z : V) =
        ((y : V) - (y₁ : V)) + ((y₁ : V) - (y₂ : V)) +
          ((y₂ : V) - (z : V)) := by
      abel
    rw [heq]
    exact D.pref.carrier.add_mem
      (D.pref.carrier.add_mem hdiff₀ hdiff₁) hdiff₂
  have hyw : (y : V) - (w : V) ∈ D.pref.carrier := by
    have hp := congrArg Subtype.val hprojResidual
    rw [QuadraticSpace.projectionToOrthogonal_coe] at hp
    have hd := ((D.decomposition.component 1).space).lineProjection_add_orthogonalProjection
      D.residual y
    rw [hp] at hd
    have heq : y - (w : (D.decomposition.component 1).carrier) =
        (D.decomposition.component 1).space.lineProjection D.residual y := by
      calc
        y - (w : (D.decomposition.component 1).carrier) =
            ((D.decomposition.component 1).space.lineProjection D.residual y +
              (w : (D.decomposition.component 1).carrier)) -
                (w : (D.decomposition.component 1).carrier) :=
          congrArg
            (fun t : (D.decomposition.component 1).carrier ↦
              t - (w : (D.decomposition.component 1).carrier)) hd.symm
        _ = (D.decomposition.component 1).space.lineProjection
            D.residual y := by abel
    have heqV := congrArg
      (fun t : (D.decomposition.component 1).carrier ↦ (t : V)) heq
    simp only [Submodule.coe_sub] at heqV
    change (y : V) - (w : V) ∈ D.pref.carrier
    rw [heqV,
      (D.decomposition.component 1).space.lineProjection_apply]
    exact D.pref.carrier.smul_mem _ D.residual_mem_pref_carrier
  have hwzPref : (w : V) - (z : V) ∈ D.pref.carrier := by
    have heq : (w : V) - (z : V) =
        ((y : V) - (z : V)) - ((y : V) - (w : V)) := by
      abel
    rw [heq]
    exact D.pref.carrier.sub_mem hyz hyw
  let d : D.pref.carrier := ⟨(w : V) - (z : V), hwzPref⟩
  have hdZero : d = 0 := by
    apply D.pref.toSegmentWitness.nondegenerate.1 d
    intro p
    change q.bilin ((w : V) - (z : V)) (p : V) = 0
    rw [LinearMap.BilinForm.sub_left]
    have hwOrth : q.bilin (w : V) (p : V) = 0 := by
      rw [q.isSymm.eq]
      exact D.pref_bilin_residualOrthogonal_eq_zero p w
    have hzOrth : q.bilin (z : V) (p : V) = 0 := by
      rw [q.isSymm.eq]
      exact D.thirdTail_bilin_pref_eq_zero p z
    rw [hwOrth, hzOrth, sub_zero]
  have hwz : (w : V) = (z : V) := by
    have h := congrArg Subtype.val hdZero
    change (w : V) - (z : V) = 0 at h
    exact sub_eq_zero.mp h
  have htarget : D.recursiveThirdTailLinearEquiv z = w := by
    apply Subtype.ext
    apply Subtype.ext
    rw [D.recursiveThirdTailLinearEquiv_coe]
    exact hwz.symm
  exact ⟨z, hz, htarget⟩

/-- The projected global remainder lattice is exactly the transported
unchanged suffix lattice. -/
theorem recursiveThirdTailMappedLattice_eq_projectedLattice
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    D.recursiveThirdTailMappedLattice =
      (D.decomposition.component 1).lattice.projectedLattice
        (D.decomposition.component 1).space D.residual
        D.residual_isAnisotropic := by
  apply Lattice.ext
  exact le_antisymm
    D.recursiveThirdTailMappedLattice_le_projectedLattice
    D.projectedLattice_le_recursiveThirdTailMappedLattice

/-- The unchanged suffix BONG, now indexed by the actual projection lattice
of the global remainder. -/
noncomputable def recursiveThirdTailProjectedBONG
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    BONG ((D.decomposition.component 1).space.vectorOrthogonal D.residual)
      ((D.decomposition.component 1).space.orthogonalSpace D.residual
        D.residual_isAnisotropic)
      ((D.decomposition.component 1).lattice.projectedLattice
        (D.decomposition.component 1).space D.residual
        D.residual_isAnisotropic) n :=
  D.recursiveThirdTailMappedBONG.castLattice
    D.recursiveThirdTailMappedLattice_eq_projectedLattice

@[simp]
theorem recursiveThirdTailProjectedBONG_value
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (j : Fin n) :
    D.recursiveThirdTailProjectedBONG.value j =
      b.value ⟨j.val + 3, by omega⟩ := by
  rw [recursiveThirdTailProjectedBONG, BONG.value_castLattice,
    D.recursiveThirdTailMappedBONG_value]

/-- The exact replacement BONG of the global complementary component. -/
noncomputable def exactRemainderBONG
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    BONG (D.decomposition.component 1).carrier
      (D.decomposition.component 1).space
      (D.decomposition.component 1).lattice (n + 1) :=
  BONG.cons D.residual D.residual_generator D.residual_isAnisotropic
    D.recursiveThirdTailProjectedBONG

@[simp]
theorem exactRemainderBONG_value_zero
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    D.exactRemainderBONG.value 0 =
      (b.lemma73ResidualValue (0 : Fin (n + 1)) : K) := by
  rw [exactRemainderBONG, BONG.value_cons_zero]
  exact D.residual_value

@[simp]
theorem exactRemainderBONG_value_succ
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (j : Fin n) :
    D.exactRemainderBONG.value j.succ =
      b.value ⟨j.val + 3, by omega⟩ := by
  rw [exactRemainderBONG, BONG.value_cons_succ,
    D.recursiveThirdTailProjectedBONG_value]

@[simp]
theorem exactRemainderBONG_order_zero
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    D.exactRemainderBONG.order 0 = b.order 0 := by
  apply WithTop.coe_injective
  rw [D.exactRemainderBONG.coe_order, b.coe_order,
    D.exactRemainderBONG_value_zero]
  rw [← coe_ordUnit, b.ordUnit_lemma73ResidualValue]
  simpa [lemma73FirstIndex] using b.coe_order (0 : Fin (n + 3))

@[simp]
theorem exactRemainderBONG_order_succ
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (j : Fin n) :
    D.exactRemainderBONG.order j.succ =
      b.order ⟨j.val + 3, by omega⟩ := by
  apply WithTop.coe_injective
  rw [D.exactRemainderBONG.coe_order, b.coe_order,
    D.exactRemainderBONG_value_succ]

/-- Goodness of the replacement sequence follows directly from goodness of
the original sequence: the new first-to-third comparison is the composite
`R₀ ≤ R₂ ≤ R₄`, and every later comparison is unchanged. -/
theorem exactRemainderBONG_isGood
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (hgood : b.IsGood) :
    D.exactRemainderBONG.IsGood := by
  intro i hi
  cases i using Fin.cases with
  | zero =>
      simp only [Fin.val_zero] at hi
      let j : Fin n := ⟨1, by omega⟩
      let i₀ : Fin (n + 3) := ⟨0, by omega⟩
      let i₂ : Fin (n + 3) := ⟨2, by omega⟩
      have h₀₂ := hgood i₀ (by simp [i₀])
      have h₂₄ := hgood i₂ (by simp [i₂]; omega)
      have hindex : j.succ = (⟨2, hi⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp [j]
      calc
        D.exactRemainderBONG.order 0 = b.order 0 :=
          D.exactRemainderBONG_order_zero
        _ ≤ b.order i₂ := by simpa [i₀, i₂] using h₀₂
        _ ≤ b.order ⟨j.val + 3, by omega⟩ := by
          simpa [i₂, j] using h₂₄
        _ = D.exactRemainderBONG.order j.succ :=
          (D.exactRemainderBONG_order_succ j).symm
        _ = D.exactRemainderBONG.order ⟨2, hi⟩ :=
          congrArg D.exactRemainderBONG.order hindex
  | succ j =>
      simp only [Fin.val_succ] at hi
      let k : Fin n := ⟨j.val + 2, by omega⟩
      let old : Fin (n + 3) := ⟨j.val + 3, by omega⟩
      have hold := hgood old (by simp [old]; omega)
      have hindex : k.succ =
          (⟨j.succ.val + 2, hi⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp [k]
      calc
        D.exactRemainderBONG.order j.succ =
            b.order ⟨j.val + 3, by omega⟩ :=
          D.exactRemainderBONG_order_succ j
        _ ≤ b.order ⟨k.val + 3, by omega⟩ := by
          simpa [old, k] using hold
        _ = D.exactRemainderBONG.order k.succ :=
          (D.exactRemainderBONG_order_succ k).symm
        _ = D.exactRemainderBONG.order
            ⟨j.succ.val + 2, hi⟩ :=
          congrArg D.exactRemainderBONG.order hindex

/-- Package the global hyperbolic splitting and the exact unchanged suffix
as the full conclusion of Lemma 7.3 at the initial position. -/
theorem nonempty_lemma73SplittingWitness
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (hgood : b.IsGood) :
    Nonempty (b.Lemma73SplittingWitness (0 : Fin (n + 1))) := by
  let c := D.exactRemainderBONG
  let remainderNorm : Lattice.NormOrderDatum
      (D.decomposition.component 1).space
      (D.decomposition.component 1).lattice := {
    generator := c.valueUnit 0
    normIdeal_eq := by
      simpa [c.value_zero_eq_quadratic_head] using
        c.head_isNormGenerator.normIdeal_eq }
  let splitting : Lattice.HyperbolicPlaneSplitting q L := {
    decomposition := D.decomposition
    scaleOrder := b.lemma73HyperbolicScaleOrder (0 : Fin (n + 1))
    hyperbolic := D.hyperbolic
    remainderNorm := remainderNorm }
  refine ⟨{
    decomposition := D.decomposition
    hyperbolic := D.hyperbolic
    remainderBONG := c
    value_before := ?_
    replacement_value := ?_
    value_after := ?_
    componentNormData := splitting.componentNormData
    hyperbolicNorm_order := ?_
    remainderNorm_order := ?_
    good := ?_ }⟩
  · intro j hj
    change j.val < 0 at hj
    omega
  · simpa only [c] using D.exactRemainderBONG_value_zero
  · intro j hj
    change 0 < j.val at hj
    cases j using Fin.cases with
    | zero =>
        change 0 < 0 at hj
        omega
    | succ k =>
        simpa only [c, Fin.val_succ, Nat.succ_eq_add_one,
          Nat.add_assoc, Nat.one_add] using
          D.exactRemainderBONG_value_succ k
  · change splitting.hyperbolicNorm.order = _
    rw [Lattice.HyperbolicPlaneSplitting.hyperbolicNorm_order]
    rfl
  · change remainderNorm.order = b.order 0
    change ordUnit K (c.valueUnit 0) = b.order 0
    rw [← c.order_eq_ordUnit]
    exact D.exactRemainderBONG_order_zero
  · exact D.exactRemainderBONG_isGood hgood

/-- The first three ambient BONG vectors lie in the retained prefix carrier. -/
theorem ambientVector_mem_pref_carrier
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (j : Fin (n + 3))
    (hj : j.val < 3) : b.ambientVector j ∈ D.pref.carrier := by
  rw [D.pref.toSegmentWitness.carrier_eq_segmentCarrier, segmentCarrier]
  apply Submodule.subset_span
  let i : Fin 3 := ⟨j.val, hj⟩
  refine ⟨i, ?_⟩
  apply congrArg b.ambientVector
  apply Fin.ext
  simp [i, segmentIndex]

/-
/-- The retained hyperbolic component has field rank two. -/
theorem component_zero_finrank
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Module.finrank K (D.decomposition.component 0).carrier = 2 := by
  rcases D.hyperbolic with ⟨f⟩
  have hfin := f.toLinearEquiv.finrank_eq
  simpa only [Module.finrank_fin_fun] using hfin

/-- Removing the hyperbolic plane leaves the expected rank. -/
theorem component_one_finrank
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Module.finrank K (D.decomposition.component 1).carrier = n + 1 := by
  letI : Module.Finite K V := L.moduleFinite
  letI (i : Fin 2) : Module.Finite K
      (D.decomposition.component i).carrier :=
    (D.decomposition.component i).lattice.moduleFinite
  have hsum := D.decomposition.carrierDirectSumEquiv.finrank_eq
  rw [Module.finrank_directSum] at hsum
  have hsum' :
      Module.finrank K (D.decomposition.component 0).carrier +
          Module.finrank K (D.decomposition.component 1).carrier =
        Module.finrank K V := by
    simpa only [Fin.sum_univ_two] using hsum
  have hambient := b.length_eq_finrank
  rw [D.component_zero_finrank] at hsum'
  omega

/-- The exact residual value is nonzero, so the retained norm generator is
anisotropic in the global complement. -/
theorem residual_isAnisotropic
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (D.decomposition.component 1).space.IsAnisotropic D.residual := by
  change (D.decomposition.component 1).space.quadratic D.residual ≠ 0
  rw [D.residual_value]
  exact Units.ne_zero _
-/

/-- The literal ambient inclusion of the unchanged suffix into the
orthogonal complement of the residual vector inside the global remainder. -/
def thirdTailToResidualOrthogonalLinearMap
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (thirdTailSegment b).carrier →ₗ[K]
      (D.decomposition.component 1).space.vectorOrthogonal D.residual where
  toFun z := ⟨⟨z, D.thirdTailSegment_mem_component_one z⟩, by
    rw [(D.decomposition.component 1).space.mem_vectorOrthogonal_iff]
    exact D.residual_bilin_thirdTailSegment_eq_zero z⟩
  map_add' z w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' a z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem thirdTailToResidualOrthogonalLinearMap_injective
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Function.Injective D.thirdTailToResidualOrthogonalLinearMap := by
  intro z w hzw
  apply Subtype.ext
  have h₁ :
      (D.thirdTailToResidualOrthogonalLinearMap z :
          (D.decomposition.component 1).carrier) =
        (D.thirdTailToResidualOrthogonalLinearMap w :
          (D.decomposition.component 1).carrier) :=
    congrArg (fun y :
      (D.decomposition.component 1).space.vectorOrthogonal D.residual ↦
        (y : (D.decomposition.component 1).carrier)) hzw
  exact congrArg (fun y : (D.decomposition.component 1).carrier ↦
    (y : V)) h₁

theorem thirdTailToResidualOrthogonal_finrank_eq
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Module.finrank K (thirdTailSegment b).carrier =
      Module.finrank K
        ((D.decomposition.component 1).space.vectorOrthogonal D.residual) := by
  letI : Module.Finite K (thirdTailSegment b).carrier :=
    (thirdTailSegment b).lattice.moduleFinite
  letI : Module.Finite K (D.decomposition.component 1).carrier :=
    (D.decomposition.component 1).lattice.moduleFinite
  have hsource := (thirdTailSegment b).bong.length_eq_finrank
  have htarget := (D.decomposition.component 1).space.finrank_vectorOrthogonal
    D.residual_isAnisotropic
  rw [D.component_one_finrank] at htarget
  omega

/-- The unchanged suffix space is exactly the orthogonal complement of the
residual line in the global remainder. -/
noncomputable def thirdTailToResidualOrthogonalLinearEquiv
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (thirdTailSegment b).carrier ≃ₗ[K]
      (D.decomposition.component 1).space.vectorOrthogonal D.residual := by
  letI : FiniteDimensional K (thirdTailSegment b).carrier :=
    (thirdTailSegment b).bong.basis.finiteDimensional_of_finite
  letI : FiniteDimensional K (D.decomposition.component 1).carrier :=
    (D.decomposition.component 1).lattice.ambientBasis.finiteDimensional_of_finite
  letI : FiniteDimensional K
      ((D.decomposition.component 1).space.vectorOrthogonal D.residual) :=
    FiniteDimensional.of_injective (Submodule.subtype _) Subtype.val_injective
  exact LinearEquiv.ofInjectiveOfFinrankEq
    D.thirdTailToResidualOrthogonalLinearMap
    D.thirdTailToResidualOrthogonalLinearMap_injective
    D.thirdTailToResidualOrthogonal_finrank_eq

@[simp]
theorem thirdTailToResidualOrthogonalLinearEquiv_coe
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (z : (thirdTailSegment b).carrier) :
    (((D.thirdTailToResidualOrthogonalLinearEquiv z :
        (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
      (D.decomposition.component 1).carrier) : V) = (z : V) :=
  by
    dsimp only [thirdTailToResidualOrthogonalLinearEquiv,
      LinearEquiv.ofInjectiveOfFinrankEq]
    rfl

/-- The preceding linear equivalence preserves the restricted quadratic
forms, since both sides use the same literal ambient vectors. -/
noncomputable def thirdTailToResidualOrthogonalIsometry
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    (q.restrict (thirdTailSegment b).carrier
      (thirdTailSegment b).nondegenerate).Isometry
      ((D.decomposition.component 1).space.orthogonalSpace D.residual
        D.residual_isAnisotropic) where
  toLinearEquiv := D.thirdTailToResidualOrthogonalLinearEquiv
  map_bilin z w := by
    change q.bilin
      (((D.thirdTailToResidualOrthogonalLinearEquiv z :
          (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
        (D.decomposition.component 1).carrier) : V)
      (((D.thirdTailToResidualOrthogonalLinearEquiv w :
          (D.decomposition.component 1).space.vectorOrthogonal D.residual) :
        (D.decomposition.component 1).carrier) : V) =
      q.bilin (z : V) (w : V)
    rw [D.thirdTailToResidualOrthogonalLinearEquiv_coe,
      D.thirdTailToResidualOrthogonalLinearEquiv_coe]

/-- The unchanged suffix lattice transported into the residual orthogonal
space. -/
noncomputable def thirdTailMappedLattice
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    Lattice K
      ((D.decomposition.component 1).space.vectorOrthogonal D.residual) :=
  Lattice.map D.thirdTailToResidualOrthogonalIsometry.toLinearEquiv
    (thirdTailSegment b).lattice

/-- The corresponding transported suffix BONG. -/
noncomputable def thirdTailMappedBONG
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    BONG ((D.decomposition.component 1).space.vectorOrthogonal D.residual)
      ((D.decomposition.component 1).space.orthogonalSpace D.residual
        D.residual_isAnisotropic)
      D.thirdTailMappedLattice n :=
  (thirdTailSegment b).bong.map D.thirdTailToResidualOrthogonalIsometry

@[simp]
theorem thirdTailMappedBONG_value
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) (j : Fin n) :
    D.thirdTailMappedBONG.value j =
      b.value ⟨j.val + 3, by omega⟩ := by
  calc
    D.thirdTailMappedBONG.value j =
        (thirdTailSegment b).bong.value j := by
      simpa only [thirdTailMappedBONG, thirdTailMappedLattice] using
        BONG.value_map D.thirdTailToResidualOrthogonalIsometry
          (thirdTailSegment b).bong j
    _ = b.value ((thirdTailSegment b).sourceIndex j) :=
      (thirdTailSegment b).value_eq j
    _ = b.value ⟨j.val + 3, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp [SegmentWitness.sourceIndex]
      omega

/-
/-- Every vector of the unchanged suffix lattice is the iterated orthogonal
projection of a parent-lattice vector; their difference lies in the initial
ternary prefix. -/
theorem exists_parent_sub_mem_pref_of_mem_thirdTailSegment
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b)
    (z : (thirdTailSegment b).carrier)
    (hz : z ∈ (thirdTailSegment b).lattice) :
    ∃ y : V, y ∈ L ∧ y - (z : V) ∈ D.pref.carrier := by
  cases b with
  | @cons _ _ _ _ _ _ x₀ generator₀ anisotropic₀ tail₀ =>
      cases tail₀ with
      | @cons _ _ _ _ _ _ x₁ generator₁ anisotropic₁ tail₁ =>
          cases tail₁ with
          | @cons _ _ _ _ _ _ x₂ generator₂ anisotropic₂ tail₂ =>
              let w₀ := SegmentWitness.whole tail₂
              let w₁ := w₀.liftTail (generator := generator₂)
              let w₂ := w₁.liftTail (generator := generator₁)
              let w₃ := w₂.liftTail (generator := generator₀)
              have hcarrier :
                  (thirdTailSegment (BONG.cons x₀ generator₀ anisotropic₀
                    (BONG.cons x₁ generator₁ anisotropic₁
                      (BONG.cons x₂ generator₂ anisotropic₂ tail₂)))).carrier =
                    w₃.carrier := by
                exact (thirdTailSegment _).carrier_eq_segmentCarrier.trans
                  w₃.carrier_eq_segmentCarrier.symm
              let z₃ : w₃.carrier := ⟨z, by
                rw [← hcarrier]
                exact z.property⟩
              have hz₃ : z₃ ∈ w₃.lattice := by
                simpa only [thirdTailSegment, w₃, w₂, w₁, w₀, z₃,
                  Subtype.coe_eta] using hz
              let F₃ := w₂.liftTailLatticeIsometry
                (generator := generator₀)
              let z₂ : w₂.carrier := F₃.toLinearEquiv.symm z₃
              have hz₂ : z₂ ∈ w₂.lattice := by
                apply (F₃.map_mem z₂).2
                simpa only [z₂, LinearEquiv.apply_symm_apply] using hz₃
              let F₂ := w₁.liftTailLatticeIsometry
                (generator := generator₁)
              let z₁ : w₁.carrier := F₂.toLinearEquiv.symm z₂
              have hz₁ : z₁ ∈ w₁.lattice := by
                apply (F₂.map_mem z₁).2
                simpa only [z₁, LinearEquiv.apply_symm_apply] using hz₂
              let F₁ := w₀.liftTailLatticeIsometry
                (generator := generator₂)
              let z₀ : w₀.carrier := F₁.toLinearEquiv.symm z₁
              have hz₀ : z₀ ∈ w₀.lattice := by
                apply (F₁.map_mem z₀).2
                simpa only [z₀, LinearEquiv.apply_symm_apply] using hz₁
              let F₀ := SegmentWitness.wholeLatticeIsometry tail₂
              let u := F₀.toLinearEquiv.symm z₀
              have hu : u ∈ tail₂.lattice := by
                apply (F₀.map_mem u).2
                simpa only [u, LinearEquiv.apply_symm_apply] using hz₀
              rcases (Lattice.mem_projectedLattice_iff _ _ x₂ anisotropic₂ u).1 hu
                with ⟨y₂, hy₂, hproj₂⟩
              rcases (Lattice.mem_projectedLattice_iff _ _ x₁ anisotropic₁ y₂).1 hy₂
                with ⟨y₁, hy₁, hproj₁⟩
              rcases (Lattice.mem_projectedLattice_iff _ _ x₀ anisotropic₀ y₁).1 hy₁
                with ⟨y₀, hy₀, hproj₀⟩
              refine ⟨y₀, hy₀, ?_⟩
              have hx₀ : x₀ ∈ D.pref.carrier := by
                simpa only [BONG.ambientVector_cons_zero] using
                  D.ambientVector_mem_pref_carrier (0 : Fin (n + 3)) (by omega)
              have hx₁ : (x₁ : V) ∈ D.pref.carrier := by
                simpa only [BONG.ambientVector_cons_succ,
                  BONG.ambientVector_cons_zero] using
                  D.ambientVector_mem_pref_carrier
                    (1 : Fin (n + 3)) (by omega)
              have hx₂ : (x₂ : V) ∈ D.pref.carrier := by
                simpa only [BONG.ambientVector_cons_succ,
                  BONG.ambientVector_cons_zero] using
                  D.ambientVector_mem_pref_carrier
                    (2 : Fin (n + 3)) (by omega)
              have hdiff₀ : y₀ - (y₁ : V) ∈ D.pref.carrier := by
                have hp := congrArg Subtype.val hproj₀
                have hd := q.lineProjection_add_orthogonalProjection x₀ y₀
                rw [hp] at hd
                have heq : y₀ - (y₁ : V) = q.lineProjection x₀ y₀ := by
                  linear_combination hd
                rw [heq, q.lineProjection_apply]
                exact D.pref.carrier.smul_mem _ hx₀
              have hdiff₁ : (y₁ : V) - (y₂ : V) ∈ D.pref.carrier := by
                have hp := congrArg Subtype.val hproj₁
                have hd :=
                  (q.orthogonalSpace x₀ anisotropic₀).
                    lineProjection_add_orthogonalProjection x₁ y₁
                rw [hp] at hd
                have heq : y₁ - (y₂ : _) =
                    (q.orthogonalSpace x₀ anisotropic₀).
                      lineProjection x₁ y₁ := by
                  linear_combination hd
                have heqV := congrArg (fun t ↦ (t : V)) heq
                change (y₁ : V) - (y₂ : V) ∈ D.pref.carrier
                rw [heqV,
                  (q.orthogonalSpace x₀ anisotropic₀).lineProjection_apply]
                exact D.pref.carrier.smul_mem _ hx₁
              have hdiff₂ : (y₂ : V) - (u : V) ∈ D.pref.carrier := by
                have hp := congrArg Subtype.val hproj₂
                have hd :=
                  ((q.orthogonalSpace x₀ anisotropic₀).orthogonalSpace
                    x₁ anisotropic₁).lineProjection_add_orthogonalProjection
                      x₂ y₂
                rw [hp] at hd
                have heq : y₂ - (u : _) =
                    ((q.orthogonalSpace x₀ anisotropic₀).orthogonalSpace
                      x₁ anisotropic₁).lineProjection x₂ y₂ := by
                  linear_combination hd
                have heqV := congrArg (fun t ↦ (t : V)) heq
                change (y₂ : V) - (u : V) ∈ D.pref.carrier
                rw [heqV,
                  ((q.orthogonalSpace x₀ anisotropic₀).orthogonalSpace
                    x₁ anisotropic₁).lineProjection_apply]
                exact D.pref.carrier.smul_mem _ hx₂
              have huz : (u : V) = (z : V) := by
                simp only [u, z₀, z₁, z₂, F₀, F₁, F₂, F₃,
                  LinearEquiv.apply_symm_apply]
                change (z₃ : V) = (z : V)
                rfl
              have hsum : y₀ - (z : V) =
                  (y₀ - (y₁ : V)) +
                    ((y₁ : V) - (y₂ : V)) +
                      ((y₂ : V) - (u : V)) := by
                rw [huz]
                abel
              rw [hsum]
              exact D.pref.carrier.add_mem
                (D.pref.carrier.add_mem hdiff₀ hdiff₁) hdiff₂
-/

/-- A residual-headed BONG of the global complement.  Its head already has
the exact replacement value; the remaining task is to identify its projected
tail with the unchanged suffix of the original BONG. -/
noncomputable def preliminaryRemainderBONG
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    BONG (D.decomposition.component 1).carrier
      (D.decomposition.component 1).space
      (D.decomposition.component 1).lattice (n + 1) :=
  BONG.ofNormGenerator D.residual D.residual_generator
    D.residual_isAnisotropic D.component_one_finrank

@[simp]
theorem preliminaryRemainderBONG_value_zero
    {n : Nat} {b : BONG V q L (n + 3)}
    (D : Lemma73HeadMiddleLeData b) :
    D.preliminaryRemainderBONG.value 0 =
      (b.lemma73ResidualValue (0 : Fin (n + 1)) : K) := by
  rw [D.preliminaryRemainderBONG.value_zero_eq_quadratic_head]
  change (D.decomposition.component 1).space.quadratic D.residual = _
  exact D.residual_value

end Lemma73HeadMiddleLeData

/-- In the branch `R₁ ≤ R₀`, the hyperbolic component constructed in
the initial ternary prefix has the ambient scale and hence splits from the
whole lattice.  This is the geometric globalization step in Beli's proof. -/
theorem exists_lemma73HeadMiddleLeData
    {n : Nat} (b : BONG V q L (n + 3)) (hgood : b.IsGood)
    (h : b.Lemma73Hypotheses (0 : Fin (n + 1)))
    (hupper : b.order (1 : Fin (n + 3)) ≤ b.order 0) :
    Nonempty (Lemma73HeadMiddleLeData b) := by
  let pref := b.prefixWitness 3 (by omega)
  let block := pref.toSegmentWitness
  have hblock : block.bong.Lemma73Hypotheses (0 : Fin 1) :=
    block.lemma73Hypotheses (0 : Fin (n + 1)) h
  rcases block.bong.exists_lemma73LocalSplittingWitness_of_hypotheses
      (block.isGood hgood) hblock with ⟨localWitness⟩
  let outer := block.toQuadraticSublattice
  let localHyperbolic := localWitness.decomposition.component 0
  let liftedHyperbolic := outer.liftNested localHyperbolic
  have hscaleOrder :
      block.bong.lemma73HyperbolicScaleOrder (0 : Fin 1) =
        b.lemma73HyperbolicScaleOrder (0 : Fin (n + 1)) := by
    unfold lemma73HyperbolicScaleOrder
    rw [block.order_eq, block.order_eq]
    congr 2
  have hresidual :
      block.bong.lemma73ResidualValue (0 : Fin 1) =
        b.lemma73ResidualValue (0 : Fin (n + 1)) := by
    unfold lemma73ResidualValue
    rw [block.order_eq, block.normalizedValue_eq,
      block.normalizedValue_eq, block.normalizedValue_eq]
    congr 2
  let scale := uniformizerPowerUnit K
    (b.lemma73HyperbolicScaleOrder (0 : Fin (n + 1)))
  have hlocalHyperbolic : Lattice.IsIsometric localHyperbolic.space
      (QuadraticSpace.hyperbolicPlane scale)
      localHyperbolic.lattice
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
    simpa only [scale, hscaleOrder] using localWitness.hyperbolic
  have hmodularLocal : Lattice.IsModular localHyperbolic.space
      localHyperbolic.lattice scale := by
    rcases hlocalHyperbolic with ⟨f⟩
    exact (Lattice.hyperbolicPlaneLattice_isModular scale).mapLatticeIsometry
      f.symm
  have hmodular : Lattice.IsModular liftedHyperbolic.space
      liftedHyperbolic.lattice scale :=
    Lattice.QuadraticSublattice.IsModular.liftNested
      outer localHyperbolic hmodularLocal
  have hcontained : liftedHyperbolic.ambientSubmodule ≤ L.toSubmodule := by
    intro z hz
    rw [outer.mem_liftNested_ambientSubmodule_iff] at hz
    rcases hz with ⟨y, hy, rfl⟩
    apply pref.contained
    exact localWitness.decomposition.component_ambientSubmodule_le 0
      ⟨y, hy, rfl⟩
  have hunit₀ : beliSpinorGroupRepresentative K
        (block.bong.adjacentParameter 0 (by omega)) ≤
      valuationUnitSquareClassSubgroup K := by
    have hclass := hblock.2.1
    change beliSpinorGroup K
        (block.bong.adjacentUnitSquareClass 0 (by omega)) ≤
      valuationUnitSquareClassSubgroup K at hclass
    simpa only [adjacentUnitSquareClass,
      beliSpinorGroup_unitSquareClass] using hclass
  have hcriterion₀ := (Dyadic.beliLemma72_i (K := K)
    (block.bong.adjacentParameter 0 (by omega))
    (block.bong.adjacentParameter_isBinaryParameterAdmissible 0
      (by omega))).1 hunit₀
  have hEven : Even
      (b.order (1 : Fin (n + 3)) - b.order 0) := by
    have hparameterOrder := block.bong.ordUnit_adjacentParameter 0 (by omega)
    change ordUnit K (block.bong.adjacentParameter 0 (by omega)) =
      block.bong.order 1 - block.bong.order 0 at hparameterOrder
    have horders : block.bong.order 1 - block.bong.order 0 =
        b.order (1 : Fin (n + 3)) - b.order 0 := by
      rw [block.order_eq, block.order_eq]
      congr 2
    rw [← horders]
    rw [← hparameterOrder]
    exact hcriterion₀.1
  have hsumEven : Even
      (b.order 0 + b.order (1 : Fin (n + 3))) := by
    rcases hEven with ⟨r, hr⟩
    refine ⟨b.order 0 + r, ?_⟩
    omega
  have hscaleIdeal : Lattice.scaleIdeal q L ≤
      Lattice.principalIdeal (K := K) (scale : K) := by
    rcases b.beliCorollary44_iv_unconditional hgood with
      ⟨a, haScale, haOrder⟩
    have hmin : min (2 * b.order 0)
        (b.order 0 + b.order (1 : Fin (n + 3))) =
          b.order 0 + b.order (1 : Fin (n + 3)) := by
      rw [min_eq_right]
      omega
    rw [hmin] at haOrder
    have haOrder' : ordUnit K a =
        (b.order 0 + b.order (1 : Fin (n + 3))) / 2 := by
      rcases hsumEven with ⟨r, hr⟩
      omega
    have hprincipal : Lattice.principalIdeal (K := K) (a : K) =
        Lattice.principalIdeal (K := K) (scale : K) := by
      apply (Lattice.principalIdeal_eq_iff_ordUnit_eq a scale).2
      rw [haOrder']
      simp [scale]
      unfold lemma73HyperbolicScaleOrder
      rfl
    rw [haScale, hprincipal]
  let decomposition := Lattice.omearaModularSplittingOfScaleIdealLe
    liftedHyperbolic hcontained hmodular hscaleIdeal
  have hglobalHyperbolic : Lattice.IsIsometric
      (decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane scale)
      (decomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
    change Lattice.IsIsometric liftedHyperbolic.space
      (QuadraticSpace.hyperbolicPlane scale)
      liftedHyperbolic.lattice (Lattice.hyperbolicPlaneLattice (K := K))
    rcases hlocalHyperbolic with ⟨f⟩
    exact ⟨(outer.liftNestedIsometry localHyperbolic).symm.trans f⟩
  let localRemainder := localWitness.decomposition.component 1
  let localResidual := localWitness.remainderBONG.head
  let residual : (decomposition.component 1).carrier :=
    ⟨(outer.nestedCarrierEquiv localRemainder localResidual : V), by
      change (outer.nestedCarrierEquiv localRemainder localResidual : V) ∈
        liftedHyperbolic.orthogonalCarrier
      intro y hy
      let y' : localHyperbolic.carrier :=
        (outer.nestedCarrierEquiv localHyperbolic).symm ⟨y, hy⟩
      have horth := localWitness.decomposition.orthogonal 0 1
        (by omega) y' localResidual
      exact horth⟩
  have hresidualMem : residual ∈ (decomposition.component 1).lattice := by
    change (residual : V) ∈ L
    apply pref.contained
    exact localWitness.decomposition.component_ambientSubmodule_le 1
      ⟨localResidual, localWitness.remainderBONG.head_isNormGenerator.mem, rfl⟩
  have hresidualValue :
      (decomposition.component 1).space.quadratic residual =
        (b.lemma73ResidualValue (0 : Fin (n + 1)) : K) := by
    change localRemainder.space.quadratic localResidual = _
    rw [← localWitness.remainderBONG.value_zero_eq_quadratic_head]
    exact localWitness.replacement_value.trans (congrArg Units.val hresidual)
  have hprincipalResidual :
      Lattice.principalIdeal (K := K) (q.quadratic b.head) =
        Lattice.principalIdeal (K := K)
          ((decomposition.component 1).space.quadratic residual) := by
    rw [← b.value_zero_eq_quadratic_head, hresidualValue]
    change Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) =
      Lattice.principalIdeal (K := K)
        (b.lemma73ResidualValue (0 : Fin (n + 1)) : K)
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).2
    rw [← b.order_eq_ordUnit, b.ordUnit_lemma73ResidualValue]
    rfl
  have hresidualGenerator : Lattice.IsNormGenerator
      (decomposition.component 1).space
      (decomposition.component 1).lattice residual := by
    refine ⟨hresidualMem, ?_⟩
    apply le_antisymm
    · calc
        Lattice.normIdeal (decomposition.component 1).space
            (decomposition.component 1).lattice ≤
            Lattice.normIdeal q L :=
          (decomposition.component 1).normIdeal_le_of_ambientSubmodule_le
            (decomposition.component_ambientSubmodule_le 1)
        _ = Lattice.principalIdeal (K := K) (q.quadratic b.head) :=
          b.head_isNormGenerator.normIdeal_eq
        _ = Lattice.principalIdeal (K := K)
            ((decomposition.component 1).space.quadratic residual) :=
          hprincipalResidual
    · rw [Lattice.principalIdeal, Submodule.span_le,
        Set.singleton_subset_iff]
      exact Lattice.quadratic_mem_normIdeal_of_mem
        (decomposition.component 1).space
        (decomposition.component 1).lattice hresidualMem
  exact ⟨{
    pref := pref
    localWitness := localWitness
    decomposition := decomposition
    component_zero := rfl
    component_one_carrier := rfl
    component_one_mem_iff := by
      intro y
      rfl
    residual := residual
    residual_ambient_eq := rfl
    residual_mem := hresidualMem
    residual_value := hresidualValue
    residual_generator := hresidualGenerator
    hyperbolic := hglobalHyperbolic }⟩

/-- Existential projection of the retained globalization data. -/
theorem exists_lemma73HeadHyperbolicDecomposition_of_middle_le
    {n : Nat} (b : BONG V q L (n + 3)) (hgood : b.IsGood)
    (h : b.Lemma73Hypotheses (0 : Fin (n + 1)))
    (hupper : b.order (1 : Fin (n + 3)) ≤ b.order 0) :
    ∃ decomposition : Lattice.OrthogonalDecomposition q L 2,
      Lattice.IsIsometric (decomposition.component 0).space
        (QuadraticSpace.hyperbolicPlane
          (uniformizerPowerUnit K
            (b.lemma73HyperbolicScaleOrder (0 : Fin (n + 1)))))
        (decomposition.component 0).lattice
        (Lattice.hyperbolicPlaneLattice (K := K)) := by
  rcases b.exists_lemma73HeadMiddleLeData hgood h hupper with ⟨D⟩
  exact ⟨D.decomposition, D.hyperbolic⟩

/-- Full arbitrary-rank initial-position conclusion in the order branch
`R₁ ≤ R₀`. -/
theorem exists_lemma73HeadSplittingWitness_of_middle_le
    {n : Nat} (b : BONG V q L (n + 3)) (hgood : b.IsGood)
    (h : b.Lemma73Hypotheses (0 : Fin (n + 1)))
    (hupper : b.order (1 : Fin (n + 3)) ≤ b.order 0) :
    Nonempty (b.Lemma73SplittingWitness (0 : Fin (n + 1))) := by
  rcases b.exists_lemma73HeadMiddleLeData hgood h hupper with ⟨D⟩
  exact D.nonempty_lemma73SplittingWitness hgood

namespace TwoBlockSplitWitness

/-- A two-block witness with its consecutive segment components made
definitionally visible.  This avoids dependent transports when a splitting
inside the right block is flattened into the ambient lattice. -/
noncomputable def canonicalDecomposition
    {n cut : Nat} {b : BONG V q L n} {hcut : cut ≤ n}
    (S : TwoBlockSplitWitness b cut hcut) :
    Lattice.OrthogonalDecomposition q L 2 := by
  let component : Fin 2 → Lattice.QuadraticSublattice q :=
    Fin.cases S.left.toQuadraticSublattice
      (fun _ ↦ S.right.toQuadraticSublattice)
  exact {
    component := component
    orthogonal := by
      intro i j hij x y
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact S.left_right_orthogonal x y
      · exact S.right_left_orthogonal x y
      · exact (hij rfl).elim
    sum_eq := by
      calc
        (⨆ i, (component i).ambientSubmodule) =
            S.left.toQuadraticSublattice.ambientSubmodule ⊔
              S.right.toQuadraticSublattice.ambientSubmodule := by
          apply le_antisymm
          · apply iSup_le
            intro i
            fin_cases i
            · exact le_sup_left
            · exact le_sup_right
          · apply sup_le
            · exact le_iSup
                (fun i : Fin 2 ↦ (component i).ambientSubmodule) 0
            · exact le_iSup
                (fun i : Fin 2 ↦ (component i).ambientSubmodule) 1
        _ = L.toSubmodule := S.ambientSubmodule_sup_eq }

@[simp]
theorem canonicalDecomposition_component_zero
    {n cut : Nat} {b : BONG V q L n} {hcut : cut ≤ n}
    (S : TwoBlockSplitWitness b cut hcut) :
    (S.canonicalDecomposition.component 0) =
      S.left.toQuadraticSublattice :=
  rfl

@[simp]
theorem canonicalDecomposition_component_one
    {n cut : Nat} {b : BONG V q L n} {hcut : cut ≤ n}
    (S : TwoBlockSplitWitness b cut hcut) :
    (S.canonicalDecomposition.component 1) =
      S.right.toQuadraticSublattice :=
  rfl

end TwoBlockSplitWitness

/-- Casting only the length index does not change BONG values. -/
@[simp]
theorem value_castLength_index'
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m s : Nat}
    (c : BONG W r M m) (hs : m = s) (j : Fin s) :
    (c.castLength hs).value j =
      c.value ⟨j.val, by simpa [hs] using j.isLt⟩ := by
  subst s
  rfl

/-- Casting only the length index does not change normalized unit values. -/
@[simp]
theorem valueUnit_castLength_index'
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m s : Nat}
    (c : BONG W r M m) (hs : m = s) (j : Fin s) :
    (c.castLength hs).valueUnit j =
      c.valueUnit ⟨j.val, by simpa [hs] using j.isLt⟩ := by
  apply Units.ext
  exact c.value_castLength_index' hs j

namespace GoodBONG

/-- Casting the length of a good BONG preserves its value sequence. -/
@[simp]
theorem value_castLength'
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m s : Nat}
    (c : GoodBONG r M m) (hs : m = s) (j : Fin s) :
    (c.castLength hs).value j =
      c.value ⟨j.val, by simpa [hs] using j.isLt⟩ := by
  subst s
  rfl

end GoodBONG

/-- The good right segment at a positive Lemma 7.3 position, with its
length normalized to `three plus the remaining suffix length`. -/
noncomputable def lemma73RightGoodBONG
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (S : TwoBlockSplitWitness b i.val (by omega))
    (hgood : b.IsGood)
    (hlen : n + 3 - i.val = (n - i.val) + 3) :
    GoodBONG (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice ((n - i.val) + 3) :=
  (⟨S.right.bong, S.right.isGood hgood⟩ :
    GoodBONG (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice (n + 3 - i.val)).castLength hlen

@[simp]
theorem lemma73RightGoodBONG_value
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (S : TwoBlockSplitWitness b i.val (by omega))
    (hgood : b.IsGood)
    (hlen : n + 3 - i.val = (n - i.val) + 3)
    (j : Fin ((n - i.val) + 3)) :
    (b.lemma73RightGoodBONG i S hgood hlen).value j =
      b.value ⟨i.val + j.val, by omega⟩ := by
  unfold lemma73RightGoodBONG
  rw [GoodBONG.value_castLength']
  change S.right.bong.value _ = _
  rw [S.right.value_eq]
  congr 1

@[simp]
theorem lemma73RightGoodBONG_order
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (S : TwoBlockSplitWitness b i.val (by omega))
    (hgood : b.IsGood)
    (hlen : n + 3 - i.val = (n - i.val) + 3)
    (j : Fin ((n - i.val) + 3)) :
    (b.lemma73RightGoodBONG i S hgood hlen).order j =
      b.order ⟨i.val + j.val, by omega⟩ := by
  unfold lemma73RightGoodBONG
  rw [GoodBONG.order_castLength]
  change S.right.bong.order _ = _
  rw [S.right.order_eq]
  congr 1

@[simp]
theorem lemma73RightGoodBONG_valueUnit
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (S : TwoBlockSplitWitness b i.val (by omega))
    (hgood : b.IsGood)
    (hlen : n + 3 - i.val = (n - i.val) + 3)
    (j : Fin ((n - i.val) + 3)) :
    (b.lemma73RightGoodBONG i S hgood hlen).valueUnit j =
      b.valueUnit ⟨i.val + j.val, by omega⟩ := by
  apply Units.ext
  exact b.lemma73RightGoodBONG_value i S hgood hlen j

@[simp]
theorem lemma73RightGoodBONG_normalizedValue
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (S : TwoBlockSplitWitness b i.val (by omega))
    (hgood : b.IsGood)
    (hlen : n + 3 - i.val = (n - i.val) + 3)
    (j : Fin ((n - i.val) + 3)) :
    (b.lemma73RightGoodBONG i S hgood hlen).toBONG.normalizedValue j =
      b.normalizedValue ⟨i.val + j.val, by omega⟩ := by
  unfold normalizedValue
  change (b.lemma73RightGoodBONG i S hgood hlen).valueUnit j * _ = _
  have horder :
      (b.lemma73RightGoodBONG i S hgood hlen).toBONG.order j =
        b.order ⟨i.val + j.val, by omega⟩ := by
    change (b.lemma73RightGoodBONG i S hgood hlen).order j = _
    exact b.lemma73RightGoodBONG_order i S hgood hlen j
  rw [b.lemma73RightGoodBONG_valueUnit i S hgood hlen, horder]

/-- Lemma 7.3's local hypotheses become the head hypotheses of the good
right segment. -/
theorem lemma73RightGoodBONG_hypotheses
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (S : TwoBlockSplitWitness b i.val (by omega))
    (hgood : b.IsGood)
    (hlen : n + 3 - i.val = (n - i.val) + 3)
    (h : b.Lemma73Hypotheses i) :
    (b.lemma73RightGoodBONG i S hgood hlen).toBONG.Lemma73Hypotheses
      (0 : Fin (n - i.val + 1)) := by
  have hi : i.val ≤ n := by omega
  let c := b.lemma73RightGoodBONG i S hgood hlen
  have hparameter₀ : c.toBONG.adjacentParameter
      (0 : Fin ((n - i.val) + 3)) (by
        change 1 < (n - i.val) + 3
        omega) =
      b.adjacentParameter (lemma73FirstIndex i) (by
        simp only [lemma73FirstIndex]
        omega) := by
    unfold adjacentParameter
    change c.valueUnit 1 / c.valueUnit 0 = _
    rw [b.lemma73RightGoodBONG_valueUnit i S hgood hlen,
      b.lemma73RightGoodBONG_valueUnit i S hgood hlen]
    congr 2
  have hparameter₁ : c.toBONG.adjacentParameter
      (1 : Fin ((n - i.val) + 3)) (by
        change 2 < (n - i.val) + 3
        omega) =
      b.adjacentParameter (lemma73MiddleIndex i) (by
        simp only [lemma73MiddleIndex]
        omega) := by
    unfold adjacentParameter
    change c.valueUnit 2 / c.valueUnit 1 = _
    rw [b.lemma73RightGoodBONG_valueUnit i S hgood hlen,
      b.lemma73RightGoodBONG_valueUnit i S hgood hlen]
    congr 2
  unfold Lemma73Hypotheses at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · change c.order 0 = c.order 2
    rw [b.lemma73RightGoodBONG_order i S hgood hlen,
      b.lemma73RightGoodBONG_order i S hgood hlen]
    exact h.1
  · change beliSpinorGroup K
        (c.toBONG.adjacentUnitSquareClass
          (0 : Fin ((n - i.val) + 3)) (by
            change 1 < (n - i.val) + 3
            omega)) ≤
      valuationUnitSquareClassSubgroup K
    rw [adjacentUnitSquareClass, hparameter₀]
    exact h.2.1
  · change beliSpinorGroup K
        (c.toBONG.adjacentUnitSquareClass
          (1 : Fin ((n - i.val) + 3)) (by
            change 2 < (n - i.val) + 3
            omega)) ≤
      valuationUnitSquareClassSubgroup K
    rw [adjacentUnitSquareClass, hparameter₁]
    exact h.2.2

/-- Data for applying the already proved head branch to the tail beginning
at a positive selected position. -/
structure Lemma73MiddleLeTailData
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hgood : b.IsGood) where
  split : TwoBlockSplitWitness b i.val (by omega)
  length_eq : n + 3 - i.val = (n - i.val) + 3
  witness : ((b.lemma73RightGoodBONG i split hgood length_eq).toBONG).Lemma73SplittingWitness
    (0 : Fin (n - i.val + 1))

/-- In the branch `R_(i+1) ≤ R_i`, Corollary 4.4 splits the prefix from
the selected tail, and the head form of Lemma 7.3 applies inside that tail. -/
theorem exists_lemma73MiddleLeTailData
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hi : 0 < i.val) (hgood : b.IsGood)
    (h : b.Lemma73Hypotheses i)
    (hupper : b.order (lemma73MiddleIndex i) ≤
      b.order (lemma73FirstIndex i)) :
    Nonempty (Lemma73MiddleLeTailData b i hgood) := by
  have hiN : i.val ≤ n := by omega
  let previous : Fin (n + 3) := ⟨i.val - 1, by omega⟩
  have hpreviousTwo : previous.val + 2 < n + 3 := by
    dsimp only [previous]
    omega
  have hpreviousStep := hgood previous hpreviousTwo
  have hprevious : b.order previous ≤
      b.order (lemma73FirstIndex i) := by
    calc
      b.order previous ≤
          b.order ⟨previous.val + 2, hpreviousTwo⟩ := hpreviousStep
      _ = b.order (lemma73MiddleIndex i) := by
        congr 1
        apply Fin.ext
        simp [previous, lemma73MiddleIndex]
        omega
      _ ≤ b.order (lemma73FirstIndex i) := hupper
  have hpreviousAdjacent : b.order previous ≤
      b.order ⟨previous.val + 1, by omega⟩ := by
    calc
      b.order previous ≤ b.order (lemma73FirstIndex i) := hprevious
      _ = b.order ⟨previous.val + 1, by omega⟩ := by
        congr 1
        apply Fin.ext
        simp [previous, lemma73FirstIndex]
        omega
  have hsplit := b.beliCorollary44_i_unconditional hgood previous
    (by dsimp only [previous]; omega) hpreviousAdjacent
  rcases hsplit with ⟨split⟩
  have hcut : previous.val + 1 = i.val := by
    dsimp only [previous]
    omega
  have split' : TwoBlockSplitWitness b i.val (by omega) := by
    simpa only [hcut] using split
  let hlen : n + 3 - i.val = (n - i.val) + 3 := by omega
  let c := b.lemma73RightGoodBONG i split' hgood hlen
  have hcHyp : c.toBONG.Lemma73Hypotheses
      (0 : Fin (n - i.val + 1)) :=
    b.lemma73RightGoodBONG_hypotheses i split' hgood hlen h
  have hcUpper : c.order (1 : Fin ((n - i.val) + 3)) ≤ c.order 0 := by
    rw [b.lemma73RightGoodBONG_order i split' hgood hlen,
      b.lemma73RightGoodBONG_order i split' hgood hlen]
    exact hupper
  rcases c.toBONG.exists_lemma73HeadSplittingWitness_of_middle_le
      c.good hcHyp hcUpper with ⟨witness⟩
  exact ⟨{
    split := split'
    length_eq := hlen
    witness := witness }⟩

namespace Lemma73MiddleLeTailData

variable {n : Nat} {b : BONG V q L (n + 3)} {i : Fin (n + 1)}
  {hgood : b.IsGood}

/-- The right good BONG used by the tail reduction. -/
noncomputable def rightGoodBONG (D : Lemma73MiddleLeTailData b i hgood) :=
  b.lemma73RightGoodBONG i D.split hgood D.length_eq

theorem rightGoodBONG_hyperbolicScaleOrder
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.rightGoodBONG.toBONG.lemma73HyperbolicScaleOrder
        (0 : Fin (n - i.val + 1)) =
      b.lemma73HyperbolicScaleOrder i := by
  unfold lemma73HyperbolicScaleOrder
  change (D.rightGoodBONG.order 0 + D.rightGoodBONG.order 1) / 2 = _
  have hzero : D.rightGoodBONG.order 0 =
      b.order (lemma73FirstIndex i) := by
    unfold rightGoodBONG
    simpa [lemma73FirstIndex] using
      b.lemma73RightGoodBONG_order i D.split hgood D.length_eq 0
  have hone : D.rightGoodBONG.order 1 =
      b.order (lemma73MiddleIndex i) := by
    unfold rightGoodBONG
    simpa [lemma73MiddleIndex] using
      b.lemma73RightGoodBONG_order i D.split hgood D.length_eq 1
  rw [hzero, hone]

theorem rightGoodBONG_residualValue
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.rightGoodBONG.toBONG.lemma73ResidualValue
        (0 : Fin (n - i.val + 1)) =
      b.lemma73ResidualValue i := by
  have horder : D.rightGoodBONG.toBONG.order
      (lemma73FirstIndex (0 : Fin (n - i.val + 1))) =
      b.order (lemma73FirstIndex i) := by
    change D.rightGoodBONG.order 0 = _
    unfold rightGoodBONG
    simpa [lemma73FirstIndex] using
      b.lemma73RightGoodBONG_order i D.split hgood D.length_eq 0
  have hzero : D.rightGoodBONG.toBONG.normalizedValue
      (lemma73FirstIndex (0 : Fin (n - i.val + 1))) =
      b.normalizedValue (lemma73FirstIndex i) := by
    unfold rightGoodBONG
    simpa [lemma73FirstIndex] using
      b.lemma73RightGoodBONG_normalizedValue i D.split hgood
        D.length_eq 0
  have hone : D.rightGoodBONG.toBONG.normalizedValue
      (lemma73MiddleIndex (0 : Fin (n - i.val + 1))) =
      b.normalizedValue (lemma73MiddleIndex i) := by
    unfold rightGoodBONG
    simpa [lemma73MiddleIndex] using
      b.lemma73RightGoodBONG_normalizedValue i D.split hgood
        D.length_eq 1
  have htwo : D.rightGoodBONG.toBONG.normalizedValue
      (lemma73LastIndex (0 : Fin (n - i.val + 1))) =
      b.normalizedValue (lemma73LastIndex i) := by
    unfold rightGoodBONG
    simpa [lemma73LastIndex] using
      b.lemma73RightGoodBONG_normalizedValue i D.split hgood
        D.length_eq 2
  unfold lemma73ResidualValue
  rw [horder, hzero, hone, htwo]

/-- Flatten the prefix/right split and the hyperbolic/remainder split inside
the right component.  Its components are prefix, hyperbolic plane, and right
remainder, in that order. -/
noncomputable def flatDecomposition
    (D : Lemma73MiddleLeTailData b i hgood) :
    Lattice.OrthogonalDecomposition q L 3 :=
  D.split.canonicalDecomposition.prependNested D.witness.decomposition

@[simp]
theorem flatDecomposition_component_zero
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.flatDecomposition.component 0 =
      D.split.left.toQuadraticSublattice :=
  rfl

@[simp]
theorem flatDecomposition_component_one
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.flatDecomposition.component 1 =
      D.split.right.toQuadraticSublattice.liftNested
        (D.witness.decomposition.component 0) :=
  rfl

@[simp]
theorem flatDecomposition_component_two
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.flatDecomposition.component 2 =
      D.split.right.toQuadraticSublattice.liftNested
        (D.witness.decomposition.component 1) :=
  rfl

/-- Put the hyperbolic component first. -/
noncomputable def reorderedDecomposition
    (D : Lemma73MiddleLeTailData b i hgood) :
    Lattice.OrthogonalDecomposition q L 3 := by
  let E := D.flatDecomposition.reindex (Equiv.swap (0 : Fin 3) 1)
  let component : Fin 3 → Lattice.QuadraticSublattice q :=
    Fin.cases (D.flatDecomposition.component 1)
      (Fin.cases (D.flatDecomposition.component 0)
        (fun _ ↦ D.flatDecomposition.component 2))
  have hcomponent : component = E.component := by
    funext j
    fin_cases j
    · change D.flatDecomposition.component 1 =
        D.flatDecomposition.component 1
      rfl
    · change D.flatDecomposition.component 0 =
        D.flatDecomposition.component 0
      rfl
    · change D.flatDecomposition.component 2 =
        D.flatDecomposition.component
          ((Equiv.swap (0 : Fin 3) 1) 2)
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  exact {
    component := component
    orthogonal := by
      rw [hcomponent]
      exact E.orthogonal
    sum_eq := by
      rw [hcomponent]
      exact E.sum_eq }

/-- Merge the old prefix with the right remainder after moving the
hyperbolic component to the first position. -/
noncomputable def globalDecomposition
    (D : Lemma73MiddleLeTailData b i hgood) :
    Lattice.OrthogonalDecomposition q L 2 := by
  let R := D.reorderedDecomposition
  let E := R.mergeAdjacent (1 : Fin 2)
  let component : Fin 2 → Lattice.QuadraticSublattice q :=
    Fin.cases (R.component 0)
      (fun _ ↦ R.orthogonalSup (show (1 : Fin 3) ≠ 2 by decide))
  have hcomponent : component = E.component := by
    funext j
    fin_cases j
    · change R.component 0 = R.mergeComponents (1 : Fin 2) 0
      have hzero : (0 : Fin 2) =
          (1 : Fin 2).succAbove (0 : Fin 1) := by
        apply Fin.ext
        rfl
      rw [hzero,
        Lattice.OrthogonalDecomposition.mergeComponents_other]
      congr 1
    · change R.orthogonalSup (show (1 : Fin 3) ≠ 2 by decide) =
          R.mergeComponents (1 : Fin 2) 1
      symm
      simpa using R.mergeComponents_self (1 : Fin 2)
  exact {
    component := component
    orthogonal := by
      rw [hcomponent]
      exact E.orthogonal
    sum_eq := by
      rw [hcomponent]
      exact E.sum_eq }

@[simp]
theorem reorderedDecomposition_component_zero
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.reorderedDecomposition.component 0 =
      D.split.right.toQuadraticSublattice.liftNested
        (D.witness.decomposition.component 0) := by
  rfl

@[simp]
theorem reorderedDecomposition_component_one
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.reorderedDecomposition.component 1 =
      D.split.left.toQuadraticSublattice := by
  rfl

@[simp]
theorem reorderedDecomposition_component_two
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.reorderedDecomposition.component 2 =
      D.split.right.toQuadraticSublattice.liftNested
        (D.witness.decomposition.component 1) := by
  rfl

@[simp]
theorem globalDecomposition_component_zero
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.globalDecomposition.component 0 =
      D.split.right.toQuadraticSublattice.liftNested
        (D.witness.decomposition.component 0) := by
  rfl

@[simp]
theorem globalDecomposition_component_one
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.globalDecomposition.component 1 =
      D.reorderedDecomposition.orthogonalSup
        (show (1 : Fin 3) ≠ 2 by decide) := by
  rfl

/-- The unchanged prefix as a good BONG. -/
noncomputable def prefixGoodBONG
    (D : Lemma73MiddleLeTailData b i hgood) :
    GoodBONG
      (q.restrict D.split.left.carrier D.split.left.nondegenerate)
      D.split.left.lattice i.val where
  toBONG := D.split.left.bong
  good := D.split.left.isGood hgood

/-- The right residual BONG lifted from the right segment carrier to the
ambient carrier. -/
noncomputable def liftedRemainderGoodBONG
    (D : Lemma73MiddleLeTailData b i hgood) :
    GoodBONG
      (D.split.right.toQuadraticSublattice.liftNested
        (D.witness.decomposition.component 1)).space
      (D.split.right.toQuadraticSublattice.liftNested
        (D.witness.decomposition.component 1)).lattice
      (n - i.val + 1) :=
  (⟨D.witness.remainderBONG, D.witness.good⟩ :
    GoodBONG (D.witness.decomposition.component 1).space
      (D.witness.decomposition.component 1).lattice
      (n - i.val + 1)).mapLatticeIsometry
        (D.split.right.toQuadraticSublattice.liftNestedIsometry
          (D.witness.decomposition.component 1))

@[simp]
theorem liftedRemainderGoodBONG_value
    (D : Lemma73MiddleLeTailData b i hgood)
    (j : Fin (n - i.val + 1)) :
    D.liftedRemainderGoodBONG.value j =
      D.witness.remainderBONG.value j := by
  let c : GoodBONG (D.witness.decomposition.component 1).space
      (D.witness.decomposition.component 1).lattice
      (n - i.val + 1) :=
    ⟨D.witness.remainderBONG, D.witness.good⟩
  let f := D.split.right.toQuadraticSublattice.liftNestedIsometry
    (D.witness.decomposition.component 1)
  change (c.mapLatticeIsometry f).value j = c.value j
  exact congrArg (fun z : Kˣ ↦ (z : K))
    (GoodBONG.valueUnit_mapLatticeIsometry f c j)

@[simp]
theorem liftedRemainderGoodBONG_order
    (D : Lemma73MiddleLeTailData b i hgood)
    (j : Fin (n - i.val + 1)) :
    D.liftedRemainderGoodBONG.order j =
      D.witness.remainderBONG.order j := by
  apply GoodBONG.order_mapLatticeIsometry

/-- The lifted right remainder begins with the replacement order `R_i`. -/
theorem liftedRemainderGoodBONG_order_zero
    (D : Lemma73MiddleLeTailData b i hgood) :
    D.liftedRemainderGoodBONG.order 0 =
      b.order (lemma73FirstIndex i) := by
  rw [D.liftedRemainderGoodBONG_order]
  calc
    D.witness.remainderBONG.order 0 =
        D.rightGoodBONG.order 0 := D.witness.replacement_order
    _ = b.order ⟨i.val + 0, by omega⟩ :=
      b.lemma73RightGoodBONG_order i D.split hgood D.length_eq 0
    _ = b.order (lemma73FirstIndex i) := by
      congr 1

/-- When it exists, the second lifted residual entry is the original entry
at index `i+3`. -/
theorem liftedRemainderGoodBONG_value_one
    (D : Lemma73MiddleLeTailData b i hgood)
    (hm : 1 < n - i.val + 1) :
    D.liftedRemainderGoodBONG.value ⟨1, hm⟩ =
      b.value ⟨i.val + 3, by omega⟩ := by
  have hiN : i.val ≤ n := by omega
  have hthree : 3 < (n - i.val) + 3 := by omega
  rw [D.liftedRemainderGoodBONG_value]
  calc
    D.witness.remainderBONG.value ⟨1, hm⟩ =
        (b.lemma73RightGoodBONG i D.split hgood D.length_eq).toBONG.value
          ⟨3, hthree⟩ := by
      simpa only [Nat.reduceAdd] using
        D.witness.value_after ⟨1, hm⟩ (by norm_num)
    _ = b.value ⟨i.val + 3, by omega⟩ := by
      exact b.lemma73RightGoodBONG_value i D.split hgood D.length_eq
        ⟨3, hthree⟩

theorem liftedRemainderGoodBONG_order_one
    (D : Lemma73MiddleLeTailData b i hgood)
    (hm : 1 < n - i.val + 1) :
    D.liftedRemainderGoodBONG.order ⟨1, hm⟩ =
      b.order ⟨i.val + 3, by omega⟩ := by
  rw [D.liftedRemainderGoodBONG_order]
  apply WithTop.coe_injective
  rw [BONG.coe_order, BONG.coe_order]
  have hv := D.liftedRemainderGoodBONG_value_one hm
  rw [D.liftedRemainderGoodBONG_value] at hv
  exact congrArg (ord K) hv

@[simp]
theorem prefixGoodBONG_order
    (D : Lemma73MiddleLeTailData b i hgood) (j : Fin i.val) :
    D.prefixGoodBONG.order j = b.order ⟨j.val, by omega⟩ := by
  change D.split.left.bong.order j = _
  rw [D.split.left.order_eq]
  congr 1
  apply Fin.ext
  simp [SegmentWitness.sourceIndex]

/-- Every unchanged prefix order is bounded by the replacement head order. -/
theorem prefix_order_le_lifted_remainder_head
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val)
    (j : Fin i.val) :
    D.prefixGoodBONG.order j ≤ D.liftedRemainderGoodBONG.order 0 := by
  rw [D.liftedRemainderGoodBONG_order_zero]
  have hlastOriginal := D.split.boundaryOrder_le hi (by omega)
  have hlast : D.prefixGoodBONG.order ⟨i.val - 1, by omega⟩ ≤
      b.order (lemma73FirstIndex i) := by
    rw [D.prefixGoodBONG_order]
    calc
      b.order ⟨i.val - 1, by omega⟩ ≤
          b.order ⟨i.val, by omega⟩ := hlastOriginal
      _ = b.order (lemma73FirstIndex i) := by
        congr 1
  by_cases hiOne : i.val = 1
  · let zero : Fin i.val := ⟨0, by omega⟩
    have hj : j = zero := by
      apply Fin.ext
      omega
    rw [hj]
    have hzeroLast : zero = (⟨i.val - 1, by omega⟩ : Fin i.val) := by
      apply Fin.ext
      dsimp only [zero]
      omega
    rw [hzeroLast]
    exact hlast
  · have hiTwo : 2 ≤ i.val := by omega
    let penultimate : Fin i.val := ⟨i.val - 2, by omega⟩
    let oldPenultimate : Fin (n + 3) := ⟨i.val - 2, by omega⟩
    have holdTwo : oldPenultimate.val + 2 < n + 3 := by
      dsimp only [oldPenultimate]
      omega
    have htwoStep := hgood oldPenultimate holdTwo
    have hpenultimate : D.prefixGoodBONG.order penultimate ≤
        b.order (lemma73FirstIndex i) := by
      rw [D.prefixGoodBONG_order]
      calc
        b.order ⟨penultimate.val, by omega⟩ =
            b.order oldPenultimate := by
          congr 1
        _ ≤ b.order ⟨oldPenultimate.val + 2, holdTwo⟩ := htwoStep
        _ = b.order (lemma73FirstIndex i) := by
          congr 1
          apply Fin.ext
          dsimp only [oldPenultimate]
          simp [lemma73FirstIndex]
          omega
    exact D.prefixGoodBONG.order_le_of_lt_cut_of_last_two_le
      i.val hiTwo (by omega) (b.order (lemma73FirstIndex i))
      hpenultimate hlast j j.isLt

/-- The last unchanged prefix order is also bounded by the second residual
order whenever that entry exists. -/
theorem prefix_last_order_le_lifted_remainder_second
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val)
    (hm : 1 < n - i.val + 1) :
    D.prefixGoodBONG.order ⟨i.val - 1, by omega⟩ ≤
      D.liftedRemainderGoodBONG.order ⟨1, hm⟩ := by
  rw [D.prefixGoodBONG_order,
    D.liftedRemainderGoodBONG_order_one hm]
  have hiN : i.val < n := by omega
  let last : Fin (n + 3) := ⟨i.val - 1, by omega⟩
  have hlastTwo : last.val + 2 < n + 3 := by
    dsimp only [last]
    omega
  have hfirst := hgood last hlastTwo
  let next : Fin (n + 3) := ⟨i.val + 1, by omega⟩
  have hnextTwo : next.val + 2 < n + 3 := by
    dsimp only [next]
    omega
  have hsecond := hgood next hnextTwo
  calc
    b.order ⟨i.val - 1, by omega⟩ ≤
        b.order ⟨i.val + 1, by omega⟩ := by
      calc
        b.order ⟨i.val - 1, by omega⟩ = b.order last := by
          congr 1
        _ ≤ b.order ⟨last.val + 2, hlastTwo⟩ := hfirst
        _ = b.order ⟨i.val + 1, by omega⟩ := by
          congr 1
          apply Fin.ext
          dsimp only [last]
          omega
    _ ≤ b.order ⟨i.val + 3, by omega⟩ := by
      calc
        b.order ⟨i.val + 1, by omega⟩ = b.order next := by
          congr 1
        _ ≤ b.order ⟨next.val + 2, hnextTwo⟩ := hsecond
        _ = b.order ⟨i.val + 3, by omega⟩ := by
          congr 1

/-- Concatenate the unchanged prefix with the lifted right remainder. -/
noncomputable def productRemainderGoodBONG
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val) :
    GoodBONG
      ((q.restrict D.split.left.carrier
        D.split.left.nondegenerate).orthogonalSum
          (D.split.right.toQuadraticSublattice.liftNested
            (D.witness.decomposition.component 1)).space)
      (Lattice.product D.split.left.lattice
        (D.split.right.toQuadraticSublattice.liftNested
          (D.witness.decomposition.component 1)).lattice)
      ((n - i.val + 1) + i.val) :=
  D.prefixGoodBONG.orthogonalProductRight_of_orderBounds
    D.liftedRemainderGoodBONG
    (fun j ↦ D.prefix_order_le_lifted_remainder_head hi j)
    (fun _ hm ↦ D.prefix_last_order_le_lifted_remainder_second hi hm)

/-- The product prefix/remainder lattice is exactly the second component of
the global two-block decomposition. -/
noncomputable def remainderProductIsometry
    (D : Lemma73MiddleLeTailData b i hgood) :
    Lattice.Isometry
      ((q.restrict D.split.left.carrier
        D.split.left.nondegenerate).orthogonalSum
          (D.split.right.toQuadraticSublattice.liftNested
            (D.witness.decomposition.component 1)).space)
      (D.globalDecomposition.component 1).space
      (Lattice.product D.split.left.lattice
        (D.split.right.toQuadraticSublattice.liftNested
          (D.witness.decomposition.component 1)).lattice)
      (D.globalDecomposition.component 1).lattice := by
  let hij : (1 : Fin 3) ≠ 2 := by decide
  change Lattice.Isometry
    ((D.reorderedDecomposition.component 1).space.orthogonalSum
      (D.reorderedDecomposition.component 2).space)
    (D.reorderedDecomposition.orthogonalSup hij).space
    (Lattice.product (D.reorderedDecomposition.component 1).lattice
      (D.reorderedDecomposition.component 2).lattice)
    (D.reorderedDecomposition.orthogonalSup hij).lattice
  exact D.reorderedDecomposition.orthogonalSupLatticeIsometry hij

/-- The final good BONG of the global orthogonal complement. -/
noncomputable def globalRemainderGoodBONG
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val) :
    GoodBONG (D.globalDecomposition.component 1).space
      (D.globalDecomposition.component 1).lattice (n + 1) :=
  ((D.productRemainderGoodBONG hi).castLength (by omega)).mapLatticeIsometry
    D.remainderProductIsometry

@[simp]
theorem productRemainderGoodBONG_value_left
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val)
    (j : Fin i.val) :
    (D.productRemainderGoodBONG hi).value
        (orthogonalProductLeftIndex (n - i.val + 1) j) =
      D.prefixGoodBONG.value j := by
  have hu : (D.productRemainderGoodBONG hi).valueUnit
        (orthogonalProductLeftIndex (n - i.val + 1) j) =
      D.prefixGoodBONG.valueUnit j := by
    unfold productRemainderGoodBONG
    apply GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left
  simpa only [GoodBONG.coe_valueUnit, BONG.coe_valueUnit] using
    congrArg (fun z : Kˣ ↦ (z : K)) hu

@[simp]
theorem productRemainderGoodBONG_value_right
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val)
    (j : Fin (n - i.val + 1)) :
    (D.productRemainderGoodBONG hi).value
        (orthogonalProductRightIndex i.val j) =
      D.liftedRemainderGoodBONG.value j := by
  have hu : (D.productRemainderGoodBONG hi).valueUnit
        (orthogonalProductRightIndex i.val j) =
      D.liftedRemainderGoodBONG.valueUnit j := by
    unfold productRemainderGoodBONG
    apply GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right
  simpa only [GoodBONG.coe_valueUnit, BONG.coe_valueUnit] using
    congrArg (fun z : Kˣ ↦ (z : K)) hu

/-- The common length-normalization index for the product complement. -/
def remainderProductIndex {m : Nat} (k : Fin (m + 1))
    (j : Fin (m + 1)) : Fin ((m - k.val + 1) + k.val) :=
  ⟨j.val, by
    have hj := j.isLt
    have hk := k.isLt
    omega⟩

/-- Mapping the normalized product BONG into the global complement preserves
its value sequence. -/
@[simp]
theorem globalRemainderGoodBONG_value
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val)
    (j : Fin (n + 1)) :
    (D.globalRemainderGoodBONG hi).value j =
      (D.productRemainderGoodBONG hi).value
        (remainderProductIndex i j) := by
  let p := D.productRemainderGoodBONG hi
  let hlen : (n - i.val + 1) + i.val = n + 1 := by omega
  let pc := p.castLength hlen
  change (pc.mapLatticeIsometry D.remainderProductIsometry).value j =
    p.value (remainderProductIndex i j)
  calc
    (pc.mapLatticeIsometry D.remainderProductIsometry).value j =
        pc.value j := by
      exact congrArg (fun z : Kˣ ↦ (z : K))
        (GoodBONG.valueUnit_mapLatticeIsometry
          D.remainderProductIsometry pc j)
    _ = p.value (remainderProductIndex i j) := by
      simpa only [remainderProductIndex] using
        GoodBONG.value_castLength' p hlen j

@[simp]
theorem prefixGoodBONG_value
    (D : Lemma73MiddleLeTailData b i hgood) (j : Fin i.val) :
    D.prefixGoodBONG.value j = b.value ⟨j.val, by omega⟩ := by
  change D.split.left.bong.value j = _
  rw [D.split.left.value_eq]
  congr 1
  apply Fin.ext
  simp [SegmentWitness.sourceIndex]

/-- The source index of an unchanged entry before the selected ternary
block.  Naming this coercion keeps proof terms out of subsequent theorem
statements. -/
def remainderSourceBefore {m : Nat} (j : Fin (m + 1)) : Fin (m + 3) :=
  ⟨j.val, by
    have hj := j.isLt
    omega⟩

/-- The source index of an entry after deleting the selected ternary block
and retaining its residual line. -/
def remainderSourceAfter {m : Nat} (j : Fin (m + 1)) : Fin (m + 3) :=
  ⟨j.val + 2, by
    have hj := j.isLt
    omega⟩

/-- Values before the selected ternary block are unchanged globally. -/
theorem globalRemainderGoodBONG_value_before
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val)
    (j : Fin (n + 1)) (hj : j.val < i.val) :
    (D.globalRemainderGoodBONG hi).value j =
      b.value (remainderSourceBefore (m := n) j) := by
  rw [D.globalRemainderGoodBONG_value hi j]
  let localIndex : Fin i.val := ⟨j.val, hj⟩
  have htotal : (n - i.val + 1) + i.val = n + 1 := by omega
  have hindex : remainderProductIndex i j =
      orthogonalProductLeftIndex (n - i.val + 1) localIndex := by
    apply Fin.ext
    rfl
  rw [hindex, D.productRemainderGoodBONG_value_left]
  simpa only [remainderSourceBefore] using D.prefixGoodBONG_value localIndex

/-- The global replacement entry has Beli's displayed residual value. -/
theorem globalRemainderGoodBONG_replacement_value
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val) :
    (D.globalRemainderGoodBONG hi).value i =
      (b.lemma73ResidualValue i : K) := by
  rw [D.globalRemainderGoodBONG_value hi i]
  let zero : Fin (n - i.val + 1) := ⟨0, by omega⟩
  have hindex : remainderProductIndex i i =
      orthogonalProductRightIndex i.val zero := by
    apply Fin.ext
    rfl
  rw [hindex, D.productRemainderGoodBONG_value_right,
    D.liftedRemainderGoodBONG_value]
  change D.witness.remainderBONG.value (0 : Fin (n - i.val + 1)) = _
  calc
    D.witness.remainderBONG.value (0 : Fin (n - i.val + 1)) =
        (((b.lemma73RightGoodBONG i D.split hgood D.length_eq).toBONG).lemma73ResidualValue
          (0 : Fin (n - i.val + 1)) : K) := D.witness.replacement_value
    _ = (b.lemma73ResidualValue i : K) := by
      have hr := D.rightGoodBONG_residualValue
      unfold rightGoodBONG at hr
      exact congrArg (fun z : Kˣ ↦ (z : K)) hr

/-- Values after the selected block are shifted left by two positions. -/
theorem globalRemainderGoodBONG_value_after
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val)
    (j : Fin (n + 1)) (hj : i.val < j.val) :
    (D.globalRemainderGoodBONG hi).value j =
      b.value (remainderSourceAfter (m := n) j) := by
  have hiN : i.val ≤ n := by omega
  let localIndex : Fin (n - i.val + 1) := ⟨j.val - i.val, by omega⟩
  have hlocalPos : 0 < localIndex.val := by
    dsimp only [localIndex]
    omega
  have hrightIndex : localIndex.val + 2 < (n - i.val) + 3 := by
    dsimp only [localIndex]
    omega
  rw [D.globalRemainderGoodBONG_value hi j]
  have htotal : (n - i.val + 1) + i.val = n + 1 := by omega
  have hindex : remainderProductIndex i j =
      orthogonalProductRightIndex i.val localIndex := by
    apply Fin.ext
    simp [remainderProductIndex, orthogonalProductRightIndex, localIndex]
    omega
  rw [hindex, D.productRemainderGoodBONG_value_right,
    D.liftedRemainderGoodBONG_value]
  calc
    D.witness.remainderBONG.value localIndex =
        D.rightGoodBONG.toBONG.value
          ⟨localIndex.val + 2, hrightIndex⟩ :=
      D.witness.value_after localIndex hlocalPos
    _ = b.value ⟨i.val + (localIndex.val + 2), by omega⟩ := by
      exact b.lemma73RightGoodBONG_value i D.split hgood D.length_eq
        ⟨localIndex.val + 2, hrightIndex⟩
    _ = b.value (remainderSourceAfter (m := n) j) := by
      congr 1
      apply Fin.ext
      dsimp only [localIndex, remainderSourceAfter]
      omega

/-- The first component of the reconstructed global decomposition is the
same scaled hyperbolic plane obtained from the selected tail. -/
theorem globalHyperbolic
    (D : Lemma73MiddleLeTailData b i hgood) :
    Lattice.IsIsometric
      (D.globalDecomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K (b.lemma73HyperbolicScaleOrder i)))
      (D.globalDecomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
  change Lattice.IsIsometric
    (D.split.right.toQuadraticSublattice.liftNested
      (D.witness.decomposition.component 0)).space
    (QuadraticSpace.hyperbolicPlane
      (uniformizerPowerUnit K (b.lemma73HyperbolicScaleOrder i)))
    (D.split.right.toQuadraticSublattice.liftNested
      (D.witness.decomposition.component 0)).lattice
    (Lattice.hyperbolicPlaneLattice (K := K))
  rw [← D.rightGoodBONG_hyperbolicScaleOrder]
  rcases D.witness.hyperbolic with ⟨f⟩
  exact ⟨(D.split.right.toQuadraticSublattice.liftNestedIsometry
    (D.witness.decomposition.component 0)).symm.trans f⟩

/-- Reassemble the tail splitting with the unchanged prefix into the full
conclusion of Lemma 7.3 at a positive selected position. -/
theorem nonempty_lemma73SplittingWitness
    (D : Lemma73MiddleLeTailData b i hgood) (hi : 0 < i.val) :
    Nonempty (b.Lemma73SplittingWitness i) := by
  let c := D.globalRemainderGoodBONG hi
  have hcValueZero : c.value 0 = b.value 0 := by
    have hv := D.globalRemainderGoodBONG_value_before hi
      (0 : Fin (n + 1)) hi
    have hsource : remainderSourceBefore (m := n) (0 : Fin (n + 1)) =
        (0 : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    rw [hsource] at hv
    exact hv
  have hcOrderZero : c.order 0 = b.order 0 := by
    apply WithTop.coe_injective
    unfold GoodBONG.order
    rw [c.toBONG.coe_order, b.coe_order]
    exact congrArg (ord K) hcValueZero
  let remainderNorm : Lattice.NormOrderDatum
      (D.globalDecomposition.component 1).space
      (D.globalDecomposition.component 1).lattice := {
    generator := c.toBONG.valueUnit 0
    normIdeal_eq := by
      simpa [c.toBONG.value_zero_eq_quadratic_head] using
        c.toBONG.head_isNormGenerator.normIdeal_eq }
  let splitting : Lattice.HyperbolicPlaneSplitting q L := {
    decomposition := D.globalDecomposition
    scaleOrder := b.lemma73HyperbolicScaleOrder i
    hyperbolic := D.globalHyperbolic
    remainderNorm := remainderNorm }
  refine ⟨{
    decomposition := D.globalDecomposition
    hyperbolic := D.globalHyperbolic
    remainderBONG := c.toBONG
    value_before := ?_
    replacement_value := ?_
    value_after := ?_
    componentNormData := splitting.componentNormData
    hyperbolicNorm_order := ?_
    remainderNorm_order := ?_
    good := c.good }⟩
  · intro j hj
    dsimp only [c, GoodBONG.value]
    have hv := D.globalRemainderGoodBONG_value_before hi j hj
    dsimp only [GoodBONG.value] at hv
    convert hv using 1
    congr 1
  · dsimp only [c, GoodBONG.value]
    have hv := D.globalRemainderGoodBONG_replacement_value hi
    dsimp only [GoodBONG.value] at hv
    convert hv using 1
  · intro j hj
    dsimp only [c, GoodBONG.value]
    have hv := D.globalRemainderGoodBONG_value_after hi j hj
    dsimp only [GoodBONG.value] at hv
    convert hv using 1
    congr 1
  · change splitting.hyperbolicNorm.order = _
    rw [Lattice.HyperbolicPlaneSplitting.hyperbolicNorm_order]
    rfl
  · change remainderNorm.order = b.order 0
    change ordUnit K (c.toBONG.valueUnit 0) = b.order 0
    rw [← c.toBONG.order_eq_ordUnit]
    exact hcOrderZero

end Lemma73MiddleLeTailData

/-- Lemma 7.3 at an arbitrary position in the branch
`R_(i+1) ≤ R_i`.  The initial position is the global head theorem; every
positive position is reduced to it by Corollary 4.4 and reconstructed above. -/
theorem exists_lemma73SplittingWitness_of_middle_le
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hgood : b.IsGood) (h : b.Lemma73Hypotheses i)
    (hupper : b.order (lemma73MiddleIndex i) ≤
      b.order (lemma73FirstIndex i)) :
    Nonempty (b.Lemma73SplittingWitness i) := by
  by_cases hiZero : i.val = 0
  · have hi : i = (0 : Fin (n + 1)) := by
      apply Fin.ext
      exact hiZero
    subst i
    have hupper' : b.order (1 : Fin (n + 3)) ≤ b.order 0 := by
      simpa [lemma73FirstIndex, lemma73MiddleIndex] using hupper
    exact b.exists_lemma73HeadSplittingWitness_of_middle_le
      hgood h hupper'
  · have hi : 0 < i.val := by omega
    rcases b.exists_lemma73MiddleLeTailData i hi hgood h hupper with ⟨D⟩
    exact D.nonempty_lemma73SplittingWitness hi

/-- Every adjacent parameter of a reverse-dual BONG is the parameter at
the reversed adjacent position of the original BONG. -/
theorem reverseDual_adjacentParameter
    {m : Nat} (b : BONG V q L (m + 1))
    (d : BONG V q (Lattice.dualLattice q L) (m + 1))
    (hvalues : ∀ j, d.value j = ((b.valueUnit (Fin.rev j))⁻¹ : K))
    (j : Fin m) :
    d.adjacentParameter j.castSucc (by
        simpa using j.succ.isLt) =
      b.adjacentParameter (Fin.rev j).castSucc (by
        simpa using (Fin.rev j).succ.isLt) := by
  have hvalueUnit : ∀ k,
      d.valueUnit k = (b.valueUnit (Fin.rev k))⁻¹ := by
    intro k
    apply Units.ext
    exact hvalues k
  unfold adjacentParameter
  change d.valueUnit j.succ / d.valueUnit j.castSucc =
    b.valueUnit (Fin.rev j).succ /
      b.valueUnit (Fin.rev j).castSucc
  rw [hvalueUnit j.succ, hvalueUnit j.castSucc,
    GoodBONG.rev_succ_eq_rev_castSucc,
    GoodBONG.rev_castSucc_eq_rev_succ]
  simp [div_eq_mul_inv, mul_comm]

/-- Start of the ternary block corresponding to `i` after reversing a
BONG of length `n+3`. -/
def lemma73MirrorIndex {m : Nat} (i : Fin (m + 1)) : Fin (m + 1) :=
  ⟨m - i.val, by omega⟩

/-- Reverse-dual data reducing the branch `R_i ≤ R_(i+1)` to the
already proved arbitrary-position branch `R_(k+1) ≤ R_k`. -/
structure Lemma73ReverseDualData
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1)) where
  dual : GoodBONG q (Lattice.dualLattice q L) (n + 3)
  values : ∀ j,
    dual.value j = ((b.valueUnit (Fin.rev j))⁻¹ : K)
  orders : ∀ j, dual.order j = -b.order (Fin.rev j)
  witness : dual.toBONG.Lemma73SplittingWitness (lemma73MirrorIndex i)
  endpoint : b.order (lemma73FirstIndex i) =
    b.order (lemma73LastIndex i)
  gapEven : Even (b.order (lemma73MiddleIndex i) -
    b.order (lemma73FirstIndex i))
  scaleOrder : dual.toBONG.lemma73HyperbolicScaleOrder
      (lemma73MirrorIndex i) =
    -b.lemma73HyperbolicScaleOrder i

/-- Construction of the reverse-dual splitting data in the remaining
order branch. -/
theorem exists_lemma73ReverseDualData
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hgood : b.IsGood) (h : b.Lemma73Hypotheses i)
    (hlower : b.order (lemma73FirstIndex i) ≤
      b.order (lemma73MiddleIndex i)) :
    Nonempty (Lemma73ReverseDualData b i) := by
  let source : GoodBONG q L (n + 3) := ⟨b, hgood⟩
  rcases source.exists_reverseDual_with_values with
    ⟨dual, _hdualVectors, hdualValues, hdualOrders⟩
  let k := lemma73MirrorIndex i
  have hfirst : dual.order (lemma73FirstIndex k) =
      -b.order (lemma73LastIndex i) := by
    rw [hdualOrders]
    congr 2
    change b.order (Fin.rev (lemma73FirstIndex k)) =
      b.order (lemma73LastIndex i)
    congr 1
    apply Fin.ext
    simp [k, lemma73MirrorIndex, lemma73FirstIndex,
      lemma73LastIndex, Fin.rev]
    omega
  have hmiddle : dual.order (lemma73MiddleIndex k) =
      -b.order (lemma73MiddleIndex i) := by
    rw [hdualOrders]
    congr 2
    change b.order (Fin.rev (lemma73MiddleIndex k)) =
      b.order (lemma73MiddleIndex i)
    congr 1
    apply Fin.ext
    simp [k, lemma73MirrorIndex, lemma73MiddleIndex, Fin.rev]
    omega
  have hlast : dual.order (lemma73LastIndex k) =
      -b.order (lemma73FirstIndex i) := by
    rw [hdualOrders]
    congr 2
    change b.order (Fin.rev (lemma73LastIndex k)) =
      b.order (lemma73FirstIndex i)
    congr 1
    apply Fin.ext
    simp [k, lemma73MirrorIndex, lemma73FirstIndex,
      lemma73LastIndex, Fin.rev]
    omega
  have hparameterZero : dual.toBONG.adjacentParameter
        (lemma73FirstIndex k) (by
          simp only [lemma73FirstIndex]
          have hk := k.isLt
          omega) =
      b.adjacentParameter (lemma73MiddleIndex i) (by
        simp only [lemma73MiddleIndex]
        have hi := i.isLt
        omega) := by
    have hp := reverseDual_adjacentParameter b dual.toBONG
      hdualValues k.castSucc
    have hleft : lemma73FirstIndex k = k.castSucc.castSucc := by
      apply Fin.ext
      rfl
    have hright : lemma73MiddleIndex i =
        (Fin.rev k.castSucc).castSucc := by
      apply Fin.ext
      simp [k, lemma73MirrorIndex, lemma73MiddleIndex, Fin.rev]
      omega
    simpa only [hleft, hright] using hp
  have hparameterOne : dual.toBONG.adjacentParameter
        (lemma73MiddleIndex k) (by
          simp only [lemma73MiddleIndex]
          have hk := k.isLt
          omega) =
      b.adjacentParameter (lemma73FirstIndex i) (by
        simp only [lemma73FirstIndex]
        have hi := i.isLt
        omega) := by
    have hp := reverseDual_adjacentParameter b dual.toBONG
      hdualValues k.succ
    have hleft : lemma73MiddleIndex k = k.succ.castSucc := by
      apply Fin.ext
      rfl
    have hright : lemma73FirstIndex i =
        (Fin.rev k.succ).castSucc := by
      apply Fin.ext
      simp [k, lemma73MirrorIndex, lemma73FirstIndex, Fin.rev]
      omega
    simpa only [hleft, hright] using hp
  have hdualHyp : dual.toBONG.Lemma73Hypotheses k := by
    unfold Lemma73Hypotheses
    refine ⟨?_, ?_, ?_⟩
    · change dual.order (lemma73FirstIndex k) =
        dual.order (lemma73LastIndex k)
      rw [hfirst, hlast, h.1]
    · rw [adjacentUnitSquareClass, hparameterZero]
      exact h.2.2
    · rw [adjacentUnitSquareClass, hparameterOne]
      exact h.2.1
  have hdualUpper : dual.order (lemma73MiddleIndex k) ≤
      dual.order (lemma73FirstIndex k) := by
    rw [hmiddle, hfirst, ← h.1]
    exact neg_le_neg hlower
  have hfirstNext : (lemma73FirstIndex i).val + 1 < n + 3 := by
    simp only [lemma73FirstIndex]
    have hi := i.isLt
    omega
  have hunit : beliSpinorGroupRepresentative K
        (b.adjacentParameter (lemma73FirstIndex i) hfirstNext) ≤
      valuationUnitSquareClassSubgroup K := by
    have hclass := h.2.1
    change beliSpinorGroup K
        (b.adjacentUnitSquareClass
          (lemma73FirstIndex i) hfirstNext) ≤
      valuationUnitSquareClassSubgroup K at hclass
    simpa only [adjacentUnitSquareClass,
      beliSpinorGroup_unitSquareClass] using hclass
  have hcriterion := (Dyadic.beliLemma72_i (K := K)
    (b.adjacentParameter (lemma73FirstIndex i) hfirstNext)
    (b.adjacentParameter_isBinaryParameterAdmissible
      (lemma73FirstIndex i) hfirstNext)).1 hunit
  have hgapEven : Even (b.order (lemma73MiddleIndex i) -
      b.order (lemma73FirstIndex i)) := by
    have hpOrder := b.ordUnit_adjacentParameter
      (lemma73FirstIndex i) hfirstNext
    change ordUnit K
        (b.adjacentParameter (lemma73FirstIndex i) hfirstNext) =
      b.order (lemma73MiddleIndex i) -
        b.order (lemma73FirstIndex i) at hpOrder
    rw [← hpOrder]
    exact hcriterion.1
  have hscaleOrder : dual.toBONG.lemma73HyperbolicScaleOrder k =
      -b.lemma73HyperbolicScaleOrder i := by
    unfold lemma73HyperbolicScaleOrder
    change (dual.order (lemma73FirstIndex k) +
        dual.order (lemma73MiddleIndex k)) / 2 = _
    rw [hfirst, hmiddle, ← h.1]
    rcases hgapEven with ⟨r, hr⟩
    omega
  rcases dual.toBONG.exists_lemma73SplittingWitness_of_middle_le
      k dual.good hdualHyp hdualUpper with ⟨witness⟩
  exact ⟨{
    dual := dual
    values := hdualValues
    orders := hdualOrders
    witness := witness
    endpoint := h.1
    gapEven := hgapEven
    scaleOrder := hscaleOrder }⟩

namespace Lemma73ReverseDualData

variable {n : Nat} {b : BONG V q L (n + 3)} {i : Fin (n + 1)}

/-- Dualize the two components of the splitting of the dual lattice and
restore their original order. -/
noncomputable def componentwiseDual (D : Lemma73ReverseDualData b i) :=
  D.witness.decomposition.reverseDual.reindex Fin.revPerm

/-- Regard the componentwise double-dual decomposition as a decomposition
of the original lattice. -/
noncomputable def originalDecomposition
    (D : Lemma73ReverseDualData b i) :
    Lattice.OrthogonalDecomposition q L 2 := {
  component := D.componentwiseDual.component
  orthogonal := D.componentwiseDual.orthogonal
  sum_eq := by
    simpa only [Lattice.dualLattice_dualLattice] using
      D.componentwiseDual.sum_eq }

@[simp]
theorem originalDecomposition_component_zero
    (D : Lemma73ReverseDualData b i) :
    D.originalDecomposition.component 0 =
      (D.witness.decomposition.component 0).dual := by
  simp [originalDecomposition, componentwiseDual,
    Lattice.OrthogonalDecomposition.reverseDualComponent]

@[simp]
theorem originalDecomposition_component_one
    (D : Lemma73ReverseDualData b i) :
    D.originalDecomposition.component 1 =
      (D.witness.decomposition.component 1).dual := by
  simp [originalDecomposition, componentwiseDual,
    Lattice.OrthogonalDecomposition.reverseDualComponent]

/-- Dualizing the hyperbolic component changes the scale exponent from
the negative dual exponent back to the original exponent. -/
theorem originalHyperbolic (D : Lemma73ReverseDualData b i) :
    Lattice.IsIsometric
      (D.originalDecomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K (b.lemma73HyperbolicScaleOrder i)))
      (D.originalDecomposition.component 0).lattice
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
  rw [D.originalDecomposition_component_zero]
  rcases D.witness.hyperbolic with ⟨f⟩
  let dualScale : Kˣ := uniformizerPowerUnit K
    (D.dual.toBONG.lemma73HyperbolicScaleOrder
      (lemma73MirrorIndex i))
  let transported := f.dual.trans
    (Lattice.dualHyperbolicPlaneLatticeIsometry dualScale)
  change Lattice.IsIsometric
    (D.witness.decomposition.component 0).space
    (QuadraticSpace.hyperbolicPlane
      (uniformizerPowerUnit K (b.lemma73HyperbolicScaleOrder i)))
    (Lattice.dualLattice
      (D.witness.decomposition.component 0).space
      (D.witness.decomposition.component 0).lattice)
    (Lattice.hyperbolicPlaneLattice (K := K))
  exact ⟨by
    simpa [Lattice.QuadraticSublattice.dual, transported, dualScale,
      D.scaleOrder, uniformizerPowerUnit, zpow_neg] using transported⟩

/-- The good BONG on the dual complement furnished by the dual splitting. -/
noncomputable def dualRemainderGoodBONG
    (D : Lemma73ReverseDualData b i) :
    GoodBONG (D.witness.decomposition.component 1).space
      (D.witness.decomposition.component 1).lattice (n + 1) :=
  ⟨D.witness.remainderBONG, D.witness.good⟩

/-- Reverse-dualize the complement BONG.  This already has all desired
values except that the replacement entry is only in the desired square
class. -/
noncomputable def rawOriginalRemainder
    (D : Lemma73ReverseDualData b i) :
    GoodBONG (D.witness.decomposition.component 1).space
      (Lattice.dualLattice
        (D.witness.decomposition.component 1).space
        (D.witness.decomposition.component 1).lattice) (n + 1) :=
  Classical.choose D.dualRemainderGoodBONG.exists_reverseDual_with_values

theorem rawOriginalRemainder_values
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1)) :
    D.rawOriginalRemainder.value j =
      ((D.witness.remainderBONG.valueUnit (Fin.rev j))⁻¹ : K) :=
  (Classical.choose_spec
    D.dualRemainderGoodBONG.exists_reverseDual_with_values).2.1 j

theorem rawOriginalRemainder_valueUnit
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1)) :
    D.rawOriginalRemainder.valueUnit j =
      (D.witness.remainderBONG.valueUnit (Fin.rev j))⁻¹ := by
  apply Units.ext
  exact D.rawOriginalRemainder_values j

theorem rawOriginalRemainder_orders
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1)) :
    D.rawOriginalRemainder.order j =
      -D.witness.remainderBONG.order (Fin.rev j) :=
  (Classical.choose_spec
    D.dualRemainderGoodBONG.exists_reverseDual_with_values).2.2 j

/-- View the raw complement BONG on the second component of the restored
original decomposition. -/
noncomputable def rawRemainder
    (D : Lemma73ReverseDualData b i) :
    GoodBONG (D.originalDecomposition.component 1).space
      (D.originalDecomposition.component 1).lattice (n + 1) := by
  rw [D.originalDecomposition_component_one]
  exact D.rawOriginalRemainder

@[simp]
theorem rawRemainder_valueUnit
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1)) :
    D.rawRemainder.valueUnit j =
      D.rawOriginalRemainder.valueUnit j := by
  rfl

@[simp]
theorem rawRemainder_order
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1)) :
    D.rawRemainder.order j = D.rawOriginalRemainder.order j := by
  rfl

theorem dual_valueUnit (D : Lemma73ReverseDualData b i)
    (j : Fin (n + 3)) :
    D.dual.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹ := by
  apply Units.ext
  exact D.values j

theorem dual_normalizedValue (D : Lemma73ReverseDualData b i)
    (j : Fin (n + 3)) :
    D.dual.toBONG.normalizedValue j =
      (b.normalizedValue (Fin.rev j))⁻¹ := by
  unfold normalizedValue
  change D.dual.valueUnit j *
      uniformizerUnit K ^ (-D.dual.order j) = _
  rw [D.dual_valueUnit, D.orders]
  simp [mul_comm]

/-- The displayed residual value is exactly preserved by reverse duality:
the residual of the mirrored dual block is the inverse of the original
residual. -/
theorem inverse_dual_residualValue
    (D : Lemma73ReverseDualData b i) :
    (D.dual.toBONG.lemma73ResidualValue
      (lemma73MirrorIndex i))⁻¹ = b.lemma73ResidualValue i := by
  let k := lemma73MirrorIndex i
  have hfirst : Fin.rev (lemma73FirstIndex k) =
      lemma73LastIndex i := by
    apply Fin.ext
    simp [k, lemma73MirrorIndex, lemma73FirstIndex,
      lemma73LastIndex, Fin.rev]
    omega
  have hmiddle : Fin.rev (lemma73MiddleIndex k) =
      lemma73MiddleIndex i := by
    apply Fin.ext
    simp [k, lemma73MirrorIndex, lemma73MiddleIndex, Fin.rev]
    omega
  have hlast : Fin.rev (lemma73LastIndex k) =
      lemma73FirstIndex i := by
    apply Fin.ext
    simp [k, lemma73MirrorIndex, lemma73FirstIndex,
      lemma73LastIndex, Fin.rev]
    omega
  have hdualFirstOrder : D.dual.toBONG.order
        (lemma73FirstIndex k) =
      -b.order (lemma73LastIndex i) := by
    change D.dual.order (lemma73FirstIndex k) = _
    rw [D.orders, hfirst]
  unfold lemma73ResidualValue
  rw [hdualFirstOrder,
    D.dual_normalizedValue, hfirst,
    D.dual_normalizedValue, hmiddle,
    D.dual_normalizedValue, hlast, D.endpoint]
  simp [uniformizerPowerUnit, zpow_neg, mul_comm,
    mul_left_comm, mul_assoc]

/-- Before the replacement coordinate, reversing the dual remainder
recovers the original values exactly. -/
theorem rawRemainder_valueUnit_before
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1))
    (hj : j.val < i.val) :
    D.rawRemainder.valueUnit j =
      b.valueUnit
        (Lemma73MiddleLeTailData.remainderSourceBefore (m := n) j) := by
  rw [D.rawRemainder_valueUnit,
    D.rawOriginalRemainder_valueUnit]
  let k := lemma73MirrorIndex i
  let reverseIndex : Fin (n + 1) := Fin.rev j
  have hafter : k.val < reverseIndex.val := by
    simp [k, reverseIndex, lemma73MirrorIndex, Fin.rev]
    omega
  let sourceIndex : Fin (n + 3) :=
    ⟨reverseIndex.val + 2, by
      have hr := reverseIndex.isLt
      omega⟩
  have hwValue := D.witness.value_after reverseIndex hafter
  have hwUnit : D.witness.remainderBONG.valueUnit reverseIndex =
      D.dual.valueUnit sourceIndex := by
    apply Units.ext
    exact hwValue
  rw [hwUnit, D.dual_valueUnit]
  simp only [inv_inv]
  congr 1
  apply Fin.ext
  simp [sourceIndex, reverseIndex,
    Lemma73MiddleLeTailData.remainderSourceBefore, Fin.rev]
  omega

/-- After the replacement coordinate, reversing the dual remainder
recovers the original value shifted by two positions. -/
theorem rawRemainder_valueUnit_after
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1))
    (hj : i.val < j.val) :
    D.rawRemainder.valueUnit j =
      b.valueUnit
        (Lemma73MiddleLeTailData.remainderSourceAfter (m := n) j) := by
  rw [D.rawRemainder_valueUnit,
    D.rawOriginalRemainder_valueUnit]
  let k := lemma73MirrorIndex i
  let reverseIndex : Fin (n + 1) := Fin.rev j
  have hbefore : reverseIndex.val < k.val := by
    simp [k, reverseIndex, lemma73MirrorIndex, Fin.rev]
    omega
  let sourceIndex : Fin (n + 3) :=
    ⟨reverseIndex.val, by
      have hr := reverseIndex.isLt
      omega⟩
  have hwValue := D.witness.value_before reverseIndex hbefore
  have hwUnit : D.witness.remainderBONG.valueUnit reverseIndex =
      D.dual.valueUnit sourceIndex := by
    apply Units.ext
    exact hwValue
  rw [hwUnit, D.dual_valueUnit]
  simp only [inv_inv]
  congr 1
  apply Fin.ext
  simp [sourceIndex, reverseIndex,
    Lemma73MiddleLeTailData.remainderSourceAfter, Fin.rev]
  omega

/-- The raw replacement entry already has the required order; only its
unit square representative remains to be normalized. -/
theorem rawRemainder_order_replacement
    (D : Lemma73ReverseDualData b i) :
    D.rawRemainder.order i = b.order (lemma73FirstIndex i) := by
  rw [D.rawRemainder_order, D.rawOriginalRemainder_orders]
  have hreverse : Fin.rev i = lemma73MirrorIndex i := by
    apply Fin.ext
    simp [lemma73MirrorIndex, Fin.rev]
  rw [hreverse, D.witness.replacement_order]
  change -D.dual.order
      (lemma73FirstIndex (lemma73MirrorIndex i)) = _
  rw [D.orders]
  have hindex : Fin.rev
        (lemma73FirstIndex (lemma73MirrorIndex i)) =
      lemma73LastIndex i := by
    apply Fin.ext
    simp [lemma73MirrorIndex, lemma73FirstIndex,
      lemma73LastIndex, Fin.rev]
    omega
  rw [hindex, D.endpoint]
  omega

/-- The raw reverse-dual remainder already has the exact displayed
replacement value, not merely its square class. -/
theorem rawRemainder_replacement_valueUnit
    (D : Lemma73ReverseDualData b i) :
    D.rawRemainder.valueUnit i = b.lemma73ResidualValue i := by
  rw [D.rawRemainder_valueUnit,
    D.rawOriginalRemainder_valueUnit]
  have hreverse : Fin.rev i = lemma73MirrorIndex i := by
    apply Fin.ext
    simp [lemma73MirrorIndex, Fin.rev]
  rw [hreverse]
  have hw : D.witness.remainderBONG.valueUnit
        (lemma73MirrorIndex i) =
      D.dual.toBONG.lemma73ResidualValue
        (lemma73MirrorIndex i) := by
    apply Units.ext
    exact D.witness.replacement_value
  rw [hw]
  exact D.inverse_dual_residualValue

theorem rawRemainder_value_before
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1))
    (hj : j.val < i.val) :
    D.rawRemainder.value j =
      b.value
        (Lemma73MiddleLeTailData.remainderSourceBefore (m := n) j) := by
  simpa only [GoodBONG.coe_valueUnit, BONG.coe_valueUnit] using
    congrArg (fun z : Kˣ ↦ (z : K))
      (D.rawRemainder_valueUnit_before j hj)

theorem rawRemainder_replacement_value
    (D : Lemma73ReverseDualData b i) :
    D.rawRemainder.value i = (b.lemma73ResidualValue i : K) := by
  simpa only [GoodBONG.coe_valueUnit] using
    congrArg (fun z : Kˣ ↦ (z : K))
      D.rawRemainder_replacement_valueUnit

theorem rawRemainder_value_after
    (D : Lemma73ReverseDualData b i) (j : Fin (n + 1))
    (hj : i.val < j.val) :
    D.rawRemainder.value j =
      b.value
        (Lemma73MiddleLeTailData.remainderSourceAfter (m := n) j) := by
  simpa only [GoodBONG.coe_valueUnit, BONG.coe_valueUnit] using
    congrArg (fun z : Kˣ ↦ (z : K))
      (D.rawRemainder_valueUnit_after j hj)

/-- The restored remainder begins with a norm generator of the original
lattice norm order, whether the replacement is first or occurs later. -/
theorem rawRemainder_order_zero
    (D : Lemma73ReverseDualData b i) :
    D.rawRemainder.order 0 = b.order 0 := by
  by_cases hiZero : i.val = 0
  · have hi : i = (0 : Fin (n + 1)) := by
      apply Fin.ext
      exact hiZero
    subst i
    simpa [lemma73FirstIndex] using
      D.rawRemainder_order_replacement
  · have hi : 0 < i.val := by omega
    have hu := D.rawRemainder_valueUnit_before
      (0 : Fin (n + 1)) hi
    have hsource :
        Lemma73MiddleLeTailData.remainderSourceBefore
            (m := n) (0 : Fin (n + 1)) =
          (0 : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    rw [hsource] at hu
    change D.rawRemainder.toBONG.order 0 = b.order 0
    rw [D.rawRemainder.toBONG.order_eq_ordUnit,
      b.order_eq_ordUnit]
    exact congrArg (ordUnit K) hu

/-- Package the reconstructed decomposition and reverse-dual remainder as
the full conclusion of Lemma 7.3 in the branch `R_i ≤ R_(i+1)`. -/
theorem nonempty_lemma73SplittingWitness
    (D : Lemma73ReverseDualData b i) :
    Nonempty (b.Lemma73SplittingWitness i) := by
  let c := D.rawRemainder
  let remainderNorm : Lattice.NormOrderDatum
      (D.originalDecomposition.component 1).space
      (D.originalDecomposition.component 1).lattice := {
    generator := c.toBONG.valueUnit 0
    normIdeal_eq := by
      simpa [c.toBONG.value_zero_eq_quadratic_head] using
        c.toBONG.head_isNormGenerator.normIdeal_eq }
  let splitting : Lattice.HyperbolicPlaneSplitting q L := {
    decomposition := D.originalDecomposition
    scaleOrder := b.lemma73HyperbolicScaleOrder i
    hyperbolic := D.originalHyperbolic
    remainderNorm := remainderNorm }
  refine ⟨{
    decomposition := D.originalDecomposition
    hyperbolic := D.originalHyperbolic
    remainderBONG := c.toBONG
    value_before := ?_
    replacement_value := ?_
    value_after := ?_
    componentNormData := splitting.componentNormData
    hyperbolicNorm_order := ?_
    remainderNorm_order := ?_
    good := c.good }⟩
  · intro j hj
    dsimp only [c, GoodBONG.value]
    have hv := D.rawRemainder_value_before j hj
    dsimp only [GoodBONG.value] at hv
    convert hv using 1
    congr 1
  · dsimp only [c, GoodBONG.value]
    have hv := D.rawRemainder_replacement_value
    dsimp only [GoodBONG.value] at hv
    convert hv using 1
  · intro j hj
    dsimp only [c, GoodBONG.value]
    have hv := D.rawRemainder_value_after j hj
    dsimp only [GoodBONG.value] at hv
    convert hv using 1
    congr 1
  · change splitting.hyperbolicNorm.order = _
    rw [Lattice.HyperbolicPlaneSplitting.hyperbolicNorm_order]
    rfl
  · change remainderNorm.order = b.order 0
    change ordUnit K (c.toBONG.valueUnit 0) = b.order 0
    rw [← c.toBONG.order_eq_ordUnit]
    exact D.rawRemainder_order_zero

end Lemma73ReverseDualData

/-- Lemma 7.3 in the remaining order branch, obtained by reversing and
dualizing the arbitrary-position result. -/
theorem exists_lemma73SplittingWitness_of_first_le_middle
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hgood : b.IsGood) (h : b.Lemma73Hypotheses i)
    (hlower : b.order (lemma73FirstIndex i) ≤
      b.order (lemma73MiddleIndex i)) :
    Nonempty (b.Lemma73SplittingWitness i) := by
  rcases b.exists_lemma73ReverseDualData i hgood h hlower with ⟨D⟩
  exact D.nonempty_lemma73SplittingWitness

/-- Complete arbitrary-rank, arbitrary-position form of Beli (2003),
Lemma 7.3. -/
theorem exists_lemma73SplittingWitness
    {n : Nat} (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hgood : b.IsGood) (h : b.Lemma73Hypotheses i) :
    Nonempty (b.Lemma73SplittingWitness i) := by
  rcases le_total (b.order (lemma73MiddleIndex i))
      (b.order (lemma73FirstIndex i)) with hupper | hlower
  · exact b.exists_lemma73SplittingWitness_of_middle_le
      i hgood h hupper
  · exact b.exists_lemma73SplittingWitness_of_first_le_middle
      i hgood h hlower

/-- Unconditional implementation of the Lemma 7.3 interface. -/
instance beliLemma73LawsOfProof : BeliLemma73Laws.{u, v} K where
  exists_splitting := fun b i hgood h ↦
    b.exists_lemma73SplittingWitness i hgood h

end BONG

end Bong
