/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Properties
import Bong.Bong.CoordinateSegment

/-!
# Consecutive BONG segment witnesses

This file packages a consecutive family of BONG vectors as a BONG in its own
nondegenerate quadratic subspace.  The package is independent of the deeper
structural laws and is used by the constructive proof of Beli (2003),
Lemma 2.7 and Corollary 2.8.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/--
A realization of a consecutive block of BONG vectors as a BONG in its own
nondegenerate quadratic subspace.
-/
structure SegmentWitness (b : BONG V q L n) (start length : Nat)
    (bound : start + length ≤ n) where
  /-- The quadratic subspace spanned by the segment. -/
  carrier : Submodule K V
  /-- Nondegeneracy of the restricted quadratic form. -/
  nondegenerate : (q.bilin.restrict carrier).Nondegenerate
  /-- The integral lattice reconstructed from the segment. -/
  lattice : Lattice K carrier
  /-- The segment, as a genuine recursive BONG. -/
  bong : BONG carrier (q.restrict carrier nondegenerate) lattice length
  /-- Its ambient vectors are the requested consecutive vectors. -/
  ambientVector_eq : ∀ i : Fin length,
    (bong.ambientVector i : V) =
      b.ambientVector ⟨start + i.1, by omega⟩

namespace SegmentWitness

variable {b : BONG V q L n} {start length : Nat}
  {bound : start + length ≤ n}

/-- The index in the original BONG corresponding to a segment index. -/
def sourceIndex (_w : SegmentWitness b start length bound)
    (i : Fin length) : Fin n :=
  ⟨start + i.1, by omega⟩

@[simp]
theorem sourceIndex_val (w : SegmentWitness b start length bound)
    (i : Fin length) : (w.sourceIndex i).1 = start + i.1 :=
  rfl

/-- A segment witness carries exactly the corresponding quadratic values. -/
@[simp]
theorem value_eq (w : SegmentWitness b start length bound) (i : Fin length) :
    w.bong.value i = b.value (w.sourceIndex i) := by
  rw [← w.bong.quadratic_ambientVector i]
  change q.quadratic (w.bong.ambientVector i : V) = _
  rw [w.ambientVector_eq]
  exact b.quadratic_ambientVector (w.sourceIndex i)

/-- A segment witness carries the same nonzero values as units. -/
@[simp]
theorem valueUnit_eq (w : SegmentWitness b start length bound)
    (i : Fin length) :
    w.bong.valueUnit i = b.valueUnit (w.sourceIndex i) := by
  apply Units.ext
  exact w.value_eq i

/-- Every segment witness has the canonical coordinate carrier. -/
theorem carrier_eq_segmentCarrier
    (w : SegmentWitness b start length bound) :
    w.carrier = b.segmentCarrier start length bound := by
  apply le_antisymm
  · intro x hx
    let y : w.carrier := ⟨x, hx⟩
    have hy : y ∈ Submodule.span K (Set.range w.bong.ambientVector) := by
      rw [w.bong.span_ambientVector_eq_top]
      trivial
    change (y : V) ∈ b.segmentCarrier start length bound
    have hmap : (y : V) ∈ Submodule.span K
        ((Submodule.subtype w.carrier) ''
          Set.range w.bong.ambientVector) :=
      Submodule.apply_mem_span_image_of_mem_span
        (Submodule.subtype w.carrier) hy
    rw [segmentCarrier]
    apply (Submodule.span_mono ?_) hmap
    rintro z ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    change b.ambientVector ⟨start + i.1, by omega⟩ =
      (w.bong.ambientVector i : V)
    exact (w.ambientVector_eq i).symm
  · rw [segmentCarrier, Submodule.span_le]
    rintro z ⟨i, rfl⟩
    change b.ambientVector (w.sourceIndex i) ∈ w.carrier
    have h := w.ambientVector_eq i
    change (w.bong.ambientVector i : V) =
      b.ambientVector (w.sourceIndex i) at h
    rw [← h]
    exact (w.bong.ambientVector i).property

/-- A segment witness carries exactly the corresponding valuation orders. -/
@[simp]
theorem order_eq (w : SegmentWitness b start length bound) (i : Fin length) :
    w.bong.order i = b.order (w.sourceIndex i) := by
  apply WithTop.coe_injective
  rw [coe_order, coe_order, w.value_eq]

/-- Normalization commutes with passage to a consecutive segment. -/
@[simp]
theorem normalizedValue_eq (w : SegmentWitness b start length bound)
    (i : Fin length) :
    w.bong.normalizedValue i = b.normalizedValue (w.sourceIndex i) := by
  simp only [normalizedValue, w.valueUnit_eq, w.order_eq]

/-- Consecutive segments of a good BONG remain good. -/
theorem isGood (w : SegmentWitness b start length bound) (hb : b.IsGood) :
    w.bong.IsGood := by
  intro i hi
  rw [w.order_eq, w.order_eq]
  have hsource : (w.sourceIndex i).1 + 2 < n := by
    simp only [sourceIndex_val]
    omega
  have hindex :
      w.sourceIndex ⟨i.1 + 2, hi⟩ =
        ⟨(w.sourceIndex i).1 + 2, hsource⟩ := by
    apply Fin.ext
    simp only [sourceIndex_val]
    omega
  rw [hindex]
  exact hb (w.sourceIndex i) hsource

/-- Consecutive segments preserve the strict two-step property A. -/
theorem hasPropertyA (w : SegmentWitness b start length bound)
    (hb : b.HasPropertyA) : w.bong.HasPropertyA := by
  intro i hi
  rw [w.order_eq, w.order_eq]
  have hsource : (w.sourceIndex i).1 + 2 < n := by
    simp only [sourceIndex_val]
    omega
  have hindex :
      w.sourceIndex ⟨i.1 + 2, hi⟩ =
        ⟨(w.sourceIndex i).1 + 2, hsource⟩ := by
    apply Fin.ext
    simp only [sourceIndex_val]
    omega
  rw [hindex]
  exact hb (w.sourceIndex i) hsource

/-- A segment witness of a good BONG, bundled as a `GoodBONG`. -/
noncomputable def toGoodBONG (w : SegmentWitness b start length bound)
    (hb : b.IsGood) : GoodBONG (q.restrict w.carrier w.nondegenerate)
      w.lattice length where
  toBONG := w.bong
  good := w.isGood hb

end SegmentWitness

end BONG

end Bong
