/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemmas45To47
import Bong.Bong.BinaryAdmissibility
import Bong.Bong.BinarySpinorGroup

/-!
# Beli (2003), Lemmas 4.8--4.9 and Corollary 4.10

This file closes Section 4.  Reverse duality is linked to reciprocal BONG
values, consecutive good and property-A segments are unconditional, and the
first two spinor inclusions of Corollary 4.10 are derived from the binary
formula once segment orthogonal groups are known to embed.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace BONG.GoodBONG

variable [BONGStructuralLaws.{u, v} K]

/--
Beli (2003), Lemma 4.8: reverse the BONG and replace every vector `x` by
`Q(x)⁻¹x`; the result is a good BONG of the dual lattice.
-/
theorem exists_reverseDual_with_values (b : BONG.GoodBONG q L n) :
    ∃ c : BONG.GoodBONG q (Lattice.dualLattice q L) n,
      (∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i) ∧
      (∀ i, c.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)) ∧
      ∀ i, c.order i = -b.order (Fin.rev i) := by
  rcases b.exists_reverseDual with ⟨c, hc⟩
  refine ⟨c, hc, ?_, ?_⟩
  · intro i
    change c.toBONG.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)
    rw [← c.toBONG.quadratic_ambientVector i, hc i]
    exact b.toBONG.quadratic_reverseDualVector i
  · intro i
    change c.toBONG.order i = -b.toBONG.order (Fin.rev i)
    apply WithTop.coe_injective
    rw [BONG.coe_order]
    have hvalue : c.toBONG.value i =
        ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K) := by
      rw [← c.toBONG.quadratic_ambientVector i, hc i]
      exact b.toBONG.quadratic_reverseDualVector i
    rw [hvalue]
    change ord K (((b.toBONG.valueUnit (Fin.rev i))⁻¹ : Kˣ) : K) = _
    rw [← coe_ordUnit, ordUnit_inv, ← b.toBONG.order_eq_ordUnit]

end BONG.GoodBONG

namespace BONG

/-- A replacement of one consecutive segment inside a global BONG. -/
structure SegmentReplacementWitness (b : BONG V q L n)
    {start length : Nat} {bound : start + length ≤ n}
    (w : SegmentWitness b start length bound)
    (c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length) where
  /-- The replacement is again a BONG of the original lattice. -/
  bong : BONG V q L n
  /-- It remains good. -/
  good : bong.IsGood
  /-- Entries before the replaced block are unchanged. -/
  before_eq : ∀ (i : Fin n), i.1 < start →
    bong.ambientVector i = b.ambientVector i
  /-- Entries inside the block are the new segment vectors. -/
  inside_eq : ∀ i : Fin length,
    bong.ambientVector ⟨start + i.1, by omega⟩ =
      (c.ambientVector i : V)
  /-- Entries after the replaced block are unchanged. -/
  after_eq : ∀ (i : Fin n), start + length ≤ i.1 →
    bong.ambientVector i = b.ambientVector i

end BONG

/-- The integral extension and replacement assertions in Beli (2003), Lemma 4.9. -/
class BeliLemma49Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  /-- The orthogonal group of every good consecutive segment embeds in `O(L)`. -/
  segment_spinorNormImage_subset
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n start length : Nat}
    {bound : start + length ≤ n}
    (b : BONG V q L n) (hgood : b.IsGood)
    (w : BONG.SegmentWitness b start length bound) :
    Lattice.spinorNormImage
        (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) ⊆
      Lattice.spinorNormImage (q := q) (L := L)
  /-- The determinant-`-1` component of every good consecutive segment also
  embeds in `O⁻(L)`. -/
  segment_improperSpinorNormImage_subset
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n start length : Nat}
    {bound : start + length ≤ n}
    (b : BONG V q L n) (hgood : b.IsGood)
    (w : BONG.SegmentWitness b start length bound) :
    Lattice.improperSpinorNormImage
        (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) ⊆
      Lattice.improperSpinorNormImage (q := q) (L := L)
  /-- Replacing a good segment BONG by another one preserves the full lattice. -/
  replace_good_segment
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n start length : Nat}
    {bound : start + length ≤ n}
    (b : BONG V q L n) (hgood : b.IsGood)
    (w : BONG.SegmentWitness b start length bound)
    (c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length) (hc : c.IsGood) :
    Nonempty (BONG.SegmentReplacementWitness b w c)

namespace BONG

variable [BeliLemma49Laws.{u, v} K]

/-- Beli (2003), Lemma 4.9(i), good-BONG part. -/
theorem beliLemma49_i_good (b : BONG V q L n) (hgood : b.IsGood)
    (start length : Nat) (bound : start + length ≤ n) :
    ∃ w : SegmentWitness b start length bound,
      w.bong.IsGood ∧
        Lattice.spinorNormImage
            (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) ⊆
          Lattice.spinorNormImage (q := q) (L := L) := by
  rcases b.exists_segmentWitness start length bound with ⟨w⟩
  exact ⟨w, w.isGood hgood,
    BeliLemma49Laws.segment_spinorNormImage_subset b hgood w⟩

/-- Beli (2003), Lemma 4.9(i), property-A part. -/
theorem beliLemma49_i_propertyA (b : BONG V q L n)
    (hproperty : b.HasPropertyA) (start length : Nat)
    (bound : start + length ≤ n) :
    ∃ w : SegmentWitness b start length bound, w.bong.HasPropertyA := by
  rcases b.exists_segmentWitness start length bound with ⟨w⟩
  exact ⟨w, w.hasPropertyA hproperty⟩

/-- Beli (2003), Lemma 4.9(ii). -/
theorem beliLemma49_ii (b : BONG V q L n) (hgood : b.IsGood)
    {start length : Nat} {bound : start + length ≤ n}
    (w : SegmentWitness b start length bound)
    (c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length) (hc : c.IsGood) :
    Nonempty (SegmentReplacementWitness b w c) :=
  BeliLemma49Laws.replace_good_segment b hgood w c hc

/-- Corollary 4.10(i): every good-BONG value lies in `θ(O⁻(L))`. -/
theorem beliCorollary410_i (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) :
    squareClass K (b.valueUnit i) ∈
      Lattice.improperSpinorNormImage (q := q) (L := L) := by
  have hbound : i.1 + 1 ≤ n := by omega
  rcases b.exists_segmentWitness i.1 1 hbound with ⟨w⟩
  have hgenerator := w.bong.head_isNormGenerator
  have hanisotropic := w.bong.head_isAnisotropic
  have hintegral := hgenerator.isIntegralReflection hanisotropic
  have hmem : Lattice.reflectionSpinorClass hanisotropic ∈
      Lattice.improperSpinorNormImage
        (q := q.restrict w.carrier w.nondegenerate)
        (L := w.lattice) :=
    ⟨Lattice.integralReflection hanisotropic hintegral,
      Lattice.det_integralReflection hanisotropic hintegral,
      Lattice.integralSpinorNorm_integralReflection hanisotropic hintegral⟩
  have hclass :
      Lattice.reflectionSpinorClass hanisotropic =
        squareClass K (b.valueUnit i) := by
    apply congrArg (squareClass K)
    apply Units.ext
    change (q.restrict w.carrier w.nondegenerate).quadratic w.bong.head =
      b.value i
    rw [← w.bong.value_zero_eq_quadratic_head]
    have hw := w.value_eq (0 : Fin 1)
    simpa [SegmentWitness.sourceIndex] using hw
  rw [hclass] at hmem
  exact BeliLemma49Laws.segment_improperSpinorNormImage_subset
    b hgood w hmem

variable [BinarySpinorLocalLaws.{u, v} K]

/-- Corollary 4.10(ii): every adjacent binary `G` lies in `theta(O(L))`. -/
theorem beliCorollary410_ii (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n) :
    (beliSpinorGroup K (b.adjacentUnitSquareClass i hi) :
        Set (SquareClass K)) ⊆
      Lattice.spinorNormImage (q := q) (L := L) := by
  have hbound : i.1 + 2 ≤ n := by omega
  rcases b.exists_segmentWitness i.1 2 hbound with ⟨w⟩
  have hw0 : w.bong.valueUnit 0 = b.valueUnit i := by
    apply Units.ext
    have h := w.value_eq (0 : Fin 2)
    simpa [SegmentWitness.sourceIndex] using h
  have hw1 : w.bong.valueUnit 1 = b.valueUnit ⟨i.1 + 1, hi⟩ := by
    apply Units.ext
    have h := w.value_eq (1 : Fin 2)
    simpa [SegmentWitness.sourceIndex] using h
  have hparameter : w.bong.binaryUnitSquareClass =
      b.adjacentUnitSquareClass i hi := by
    apply congrArg (unitSquareClass K)
    simp only [binaryParameter, adjacentParameter, adjacentUnitSquareClass]
    rw [hw0, hw1]
  intro z hz
  have hzseg : z ∈ Lattice.spinorNormImage
      (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) := by
    rw [w.bong.spinorNormImage_eq_beliSpinorGroup, hparameter]
    exact hz
  exact BeliLemma49Laws.segment_spinorNormImage_subset b hgood w hzseg

end BONG

/-- The ternary norm-generator replacement in Corollary 4.10(iii). -/
class BeliCorollary410IIILaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  twistedAdjacentSpinorGroup_subset
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hpair : i.1 + 1 < n)
    (ζ : valuationUnitSubgroup K) :
    ((∃ hleft : 1 ≤ i.1,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit i / b.valueUnit ⟨i.1 - 1, by omega⟩)) ∨
      (∃ hright : i.1 + 2 < n,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit ⟨i.1 + 2, hright⟩ /
            b.valueUnit ⟨i.1 + 1, hpair⟩))) →
      (beliSpinorGroup K
          (unitSquareClass K ((ζ : Kˣ) * b.adjacentParameter i hpair)) :
        Set (SquareClass K)) ⊆
        Lattice.spinorNormImage (q := q) (L := L)

namespace BONG

variable [BeliCorollary410IIILaws.{u, v} K]

/-- Beli (2003), Corollary 4.10(iii). -/
theorem beliCorollary410_iii (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hpair : i.1 + 1 < n)
    (ζ : valuationUnitSubgroup K)
    (hζ : (∃ hleft : 1 ≤ i.1,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit i / b.valueUnit ⟨i.1 - 1, by omega⟩)) ∨
      (∃ hright : i.1 + 2 < n,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit ⟨i.1 + 2, hright⟩ /
            b.valueUnit ⟨i.1 + 1, hpair⟩))) :
    (beliSpinorGroup K
        (unitSquareClass K ((ζ : Kˣ) * b.adjacentParameter i hpair)) :
      Set (SquareClass K)) ⊆
      Lattice.spinorNormImage (q := q) (L := L) :=
  BeliCorollary410IIILaws.twistedAdjacentSpinorGroup_subset
    b hgood i hpair ζ hζ

end BONG

end Bong
