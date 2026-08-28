/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDualModular
import Bong.Bong.BeliLemma43

/-!
# Good combinatorics of the reversed normalized dual basis

This file proves the non-integral part of Beli (2003), Lemma 4.8 in arbitrary
rank.  The reversed normalized dual vectors form an orthogonal basis, every
adjacent pair is a binary BONG, and the reversed order sequence satisfies the
good two-step inequalities.  Consequently Lemma 4.3(ii) realizes these
vectors as a good BONG of some lattice.

The remaining integral step is to identify that lattice with the integral
dual of the original lattice.  Keeping that step separate makes the exact
content still needed from the maximal-norm-splitting argument visible.
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

/-- Orthogonal-basis data carried by the reversed normalized dual vectors of
a good BONG. -/
noncomputable def GoodBONG.reverseDualOrthogonalBasisData
    (b : GoodBONG q L n) : OrthogonalBasisData q n where
  basis := b.toBONG.reverseDualBasis
  orthogonal := b.toBONG.reverseDualBasis_iIsOrtho

@[simp]
theorem GoodBONG.reverseDualOrthogonalBasisData_basis
    (b : GoodBONG q L n) (i : Fin n) :
    b.reverseDualOrthogonalBasisData.basis i =
      b.toBONG.reverseDualVector i :=
  b.toBONG.reverseDualBasis_apply i

/-- The reverse-dual order sequence is the reversed negative of the original
order sequence. -/
@[simp]
theorem GoodBONG.reverseDualOrthogonalBasisData_order
    (b : GoodBONG q L n) (i : Fin n) :
    b.reverseDualOrthogonalBasisData.order i =
      -b.toBONG.order (Fin.rev i) := by
  apply WithTop.coe_injective
  rw [OrthogonalBasisData.order, coe_ordUnit]
  change ord K
      (q.quadratic (b.reverseDualOrthogonalBasisData.basis i)) = _
  rw [b.reverseDualOrthogonalBasisData_basis,
    b.toBONG.ord_quadratic_reverseDualVector]

namespace SegmentWitness

/-- Normalized dual vectors commute with inclusion of a consecutive segment
into the parent ambient space. -/
private theorem coe_reverseDualVector_eq_parentDual
    {start length : Nat} {bound : start + length ≤ n}
    {b : BONG V q L n}
    (w : SegmentWitness b start length bound) (i : Fin length) :
    (w.bong.reverseDualVector i : V) =
      b.dualVector (w.sourceIndex (Fin.rev i)) := by
  rw [BONG.reverseDualVector, BONG.dualVector, BONG.dualVector,
    w.valueUnit_eq]
  change ((b.valueUnit (w.sourceIndex (Fin.rev i)))⁻¹ : K) •
      (w.bong.ambientVector (Fin.rev i) : V) =
    ((b.valueUnit (w.sourceIndex (Fin.rev i)))⁻¹ : K) •
      b.ambientVector (w.sourceIndex (Fin.rev i))
  rw [w.ambientVector_eq]
  congr 1

end SegmentWitness

/-- Every adjacent pair of reversed normalized dual vectors is a binary BONG.
This is the arbitrary-rank local input in Beli's proof of Lemma 4.8. -/
theorem GoodBONG.reverseDualOrthogonalBasisData_hasAdjacentBONGs
    (b : GoodBONG q L n) :
    b.reverseDualOrthogonalBasisData.HasAdjacentBONGs := by
  intro i hi
  let start : Nat := n - (i.1 + 2)
  have bound : start + 2 ≤ n := by
    dsimp [start]
    omega
  let w : SegmentWitness b.toBONG start 2 bound :=
    Classical.choice
      (b.toBONG.exists_segmentWitness_unconditional start 2 bound)
  let d : GoodBONG (q.restrict w.carrier w.nondegenerate)
      (Lattice.dualLattice (q.restrict w.carrier w.nondegenerate)
        w.lattice) 2 :=
    w.bong.reverseDualBinaryGood
  let next : Fin n := ⟨i.1 + 1, hi⟩
  have hindexZero : w.sourceIndex (Fin.rev (0 : Fin 2)) =
      Fin.rev i := by
    apply Fin.ext
    simp only [SegmentWitness.sourceIndex_val, Fin.rev]
    dsimp [start]
    omega
  have hindexOne : w.sourceIndex (Fin.rev (1 : Fin 2)) =
      Fin.rev next := by
    apply Fin.ext
    simp only [SegmentWitness.sourceIndex_val, Fin.rev]
    dsimp [start, next]
  refine ⟨{
    carrier := w.carrier
    nondegenerate := w.nondegenerate
    lattice := Lattice.dualLattice
      (q.restrict w.carrier w.nondegenerate) w.lattice
    bong := d.toBONG
    ambientVector_zero := ?_
    ambientVector_one := ?_
  }⟩
  · calc
      (d.toBONG.ambientVector 0 : V) =
          (w.bong.reverseDualVector 0 : V) := by
        exact congrArg Subtype.val
          (w.bong.ambientVector_reverseDualBinaryGood 0)
      _ = b.toBONG.dualVector (w.sourceIndex (Fin.rev 0)) :=
        w.coe_reverseDualVector_eq_parentDual 0
      _ = b.toBONG.dualVector (Fin.rev i) := by rw [hindexZero]
      _ = b.toBONG.reverseDualVector i := rfl
      _ = b.reverseDualOrthogonalBasisData.basis i :=
        (b.reverseDualOrthogonalBasisData_basis i).symm
  · calc
      (d.toBONG.ambientVector 1 : V) =
          (w.bong.reverseDualVector 1 : V) := by
        exact congrArg Subtype.val
          (w.bong.ambientVector_reverseDualBinaryGood 1)
      _ = b.toBONG.dualVector (w.sourceIndex (Fin.rev 1)) :=
        w.coe_reverseDualVector_eq_parentDual 1
      _ = b.toBONG.dualVector (Fin.rev next) := by rw [hindexOne]
      _ = b.toBONG.reverseDualVector next := rfl
      _ = b.reverseDualOrthogonalBasisData.basis next :=
        (b.reverseDualOrthogonalBasisData_basis next).symm

/-- Good two-step inequalities are preserved by reversing the sequence and
negating all orders. -/
theorem GoodBONG.reverseDualOrthogonalBasisData_hasWeakTwoStepOrder
    (b : GoodBONG q L n) :
    b.reverseDualOrthogonalBasisData.HasWeakTwoStepOrder := by
  intro i hi
  let nextTwo : Fin n := ⟨i.1 + 2, hi⟩
  rw [b.reverseDualOrthogonalBasisData_order,
    b.reverseDualOrthogonalBasisData_order]
  change -b.toBONG.order (Fin.rev i) ≤
    -b.toBONG.order (Fin.rev nextTwo)
  have hsource : (Fin.rev nextTwo).1 + 2 < n := by
    simp only [Fin.rev]
    dsimp [nextTwo]
    omega
  have hgood := b.good (Fin.rev nextTwo) hsource
  have hindex :
      ⟨(Fin.rev nextTwo).1 + 2, hsource⟩ = Fin.rev i := by
    apply Fin.ext
    simp only [Fin.rev]
    dsimp [nextTwo]
    omega
  rw [hindex] at hgood
  omega

/-- Lemma 4.3(ii) realizes the reversed normalized dual basis as a good BONG
of some lattice.  The vector identity is literal in the original ambient
quadratic space. -/
theorem GoodBONG.exists_reverseDualGoodRealization
    [BeliLemma43ConstructionLaws.{u, v} K]
    (b : GoodBONG q L n) :
    ∃ (M : Lattice K V) (c : GoodBONG q M n),
      ∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i := by
  rcases b.reverseDualOrthogonalBasisData.hasGoodRealization_of_conditions
      b.reverseDualOrthogonalBasisData_hasAdjacentBONGs
      b.reverseDualOrthogonalBasisData_hasWeakTwoStepOrder with
    ⟨M, c, hreal, hgood⟩
  refine ⟨M, ⟨c, hgood⟩, ?_⟩
  intro i
  calc
    c.ambientVector i = b.reverseDualOrthogonalBasisData.basis i := hreal i
    _ = b.toBONG.reverseDualVector i :=
      b.reverseDualOrthogonalBasisData_basis i

end BONG

end Bong
