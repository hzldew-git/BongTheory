/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIEndpoint

/-!
# Beli (2019), Lemma 7.14(ii): the literal stopping suffix

The first application of Lemma 7.10 is made to the suffix beginning with
the exceptional ternary block.  This file extracts that suffix as an actual
segment BONG.  Its first three vectors are the block constructed in Lemma
7.12, and every later vector is the unchanged right suffix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private theorem lemma714TypeIIStopSegment_two_le_rank (n : Nat) :
    2 ≤ n + 3 := by
  omega

section StopSegment

variable [DyadicDiscriminantClassLaws K]
variable (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
variable (D : Lemma714StoppingData b R s)
variable (hfirst : b.order ⟨0, by omega⟩ = R)
variable (hsecond : b.order ⟨1, by omega⟩ =
  R - 2 * (ramificationIndex K : Int))
variable (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
variable (hsCurrent : s < n + 3)
variable (S : BONG.TwoBlockSplitWitness b.toBONG 2
  (lemma714TypeIIStopSegment_two_le_rank n))
variable (hsFour : s = 2 ∨ 4 ≤ s)
variable (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
  (s - 2) (by have := D.le_rank; omega))
variable (block : GoodBONG
  ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
    ((q.restrict S.right.carrier S.right.nondegenerate).restrict
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).nondegenerate))
  (Lattice.product
    (Lattice.rescale (uniformizerUnit K) S.left.lattice)
    (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).lattice) 3)
variable {N : Lattice K (S.right.carrier × S.left.carrier)}
variable (target : GoodBONG
  ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
    (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
variable (htargetVectors : ∀ i, target.toBONG.ambientVector i =
  lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)

/-- The exceptional block together with the retained suffix fits exactly
after the unchanged prefix. -/
theorem lemma714TypeIIStopSegment_bound :
    s - 2 + lemma714TypeIIBaseLength n s ≤
      lemma714TypeIIBaseLength n s + (s - 2) := by
  omega

/-- The actual consecutive suffix used by the reverse-dual endpoint
argument. -/
noncomputable def lemma714TypeIIStopSegment :=
  (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
    target).toBONG.segmentWitness (s - 2)
      (lemma714TypeIIBaseLength n s)
      (lemma714TypeIIStopSegment_bound (n := n) s)

/-- The stopping suffix inherits goodness from the complete candidate. -/
noncomputable def lemma714TypeIIStopGoodBONG :=
  (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
    target).toGoodBONG
      (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
        target).good

include block htargetVectors

/-- Local coordinate zero of the stopping segment is the first exceptional
block vector. -/
@[simp]
theorem lemma714TypeIIStopSegment_ambientVector_zero :
    ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).bong.ambientVector
        ⟨0, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ :
      (U.left.carrier × S.left.carrier) × U.right.carrier) =
      ((0, (block.toBONG.ambientVector 0).1),
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector 0).2) := by
  calc
    _ = (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
          target).toBONG.ambientVector ⟨s - 2, by
            rw [lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
            omega⟩ := by
      simpa only [Nat.add_zero] using
        (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).ambientVector_eq
          ⟨0, by
            unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
            omega⟩
    _ = _ := b.lemma714TypeIITargetForLemma710_block_zero R s D
      hsCurrent S hsFour U block target htargetVectors

/-- Local coordinate one of the stopping segment is the middle exceptional
block vector. -/
@[simp]
theorem lemma714TypeIIStopSegment_ambientVector_one :
    ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).bong.ambientVector
        ⟨1, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ :
      (U.left.carrier × S.left.carrier) × U.right.carrier) =
      ((0, (block.toBONG.ambientVector 1).1),
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector 1).2) := by
  calc
    _ = (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
          target).toBONG.ambientVector
          ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).sourceIndex
            ⟨1, by
              unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
              omega⟩) :=
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).ambientVector_eq
          ⟨1, by
            unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
            omega⟩
    _ = (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
          target).toBONG.ambientVector ⟨s - 1, by
            rw [lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
            omega⟩ := by
      apply congrArg
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega
    _ = _ := b.lemma714TypeIITargetForLemma710_block_one R s D
      hsCurrent S hsFour U block target htargetVectors

/-- Local coordinate two of the stopping segment is the last exceptional
block vector. -/
@[simp]
theorem lemma714TypeIIStopSegment_ambientVector_two :
    ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).bong.ambientVector
        ⟨2, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ :
      (U.left.carrier × S.left.carrier) × U.right.carrier) =
      ((0, (block.toBONG.ambientVector 2).1),
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector 2).2) := by
  calc
    _ = (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
          target).toBONG.ambientVector
          ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).sourceIndex
            ⟨2, by
              unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
              omega⟩) :=
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).ambientVector_eq
          ⟨2, by
            unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
            omega⟩
    _ = (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
          target).toBONG.ambientVector ⟨s, by
            rw [lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
            omega⟩ := by
      apply congrArg
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega
    _ = _ := b.lemma714TypeIITargetForLemma710_block_two R s D
      hsCurrent S hsFour U block target htargetVectors

/-- Uniform finite-index form of the three exceptional coordinates. -/
@[simp]
theorem lemma714TypeIIStopSegment_ambientVector_block (i : Fin 3) :
    ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).bong.ambientVector
        ⟨i.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ :
      (U.left.carrier × S.left.carrier) × U.right.carrier) =
      ((0, (block.toBONG.ambientVector i).1),
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector i).2) := by
  fin_cases i
  · exact b.lemma714TypeIIStopSegment_ambientVector_zero R s D hsCurrent
      S hsFour U block target htargetVectors
  · exact b.lemma714TypeIIStopSegment_ambientVector_one R s D hsCurrent
      S hsFour U block target htargetVectors
  · exact b.lemma714TypeIIStopSegment_ambientVector_two R s D hsCurrent
      S hsFour U block target htargetVectors

/-- After the local ternary block, the stopping segment is the unchanged
non-head part of the right factor. -/
@[simp]
theorem lemma714TypeIIStopSegment_ambientVector_suffix
    (j : Fin (n + 2 - s)) :
    ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).bong.ambientVector
        ⟨3 + j.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ :
      (U.left.carrier × S.left.carrier) × U.right.carrier) =
      ((0, 0),
        (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.ambientVector
          ⟨j.val + 1, by omega⟩) := by
  calc
    _ = (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
          target).toBONG.ambientVector
          ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).sourceIndex
            ⟨3 + j.val, by
              unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
              omega⟩) :=
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).ambientVector_eq
          ⟨3 + j.val, by
            unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
            omega⟩
    _ = (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U
          target).toBONG.ambientVector ⟨s + 1 + j.val, by
            rw [lemma714TypeIIBaseLength_add_prefix n s hsFour hsCurrent]
            omega⟩ := by
      apply congrArg
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega
    _ = _ := b.lemma714TypeIITargetForLemma710_suffix R s D
      hsCurrent S hsFour U block target htargetVectors j

end StopSegment

end BONG.GoodBONG

end Bong
