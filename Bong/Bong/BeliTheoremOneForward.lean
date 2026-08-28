/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma411
import Bong.Lattice.SpinorNormMultiplicative

/-!
# Beli (2003), Theorem 1: the forward inclusion

For lattices of rank at least three, this file defines the two factors on the
right-hand side of Theorem 1.  The adjacent binary factors are joined as
subgroups.  The exponent `alpha` is the minimum of the floored half-gaps
`(R_(i+2) - R_i) / 2`.

The long ternary calculation in Section 5 is isolated as a non-default local
law.  From that rank-three statement, the global forward inclusion is proved
using consecutive segments and Corollary 4.10.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- The floored half-gap `floor((R_(i+2) - R_i) / 2)`. -/
noncomputable def theoremOneTwoStepDepth (b : BONG V q L (n + 3))
    (i : Fin (n + 1)) : Nat :=
  Int.toNat ((b.order ⟨i.1 + 2, by omega⟩ -
    b.order ⟨i.1, by omega⟩) / 2)

/-- The finite nonempty set whose minimum is Theorem 1's `alpha`. -/
noncomputable def theoremOneAlphaCandidates (b : BONG V q L (n + 3)) :
    Finset Nat :=
  Finset.univ.image b.theoremOneTwoStepDepth

theorem theoremOneAlphaCandidates_nonempty (b : BONG V q L (n + 3)) :
    b.theoremOneAlphaCandidates.Nonempty := by
  refine ⟨b.theoremOneTwoStepDepth 0, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

/-- The exponent `alpha` in Beli (2003), Theorem 1. -/
noncomputable def theoremOneAlpha (b : BONG V q L (n + 3)) : Nat :=
  b.theoremOneAlphaCandidates.min' b.theoremOneAlphaCandidates_nonempty

theorem theoremOneAlpha_mem_candidates (b : BONG V q L (n + 3)) :
    b.theoremOneAlpha ∈ b.theoremOneAlphaCandidates :=
  Finset.min'_mem _ b.theoremOneAlphaCandidates_nonempty

theorem theoremOneAlpha_le_twoStepDepth (b : BONG V q L (n + 3))
    (i : Fin (n + 1)) :
    b.theoremOneAlpha ≤ b.theoremOneTwoStepDepth i := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The product of all adjacent binary `G(a_(i+1)/a_i)` factors. -/
noncomputable def theoremOneAdjacentFactor (b : BONG V q L (n + 3)) :
    Subgroup (SquareClass K) :=
  ⨆ i : Fin (n + 2),
    beliSpinorGroup K
      (b.adjacentUnitSquareClass i.castSucc (by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          Nat.succ_lt_succ i.isLt))

/-- The principal-unit factor `(1 + p^alpha) F^times^2`. -/
noncomputable def theoremOneCongruenceFactor (b : BONG V q L (n + 3)) :
    Subgroup (SquareClass K) :=
  beliCongruenceSquareClassSubgroup K b.theoremOneAlpha

/-- The subgroup displayed on the right-hand side of Theorem 1. -/
noncomputable def theoremOneRHS (b : BONG V q L (n + 3)) :
    Subgroup (SquareClass K) :=
  b.theoremOneAdjacentFactor ⊔ b.theoremOneCongruenceFactor

end BONG

/-- The rank-three calculation occupying Beli (2003), Section 5. -/
class BeliTheoremOneTernaryLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  congruence_le_spinorNormImage
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 3) (hA : b.HasPropertyA) :
    beliCongruenceSquareClassSubgroup K (b.theoremOneTwoStepDepth 0) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L)

namespace BONG

variable [BeliLemma49Laws.{u, v} K]
  [BinarySpinorLocalLaws.{u, v} K]
  [BeliTheoremOneTernaryLaws.{u, v} K]

omit [BeliTheoremOneTernaryLaws K] in
/-- Every adjacent factor on the right of Theorem 1 is globally integral. -/
theorem theoremOneAdjacentFactor_le_spinorNormImage
    (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    b.theoremOneAdjacentFactor ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  apply iSup_le
  intro i z hz
  have hmem := b.beliCorollary410_ii hA.isGood
    (i := i.castSucc) (by
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        Nat.succ_lt_succ i.isLt) hz
  exact hmem

omit [BeliLemma49Laws K]
  [BinarySpinorLocalLaws K]
  [BeliTheoremOneTernaryLaws K] in
/-- The minimum `alpha` is attained by one consecutive ternary segment. -/
theorem exists_ternarySegment_at_theoremOneAlpha
    (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    ∃ i : Fin (n + 1),
      b.theoremOneTwoStepDepth i = b.theoremOneAlpha ∧
        ∃ w : SegmentWitness b i.1 3 (by omega),
          w.bong.HasPropertyA ∧
            w.bong.theoremOneTwoStepDepth 0 = b.theoremOneAlpha := by
  have halpha := b.theoremOneAlpha_mem_candidates
  rw [theoremOneAlphaCandidates, Finset.mem_image] at halpha
  rcases halpha with ⟨i, _hi, hidepth⟩
  refine ⟨i, hidepth, ?_⟩
  rcases b.exists_segmentWitness i.1 3 (by omega) with ⟨w⟩
  refine ⟨w, w.hasPropertyA hA, ?_⟩
  rw [← hidepth]
  unfold theoremOneTwoStepDepth
  rw [w.order_eq, w.order_eq]
  congr 2

/-- The principal-unit factor on the right of Theorem 1 is globally integral. -/
theorem theoremOneCongruenceFactor_le_spinorNormImage
    (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    b.theoremOneCongruenceFactor ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  rcases b.exists_ternarySegment_at_theoremOneAlpha hA with
    ⟨_i, _hidepth, w, hwA, hwDepth⟩
  intro z hz
  have hzLocal : z ∈ Lattice.spinorNormImageSubgroup
      (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) := by
    apply BeliTheoremOneTernaryLaws.congruence_le_spinorNormImage w.bong hwA
    rw [hwDepth]
    exact hz
  have hzLocalSet : z ∈ Lattice.spinorNormImage
      (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) := by
    rw [← Lattice.coe_spinorNormImageSubgroup]
    exact hzLocal
  have hzGlobal :=
    BeliLemma49Laws.segment_spinorNormImage_subset b hA.isGood w hzLocalSet
  change z ∈ (Lattice.spinorNormImageSubgroup (q := q) (L := L) :
    Set (SquareClass K))
  rw [Lattice.coe_spinorNormImageSubgroup]
  exact hzGlobal

/-- Beli (2003), Section 5: the forward inclusion in Theorem 1. -/
theorem theoremOneRHS_le_spinorNormImage
    (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    b.theoremOneRHS ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  apply sup_le
  · exact b.theoremOneAdjacentFactor_le_spinorNormImage hA
  · exact b.theoremOneCongruenceFactor_le_spinorNormImage hA

end BONG

end Bong
