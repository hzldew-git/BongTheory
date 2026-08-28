/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44Proof
import Bong.Bong.TwoBlockProductIsometry

/-!
# Gluing good BONG segments across an orthogonal cut

This file proves Beli (2003), Corollary 4.4(v), without a law parameter.
The key necessity argument is recursive: an integral vector orthogonal to
the BONG prefix remains integral in every successive projected lattice, so
the last norm generator in that prefix has no larger norm order.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- An integral vector orthogonal to the BONG coordinates through `i` has
quadratic order at least the order of the `i`-th recursive norm generator. -/
theorem order_le_ord_quadratic_of_mem_of_orthogonal_prefix
    (b : BONG V q L n) (i : Fin n) (y : V) (hy : y ∈ L)
    (horth : ∀ j : Fin n, j.val ≤ i.val →
      q.bilin (b.ambientVector j) y = 0) :
    (b.order i : WithTop Int) ≤ ord K (q.quadratic y) := by
  induction b with
  | nil => exact Fin.elim0 i
  | @cons V _ _ q L m x generator anisotropic tail ih =>
      cases i using Fin.cases with
      | zero =>
          have hvalue := Lattice.quadratic_mem_normIdeal_of_mem q L hy
          rw [generator.normIdeal_eq] at hvalue
          simpa only [coe_order, value_cons_zero] using
            (Lattice.ord_le_of_mem_principalIdeal anisotropic hvalue)
      | succ i =>
          have hxy : q.bilin x y = 0 := by
            simpa only [ambientVector_cons_zero] using
              horth (0 : Fin (m + 1)) (Nat.zero_le _)
          let y' : q.vectorOrthogonal x :=
            ⟨y, (q.mem_vectorOrthogonal_iff x y).2 hxy⟩
          have hy' : y' ∈ L.projectedLattice q x anisotropic := by
            rw [Lattice.mem_projectedLattice_iff]
            refine ⟨y, hy, ?_⟩
            apply Subtype.ext
            exact q.orthogonalProjection_eq_self y'.property
          have horth' : ∀ j : Fin m, j.val ≤ i.val →
              (q.orthogonalSpace x anisotropic).bilin
                (tail.ambientVector j) y' = 0 := by
            intro j hj
            change q.bilin (tail.ambientVector j : V) (y' : V) = 0
            simpa only [ambientVector_cons_succ] using
              horth j.succ (Nat.succ_le_succ hj)
          have hrec := ih i y' hy' horth'
          change (tail.order i : WithTop Int) ≤ ord K (q.quadratic y)
          simpa only [QuadraticSpace.orthogonalSpace_quadratic, y'] using hrec

namespace TwoBlockSplitWitness

/-- At a nontrivial orthogonal cut, the last order on the left is bounded by
the first order on the right. -/
theorem boundaryOrder_le
    {b : BONG V q L n} {cut : Nat} {hcut : cut ≤ n}
    (S : TwoBlockSplitWitness b cut hcut)
    (hcutPos : 0 < cut) (hright : cut < n) :
    b.order ⟨cut - 1, by omega⟩ ≤ b.order ⟨cut, hright⟩ := by
  have hrightLength : 0 < n - cut := by omega
  have hrightLengthEq : n - cut = (n - cut - 1) + 1 := by omega
  let rightBong := S.right.bong.castLength hrightLengthEq
  let zeroRight : Fin (n - cut) := ⟨0, hrightLength⟩
  let yRight : S.right.carrier :=
    rightBong.ambientVector (0 : Fin ((n - cut - 1) + 1))
  have hyRight : yRight ∈ S.right.lattice := by
    dsimp only [yRight]
    rw [rightBong.ambientVector_zero_eq_head]
    exact rightBong.head_isNormGenerator.mem
  have hyParent : (yRight : V) ∈ L := S.right_contained yRight hyRight
  let lastLeft : Fin n := ⟨cut - 1, by omega⟩
  have horth : ∀ j : Fin n, j.val ≤ lastLeft.val →
      q.bilin (b.ambientVector j) (yRight : V) = 0 := by
    intro j hj
    have hjCut : j.val < cut := by
      dsimp only [lastLeft] at hj
      omega
    let localIndex : Fin cut := ⟨j.val, hjCut⟩
    have hsource : S.left.sourceIndex localIndex = j := by
      apply Fin.ext
      simp [SegmentWitness.sourceIndex, localIndex]
    have hvector : (S.left.bong.ambientVector localIndex : V) =
        b.ambientVector j := by
      calc
        (S.left.bong.ambientVector localIndex : V) =
            b.ambientVector (S.left.sourceIndex localIndex) :=
          S.left.ambientVector_eq localIndex
        _ = b.ambientVector j := congrArg b.ambientVector hsource
    rw [← hvector]
    exact S.left_right_orthogonal
      (S.left.bong.ambientVector localIndex) yRight
  have hbound :=
    order_le_ord_quadratic_of_mem_of_orthogonal_prefix
      b lastLeft (yRight : V) hyParent horth
  have hyOrder : ord K (q.quadratic (yRight : V)) =
      (b.order ⟨cut, hright⟩ : WithTop Int) := by
    calc
      ord K (q.quadratic (yRight : V)) =
          ord K (rightBong.value 0) := by
        rw [← rightBong.quadratic_ambientVector 0]
        rfl
      _ = (rightBong.order 0 : WithTop Int) := by
        rw [rightBong.coe_order]
      _ = (S.right.bong.order zeroRight : WithTop Int) := by
        congr 1
        simpa [rightBong, zeroRight] using
          order_castLength_index S.right.bong hrightLengthEq
            (0 : Fin ((n - cut - 1) + 1))
      _ = (b.order ⟨cut, hright⟩ : WithTop Int) := by
        have horders : S.right.bong.order zeroRight =
            b.order ⟨cut, hright⟩ := by
          simpa [SegmentWitness.sourceIndex, zeroRight] using
            S.right.order_eq zeroRight
        exact congrArg (fun z : Int => (z : WithTop Int)) horders
  rw [hyOrder] at hbound
  exact WithTop.coe_le_coe.mp hbound

end TwoBlockSplitWitness

/-- Goodness on the two sides of a cut, together with the two crossing
two-step inequalities, gives goodness of the full BONG. -/
theorem isGood_of_goodSegmentsAroundCut_of_boundary
    (b : BONG V q L n) (cut : Nat)
    (hleft : 2 ≤ cut) (hright : cut + 1 < n)
    (hsegments : b.HasGoodSegmentsAroundCut cut (by omega))
    (hboundary : b.BoundaryGoodConditions cut hleft hright) :
    b.IsGood := by
  rcases hsegments with ⟨⟨left, leftGood⟩, ⟨right, rightGood⟩⟩
  intro i hi
  by_cases hinsideLeft : i.val + 2 < cut
  · let localIndex : Fin cut := ⟨i.val, by omega⟩
    have hlocal := leftGood localIndex (by
      dsimp only [localIndex]
      omega)
    rw [left.order_eq, left.order_eq] at hlocal
    simpa [SegmentWitness.sourceIndex, localIndex] using hlocal
  · by_cases hinsideRight : cut ≤ i.val
    · let localIndex : Fin (n - cut) := ⟨i.val - cut, by omega⟩
      have hlocalBound : localIndex.val + 2 < n - cut := by
        dsimp only [localIndex]
        omega
      have hlocal := rightGood localIndex hlocalBound
      rw [right.order_eq, right.order_eq] at hlocal
      have hsource : right.sourceIndex localIndex = i := by
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val, localIndex]
        omega
      have hsourceTwo :
          right.sourceIndex ⟨localIndex.val + 2, hlocalBound⟩ =
            ⟨i.val + 2, hi⟩ := by
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val, localIndex]
        omega
      rw [hsource, hsourceTwo] at hlocal
      exact hlocal
    · rcases hboundary with ⟨hfirst, hsecond, _⟩
      by_cases hpenultimate : i.val = cut - 2
      · convert hfirst using 1
        · apply congrArg b.order
          apply Fin.ext
          simpa using hpenultimate
        · apply congrArg b.order
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
      · convert hsecond using 1
        · apply congrArg b.order
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        · apply congrArg b.order
          apply Fin.ext
          simp only [Fin.val_mk]
          omega

/-- Beli (2003), Corollary 4.4(v), with every decomposition constructed and
no `BeliCorollary44Laws` parameter. -/
theorem beliCorollary44_v_unconditional
    (b : BONG V q L n) (cut : Nat)
    (hleft : 2 ≤ cut) (hright : cut + 1 < n)
    (hsegments : b.HasGoodSegmentsAroundCut cut (by omega)) :
    (b.IsGood ∧ b.HasTwoBlockSplit cut (by omega)) ↔
      b.BoundaryGoodConditions cut hleft hright := by
  constructor
  · rintro ⟨hgood, ⟨split⟩⟩
    refine ⟨?_, ?_, split.boundaryOrder_le (by omega) (by omega)⟩
    · let index : Fin n := ⟨cut - 2, by omega⟩
      have h := hgood index (by
        dsimp only [index]
        omega)
      convert h using 1 <;>
        apply congrArg b.order <;>
        apply Fin.ext <;>
        simp only [index, Fin.val_mk] <;>
        omega
    · let index : Fin n := ⟨cut - 1, by omega⟩
      have h := hgood index (by
        dsimp only [index]
        omega)
      convert h using 1 <;>
        apply congrArg b.order <;>
        apply Fin.ext <;>
        simp only [index, Fin.val_mk] <;>
        omega
  · intro hboundary
    have hgood := b.isGood_of_goodSegmentsAroundCut_of_boundary
      cut hleft hright hsegments hboundary
    refine ⟨hgood, ?_⟩
    let index : Fin n := ⟨cut - 1, by omega⟩
    have hindexNext : index.val + 1 < n := by
      dsimp only [index]
      omega
    have horder : b.order index ≤
        b.order ⟨index.val + 1, hindexNext⟩ := by
      convert hboundary.2.2 using 1 <;>
        apply congrArg b.order <;>
        apply Fin.ext <;>
        simp only [index, Fin.val_mk] <;>
        omega
    have hsplit := b.beliCorollary44_i_unconditional hgood index
      (by dsimp only [index]; omega) horder
    have hcutEq : index.val + 1 = cut := by
      dsimp only [index]
      omega
    simpa only [hcutEq] using hsplit

end BONG

end Bong
