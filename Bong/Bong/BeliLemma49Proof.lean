/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliSegmentDual
import Bong.Bong.SpinorNorm
import Bong.Lattice.SpinorNormIsometry
import Bong.Bong.ValueIsometry
import Bong.Bong.GoodMap
import Bong.Bong.BeliLemmas48To410

/-!
# Beli (2003), Lemma 4.9

This file proves both parts of Lemma 4.9 from the explicit Section 4
reverse-dual construction.  Consecutive orthogonal groups extend to the full
lattice, and an arbitrary good consecutive BONG can be replaced while keeping
all other ambient BONG vectors fixed.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

theorem latticeIsometryOfValueEq_map_eq
    {U : Type v} [AddCommGroup U] [Module K U]
    {W : Type w} [AddCommGroup W] [Module K W]
    {Z : Type z} [AddCommGroup Z] [Module K Z]
    {s : QuadraticSpace K U} {r : QuadraticSpace K W}
    {N : Lattice K U} {M : Lattice K W} {m : Nat}
    (a : BONG U s N m) (b : BONG W r M m)
    (hvalues : ∀ i, a.value i = b.value i)
    (left : U →ₗ[K] Z) (right : W →ₗ[K] Z)
    (vectors : ∀ i, right (b.ambientVector i) = left (a.ambientVector i))
    (x : U) :
    right ((a.latticeIsometryOfValueEq b hvalues).toLinearEquiv x) =
      left x := by
  let e := a.latticeIsometryOfValueEq b hvalues
  let f := right.comp e.toLinearEquiv.toLinearMap
  have hmaps : f = left := by
    apply a.basis.ext
    intro i
    change right (e.toLinearEquiv (a.ambientVector i)) =
      left (a.ambientVector i)
    rw [latticeIsometryOfValueEq_apply_ambientVector]
    exact vectors i
  exact DFunLike.congr_fun hmaps x

theorem spinorNormImage_suffix_segment_subset (b : BONG V q L n)
    {start length : Nat} (cover : start + length = n)
    (w : SegmentWitness b start length (by omega)) :
    Lattice.spinorNormImage
        (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) ⊆
      Lattice.spinorNormImage (q := q) (L := L) := by
  induction start generalizing V n with
  | zero =>
      let b' : BONG V q L length :=
        b.castLength (by simpa only [Nat.zero_add] using cover.symm)
      have hvalues : ∀ i : Fin length, b'.value i = w.bong.value i := by
        intro i
        rw [← b'.quadratic_ambientVector, ← w.bong.quadratic_ambientVector,
          BONG.ambientVector_castLength]
        change q.quadratic (b.ambientVector ⟨i.val, by omega⟩) =
          q.quadratic (w.bong.ambientVector i : V)
        rw [w.ambientVector_eq]
        apply congrArg q.quadratic
        apply congrArg b.ambientVector
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val]
        omega
      let e := b'.latticeIsometryOfValueEq w.bong hvalues
      intro a ha
      have hisometry := Lattice.spinorNormImage_eq_of_isometry e
      rw [hisometry]
      exact ha
  | succ start ih =>
      cases b with
      | nil _ _ _ => omega
      | @cons V _ _ q L m x generator anisotropic tail =>
          have tailCover : start + length = m := by omega
          let t := tail.segmentWitness start length (by omega)
          have hvalues : ∀ i : Fin length,
              t.bong.value i = w.bong.value i := by
            intro i
            rw [t.value_eq, w.value_eq]
            change tail.value (t.sourceIndex i) =
              (BONG.cons x generator anisotropic tail).value (w.sourceIndex i)
            have hindex : w.sourceIndex i = (t.sourceIndex i).succ := by
              apply Fin.ext
              change start + 1 + i.val = start + i.val + 1
              omega
            rw [hindex, BONG.value_cons_succ]
          let e := t.bong.latticeIsometryOfValueEq w.bong hvalues
          intro a ha
          have hisometry := Lattice.spinorNormImage_eq_of_isometry e
          have haTailSegment : a ∈ Lattice.spinorNormImage
              (q := (q.orthogonalSpace x anisotropic).restrict
                t.carrier t.nondegenerate) (L := t.lattice) := by
            rw [hisometry]
            exact ha
          have haTail : a ∈ Lattice.spinorNormImage
              (q := q.orthogonalSpace x anisotropic)
              (L := L.projectedLattice q x anisotropic) :=
            ih tail tailCover t haTailSegment
          exact Lattice.spinorNormImage_projectedLattice_subset generator haTail

theorem spinorNormImage_prefix_subset
    [BONGReverseDualLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood)
    {length : Nat} (bound : length ≤ n)
    (p : SegmentWitness b 0 length (by omega)) :
    Lattice.spinorNormImage
        (q := q.restrict p.carrier p.nondegenerate) (L := p.lattice) ⊆
      Lattice.spinorNormImage (q := q) (L := L) := by
  let good : GoodBONG q L n := ⟨b, hgood⟩
  choose dual hdualVectors using good.exists_reverseDual
  let D := dual.toBONG.segmentWitness (n - length) length (by omega)
  have hdualSegmentVectors : ∀ i : Fin length,
      (D.bong.ambientVector i : V) =
        p.bong.reverseDualVector i := by
    intro i
    calc
      (D.bong.ambientVector i : V) =
          dual.toBONG.ambientVector (D.sourceIndex i) :=
        D.ambientVector_eq i
      _ = dual.toBONG.ambientVector ⟨n - length + i.val, by omega⟩ := by
        congr 1
      _ = b.reverseDualVector ⟨n - length + i.val, by omega⟩ :=
        hdualVectors _
      _ = (p.bong.reverseDualVector i : V) := by
        change b.dualVector (Fin.rev ⟨n - length + i.val, by omega⟩) =
          (p.bong.dualVector (Fin.rev i) : V)
        rw [p.coe_dualVector_eq]
        congr 1
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val, Fin.rev]
        omega
  let e := p.segmentDualLatticeIsometry hgood D
    (QuadraticSpace.Isometry.refl q) hdualSegmentVectors
  intro a ha
  have haDual : a ∈ Lattice.spinorNormImage
      (q := q.restrict p.carrier p.nondegenerate)
      (L := Lattice.dualLattice
        (q.restrict p.carrier p.nondegenerate) p.lattice) := by
    rw [Lattice.spinorNormImage_dualLattice]
    exact ha
  have haSegment : a ∈ Lattice.spinorNormImage
      (q := q.restrict D.carrier D.nondegenerate)
      (L := D.lattice) := by
    rw [← Lattice.spinorNormImage_eq_of_isometry e]
    exact haDual
  have haDualParent := dual.toBONG.spinorNormImage_suffix_segment_subset
    (start := n - length) (length := length) (by omega) D haSegment
  rw [Lattice.spinorNormImage_dualLattice] at haDualParent
  exact haDualParent

/-- Beli (2003), Lemma 4.9(i): the spinor image of every good consecutive
segment embeds in the spinor image of the full lattice. -/
theorem spinorNormImage_segment_subset_of_good
    [BONGReverseDualLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood)
    {start length : Nat} {bound : start + length ≤ n}
    (w : SegmentWitness b start length bound) :
    Lattice.spinorNormImage
        (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) ⊆
      Lattice.spinorNormImage (q := q) (L := L) := by
  have hstart : start ≤ n := by omega
  let outer := b.segmentWitness start (n - start) (by omega)
  have hlength : length ≤ n - start := by omega
  let p := outer.bong.segmentWitness 0 length (by omega)
  have hvalues : ∀ i : Fin length, p.bong.value i = w.bong.value i := by
    intro i
    rw [p.value_eq, outer.value_eq, w.value_eq]
    congr 1
    apply Fin.ext
    simp only [SegmentWitness.sourceIndex_val]
    omega
  let e := p.bong.latticeIsometryOfValueEq w.bong hvalues
  intro a ha
  have hisometry := Lattice.spinorNormImage_eq_of_isometry e
  have haPrefix : a ∈ Lattice.spinorNormImage
      (q := (q.restrict outer.carrier outer.nondegenerate).restrict
        p.carrier p.nondegenerate) (L := p.lattice) := by
    rw [hisometry]
    exact ha
  have haOuter := outer.bong.spinorNormImage_prefix_subset
    (outer.isGood hgood) hlength p haPrefix
  exact b.spinorNormImage_suffix_segment_subset
    (start := start) (length := n - start) (by omega) outer haOuter

/-- Determinant-`-1` spinor classes of a suffix segment extend to the full
lattice. -/
theorem improperSpinorNormImage_suffix_segment_subset
    (b : BONG V q L n) {start length : Nat}
    (cover : start + length = n)
    (w : SegmentWitness b start length (by omega)) :
    Lattice.improperSpinorNormImage
        (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) ⊆
      Lattice.improperSpinorNormImage (q := q) (L := L) := by
  induction start generalizing V n with
  | zero =>
      let b' : BONG V q L length :=
        b.castLength (by simpa only [Nat.zero_add] using cover.symm)
      have hvalues : ∀ i : Fin length, b'.value i = w.bong.value i := by
        intro i
        rw [← b'.quadratic_ambientVector, ← w.bong.quadratic_ambientVector,
          BONG.ambientVector_castLength]
        change q.quadratic (b.ambientVector ⟨i.val, by omega⟩) =
          q.quadratic (w.bong.ambientVector i : V)
        rw [w.ambientVector_eq]
        apply congrArg q.quadratic
        apply congrArg b.ambientVector
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val]
        omega
      let e := b'.latticeIsometryOfValueEq w.bong hvalues
      intro a ha
      have hisometry := Lattice.improperSpinorNormImage_eq_of_isometry e
      rw [hisometry]
      exact ha
  | succ start ih =>
      cases b with
      | nil _ _ _ => omega
      | @cons V _ _ q L m x generator anisotropic tail =>
          have tailCover : start + length = m := by omega
          let t := tail.segmentWitness start length (by omega)
          have hvalues : ∀ i : Fin length,
              t.bong.value i = w.bong.value i := by
            intro i
            rw [t.value_eq, w.value_eq]
            change tail.value (t.sourceIndex i) =
              (BONG.cons x generator anisotropic tail).value (w.sourceIndex i)
            have hindex : w.sourceIndex i = (t.sourceIndex i).succ := by
              apply Fin.ext
              change start + 1 + i.val = start + i.val + 1
              omega
            rw [hindex, BONG.value_cons_succ]
          let e := t.bong.latticeIsometryOfValueEq w.bong hvalues
          intro a ha
          have hisometry := Lattice.improperSpinorNormImage_eq_of_isometry e
          have haTailSegment : a ∈ Lattice.improperSpinorNormImage
              (q := (q.orthogonalSpace x anisotropic).restrict
                t.carrier t.nondegenerate) (L := t.lattice) := by
            rw [hisometry]
            exact ha
          have haTail : a ∈ Lattice.improperSpinorNormImage
              (q := q.orthogonalSpace x anisotropic)
              (L := L.projectedLattice q x anisotropic) :=
            ih tail tailCover t haTailSegment
          exact Lattice.improperSpinorNormImage_projectedLattice_subset
            generator haTail

/-- Determinant-`-1` spinor classes of a good prefix segment extend to the
full lattice. -/
theorem improperSpinorNormImage_prefix_subset
    [BONGReverseDualLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood)
    {length : Nat} (bound : length ≤ n)
    (p : SegmentWitness b 0 length (by omega)) :
    Lattice.improperSpinorNormImage
        (q := q.restrict p.carrier p.nondegenerate) (L := p.lattice) ⊆
      Lattice.improperSpinorNormImage (q := q) (L := L) := by
  let good : GoodBONG q L n := ⟨b, hgood⟩
  choose dual hdualVectors using good.exists_reverseDual
  let D := dual.toBONG.segmentWitness (n - length) length (by omega)
  have hdualSegmentVectors : ∀ i : Fin length,
      (D.bong.ambientVector i : V) = p.bong.reverseDualVector i := by
    intro i
    calc
      (D.bong.ambientVector i : V) =
          dual.toBONG.ambientVector (D.sourceIndex i) :=
        D.ambientVector_eq i
      _ = dual.toBONG.ambientVector ⟨n - length + i.val, by omega⟩ := by
        congr 1
      _ = b.reverseDualVector ⟨n - length + i.val, by omega⟩ :=
        hdualVectors _
      _ = (p.bong.reverseDualVector i : V) := by
        change b.dualVector (Fin.rev ⟨n - length + i.val, by omega⟩) =
          (p.bong.dualVector (Fin.rev i) : V)
        rw [p.coe_dualVector_eq]
        congr 1
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val, Fin.rev]
        omega
  let e := p.segmentDualLatticeIsometry hgood D
    (QuadraticSpace.Isometry.refl q) hdualSegmentVectors
  intro a ha
  have haDual : a ∈ Lattice.improperSpinorNormImage
      (q := q.restrict p.carrier p.nondegenerate)
      (L := Lattice.dualLattice
        (q.restrict p.carrier p.nondegenerate) p.lattice) := by
    rw [Lattice.improperSpinorNormImage_dualLattice]
    exact ha
  have haSegment : a ∈ Lattice.improperSpinorNormImage
      (q := q.restrict D.carrier D.nondegenerate)
      (L := D.lattice) := by
    rw [← Lattice.improperSpinorNormImage_eq_of_isometry e]
    exact haDual
  have haDualParent := dual.toBONG.improperSpinorNormImage_suffix_segment_subset
    (start := n - length) (length := length) (by omega) D haSegment
  rw [Lattice.improperSpinorNormImage_dualLattice] at haDualParent
  exact haDualParent

/-- Beli (2003), Lemma 4.9(i), for the determinant-`-1` component of the
integral orthogonal group. -/
theorem improperSpinorNormImage_segment_subset_of_good
    [BONGReverseDualLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood)
    {start length : Nat} {bound : start + length ≤ n}
    (w : SegmentWitness b start length bound) :
    Lattice.improperSpinorNormImage
        (q := q.restrict w.carrier w.nondegenerate) (L := w.lattice) ⊆
      Lattice.improperSpinorNormImage (q := q) (L := L) := by
  have hstart : start ≤ n := by omega
  let outer := b.segmentWitness start (n - start) (by omega)
  have hlength : length ≤ n - start := by omega
  let p := outer.bong.segmentWitness 0 length (by omega)
  have hvalues : ∀ i : Fin length, p.bong.value i = w.bong.value i := by
    intro i
    rw [p.value_eq, outer.value_eq, w.value_eq]
    congr 1
    apply Fin.ext
    simp only [SegmentWitness.sourceIndex_val]
    omega
  let e := p.bong.latticeIsometryOfValueEq w.bong hvalues
  intro a ha
  have hisometry := Lattice.improperSpinorNormImage_eq_of_isometry e
  have haPrefix : a ∈ Lattice.improperSpinorNormImage
      (q := (q.restrict outer.carrier outer.nondegenerate).restrict
        p.carrier p.nondegenerate) (L := p.lattice) := by
    rw [hisometry]
    exact ha
  have haOuter := outer.bong.improperSpinorNormImage_prefix_subset
    (outer.isGood hgood) hlength p haPrefix
  exact b.improperSpinorNormImage_suffix_segment_subset
    (start := start) (length := n - start) (by omega) outer haOuter

/-- The vector-level part of a consecutive replacement, before proving that
the resulting BONG is good. -/
structure RawSegmentReplacementWitness (b : BONG V q L n)
    {start length : Nat} {bound : start + length ≤ n}
    (w : SegmentWitness b start length bound)
    (c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length) where
  bong : BONG V q L n
  before_eq : ∀ (i : Fin n), i.val < start →
    bong.ambientVector i = b.ambientVector i
  inside_eq : ∀ i : Fin length,
    bong.ambientVector ⟨start + i.val, by omega⟩ =
      (c.ambientVector i : V)
  after_eq : ∀ (i : Fin n), start + length ≤ i.val →
    bong.ambientVector i = b.ambientVector i

/-- A replacement whose block reaches the end of a BONG can be assembled by
recursively retaining the preceding heads. -/
noncomputable def rawSuffixSegmentReplacement
    (b : BONG V q L n) {start length : Nat}
    (cover : start + length = n)
    (w : SegmentWitness b start length (by omega))
    (c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length) :
    RawSegmentReplacementWitness b w c := by
  induction start generalizing V n with
  | zero =>
      have hlength : length = n := by omega
      let b' := b.castLength hlength.symm
      have hvalues : ∀ i : Fin length,
          w.bong.value i = b'.value i := by
        intro i
        rw [← w.bong.quadratic_ambientVector,
          ← b'.quadratic_ambientVector, BONG.ambientVector_castLength]
        change q.quadratic (w.bong.ambientVector i : V) =
          q.quadratic (b.ambientVector ⟨i.val, by omega⟩)
        rw [w.ambientVector_eq]
        apply congrArg q.quadratic
        apply congrArg b.ambientVector
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val]
        omega
      let e := w.bong.latticeIsometryOfValueEq b' hvalues
      let d' := c.mapLatticeIsometry e
      let d := d'.castLength hlength
      have hmapCoe : ∀ z : w.carrier,
          e.toLinearEquiv z = (z : V) := by
        intro z
        let left : w.carrier →ₗ[K] V := w.carrier.subtype
        let right : V →ₗ[K] V := LinearMap.id
        exact w.bong.latticeIsometryOfValueEq_map_eq b' hvalues
          left right (by
            intro i
            change b'.ambientVector i = (w.bong.ambientVector i : V)
            rw [BONG.ambientVector_castLength, w.ambientVector_eq]
            apply congrArg b.ambientVector
            apply Fin.ext
            simp only [SegmentWitness.sourceIndex_val]
            omega) z
      refine {
        bong := d
        before_eq := ?_
        inside_eq := ?_
        after_eq := ?_ }
      · intro i hi
        omega
      · intro i
        rw [show d = d'.castLength hlength by rfl,
          BONG.ambientVector_castLength]
        rw [show d' = c.mapLatticeIsometry e by rfl,
          BONG.ambientVector_mapLatticeIsometry]
        simpa only [Nat.zero_add] using hmapCoe (c.ambientVector i)
      · intro i hi
        omega
  | succ start ih =>
      cases b with
      | nil _ _ _ => omega
      | @cons V _ _ q L m x generator anisotropic tail =>
          have tailCover : start + length = m := by omega
          let t := tail.segmentWitness start length (by omega)
          have hvalues : ∀ i : Fin length,
              w.bong.value i = t.bong.value i := by
            intro i
            rw [w.value_eq, t.value_eq]
            change (BONG.cons x generator anisotropic tail).value
                (w.sourceIndex i) = tail.value (t.sourceIndex i)
            have hindex : w.sourceIndex i = (t.sourceIndex i).succ := by
              apply Fin.ext
              change start + 1 + i.val = start + i.val + 1
              omega
            rw [hindex, BONG.value_cons_succ]
          let e := w.bong.latticeIsometryOfValueEq t.bong hvalues
          let cTail := c.mapLatticeIsometry e
          let D := ih tail tailCover t cTail
          let d := BONG.cons x generator anisotropic D.bong
          let right : t.carrier →ₗ[K] V :=
            (q.vectorOrthogonal x).subtype.comp t.carrier.subtype
          have hmapCoe : ∀ z : w.carrier,
              ((e.toLinearEquiv z : t.carrier) : q.vectorOrthogonal x) =
                (z : V) := by
            intro z
            let left : w.carrier →ₗ[K] V := w.carrier.subtype
            exact w.bong.latticeIsometryOfValueEq_map_eq t.bong hvalues
              left right (by
                intro i
                change (t.bong.ambientVector i : V) =
                  (w.bong.ambientVector i : V)
                rw [t.ambientVector_eq, w.ambientVector_eq]
                change (tail.ambientVector (t.sourceIndex i) : V) =
                  (BONG.cons x generator anisotropic tail).ambientVector
                    (w.sourceIndex i)
                have hindex : w.sourceIndex i = (t.sourceIndex i).succ := by
                  apply Fin.ext
                  change start + 1 + i.val = start + i.val + 1
                  omega
                rw [hindex, BONG.ambientVector_cons_succ]) z
          refine {
            bong := d
            before_eq := ?_
            inside_eq := ?_
            after_eq := ?_ }
          · intro i hi
            cases i using Fin.cases with
            | zero =>
                rw [show d = BONG.cons x generator anisotropic D.bong by rfl,
                  BONG.ambientVector_cons_zero,
                  BONG.ambientVector_cons_zero]
            | succ j =>
                rw [show d = BONG.cons x generator anisotropic D.bong by rfl,
                  BONG.ambientVector_cons_succ,
                  BONG.ambientVector_cons_succ]
                change j.val + 1 < start + 1 at hi
                exact congrArg Subtype.val (D.before_eq j (by omega))
          · intro i
            let j : Fin m := ⟨start + i.val, by omega⟩
            have hindex : (⟨start + 1 + i.val, by omega⟩ : Fin (m + 1)) =
                j.succ := by
              apply Fin.ext
              simp only [j, Fin.succ_mk]
              omega
            rw [hindex,
              show d = BONG.cons x generator anisotropic D.bong by rfl,
              BONG.ambientVector_cons_succ]
            calc
              (D.bong.ambientVector j : V) =
                  (cTail.ambientVector i : q.vectorOrthogonal x) :=
                congrArg Subtype.val (D.inside_eq i)
              _ = ((e.toLinearEquiv (c.ambientVector i) : t.carrier) :
                    q.vectorOrthogonal x) := by
                rw [show cTail = c.mapLatticeIsometry e by rfl,
                  BONG.ambientVector_mapLatticeIsometry]
              _ = (c.ambientVector i : V) := hmapCoe (c.ambientVector i)
          · intro i hi
            cases i using Fin.cases with
            | zero => omega
            | succ j =>
                rw [show d = BONG.cons x generator anisotropic D.bong by rfl,
                  BONG.ambientVector_cons_succ,
                  BONG.ambientVector_cons_succ]
                change start + 1 + length ≤ j.val + 1 at hi
                exact congrArg Subtype.val (D.after_eq j (by omega))

variable [BeliLemma47Laws.{u, v} K]

/-- A raw replacement of a good segment by a good BONG has the same order at
every global index.  Outside the segment this follows from equality of ambient
vectors; inside it is precisely the order-invariance consequence of Lemma 4.7. -/
theorem RawSegmentReplacementWitness.order_eq
    {start length : Nat} {bound : start + length ≤ n}
    {b : BONG V q L n} (hgood : b.IsGood)
    {w : SegmentWitness b start length bound}
    {c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length} (hc : c.IsGood)
    (D : RawSegmentReplacementWitness b w c) (i : Fin n) :
    D.bong.order i = b.order i := by
  by_cases hbefore : i.val < start
  · apply WithTop.coe_injective
    rw [BONG.coe_order, BONG.coe_order,
      ← D.bong.quadratic_ambientVector,
      ← b.quadratic_ambientVector, D.before_eq i hbefore]
  by_cases hafter : start + length ≤ i.val
  · apply WithTop.coe_injective
    rw [BONG.coe_order, BONG.coe_order,
      ← D.bong.quadratic_ambientVector,
      ← b.quadratic_ambientVector, D.after_eq i hafter]
  · let j : Fin length := ⟨i.val - start, by omega⟩
    have hsource : w.sourceIndex j = i := by
      apply Fin.ext
      simp only [SegmentWitness.sourceIndex_val, j]
      omega
    have hvalue : D.bong.value i = c.value j := by
      rw [← D.bong.quadratic_ambientVector]
      change q.quadratic (D.bong.ambientVector i) = c.value j
      rw [← hsource]
      change q.quadratic
        (D.bong.ambientVector ⟨start + j.val, by omega⟩) = c.value j
      rw [D.inside_eq]
      exact c.quadratic_ambientVector j
    calc
      D.bong.order i = c.order j := by
        apply WithTop.coe_injective
        rw [BONG.coe_order, BONG.coe_order, hvalue]
      _ = w.bong.order j :=
        BeliLemma47Laws.goodBONG_orders_eq c w.bong hc
          (w.isGood hgood) j
      _ = b.order (w.sourceIndex j) := w.order_eq j
      _ = b.order i := congrArg b.order hsource

/-- Adding the recovered goodness proof upgrades a raw replacement to the
replacement witness required in Beli (2003), Lemma 4.9(ii). -/
def RawSegmentReplacementWitness.toSegmentReplacement
    {start length : Nat} {bound : start + length ≤ n}
    {b : BONG V q L n} (hgood : b.IsGood)
    {w : SegmentWitness b start length bound}
    {c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length} (hc : c.IsGood)
    (D : RawSegmentReplacementWitness b w c) :
    SegmentReplacementWitness b w c where
  bong := D.bong
  good := by
    intro i hi
    rw [D.order_eq hgood hc i,
      D.order_eq hgood hc ⟨i.val + 2, hi⟩]
    exact hgood i hi
  before_eq := D.before_eq
  inside_eq := D.inside_eq
  after_eq := D.after_eq

/-- Lemma 4.9(ii) for a segment reaching the final BONG vector. -/
noncomputable def suffixSegmentReplacement
    (b : BONG V q L n) (hgood : b.IsGood) {start length : Nat}
    (cover : start + length = n)
    (w : SegmentWitness b start length (by omega))
    (c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length) (hc : c.IsGood) :
    SegmentReplacementWitness b w c :=
  (rawSuffixSegmentReplacement b cover w c).toSegmentReplacement hgood hc

/-- Applying the normalized reverse-dual operation twice recovers the original
ambient vectors whenever the intermediate BONG realizes the first reverse
dual literally. -/
theorem reverseDualVector_eq_ambientVector_of_realization
    {M N : Lattice K V} {m : Nat}
    (source : BONG V q M m) (dual : BONG V q N m)
    (vectors : ∀ i, dual.ambientVector i = source.reverseDualVector i)
    (i : Fin m) :
    dual.reverseDualVector i = source.ambientVector i := by
  change
    (dual.value (Fin.rev i))⁻¹ • dual.ambientVector (Fin.rev i) =
      source.ambientVector i
  rw [← dual.quadratic_ambientVector, vectors]
  exact source.normalize_reverseDualVector_rev i

/-- Reverse-dual vectors commute with transport by a lattice isometry. -/
@[simp]
theorem reverseDualVector_mapLatticeIsometry
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (e : Lattice.Isometry q r L M) (b : BONG V q L n)
    (i : Fin n) :
    (b.mapLatticeIsometry e).reverseDualVector i =
      e.toLinearEquiv (b.reverseDualVector i) := by
  change ((b.mapLatticeIsometry e).value (Fin.rev i))⁻¹ •
      (b.mapLatticeIsometry e).ambientVector (Fin.rev i) =
    e.toLinearEquiv
      ((b.value (Fin.rev i))⁻¹ • b.ambientVector (Fin.rev i))
  rw [BONG.value_mapLatticeIsometry,
    BONG.ambientVector_mapLatticeIsometry]
  exact (e.toLinearEquiv.map_smul _ _).symm

/-- Reversing a suffix replacement turns its local replacement BONG into the
corresponding prefix of the reversed global BONG. -/
theorem SegmentReplacementWitness.reverseDualVector_prefix_eq
    {start length : Nat} {bound : start + length ≤ n}
    {b : BONG V q L n} {w : SegmentWitness b start length bound}
    {c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length}
    (D : SegmentReplacementWitness b w c)
    (cover : start + length = n) (i : Fin length) :
    D.bong.reverseDualVector ⟨i.val, by omega⟩ =
      (c.reverseDualVector i : V) := by
  let k : Fin n := ⟨i.val, by omega⟩
  let j : Fin length := Fin.rev i
  have hrev : Fin.rev k =
      (⟨start + j.val, by omega⟩ : Fin n) := by
    apply Fin.ext
    simp only [k, j, Fin.rev]
    omega
  have hvalue : D.bong.value (Fin.rev k) = c.value j := by
    rw [← D.bong.quadratic_ambientVector]
    change q.quadratic (D.bong.ambientVector (Fin.rev k)) = c.value j
    rw [hrev, D.inside_eq]
    exact c.quadratic_ambientVector j
  change (D.bong.value (Fin.rev k))⁻¹ •
      D.bong.ambientVector (Fin.rev k) =
    ((c.value (Fin.rev i))⁻¹ • c.ambientVector (Fin.rev i) :
      w.carrier)
  rw [show Fin.rev i = j by rfl, hvalue, hrev, D.inside_eq]
  rfl

namespace SegmentWitness

/-- The segment-dual isometry is the ambient isometry on every vector, not
only on the displayed reversed dual basis. -/
theorem coe_segmentDualLatticeIsometry
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {m start dualStart length : Nat}
    {bound : start + length ≤ n}
    {dualBound : dualStart + length ≤ m}
    {b : BONG V q L n} {d : BONG W r M m}
    [BONGReverseDualLaws.{u, v} K]
    (original : SegmentWitness b start length bound)
    (originalGood : b.IsGood)
    (dual : SegmentWitness d dualStart length dualBound)
    (ambient : q.Isometry r)
    (dualVectors : ∀ i : Fin length,
      (dual.bong.ambientVector i : W) =
        ambient.toLinearEquiv
          (original.bong.reverseDualVector i : V))
    (z : original.carrier) :
    ((original.segmentDualLatticeIsometry originalGood dual ambient
        dualVectors).toLinearEquiv z : dual.carrier) =
      ambient.toLinearEquiv (z : V) := by
  let e := original.segmentDualLatticeIsometry originalGood dual ambient
    dualVectors
  let left : original.carrier →ₗ[K] W :=
    dual.carrier.subtype.comp e.toLinearEquiv.toLinearMap
  let right : original.carrier →ₗ[K] W :=
    ambient.toLinearEquiv.toLinearMap.comp original.carrier.subtype
  have hmaps : left = right := by
    apply original.bong.reverseDualBasis.ext
    intro i
    rw [BONG.reverseDualBasis_apply]
    change ((e.toLinearEquiv (original.bong.reverseDualVector i) :
        dual.carrier) : W) =
      ambient.toLinearEquiv (original.bong.reverseDualVector i : V)
    rw [show e = original.segmentDualLatticeIsometry originalGood dual
          ambient dualVectors by rfl,
      original.segmentDualLatticeIsometry_apply_reverseDualVector
        originalGood dual ambient dualVectors,
      dualVectors]
  exact DFunLike.congr_fun hmaps z

end SegmentWitness

/-- Transporting only the lattice index preserves goodness. -/
theorem IsGood.castLattice
    {M N : Lattice K V} {m : Nat} {b : BONG V q M m}
    (good : b.IsGood) (h : M = N) : (b.castLattice h).IsGood := by
  subst N
  exact good

/-- Prefix replacement, obtained by applying the suffix construction to the
reverse-dual BONG and then dualizing back. -/
noncomputable def prefixSegmentReplacement
    [BONGReverseDualLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood) {length : Nat}
    (bound : length ≤ n)
    (w : SegmentWitness b 0 length (by omega))
    (c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length) (hc : c.IsGood) :
    SegmentReplacementWitness b w c := by
  let bgood : GoodBONG q L n := ⟨b, hgood⟩
  let d : GoodBONG q (Lattice.dualLattice q L) n :=
    Classical.choose bgood.exists_reverseDual
  have hd : ∀ i, d.toBONG.ambientVector i = b.reverseDualVector i :=
    Classical.choose_spec bgood.exists_reverseDual
  let dualStart := n - length
  let wd := d.toBONG.segmentWitness dualStart length (by omega)
  have hdSegment : ∀ i : Fin length,
      (wd.bong.ambientVector i : V) =
        w.bong.reverseDualVector i := by
    intro i
    calc
      (wd.bong.ambientVector i : V) =
          d.toBONG.ambientVector (wd.sourceIndex i) :=
        wd.ambientVector_eq i
      _ = b.reverseDualVector (wd.sourceIndex i) := hd (wd.sourceIndex i)
      _ = b.reverseDualVector ⟨n - length + i.val, by omega⟩ := by
        congr 1
      _ = (w.bong.reverseDualVector i : V) :=
        (w.coe_reverseDualVector_prefix_eq
          (m := 0) (start := 0) (dualStart := 0) i).symm
  let ambient := QuadraticSpace.Isometry.refl q
  let e := w.segmentDualLatticeIsometry hgood wd ambient hdSegment
  let cgood : GoodBONG (q.restrict w.carrier w.nondegenerate)
      w.lattice length := ⟨c, hc⟩
  let cdual : GoodBONG (q.restrict w.carrier w.nondegenerate)
      (Lattice.dualLattice
        (q.restrict w.carrier w.nondegenerate) w.lattice) length :=
    Classical.choose cgood.exists_reverseDual
  have hcdual : ∀ i, cdual.toBONG.ambientVector i =
      c.reverseDualVector i :=
    Classical.choose_spec cgood.exists_reverseDual
  let mapped := cdual.mapLatticeIsometry e
  have dualCover : dualStart + length = n := by
    dsimp [dualStart]
    omega
  let Ddual := suffixSegmentReplacement d.toBONG d.good dualCover wd
    mapped.toBONG mapped.good
  let Dgood : GoodBONG q (Lattice.dualLattice q L) n :=
    ⟨Ddual.bong, Ddual.good⟩
  let back : GoodBONG q
      (Lattice.dualLattice q (Lattice.dualLattice q L)) n :=
    Classical.choose Dgood.exists_reverseDual
  have hback : ∀ i, back.toBONG.ambientVector i =
      Ddual.bong.reverseDualVector i :=
    Classical.choose_spec Dgood.exists_reverseDual
  let result := back.toBONG.castLattice
    (Lattice.dualLattice_dualLattice q L)
  refine {
    bong := result
    good := ?_
    before_eq := ?_
    inside_eq := ?_
    after_eq := ?_ }
  · exact back.good.castLattice (Lattice.dualLattice_dualLattice q L)
  · intro i hi
    omega
  · intro i
    have hindex : (⟨0 + i.val, by omega⟩ : Fin n) =
        (⟨i.val, by omega⟩ : Fin n) := by
      apply Fin.ext
      simp
    rw [hindex, show result = back.toBONG.castLattice
        (Lattice.dualLattice_dualLattice q L) by rfl,
      BONG.ambientVector_castLattice, hback]
    have hprefix := Ddual.reverseDualVector_prefix_eq dualCover i
    rw [hprefix]
    have hcoe := w.coe_segmentDualLatticeIsometry hgood wd ambient
      hdSegment (c.ambientVector i)
    calc
      (mapped.toBONG.reverseDualVector i : V) =
          ((e.toLinearEquiv (cdual.toBONG.reverseDualVector i) :
            wd.carrier) : V) := by
        exact congrArg Subtype.val
          (BONG.reverseDualVector_mapLatticeIsometry e cdual.toBONG i)
      _ = ((e.toLinearEquiv (c.ambientVector i) : wd.carrier) : V) := by
        rw [BONG.reverseDualVector_eq_ambientVector_of_realization
          c cdual.toBONG hcdual]
      _ = (c.ambientVector i : V) := by
        rw [show e = w.segmentDualLatticeIsometry hgood wd ambient
          hdSegment by rfl]
        simpa [ambient, QuadraticSpace.Isometry.refl] using hcoe
  · intro i hi
    have hrevBefore : (Fin.rev i).val < dualStart := by
      dsimp [dualStart]
      change n - (i.val + 1) < n - length
      omega
    have hvec : Ddual.bong.ambientVector (Fin.rev i) =
        d.toBONG.ambientVector (Fin.rev i) :=
      Ddual.before_eq (Fin.rev i) hrevBefore
    have hvalue : Ddual.bong.value (Fin.rev i) =
        d.toBONG.value (Fin.rev i) := by
      rw [← Ddual.bong.quadratic_ambientVector,
        ← d.toBONG.quadratic_ambientVector, hvec]
    have hreverse : Ddual.bong.reverseDualVector i =
        d.toBONG.reverseDualVector i := by
      change (Ddual.bong.value (Fin.rev i))⁻¹ •
          Ddual.bong.ambientVector (Fin.rev i) =
        (d.toBONG.value (Fin.rev i))⁻¹ •
          d.toBONG.ambientVector (Fin.rev i)
      rw [hvalue, hvec]
    rw [show result = back.toBONG.castLattice
        (Lattice.dualLattice_dualLattice q L) by rfl,
      BONG.ambientVector_castLattice, hback, hreverse]
    exact BONG.reverseDualVector_eq_ambientVector_of_realization
      b d.toBONG hd i

/-- Beli (2003), Lemma 4.9(ii) for an arbitrary consecutive segment.  The
prefix case is the dual construction above; subsequent heads are retained
recursively. -/
noncomputable def segmentReplacement
    [BONGReverseDualLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood)
    {start length : Nat} {bound : start + length ≤ n}
    (w : SegmentWitness b start length bound)
    (c : BONG w.carrier (q.restrict w.carrier w.nondegenerate)
      w.lattice length) (hc : c.IsGood) :
    SegmentReplacementWitness b w c := by
  induction start generalizing V n with
  | zero =>
      exact prefixSegmentReplacement b hgood (by omega) w c hc
  | succ start ih =>
      cases b with
      | nil _ _ _ => omega
      | @cons V _ _ q L m x generator anisotropic tail =>
          have tailBound : start + length ≤ m := by omega
          let t := tail.segmentWitness start length tailBound
          have hvalues : ∀ i : Fin length,
              w.bong.value i = t.bong.value i := by
            intro i
            rw [w.value_eq, t.value_eq]
            have hindex : w.sourceIndex i = (t.sourceIndex i).succ := by
              apply Fin.ext
              change start + 1 + i.val = start + i.val + 1
              omega
            rw [hindex, BONG.value_cons_succ]
          let e := w.bong.latticeIsometryOfValueEq t.bong hvalues
          let cTail := c.mapLatticeIsometry e
          have htailGood : tail.IsGood := BONG.IsGood.tail hgood
          have hcTail : cTail.IsGood := hc.mapLatticeIsometry e
          let D := ih tail htailGood t cTail hcTail
          let d := BONG.cons x generator anisotropic D.bong
          let right : t.carrier →ₗ[K] V :=
            (q.vectorOrthogonal x).subtype.comp t.carrier.subtype
          have hmapCoe : ∀ z : w.carrier,
              ((e.toLinearEquiv z : t.carrier) : q.vectorOrthogonal x) =
                (z : V) := by
            intro z
            let left : w.carrier →ₗ[K] V := w.carrier.subtype
            exact w.bong.latticeIsometryOfValueEq_map_eq t.bong hvalues
              left right (by
                intro i
                change (t.bong.ambientVector i : V) =
                  (w.bong.ambientVector i : V)
                rw [t.ambientVector_eq, w.ambientVector_eq]
                have hindex :
                    (⟨start + 1 + i.val, by omega⟩ : Fin (m + 1)) =
                      (⟨start + i.val, by omega⟩ : Fin m).succ := by
                  apply Fin.ext
                  change start + 1 + i.val = start + i.val + 1
                  omega
                rw [hindex, BONG.ambientVector_cons_succ]) z
          let R : RawSegmentReplacementWitness
              (BONG.cons x generator anisotropic tail) w c := {
            bong := d
            before_eq := by
              intro i hi
              cases i using Fin.cases with
              | zero =>
                  rw [show d = BONG.cons x generator anisotropic D.bong by rfl,
                    BONG.ambientVector_cons_zero,
                    BONG.ambientVector_cons_zero]
              | succ j =>
                  rw [show d = BONG.cons x generator anisotropic D.bong by rfl,
                    BONG.ambientVector_cons_succ,
                    BONG.ambientVector_cons_succ]
                  change j.val + 1 < start + 1 at hi
                  exact congrArg Subtype.val (D.before_eq j (by omega))
            inside_eq := by
              intro i
              let j : Fin m := ⟨start + i.val, by omega⟩
              have hindex :
                  (⟨start + 1 + i.val, by omega⟩ : Fin (m + 1)) =
                    j.succ := by
                apply Fin.ext
                simp only [j, Fin.succ_mk]
                omega
              rw [hindex,
                show d = BONG.cons x generator anisotropic D.bong by rfl,
                BONG.ambientVector_cons_succ]
              calc
                (D.bong.ambientVector j : V) =
                    (cTail.ambientVector i : q.vectorOrthogonal x) :=
                  congrArg Subtype.val (D.inside_eq i)
                _ = ((e.toLinearEquiv (c.ambientVector i) : t.carrier) :
                      q.vectorOrthogonal x) := by
                  rw [show cTail = c.mapLatticeIsometry e by rfl,
                    BONG.ambientVector_mapLatticeIsometry]
                _ = (c.ambientVector i : V) := hmapCoe (c.ambientVector i)
            after_eq := by
              intro i hi
              cases i using Fin.cases with
              | zero =>
                  change start + 1 + length ≤ 0 at hi
                  omega
              | succ j =>
                  rw [show d = BONG.cons x generator anisotropic D.bong by rfl,
                    BONG.ambientVector_cons_succ,
                    BONG.ambientVector_cons_succ]
                  change start + 1 + length ≤ j.val + 1 at hi
                  exact congrArg Subtype.val (D.after_eq j (by omega)) }
          exact R.toSegmentReplacement hgood hc

/-- The two assertions of Beli (2003), Lemma 4.9 are consequences of the
explicit Section 4 reverse-dual construction and Lemma 4.7 order invariance. -/
instance beliLemma49LawsOfReverseDual
    [BONGReverseDualLaws.{u, v} K] :
    BeliLemma49Laws.{u, v} K where
  segment_spinorNormImage_subset := fun b hgood w =>
    b.spinorNormImage_segment_subset_of_good hgood w
  segment_improperSpinorNormImage_subset := fun b hgood w =>
    b.improperSpinorNormImage_segment_subset_of_good hgood w
  replace_good_segment := fun b hgood w c hc =>
    ⟨b.segmentReplacement hgood w c hc⟩

end BONG

end Bong
