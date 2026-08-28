/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Map
import Bong.Bong.Segment

/-!
# Transport of consecutive BONG segments

A consecutive segment is geometric data, so it transports functorially under
an ambient quadratic-space isometry.  This file packages the mapped carrier,
the induced restricted isometry, the mapped integral lattice, and the literal
ambient-vector formula in one reusable `SegmentWitness`.
-/

namespace Bong

open Dyadic

namespace BONG.SegmentWitness

universe u v w

section MapTransport

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {n start length : Nat}
  {bound : start + length ≤ n}
  {b : BONG V q L n}

/-- The image of a segment carrier under an ambient isometry. -/
def mapCarrier (w : SegmentWitness b start length bound)
    (f : q.Isometry r) : Submodule K W :=
  w.carrier.map f.toLinearEquiv.toLinearMap

/-- Nondegeneracy is preserved when a segment carrier is mapped by an
ambient quadratic isometry. -/
theorem mapCarrier_nondegenerate
    (w : SegmentWitness b start length bound) (f : q.Isometry r) :
    (r.bilin.restrict (w.mapCarrier f)).Nondegenerate := by
  let e : w.carrier ≃ₗ[K] w.mapCarrier f := by
    simpa only [mapCarrier] using
      f.toLinearEquiv.submoduleMap w.carrier
  constructor
  · intro y hy
    have hy' : ∀ z : w.carrier,
        (q.bilin.restrict w.carrier) (e.symm y) z = 0 := by
      intro z
      have h := hy (e z)
      change r.bilin (y : W) (f.toLinearEquiv (z : V)) = 0 at h
      have hmap := f.map_bilin (e.symm y : V) (z : V)
      rw [show f.toLinearEquiv (e.symm y : V) = (y : W) by
        exact congrArg Subtype.val (e.apply_symm_apply y)] at hmap
      rwa [hmap] at h
    have hzero : e.symm y = 0 := w.nondegenerate.1 (e.symm y) hy'
    apply e.symm.injective
    simpa only [map_zero] using hzero
  · intro y hy
    have hy' : ∀ z : w.carrier,
        (q.bilin.restrict w.carrier) z (e.symm y) = 0 := by
      intro z
      have h := hy (e z)
      change r.bilin (f.toLinearEquiv (z : V)) (y : W) = 0 at h
      have hmap := f.map_bilin (z : V) (e.symm y : V)
      rw [show f.toLinearEquiv (e.symm y : V) = (y : W) by
        exact congrArg Subtype.val (e.apply_symm_apply y)] at hmap
      rwa [hmap] at h
    have hzero : e.symm y = 0 := w.nondegenerate.2 (e.symm y) hy'
    apply e.symm.injective
    simpa only [map_zero] using hzero

/-- The restriction of an ambient isometry to a segment carrier and its
image. -/
noncomputable def mapIsometry
    (w : SegmentWitness b start length bound) (f : q.Isometry r) :
    (q.restrict w.carrier w.nondegenerate).Isometry
      (r.restrict (w.mapCarrier f) (w.mapCarrier_nondegenerate f)) where
  toLinearEquiv := f.toLinearEquiv.submoduleMap w.carrier
  map_bilin x y := f.map_bilin (x : V) (y : V)

/-- Transport a consecutive BONG segment through an ambient quadratic
isometry. -/
noncomputable def map
    (w : SegmentWitness b start length bound) (f : q.Isometry r) :
    SegmentWitness (b.map f) start length bound where
  carrier := w.mapCarrier f
  nondegenerate := w.mapCarrier_nondegenerate f
  lattice := Lattice.map (w.mapIsometry f).toLinearEquiv w.lattice
  bong := w.bong.map (w.mapIsometry f)
  ambientVector_eq := by
    intro i
    rw [BONG.ambientVector_map]
    change f.toLinearEquiv (w.bong.ambientVector i : V) =
      (b.map f).ambientVector ⟨start + i.1, by omega⟩
    rw [w.ambientVector_eq, BONG.ambientVector_map]

/-- The restricted isometry used by `SegmentWitness.map`, now bundled with
its exact source and target segment lattices. -/
noncomputable def mapLatticeIsometry
    (w : SegmentWitness b start length bound) (f : q.Isometry r) :
    Lattice.Isometry
      (q.restrict w.carrier w.nondegenerate)
      (r.restrict (w.map f).carrier (w.map f).nondegenerate)
      w.lattice (w.map f).lattice where
  toLinearEquiv := (w.mapIsometry f).toLinearEquiv
  map_bilin := (w.mapIsometry f).map_bilin
  map_mem z := (Lattice.map_mem_map_iff
    (w.mapIsometry f).toLinearEquiv w.lattice z).symm

@[simp]
theorem mapLatticeIsometry_apply_ambientVector
    (w : SegmentWitness b start length bound) (f : q.Isometry r)
    (i : Fin length) :
    (w.mapLatticeIsometry f).toLinearEquiv (w.bong.ambientVector i) =
      (w.map f).bong.ambientVector i := by
  change (w.mapIsometry f).toLinearEquiv (w.bong.ambientVector i) =
    (w.bong.map (w.mapIsometry f)).ambientVector i
  rw [BONG.ambientVector_map]

@[simp]
theorem coe_mapIsometry_apply
    (w : SegmentWitness b start length bound) (f : q.Isometry r)
    (x : w.carrier) :
    ((w.mapIsometry f).toLinearEquiv x : W) = f.toLinearEquiv (x : V) :=
  rfl

@[simp]
theorem coe_ambientVector_map
    (w : SegmentWitness b start length bound) (f : q.Isometry r)
    (i : Fin length) :
    ((w.map f).bong.ambientVector i : W) =
      f.toLinearEquiv (w.bong.ambientVector i : V) := by
  change
    (((w.bong.map (w.mapIsometry f)).ambientVector i :
      w.mapCarrier f) : W) = _
  rw [BONG.ambientVector_map]
  rfl

end MapTransport

end BONG.SegmentWitness

namespace BONG.SegmentWitness

universe u v

section LiftTransport

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

section LiftTail

variable {m : Nat} {x : V}
  {generator : Lattice.IsNormGenerator q L x}
  {anisotropic : q.IsAnisotropic x}
  {tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic)
    (L.projectedLattice q x anisotropic) m}
  {tailStart tailLength : Nat}
  {tailBound : tailStart + tailLength ≤ m}

/-- The carrier of a tail segment, embedded back into the parent ambient
space. -/
def liftTailCarrier
    (w : SegmentWitness tail tailStart tailLength tailBound) :
    Submodule K V :=
  w.carrier.map (q.vectorOrthogonal x).subtype

/-- The embedded carrier of a tail segment remains nondegenerate. -/
theorem liftTailCarrier_nondegenerate
    (w : SegmentWitness tail tailStart tailLength tailBound) :
    (q.bilin.restrict w.liftTailCarrier).Nondegenerate := by
  let e := (q.vectorOrthogonal x).equivSubtypeMap w.carrier
  constructor
  · intro y hy
    apply e.symm.injective
    apply w.nondegenerate.1
    intro z
    have hycoe : ((e.symm y : w.carrier) : V) = (y : V) := by
      exact congrArg Subtype.val (e.apply_symm_apply y)
    have hzcoe : ((e z : w.liftTailCarrier) : V) = (z : V) := rfl
    calc
      q.bilin ((e.symm y : w.carrier) : V) (z : V) =
          q.bilin (y : V) ((e z : w.liftTailCarrier) : V) := by
        rw [hycoe, hzcoe]
      _ = 0 := hy (e z)
  · intro y hy
    apply e.symm.injective
    apply w.nondegenerate.2
    intro z
    have hycoe : ((e.symm y : w.carrier) : V) = (y : V) := by
      exact congrArg Subtype.val (e.apply_symm_apply y)
    have hzcoe : ((e z : w.liftTailCarrier) : V) = (z : V) := rfl
    calc
      q.bilin (z : V) ((e.symm y : w.carrier) : V) =
          q.bilin ((e z : w.liftTailCarrier) : V) (y : V) := by
        rw [hycoe, hzcoe]
      _ = 0 := hy (e z)

/-- The restricted quadratic isometry embedding a tail segment into the
parent space. -/
noncomputable def liftTailIsometry
    (w : SegmentWitness tail tailStart tailLength tailBound) :
    ((q.orthogonalSpace x anisotropic).restrict
      w.carrier w.nondegenerate).Isometry
      (q.restrict w.liftTailCarrier w.liftTailCarrier_nondegenerate) where
  toLinearEquiv := (q.vectorOrthogonal x).equivSubtypeMap w.carrier
  map_bilin _ _ := rfl

/-- Embed a consecutive segment of the recursive tail as the corresponding
segment of the parent BONG. -/
noncomputable def liftTail
    (w : SegmentWitness tail tailStart tailLength tailBound) :
    SegmentWitness (BONG.cons x generator anisotropic tail)
      (tailStart + 1) tailLength (by omega) where
  carrier := w.liftTailCarrier
  nondegenerate := w.liftTailCarrier_nondegenerate
  lattice := Lattice.map w.liftTailIsometry.toLinearEquiv w.lattice
  bong := w.bong.map w.liftTailIsometry
  ambientVector_eq := by
    intro i
    rw [BONG.ambientVector_map]
    change (w.bong.ambientVector i : V) =
      (BONG.cons x generator anisotropic tail).ambientVector
        ⟨(tailStart + 1) + i.1, by omega⟩
    calc
      (w.bong.ambientVector i : V) =
          (tail.ambientVector (w.sourceIndex i) : V) :=
        congrArg Subtype.val (w.ambientVector_eq i)
      _ = (BONG.cons x generator anisotropic tail).ambientVector
          (w.sourceIndex i).succ := by
        rw [BONG.ambientVector_cons_succ]
      _ = (BONG.cons x generator anisotropic tail).ambientVector
          ⟨(tailStart + 1) + i.1, by omega⟩ := by
        congr 1
        apply Fin.ext
        simp [BONG.SegmentWitness.sourceIndex]
        omega

/-- The restricted embedding used by `liftTail`, bundled as an isometry of
the corresponding segment lattices. -/
noncomputable def liftTailLatticeIsometry
    (w : SegmentWitness tail tailStart tailLength tailBound) :
    Lattice.Isometry
      ((q.orthogonalSpace x anisotropic).restrict
        w.carrier w.nondegenerate)
      (q.restrict
        (liftTail (generator := generator) w).carrier
        (liftTail (generator := generator) w).nondegenerate)
      w.lattice (liftTail (generator := generator) w).lattice where
  toLinearEquiv := w.liftTailIsometry.toLinearEquiv
  map_bilin := w.liftTailIsometry.map_bilin
  map_mem z := (Lattice.map_mem_map_iff
    w.liftTailIsometry.toLinearEquiv w.lattice z).symm

@[simp]
theorem liftTailLatticeIsometry_apply_ambientVector
    (w : SegmentWitness tail tailStart tailLength tailBound)
    (i : Fin tailLength) :
    (w.liftTailLatticeIsometry
        (generator := generator)).toLinearEquiv (w.bong.ambientVector i) =
      (w.liftTail (generator := generator)).bong.ambientVector i := by
  change w.liftTailIsometry.toLinearEquiv (w.bong.ambientVector i) =
    (w.bong.map w.liftTailIsometry).ambientVector i
  rw [BONG.ambientVector_map]

@[simp]
theorem coe_liftTailIsometry_apply
    (w : SegmentWitness tail tailStart tailLength tailBound)
    (z : w.carrier) :
    ((w.liftTailIsometry).toLinearEquiv z : V) = (z : V) :=
  rfl

end LiftTail

end LiftTransport

end BONG.SegmentWitness

namespace BONG.SegmentWitness

universe u z

section Whole

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

variable {U : Type z} [AddCommGroup U] [Module K U]
  {s : QuadraticSpace K U} {N : Lattice K U} {m : Nat}

private theorem wholeCarrier_nondegenerate :
    (s.bilin.restrict (⊤ : Submodule K U)).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    exact s.nondegenerate.1 (x : U) (fun y => hx ⟨y, trivial⟩)
  · intro y hy
    apply Subtype.ext
    exact s.nondegenerate.2 (y : U) (fun x => hy ⟨x, trivial⟩)

/-- Regard an entire BONG as its length-`m` consecutive segment. -/
noncomputable def whole (c : BONG U s N m) :
    SegmentWitness c 0 m (by omega) := by
  let nondegenerate := wholeCarrier_nondegenerate (s := s)
  let f : s.Isometry (s.restrict (⊤ : Submodule K U) nondegenerate) :=
    { toLinearEquiv := Submodule.topEquiv.symm
      map_bilin _ _ := rfl }
  exact
    { carrier := ⊤
      nondegenerate := nondegenerate
      lattice := Lattice.map f.toLinearEquiv N
      bong := c.map f
      ambientVector_eq := by
        intro i
        rw [BONG.ambientVector_map]
        change c.ambientVector i = c.ambientVector ⟨0 + i.1, by omega⟩
        congr 1
        apply Fin.ext
        simp }

/-- The canonical isometry from a BONG lattice to its whole-segment model. -/
noncomputable def wholeLatticeIsometry (c : BONG U s N m) :
    Lattice.Isometry s
      (s.restrict (whole c).carrier (whole c).nondegenerate)
      N (whole c).lattice := by
  let f : s.Isometry
      (s.restrict (⊤ : Submodule K U)
        (wholeCarrier_nondegenerate (s := s))) :=
    { toLinearEquiv := Submodule.topEquiv.symm
      map_bilin _ _ := rfl }
  change Lattice.Isometry s
    (s.restrict (⊤ : Submodule K U)
      (wholeCarrier_nondegenerate (s := s)))
    N (Lattice.map f.toLinearEquiv N)
  exact
    { toLinearEquiv := f.toLinearEquiv
      map_bilin := f.map_bilin
      map_mem z := (Lattice.map_mem_map_iff f.toLinearEquiv N z).symm }

/-- Whole-segment realization with an explicitly rewritten length. -/
noncomputable def wholeCast {m' : Nat} (c : BONG U s N m)
    (h : m = m') : SegmentWitness c 0 m' (by omega) := by
  subst m'
  exact whole c

/-- The lattice isometry accompanying `wholeCast`. -/
noncomputable def wholeCastLatticeIsometry {m' : Nat}
    (c : BONG U s N m) (h : m = m') :
    Lattice.Isometry s
      (s.restrict (wholeCast c h).carrier (wholeCast c h).nondegenerate)
      N (wholeCast c h).lattice := by
  subst m'
  exact wholeLatticeIsometry c

end Whole

end BONG.SegmentWitness

namespace BONG.SegmentWitness

universe u v

section Rebase

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V}
  {n start length : Nat} {bound : start + length ≤ n}
  {b : BONG V q L n}

/-- Reinterpret a segment witness relative to another parent BONG once the
literal ambient vectors on that interval have been identified.  The segment
carrier, restricted lattice, and internal BONG are unchanged. -/
def rebase (w : SegmentWitness b start length bound)
    (c : BONG V q N n)
    (vectors : ∀ i : Fin length,
      (w.bong.ambientVector i : V) = c.ambientVector (w.sourceIndex i)) :
    SegmentWitness c start length bound where
  carrier := w.carrier
  nondegenerate := w.nondegenerate
  lattice := w.lattice
  bong := w.bong
  ambientVector_eq := vectors

/-- Rebasing does not alter the segment lattice. -/
def rebaseLatticeIsometry (w : SegmentWitness b start length bound)
    (c : BONG V q N n)
    (vectors : ∀ i : Fin length,
      (w.bong.ambientVector i : V) = c.ambientVector (w.sourceIndex i)) :
    Lattice.Isometry
      (q.restrict w.carrier w.nondegenerate)
      (q.restrict (w.rebase c vectors).carrier
        (w.rebase c vectors).nondegenerate)
      w.lattice (w.rebase c vectors).lattice :=
  Lattice.Isometry.refl (q.restrict w.carrier w.nondegenerate) w.lattice

end Rebase

end BONG.SegmentWitness

namespace BONG.SegmentWitness

universe u v w

section UnmapTransport

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {n start length : Nat}
  {bound : start + length ≤ n}
  {b : BONG V q L n}

/-- Ambient-vector coherence for transporting a segment of `b.map f` back
to the original BONG. -/
theorem ambientVectors_unmap
    (f : q.Isometry r)
    (w : SegmentWitness (b.map f) start length bound)
    (i : Fin length) :
    (((w.map f.symm).bong.ambientVector i :
      (w.map f.symm).carrier) : V) =
      b.ambientVector ((w.map f.symm).sourceIndex i) := by
  rw [coe_ambientVector_map]
  have hw := w.ambientVector_eq i
  change f.symm.toLinearEquiv (w.bong.ambientVector i : W) = _
  rw [hw]
  change f.symm.toLinearEquiv
      ((b.map f).ambientVector (w.sourceIndex i)) = _
  rw [BONG.ambientVector_map]
  exact f.toLinearEquiv.symm_apply_apply _

/-- Transport a segment of an isometric image back to the original BONG.
The intermediate double-mapped BONG is rebased using its literal vector
identity with the source. -/
noncomputable def unmap
    (f : q.Isometry r)
    (w : SegmentWitness (b.map f) start length bound) :
    SegmentWitness b start length bound :=
  (w.map f.symm).rebase b (w.ambientVectors_unmap f)

/-- The lattice isometry accompanying `unmap`. -/
noncomputable def unmapLatticeIsometry
    (f : q.Isometry r)
    (w : SegmentWitness (b.map f) start length bound) :
    Lattice.Isometry
      (r.restrict w.carrier w.nondegenerate)
      (q.restrict (w.unmap f).carrier (w.unmap f).nondegenerate)
      w.lattice (w.unmap f).lattice :=
  (w.mapLatticeIsometry f.symm).trans
    ((w.map f.symm).rebaseLatticeIsometry b
      (w.ambientVectors_unmap f))

@[simp]
theorem unmapLatticeIsometry_apply_ambientVector
    (f : q.Isometry r)
    (w : SegmentWitness (b.map f) start length bound)
    (i : Fin length) :
    (w.unmapLatticeIsometry f).toLinearEquiv (w.bong.ambientVector i) =
      (w.unmap f).bong.ambientVector i := by
  change
    ((w.map f.symm).rebaseLatticeIsometry b
        (w.ambientVectors_unmap f)).toLinearEquiv
      ((w.mapLatticeIsometry f.symm).toLinearEquiv
        (w.bong.ambientVector i)) =
      (w.map f.symm).bong.ambientVector i
  rw [mapLatticeIsometry_apply_ambientVector]
  rfl

end UnmapTransport

end BONG.SegmentWitness

end Bong
