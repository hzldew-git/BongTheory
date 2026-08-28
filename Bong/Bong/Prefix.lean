/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.SegmentConstruction
import Bong.Bong.Suffix
import Bong.Lattice.Restriction

/-!
# Prefixes of a recursive BONG

This file constructs the integral coordinate lattice carried by an initial
block of BONG vectors.  Together with suffix transport, this supplies the
consecutive-block statement in Beli (2003), Lemma 2.7 and Corollary 2.8.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A prefix segment whose integral lattice maps back into the parent lattice. -/
structure PrefixWitness (b : BONG V q L n) (length : Nat)
    (bound : length ≤ n)
    extends SegmentWitness b 0 length (by omega) where
  /-- Every integral vector of the prefix lattice belongs to the parent. -/
  contained : ∀ y : carrier, y ∈ lattice → (y : V) ∈ L
  /-- Every parent-lattice vector in the prefix carrier belongs to the prefix lattice. -/
  contains_parent : ∀ y : carrier, (y : V) ∈ L → y ∈ lattice

private theorem prefixCarrier_eq_segmentCarrier
    {m length : Nat} {x : V}
    {generator : Lattice.IsNormGenerator q L x}
    {anisotropic : q.IsAnisotropic x}
    (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) m)
    (bound : length ≤ m) (w : PrefixWitness tail length bound) :
    K ∙ x ⊔ w.carrier.map (q.vectorOrthogonal x).subtype =
      (BONG.cons x generator anisotropic tail).segmentCarrier
        0 (length + 1) (by omega) := by
  apply le_antisymm
  · apply sup_le
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      apply Submodule.subset_span
      refine ⟨0, ?_⟩
      simp [segmentVector, segmentIndex]
    · rintro y ⟨z, hz, rfl⟩
      let z' : w.carrier := ⟨z, hz⟩
      have hzSpan : z' ∈
          Submodule.span K (Set.range w.bong.ambientVector) := by
        rw [w.bong.span_ambientVector_eq_top]
        trivial
      have hmap : (z' : q.vectorOrthogonal x) ∈
          Submodule.span K
            ((Submodule.subtype w.carrier) ''
              Set.range w.bong.ambientVector) :=
        Submodule.apply_mem_span_image_of_mem_span
          (Submodule.subtype w.carrier) hzSpan
      have hmapV : (z : V) ∈ Submodule.span K
          ((q.vectorOrthogonal x).subtype ''
            ((Submodule.subtype w.carrier) ''
              Set.range w.bong.ambientVector)) :=
        Submodule.apply_mem_span_image_of_mem_span
          (q.vectorOrthogonal x).subtype hmap
      rw [segmentCarrier]
      apply (Submodule.span_mono ?_) hmapV
      rintro _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
      refine ⟨i.succ, ?_⟩
      symm
      calc
        (w.bong.ambientVector i : V) =
            (tail.ambientVector (w.sourceIndex i) : V) :=
          congrArg Subtype.val (w.ambientVector_eq i)
        _ = (BONG.cons x generator anisotropic tail).ambientVector
            (w.sourceIndex i).succ := by
          rw [ambientVector_cons_succ]
        _ = (BONG.cons x generator anisotropic tail).segmentVector
            0 (length + 1) (by omega) i.succ := by
          congr 1
  · rw [segmentCarrier, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero =>
        simpa [segmentVector, segmentIndex] using
          (Submodule.mem_sup_left
            (Submodule.mem_span_singleton_self x) :
              x ∈ K ∙ x ⊔
                w.carrier.map (q.vectorOrthogonal x).subtype)
    | succ i =>
        have hmem : (tail.ambientVector (w.sourceIndex i) : V) ∈
          K ∙ x ⊔ w.carrier.map (q.vectorOrthogonal x).subtype
            := by
          apply Submodule.mem_sup_right
          refine ⟨tail.ambientVector (w.sourceIndex i), ?_, rfl⟩
          have h := w.ambientVector_eq i
          change (w.bong.ambientVector i : q.vectorOrthogonal x) =
            tail.ambientVector (w.sourceIndex i) at h
          rw [← h]
          exact (w.bong.ambientVector i).property
        change (BONG.cons x generator anisotropic tail).ambientVector
          (segmentIndex 0 (length + 1) (by omega) i.succ) ∈
            K ∙ x ⊔ w.carrier.map (q.vectorOrthogonal x).subtype
        have hind : segmentIndex 0 (length + 1) (by omega) i.succ =
            (w.sourceIndex i).succ := by
          apply Fin.ext
          simp [segmentIndex, SegmentWitness.sourceIndex]
        rw [hind, ambientVector_cons_succ]
        exact hmem

private noncomputable def zeroPrefixWitness (b : BONG V q L n) :
    PrefixWitness b 0 (Nat.zero_le n) := by
  let carrier := b.segmentCarrier 0 0 (by omega)
  let nondegenerate := b.segmentCarrier_nondegenerate 0 0 (by omega)
  have carrier_subsingleton : Subsingleton carrier := by
    constructor
    intro x y
    apply Subtype.ext
    have hcarrier : carrier = ⊥ := by
      simp [carrier, segmentCarrier, segmentVector]
    have hx : (x : V) = 0 := by
      simpa [hcarrier] using x.property
    have hy : (y : V) = 0 := by
      simpa [hcarrier] using y.property
    exact hx.trans hy.symm
  have hspan : Submodule.span K
      ({x : carrier | (x : V) ∈ L} : Set carrier) = ⊤ := by
    apply top_unique
    intro x _
    have hx : x = 0 := carrier_subsingleton.elim x 0
    subst x
    exact Submodule.zero_mem _
  let lattice := Lattice.comapSubtype L carrier hspan
  exact
    { carrier := carrier
      nondegenerate := nondegenerate
      lattice := lattice
      bong := BONG.nil (q.restrict carrier nondegenerate) lattice
        carrier_subsingleton
      ambientVector_eq := fun i => Fin.elim0 i
      contained := by
        intro y hy
        exact hy
      contains_parent := by
        intro y hy
        exact hy }

namespace PrefixWitness

section General

variable {b : BONG V q L n} {length : Nat} {bound : length ≤ n}

/-- Membership in a prefix lattice is exactly parent-lattice membership. -/
theorem mem_lattice_iff_parent (w : PrefixWitness b length bound)
    (y : w.carrier) : y ∈ w.lattice ↔ (y : V) ∈ L :=
  ⟨w.contained y, w.contains_parent y⟩

/-- The parent lattice integrally spans the prefix carrier. -/
theorem parentIntersection_spans (w : PrefixWitness b length bound) :
    Submodule.span K
      ({y : w.carrier | (y : V) ∈ L} : Set w.carrier) = ⊤ := by
  apply top_unique
  have hle : Submodule.span K
      (w.lattice.toSubmodule : Set w.carrier) ≤
        Submodule.span K
          ({y : w.carrier | (y : V) ∈ L} : Set w.carrier) := by
    apply Submodule.span_mono
    intro y hy
    exact w.contained y hy
  rw [w.lattice.span_eq_top] at hle
  exact hle

/-- A prefix lattice is the exact restriction of its parent lattice. -/
theorem lattice_eq_comapSubtype (w : PrefixWitness b length bound) :
    w.lattice = Lattice.comapSubtype L w.carrier
      w.parentIntersection_spans := by
  apply Lattice.ext
  ext y
  change y ∈ w.lattice ↔ (y : V) ∈ L
  exact w.mem_lattice_iff_parent y

end General

variable {m length : Nat} {x : V}
  {anisotropic : q.IsAnisotropic x}
  {tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic)
    (L.projectedLattice q x anisotropic) m}
  {bound : length ≤ m}

/-- The canonical ambient carrier after adjoining the preceding BONG vector. -/
noncomputable def stepCarrier (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    Submodule K V :=
  (BONG.cons x generator anisotropic tail).segmentCarrier
    0 (length + 1) (by omega)

/-- Nondegeneracy of the carrier obtained in one prefix step. -/
theorem stepCarrier_nondegenerate (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    (q.bilin.restrict (w.stepCarrier generator)).Nondegenerate :=
  (BONG.cons x generator anisotropic tail).segmentCarrier_nondegenerate
    0 (length + 1) (by omega)

/-- The preceding vector, regarded as a vector of the enlarged carrier. -/
noncomputable def stepHead (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    w.stepCarrier generator :=
  ⟨x, by
    change x ∈ (BONG.cons x generator anisotropic tail).segmentCarrier
      0 (length + 1) (by omega)
    rw [← prefixCarrier_eq_segmentCarrier tail bound w]
    exact Submodule.mem_sup_left
      (Submodule.mem_span_singleton_self x)⟩

/-- The enlarged head remains anisotropic after restriction. -/
theorem stepHead_isAnisotropic (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    (q.restrict (w.stepCarrier generator)
      (w.stepCarrier_nondegenerate generator)).IsAnisotropic
      (w.stepHead generator) :=
  anisotropic

/-- Inclusion of the old prefix carrier into the new head complement. -/
noncomputable def stepTailLinearMap (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    w.carrier →ₗ[K]
      (q.restrict (w.stepCarrier generator)
        (w.stepCarrier_nondegenerate generator)).vectorOrthogonal
        (w.stepHead generator) where
  toFun z :=
    ⟨⟨(z : V), by
      change (z : V) ∈
        (BONG.cons x generator anisotropic tail).segmentCarrier
          0 (length + 1) (by omega)
      rw [← prefixCarrier_eq_segmentCarrier tail bound w]
      apply Submodule.mem_sup_right
      exact ⟨(z : q.vectorOrthogonal x), z.property, rfl⟩⟩, by
        rw [QuadraticSpace.mem_vectorOrthogonal_iff]
        change q.bilin x (z : V) = 0
        exact (q.mem_vectorOrthogonal_iff x (z : V)).1
          (z : q.vectorOrthogonal x).property⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The carrier inclusion in one prefix step is injective. -/
theorem stepTailLinearMap_injective (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    Function.Injective (w.stepTailLinearMap generator) := by
  intro y z hyz
  let T := (q.restrict (w.stepCarrier generator)
    (w.stepCarrier_nondegenerate generator)).vectorOrthogonal
      (w.stepHead generator)
  have hcarrier := congrArg
    (fun a : T => (a : w.stepCarrier generator)) hyz
  have hV := congrArg
    (fun a : w.stepCarrier generator => (a : V)) hcarrier
  apply Subtype.ext
  apply Subtype.ext
  exact hV

/-- The old carrier is naturally equivalent to the new head complement. -/
noncomputable def stepTailLinearEquiv (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    w.carrier ≃ₗ[K]
      (q.restrict (w.stepCarrier generator)
        (w.stepCarrier_nondegenerate generator)).vectorOrthogonal
        (w.stepHead generator) := by
  letI := w.bong.basis.finiteDimensional_of_finite
  letI : FiniteDimensional K (w.stepCarrier generator) :=
    ((BONG.cons x generator anisotropic tail).segmentBasis
      0 (length + 1) (by omega)).finiteDimensional_of_finite
  letI : FiniteDimensional K
      ((q.restrict (w.stepCarrier generator)
        (w.stepCarrier_nondegenerate generator)).vectorOrthogonal
          (w.stepHead generator)) :=
    FiniteDimensional.of_injective
      (Submodule.subtype _) Subtype.val_injective
  apply LinearEquiv.ofInjectiveOfFinrankEq (w.stepTailLinearMap generator)
    (w.stepTailLinearMap_injective generator)
  have hsource : Module.finrank K w.carrier = length :=
    w.bong.length_eq_finrank.symm
  have htarget :=
    (q.restrict (w.stepCarrier generator)
      (w.stepCarrier_nondegenerate generator)).finrank_vectorOrthogonal
      (w.stepHead_isAnisotropic generator)
  have hcarrier : Module.finrank K (w.stepCarrier generator) =
      length + 1 :=
    (BONG.cons x generator anisotropic tail).finrank_segmentCarrier
      0 (length + 1) (by omega)
  omega

@[simp]
theorem stepTailLinearEquiv_coe (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) (z : w.carrier) :
    ((w.stepTailLinearEquiv generator z : w.stepCarrier generator) : V) =
      (z : V) := by
  have hmap : (w.stepTailLinearEquiv generator).toLinearMap =
      w.stepTailLinearMap generator := by
    simp [stepTailLinearEquiv]
  have happ := DFunLike.congr_fun hmap z
  let T := (q.restrict (w.stepCarrier generator)
    (w.stepCarrier_nondegenerate generator)).vectorOrthogonal
      (w.stepHead generator)
  have hcarrier := congrArg
    (fun a : T => (a : w.stepCarrier generator)) happ
  exact congrArg
    (fun a : w.stepCarrier generator => (a : V)) hcarrier

/-- The parent lattice spans the enlarged prefix carrier. -/
theorem stepCarrier_spans_comap (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    Submodule.span K
      ({y : w.stepCarrier generator | (y : V) ∈ L} :
        Set (w.stepCarrier generator)) = ⊤ := by
  let P := w.stepCarrier generator
  let A : Submodule K P := Submodule.span K
    ({y : P | (y : V) ∈ L} : Set P)
  let qP := q.restrict P (w.stepCarrier_nondegenerate generator)
  let head : P := w.stepHead generator
  let lift : w.carrier →ₗ[K] P :=
    (Submodule.subtype (qP.vectorOrthogonal head)).comp
      (w.stepTailLinearMap generator)
  have hxA : head ∈ A := by
    apply Submodule.subset_span
    change (head : V) ∈ L
    exact generator.mem
  have htailA : ∀ z : w.carrier, lift z ∈ A := by
    intro z
    have hzSpan : z ∈ Submodule.span K
        (w.lattice.toSubmodule : Set w.carrier) := by
      rw [w.lattice.span_eq_top]
      trivial
    have hle : Submodule.span K
        (w.lattice.toSubmodule : Set w.carrier) ≤ A.comap lift := by
      rw [Submodule.span_le]
      intro t ht
      change lift t ∈ A
      have htProjected : (t : q.vectorOrthogonal x) ∈
          L.projectedLattice q x anisotropic :=
        w.contained t ht
      rcases (Lattice.mem_projectedLattice_iff q L x anisotropic
        (t : q.vectorOrthogonal x)).1 htProjected with
        ⟨y, hyL, hprojection⟩
      have hyP : y ∈ P := by
        change y ∈ (BONG.cons x generator anisotropic tail).segmentCarrier
          0 (length + 1) (by omega)
        rw [← prefixCarrier_eq_segmentCarrier tail bound w]
        rw [← q.lineProjection_add_orthogonalProjection x y]
        apply Submodule.add_mem
        · apply Submodule.mem_sup_left
          rw [q.lineProjection_apply]
          exact Submodule.smul_mem _ _
            (Submodule.mem_span_singleton_self x)
        · apply Submodule.mem_sup_right
          refine ⟨(t : q.vectorOrthogonal x), t.property, ?_⟩
          exact (congrArg Subtype.val hprojection).symm
      let yp : P := ⟨y, hyP⟩
      have hypA : yp ∈ A := Submodule.subset_span hyL
      have heq : lift t = yp -
          (q.bilin x y / q.quadratic x) • head := by
        apply Subtype.ext
        change (t : V) = y -
          (q.bilin x y / q.quadratic x) • x
        rw [← congrArg Subtype.val hprojection]
        exact q.orthogonalProjection_apply x y
      rw [heq]
      exact Submodule.sub_mem _ hypA
        (Submodule.smul_mem _ _ hxA)
    exact hle hzSpan
  apply top_unique
  intro y _
  change y ∈ A
  have hySup : (y : V) ∈
      K ∙ x ⊔ w.carrier.map (q.vectorOrthogonal x).subtype := by
    rw [prefixCarrier_eq_segmentCarrier tail bound w]
    exact y.property
  rcases Submodule.mem_sup.mp hySup with ⟨u, hu, v, hv, huv⟩
  rcases Submodule.mem_span_singleton.mp hu with ⟨a, rfl⟩
  rcases hv with ⟨z, hz, rfl⟩
  let z' : w.carrier := ⟨z, hz⟩
  have hyEq : y = a • head + lift z' := by
    apply Subtype.ext
    exact huv.symm
  rw [hyEq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ a hxA) (htailA z')

/-- The parent lattice restricted to the enlarged prefix carrier. -/
noncomputable def stepAmbientLattice (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    Lattice K (w.stepCarrier generator) :=
  Lattice.comapSubtype L (w.stepCarrier generator)
    (w.stepCarrier_spans_comap generator)

/-- The enlarged head is a norm generator of the restricted parent lattice. -/
theorem stepHead_isNormGenerator (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    Lattice.IsNormGenerator
      (q.restrict (w.stepCarrier generator)
        (w.stepCarrier_nondegenerate generator))
      (w.stepAmbientLattice generator) (w.stepHead generator) := by
  exact Lattice.isNormGenerator_comapSubtype q L
    (w.stepCarrier generator) (w.stepCarrier_nondegenerate generator)
    (w.stepCarrier_spans_comap generator) (w.stepHead generator) generator

/-- A parent vector whose projection lies in the old carrier lies in the new carrier. -/
theorem mem_stepCarrier_of_projection_eq
    (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) (t : w.carrier)
    (y : V) (hprojection :
      q.projectionToOrthogonal x anisotropic y =
        (t : q.vectorOrthogonal x)) :
    y ∈ w.stepCarrier generator := by
  change y ∈ (BONG.cons x generator anisotropic tail).segmentCarrier
    0 (length + 1) (by omega)
  rw [← prefixCarrier_eq_segmentCarrier tail bound w]
  rw [← q.lineProjection_add_orthogonalProjection x y]
  apply Submodule.add_mem
  · apply Submodule.mem_sup_left
    rw [q.lineProjection_apply]
    exact Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self x)
  · apply Submodule.mem_sup_right
    refine ⟨(t : q.vectorOrthogonal x), t.property, ?_⟩
    exact (congrArg Subtype.val hprojection).symm

/-- The old restricted quadratic space is isometric to the new head complement. -/
noncomputable def stepTailIsometry (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    QuadraticSpace.Isometry
      ((q.orthogonalSpace x anisotropic).restrict
        w.carrier w.nondegenerate)
      ((q.restrict (w.stepCarrier generator)
        (w.stepCarrier_nondegenerate generator)).orthogonalSpace
        (w.stepHead generator) (w.stepHead_isAnisotropic generator)) where
  toLinearEquiv := w.stepTailLinearEquiv generator
  map_bilin y z := by
    change q.bilin
      ((w.stepTailLinearEquiv generator y :
        w.stepCarrier generator) : V)
      ((w.stepTailLinearEquiv generator z :
        w.stepCarrier generator) : V) =
        q.bilin (y : V) (z : V)
    rw [w.stepTailLinearEquiv_coe, w.stepTailLinearEquiv_coe]

/-- The mapped old prefix lattice lies in the projected enlarged lattice. -/
theorem stepMappedLattice_le_projectedLattice
    (w : PrefixWitness tail length bound)
    (generator : Lattice.IsNormGenerator q L x) :
    Lattice.map (w.stepTailIsometry generator).toLinearEquiv w.lattice ≤
      Lattice.projectedLattice
        (q.restrict (w.stepCarrier generator)
          (w.stepCarrier_nondegenerate generator))
        (w.stepAmbientLattice generator) (w.stepHead generator)
        (w.stepHead_isAnisotropic generator) := by
  intro y hy
  change y ∈ Lattice.map
    (w.stepTailIsometry generator).toLinearEquiv w.lattice at hy
  rw [Lattice.mem_map_iff] at hy
  let z : w.carrier := (w.stepTailIsometry generator).toLinearEquiv.symm y
  have hz : z ∈ w.lattice := hy
  have hzProjected : (z : q.vectorOrthogonal x) ∈
      L.projectedLattice q x anisotropic :=
    w.contained z hz
  rcases (Lattice.mem_projectedLattice_iff q L x anisotropic
    (z : q.vectorOrthogonal x)).1 hzProjected with
    ⟨a, haL, hprojection⟩
  have haCarrier : a ∈ w.stepCarrier generator :=
    w.mem_stepCarrier_of_projection_eq generator z a hprojection
  let aP : w.stepCarrier generator := ⟨a, haCarrier⟩
  apply (Lattice.mem_projectedLattice_iff
    (q.restrict (w.stepCarrier generator)
      (w.stepCarrier_nondegenerate generator))
    (w.stepAmbientLattice generator) (w.stepHead generator)
    (w.stepHead_isAnisotropic generator) y).2
  refine ⟨aP, haL, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change q.orthogonalProjection x a =
    ((y : w.stepCarrier generator) : V)
  calc
    q.orthogonalProjection x a =
        (q.projectionToOrthogonal x anisotropic a : V) := rfl
    _ = ((z : q.vectorOrthogonal x) : V) :=
      congrArg Subtype.val hprojection
    _ = ((w.stepTailLinearEquiv generator z :
          w.stepCarrier generator) : V) :=
      (w.stepTailLinearEquiv_coe generator z).symm
    _ = ((y : w.stepCarrier generator) : V) := by
      congr 2
      exact (w.stepTailIsometry generator).toLinearEquiv.apply_symm_apply y

end PrefixWitness

private noncomputable def succPrefixWitness
    {m length : Nat} {x : V}
    {generator : Lattice.IsNormGenerator q L x}
    {anisotropic : q.IsAnisotropic x}
    (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) m)
    (bound : length ≤ m) (w : PrefixWitness tail length bound) :
    PrefixWitness (BONG.cons x generator anisotropic tail)
      (length + 1) (by omega) := by
  let P := w.stepCarrier generator
  let nondegenerate := w.stepCarrier_nondegenerate generator
  let qP := q.restrict P nondegenerate
  let head : P := w.stepHead generator
  let headAnisotropic : qP.IsAnisotropic head :=
    w.stepHead_isAnisotropic generator
  let ambientLattice : Lattice K P := w.stepAmbientLattice generator
  let headGenerator : Lattice.IsNormGenerator qP ambientLattice head :=
    w.stepHead_isNormGenerator generator
  let e := w.stepTailIsometry generator
  let N : Lattice K (qP.vectorOrthogonal head) :=
    Lattice.map e.toLinearEquiv w.lattice
  let hN : N ≤ ambientLattice.projectedLattice qP head headAnisotropic :=
    w.stepMappedLattice_le_projectedLattice generator
  let mappedTail : BONG (qP.vectorOrthogonal head)
      (qP.orthogonalSpace head headAnisotropic) N length :=
    w.bong.map e
  let lattice := Lattice.projectionPreimage qP ambientLattice head
    headAnisotropic headGenerator.mem N hN
  let bong : BONG P qP lattice (length + 1) :=
    prependProjectionPreimage headGenerator N hN mappedTail
  exact
    { carrier := P
      nondegenerate := nondegenerate
      lattice := lattice
      bong := bong
      ambientVector_eq := by
        intro i
        cases i using Fin.cases with
        | zero =>
            change (bong.ambientVector 0 : V) =
              (BONG.cons x generator anisotropic tail).ambientVector 0
            rw [show bong = prependProjectionPreimage
              headGenerator N hN mappedTail by rfl]
            rw [ambientVector_prependProjectionPreimage_zero]
            rw [ambientVector_cons_zero]
            change (head : V) = x
            rfl
        | succ i =>
            change (bong.ambientVector i.succ : V) =
              (BONG.cons x generator anisotropic tail).ambientVector
                ⟨0 + i.succ.1, by omega⟩
            rw [show bong = prependProjectionPreimage
              headGenerator N hN mappedTail by rfl]
            rw [ambientVector_prependProjectionPreimage_succ]
            change (((mappedTail.ambientVector i :
              qP.vectorOrthogonal head) : P) : V) = _
            rw [show mappedTail = w.bong.map e by rfl]
            rw [ambientVector_map]
            change ((w.stepTailLinearEquiv generator
              (w.bong.ambientVector i) : P) : V) = _
            rw [w.stepTailLinearEquiv_coe]
            calc
              (w.bong.ambientVector i : V) =
                  (tail.ambientVector (w.sourceIndex i) : V) :=
                congrArg Subtype.val (w.ambientVector_eq i)
              _ = (BONG.cons x generator anisotropic tail).ambientVector
                  (w.sourceIndex i).succ := by
                rw [ambientVector_cons_succ]
              _ = (BONG.cons x generator anisotropic tail).ambientVector
                  ⟨0 + i.succ.1, by omega⟩ := by
                congr 1
      contained := by
        intro y hy
        have hyAmbient : y ∈ ambientLattice :=
          Lattice.projectionPreimage_le qP ambientLattice head
            headAnisotropic headGenerator.mem N hN hy
        exact hyAmbient
      contains_parent := by
        intro y hy
        change y ∈ lattice
        rw [show lattice = Lattice.projectionPreimage qP ambientLattice
          head headAnisotropic headGenerator.mem N hN by rfl]
        rw [Lattice.mem_projectionPreimage_iff]
        refine ⟨hy, ?_⟩
        change qP.projectionToOrthogonal head headAnisotropic y ∈ N
        rw [show N = Lattice.map e.toLinearEquiv w.lattice by rfl]
        rw [Lattice.mem_map_iff]
        let p := qP.projectionToOrthogonal head headAnisotropic y
        let z : w.carrier := e.toLinearEquiv.symm p
        change z ∈ w.lattice
        apply w.contains_parent
        have hzProjection : (z : q.vectorOrthogonal x) =
            q.projectionToOrthogonal x anisotropic (y : V) := by
          apply Subtype.ext
          calc
            ((z : q.vectorOrthogonal x) : V) =
                ((e.toLinearEquiv z : qP.vectorOrthogonal head) : P) := by
              exact (w.stepTailLinearEquiv_coe generator z).symm
            _ = (p : P) := by
              rw [show e.toLinearEquiv z = p by
                exact e.toLinearEquiv.apply_symm_apply p]
            _ = (q.projectionToOrthogonal x anisotropic (y : V) : V) := by
              rfl
        rw [hzProjection]
        exact Lattice.projection_mem_projectedLattice
          q L x anisotropic hy }

/-- The initial block of any recursive BONG has an exact restricted realization. -/
noncomputable def prefixWitness (b : BONG V q L n)
    (length : Nat) (bound : length ≤ n) :
    PrefixWitness b length bound := by
  induction length generalizing V n with
  | zero =>
      exact zeroPrefixWitness b
  | succ length ih =>
      cases b with
      | nil _ _ _ => omega
      | @cons V _ _ q L m x generator anisotropic tail =>
          have tailBound : length ≤ m := by omega
          let w := ih tail tailBound
          simpa [Nat.succ_eq_add_one] using
            succPrefixWitness tail tailBound w

@[simp]
theorem mem_prefixWitness_lattice_iff (b : BONG V q L n)
    (length : Nat) (bound : length ≤ n)
    (y : (b.prefixWitness length bound).carrier) :
    y ∈ (b.prefixWitness length bound).lattice ↔ (y : V) ∈ L :=
  (b.prefixWitness length bound).mem_lattice_iff_parent y

/-- The initial-block lattice is the parent lattice restricted to its carrier. -/
theorem prefixWitness_lattice_eq_comapSubtype (b : BONG V q L n)
    (length : Nat) (bound : length ≤ n) :
    (b.prefixWitness length bound).lattice =
      Lattice.comapSubtype L (b.prefixWitness length bound).carrier
        (b.prefixWitness length bound).parentIntersection_spans :=
  (b.prefixWitness length bound).lattice_eq_comapSubtype

/-- Every initial block has a segment realization, without structural laws. -/
theorem exists_prefixWitness (b : BONG V q L n)
    (length : Nat) (bound : length ≤ n) :
    Nonempty (SegmentWitness b 0 length (by omega)) :=
  ⟨(b.prefixWitness length bound).toSegmentWitness⟩

private theorem nestedCarrier_nondegenerate
    (S : Submodule K V) (hS : (q.bilin.restrict S).Nondegenerate)
    (T : Submodule K S)
    (hT : ((q.restrict S hS).bilin.restrict T).Nondegenerate) :
    (q.bilin.restrict (T.map S.subtype)).Nondegenerate := by
  let e := S.equivSubtypeMap T
  constructor
  · intro y hy
    apply e.symm.injective
    apply hT.1
    intro z
    change q.bilin ((e.symm y : T) : V) (z : V) = 0
    simpa [e] using hy (e z)
  · intro y hy
    apply e.symm.injective
    apply hT.2
    intro z
    change q.bilin (z : V) ((e.symm y : T) : V) = 0
    simpa [e] using hy (e z)

private noncomputable def composePrefixWitness
    {start outerLength length : Nat}
    {outerBound : start + outerLength ≤ n}
    (outer : SegmentWitness b start outerLength outerBound)
    (bound : length ≤ outerLength)
    (inner : PrefixWitness
      (K := K) (V := outer.carrier)
      (q := q.restrict outer.carrier outer.nondegenerate)
      (L := outer.lattice) (n := outerLength)
      outer.bong length bound) :
    SegmentWitness b start length (by omega) := by
  let carrier : Submodule K V :=
    inner.carrier.map outer.carrier.subtype
  let nondegenerate : (q.bilin.restrict carrier).Nondegenerate :=
    nestedCarrier_nondegenerate outer.carrier outer.nondegenerate
      inner.carrier inner.nondegenerate
  let f : QuadraticSpace.Isometry
      ((q.restrict outer.carrier outer.nondegenerate).restrict
        inner.carrier inner.nondegenerate)
      (q.restrict carrier nondegenerate) :=
    { toLinearEquiv := outer.carrier.equivSubtypeMap inner.carrier
      map_bilin _ _ := rfl }
  exact
    { carrier := carrier
      nondegenerate := nondegenerate
      lattice := Lattice.map f.toLinearEquiv inner.lattice
      bong := inner.bong.map f
      ambientVector_eq := by
        intro i
        rw [ambientVector_map]
        change (inner.bong.ambientVector i : V) =
          b.ambientVector ⟨start + i.1, by omega⟩
        calc
          (inner.bong.ambientVector i : V) =
              (outer.bong.ambientVector (inner.sourceIndex i) : V) :=
            congrArg Subtype.val (inner.ambientVector_eq i)
          _ = b.ambientVector (outer.sourceIndex (inner.sourceIndex i)) :=
            outer.ambientVector_eq (inner.sourceIndex i)
          _ = b.ambientVector ⟨start + i.1, by omega⟩ := by
            congr 1
            apply Fin.ext
            simp [SegmentWitness.sourceIndex] }

/-- Canonical realization of an arbitrary consecutive BONG block. -/
noncomputable def segmentWitness (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    SegmentWitness b start length bound := by
  have startBound : start ≤ n := by omega
  let outer := b.suffixWitness start startBound
  have lengthBound : length ≤ n - start := by omega
  let inner := outer.bong.prefixWitness length lengthBound
  exact composePrefixWitness outer lengthBound inner

/-- Every consecutive block has a BONG realization without extra laws. -/
theorem exists_segmentWitness_unconditional (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    Nonempty (SegmentWitness b start length bound) :=
  ⟨b.segmentWitness start length bound⟩

end BONG

end Bong
