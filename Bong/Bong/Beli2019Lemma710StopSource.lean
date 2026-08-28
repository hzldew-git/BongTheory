/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710SegmentDual

/-!
# Beli (2019), Lemma 7.10: the source at the stopping node

The dependent recursion used by `OrthogonalPrefixRawSeed` changes ambient
spaces at every discarded head.  This file packages the literal source BONG
left at its unique stopping node, together with its canonical linear embedding
back into the original source space.  The package also records that its BONG
is precisely the suffix of the original source BONG.
-/

namespace Bong

open Dyadic

namespace BONG.OrthogonalPrefixRawSeed

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat}

/-- The literal source remaining at the stopping node, bundled so that the
dependent additive-group and module instances travel with its ambient type. -/
structure StopSourceData
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) where
  Ambient : Type v
  [addCommGroup : AddCommGroup Ambient]
  [module : Module K Ambient]
  form : QuadraticSpace K Ambient
  lattice : Lattice K Ambient
  length : Nat
  bong : BONG Ambient form lattice length
  stopLattice : Lattice K (Ambient × W)
  base : BONG (Ambient × W) (form.orthogonalSum r) stopLattice baseLength
  embedding : Ambient →ₗ[K] V
  embedding_injective : Function.Injective embedding
  length_add_steps : length + steps = n
  value_eq : ∀ i : Fin length,
    bong.value i = b.value ⟨steps + i.val, by omega⟩
  ambientVector_eq : ∀ i : Fin length,
    embedding (bong.ambientVector i) =
      b.ambientVector ⟨steps + i.val, by omega⟩
  baseAmbientVector_eq : ∀ j : Fin baseLength,
    (embedding (base.ambientVector j).1, (base.ambientVector j).2) =
      S.baseAmbientVector j

/-- Follow a raw prefix seed to its unique stopping node while composing the
orthogonal-complement inclusions back into the original source ambient space. -/
noncomputable def stopSourceData
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    StopSourceData S := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact
        { Ambient := V
          form := q
          lattice := L
          length := n
          bong := source
          stopLattice := N
          base := base
          embedding := LinearMap.id
          embedding_injective := LinearMap.ker_eq_bot.mp rfl
          length_add_steps := rfl
          value_eq := by
            intro i
            apply congrArg source.value
            apply Fin.ext
            simp
          ambientVector_eq := by
            intro i
            change source.ambientVector i =
              source.ambientVector ⟨0 + i.val, by omega⟩
            apply congrArg source.ambientVector
            apply Fin.ext
            simp
          baseAmbientVector_eq := by
            intro j
            rfl }
  | @cons V _ _ q L n tailSteps x generator anisotropic tail tailSeed ih =>
      let D := ih
      letI := D.addCommGroup
      letI := D.module
      exact
        { Ambient := D.Ambient
          form := D.form
          lattice := D.lattice
          length := D.length
          bong := D.bong
          stopLattice := D.stopLattice
          base := D.base
          embedding := (q.vectorOrthogonal x).subtype.comp D.embedding
          embedding_injective := by
            intro a b h
            apply D.embedding_injective
            apply Subtype.ext
            exact h
          length_add_steps := by
            have h := D.length_add_steps
            omega
          value_eq := by
            intro i
            have hindex :
                (⟨tailSteps + 1 + i.val, by
                  have h := D.length_add_steps
                  omega⟩ : Fin (n + 1)) =
                  (⟨tailSteps + i.val, by
                    have h := D.length_add_steps
                    omega⟩ : Fin n).succ := by
              apply Fin.ext
              simp only [Fin.val_succ]
              omega
            rw [hindex, BONG.value_cons_succ]
            exact D.value_eq i
          ambientVector_eq := by
            intro i
            change
              ((D.embedding (D.bong.ambientVector i) :
                  q.vectorOrthogonal x) : V) =
                (BONG.cons x generator anisotropic tail).ambientVector
                  ⟨tailSteps + 1 + i.val, by
                    have h := D.length_add_steps
                    omega⟩
            rw [D.ambientVector_eq i]
            have hlength := D.length_add_steps
            have hindex :
                (⟨tailSteps + 1 + i.val, by omega⟩ : Fin (n + 1)) =
                  (⟨tailSteps + i.val, by
                    omega⟩ : Fin n).succ := by
              apply Fin.ext
              simp only [Fin.val_succ]
              omega
            rw [hindex, BONG.ambientVector_cons_succ]
          baseAmbientVector_eq := by
            intro j
            change
              (((D.embedding (D.base.ambientVector j).1 :
                    q.vectorOrthogonal x) : V),
                (D.base.ambientVector j).2) =
                (((Lattice.projectedOrthogonalProductIsometry
                    (q := q) (r := r) (L := L) (M := M)
                    anisotropic).symm.toLinearEquiv
                      (tailSeed.baseAmbientVector j) :
                    (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W)
            rw [← D.baseAmbientVector_eq j]
            rfl }

namespace StopSourceData

attribute [local instance] StopSourceData.addCommGroup StopSourceData.module

/-- Embed the full hidden stopping product into the original source product,
leaving the external right factor unchanged. -/
noncomputable def productEmbedding
    {b : BONG V q L n}
    {S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b}
    (D : StopSourceData S) : D.Ambient × W →ₗ[K] V × W := by
  letI := D.addCommGroup
  letI := D.module
  exact D.embedding.prodMap LinearMap.id

@[simp]
theorem productEmbedding_apply
    {b : BONG V q L n}
    {S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b}
    (D : StopSourceData S) (x : D.Ambient × W) :
    D.productEmbedding x = (D.embedding x.1, x.2) := by
  letI := D.addCommGroup
  letI := D.module
  rfl

/-- The product embedding remains injective because every discarded
orthogonal-complement inclusion is injective. -/
theorem productEmbedding_injective
    {b : BONG V q L n}
    {S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b}
    (D : StopSourceData S) : Function.Injective D.productEmbedding := by
  letI := D.addCommGroup
  letI := D.module
  intro x y h
  change (D.embedding x.1, x.2) = (D.embedding y.1, y.2) at h
  apply Prod.ext
  · apply D.embedding_injective
    exact congrArg (fun z : V × W => z.1) h
  · exact congrArg (fun z : V × W => z.2) h

end StopSourceData

/-- A non-dependent view of the segment-to-product certificate at the hidden
stopping node.  It uses `StopSourceData` to expose the source ambient space
and the literal stopping BONG without losing their typeclass instances. -/
def StopSourceSegmentProductIsometryData
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound) : Type _ :=
  let D := S.stopSourceData
  letI := D.addCommGroup
  letI := D.module
  { segmentToProduct : Lattice.Isometry
      (s.restrict segment.carrier segment.nondegenerate)
      (D.form.orthogonalSum r) segment.lattice
      (Lattice.product D.lattice M) //
    ∀ i : Fin baseLength,
      segmentToProduct.toLinearEquiv (segment.bong.ambientVector i) =
        D.base.ambientVector i }

/-- Repackage the exposed stopping-node certificate into the original
dependent family consumed by Lemma 7.10. -/
noncomputable def StopSourceSegmentProductIsometryData.toDependent
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (E : S.StopSourceSegmentProductIsometryData segment) :
    S.StopSegmentProductIsometryData segment := by
  induction S with
  | stop =>
      exact ⟨E.1, E.2⟩
  | cons generator anisotropic tail tailSeed ih =>
      let E' : tailSeed.StopSourceSegmentProductIsometryData segment :=
        by
          unfold StopSourceSegmentProductIsometryData at E ⊢
          simp only [stopSourceData] at E ⊢
          exact E
      exact ih E'

end BONG.OrthogonalPrefixRawSeed

end Bong
