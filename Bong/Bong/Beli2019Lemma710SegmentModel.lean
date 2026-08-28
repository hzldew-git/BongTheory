/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710TargetPrefix
import Bong.Bong.SegmentTransport

/-!
# Beli (2019), Lemma 7.10: the stopping lattice as a concrete segment

Automatic prefix extraction produces a dependent stopping BONG whose ambient
space is hidden behind successive orthogonal complements.  This file follows
the same recursion while also realizing that stopping lattice as the literal
consecutive suffix segment of the candidate BONG.  The resulting lattice
isometry is the geometric bridge needed to turn the paper's consecutive-block
identity into the internal `StopLatticeEq` used by the two-endpoint proof.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w z z'

namespace SegmentWitness

section WholeCast

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {U : Type v} [AddCommGroup U] [Module K U]
  {s : QuadraticSpace K U} {N : Lattice K U} {m : Nat}

/-- The canonical whole-segment isometry carries the length-cast BONG vectors
to the corresponding vectors of the whole-segment realization.  This lemma is
kept in the 2019 layer because `BONG.castLength` belongs to the existence API. -/
@[simp]
theorem wholeCastLatticeIsometry_apply_castLength_ambientVector {m' : Nat}
    (c : BONG U s N m) (h : m = m') (i : Fin m') :
    (wholeCastLatticeIsometry c h).toLinearEquiv
        ((c.castLength h).ambientVector i) =
      (wholeCast c h).bong.ambientVector i := by
  subst m'
  change (wholeLatticeIsometry c).toLinearEquiv (c.ambientVector i) =
    (whole c).bong.ambientVector i
  change Submodule.topEquiv.symm (c.ambientVector i) =
    (c.map
      { toLinearEquiv := Submodule.topEquiv.symm
        map_bilin := fun _ _ => rfl }).ambientVector i
  rw [BONG.ambientVector_map]

end WholeCast

end SegmentWitness

namespace OrthogonalPrefixRawSeed

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat}

/-- The lattice isometry at the stopping node of a raw prefix extraction.
Outer `cons` nodes only change how that node is embedded into the original
ambient space, so the type recursively discards them. -/
def StopSegmentIsometry
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound) :
    Type (max v w z) := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact Lattice.Isometry (q.orthogonalSum r)
        (s.restrict segment.carrier segment.nondegenerate)
        N segment.lattice
  | cons _ _ _ _ tailModel =>
      exact tailModel

/-- The literal stopping BONG stored by a raw prefix seed. -/
def StopBaseBONG
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    Type (max (u + 1) (v + 1) (w + 1)) := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact BONG (V × W) (q.orthogonalSum r) N baseLength
  | cons _ _ _ _ tailBase =>
      exact tailBase

/-- Recover the literal BONG at the hidden stopping node. -/
noncomputable def stopBase
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    S.StopBaseBONG := by
  induction S with
  | stop source base => exact base
  | cons _ _ _ _ tailBase => exact tailBase

/-- The canonical stopping-space isometry sends the hidden raw BONG vectors
to the vectors of the concrete target segment. -/
def StopBaseVectorEq
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (stopToSegment : S.StopSegmentIsometry segment) : Prop := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact ∀ i : Fin baseLength,
        stopToSegment.toLinearEquiv (base.ambientVector i) =
          segment.bong.ambientVector i
  | cons _ _ _ _ tailEq =>
      exact tailEq stopToSegment

/-- The paper-facing isometry from a literal replacement segment to the
orthogonal product required at the hidden stopping node.  As for
`StopSegmentIsometry`, prefix nodes merely pass the datum to the recursive
tail. -/
def StopSegmentProductIsometry
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound) :
    Type (max v w z) := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact Lattice.Isometry
        (s.restrict segment.carrier segment.nondegenerate)
        (q.orthogonalSum r)
        segment.lattice (Lattice.product L M)
  | cons _ _ _ _ tailModel =>
      exact tailModel

/-- The literal consecutive-block equality in the coordinates supplied by
`StopSegmentIsometry`: the extracted segment lattice is the image of the
expected orthogonal product under the very same stopping-space isometry. -/
def StopSegmentProductEq
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (stopToSegment : S.StopSegmentIsometry segment) : Prop := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact segment.lattice = Lattice.map stopToSegment.toLinearEquiv
        (Lattice.product L M)
  | cons _ _ _ _ tailEq =>
      exact tailEq stopToSegment

/-- The geometric consecutive-block equality implies the equality of the
hidden stopping lattice with the orthogonal product. -/
theorem stopLatticeEq_of_segmentProductEq
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (stopToSegment : S.StopSegmentIsometry segment)
    (segmentProductEq : S.StopSegmentProductEq segment stopToSegment) :
    S.StopLatticeEq := by
  induction S with
  | @stop V _ _ q L n N source base =>
      have hmap : Lattice.map stopToSegment.toLinearEquiv N =
          Lattice.map stopToSegment.toLinearEquiv
            (Lattice.product L M) :=
        stopToSegment.map_eq.trans segmentProductEq
      apply Lattice.ext
      ext x
      constructor
      · intro hx
        have hmapped : stopToSegment.toLinearEquiv x ∈
            Lattice.map stopToSegment.toLinearEquiv N :=
          (Lattice.map_mem_map_iff _ _ _).2 hx
        rw [hmap] at hmapped
        exact (Lattice.map_mem_map_iff _ _ _).1 hmapped
      · intro hx
        have hmapped : stopToSegment.toLinearEquiv x ∈
            Lattice.map stopToSegment.toLinearEquiv
              (Lattice.product L M) :=
          (Lattice.map_mem_map_iff _ _ _).2 hx
        rw [← hmap] at hmapped
        exact (Lattice.map_mem_map_iff _ _ _).1 hmapped
  | cons _ _ _ _ ih =>
      exact ih stopToSegment segmentProductEq

/-- Postcompose the hidden stopping-lattice realization with an isometry of
external segment models. -/
noncomputable def StopSegmentIsometry.trans
    {U₁ : Type z} [AddCommGroup U₁] [Module K U₁]
    {s₁ : QuadraticSpace K U₁} {P₁ : Lattice K U₁}
    {targetLength₁ start₁ : Nat}
    {bound₁ : start₁ + baseLength ≤ targetLength₁}
    {target₁ : BONG U₁ s₁ P₁ targetLength₁}
    {U₂ : Type z'} [AddCommGroup U₂] [Module K U₂]
    {s₂ : QuadraticSpace K U₂} {P₂ : Lattice K U₂}
    {targetLength₂ start₂ : Nat}
    {bound₂ : start₂ + baseLength ≤ targetLength₂}
    {target₂ : BONG U₂ s₂ P₂ targetLength₂}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment₁ : SegmentWitness target₁ start₁ baseLength bound₁)
    (segment₂ : SegmentWitness target₂ start₂ baseLength bound₂)
    (f : S.StopSegmentIsometry segment₁)
    (g : Lattice.Isometry
      (s₁.restrict segment₁.carrier segment₁.nondegenerate)
      (s₂.restrict segment₂.carrier segment₂.nondegenerate)
      segment₁.lattice segment₂.lattice) :
    S.StopSegmentIsometry segment₂ := by
  induction S with
  | stop => exact Lattice.Isometry.trans f g
  | cons _ _ _ _ ih => exact ih f

/-- Exact stopping-vector compatibility is stable under postcomposition by
an isometry of concrete segment models that itself preserves their BONG
vectors. -/
theorem StopBaseVectorEq.trans
    {U₁ : Type z} [AddCommGroup U₁] [Module K U₁]
    {s₁ : QuadraticSpace K U₁} {P₁ : Lattice K U₁}
    {targetLength₁ start₁ : Nat}
    {bound₁ : start₁ + baseLength ≤ targetLength₁}
    {target₁ : BONG U₁ s₁ P₁ targetLength₁}
    {U₂ : Type z'} [AddCommGroup U₂] [Module K U₂]
    {s₂ : QuadraticSpace K U₂} {P₂ : Lattice K U₂}
    {targetLength₂ start₂ : Nat}
    {bound₂ : start₂ + baseLength ≤ targetLength₂}
    {target₂ : BONG U₂ s₂ P₂ targetLength₂}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment₁ : SegmentWitness target₁ start₁ baseLength bound₁)
    (segment₂ : SegmentWitness target₂ start₂ baseLength bound₂)
    (f : S.StopSegmentIsometry segment₁)
    (g : Lattice.Isometry
      (s₁.restrict segment₁.carrier segment₁.nondegenerate)
      (s₂.restrict segment₂.carrier segment₂.nondegenerate)
      segment₁.lattice segment₂.lattice)
    (baseVectors : S.StopBaseVectorEq segment₁ f)
    (segmentVectors : ∀ i : Fin baseLength,
      g.toLinearEquiv (segment₁.bong.ambientVector i) =
        segment₂.bong.ambientVector i) :
    S.StopBaseVectorEq segment₂
      (StopSegmentIsometry.trans S segment₁ segment₂ f g) := by
  induction S with
  | @stop V _ _ q L n N source base =>
      intro i
      change g.toLinearEquiv
          (f.toLinearEquiv (base.ambientVector i)) =
        segment₂.bong.ambientVector i
      rw [baseVectors i]
      exact segmentVectors i
  | cons _ _ _ _ ih =>
      exact ih f baseVectors

/-- Replace the equality-only realization `OrthogonalPrefixRawSeed.toSeed`
by the geometric formulation used in Beli's argument: realize the hidden
stopping lattice as a consecutive segment, identify that segment with the
orthogonal product, and rebuild all unchanged prefix nodes. -/
noncomputable def toSeedOfSegmentIsometries
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (stopToSegment : S.StopSegmentIsometry segment)
    (segmentToProduct : S.StopSegmentProductIsometry segment) :
    OrthogonalPrefixSeed r M baseLength (steps := steps) b := by
  induction S with
  | stop source base =>
      exact OrthogonalPrefixSeed.stopOfLatticeIsometry source base
        (Lattice.Isometry.trans stopToSegment segmentToProduct)
  | cons generator anisotropic tail tailSeed ih =>
      exact .cons generator anisotropic tail
        (ih stopToSegment segmentToProduct)

/-- Target-prefix extraction enhanced with a literal consecutive replacement
segment and an isometry from the hidden stopping lattice to that segment. -/
structure TargetPrefixSegmentExtraction
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {N : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps)) where
  extraction : TargetPrefixExtraction (M := M) source hsteps target
  segment : SegmentWitness target steps baseLength (by omega)
  stopToSegment : extraction.seed.StopSegmentIsometry segment
  stopVectors : extraction.seed.StopBaseVectorEq segment stopToSegment

/-- Follow `extractTargetPrefix` while retaining the actual suffix segment.
At each prefix node the recursive segment is transported back through the
orthogonal-complement isometry and then embedded into the parent space. -/
noncomputable def extractTargetPrefixSegment
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {N : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0)) :
    TargetPrefixSegmentExtraction (M := M) source hsteps target := by
  induction source generalizing steps with
  | nil q L exhausted =>
      have hzero : steps = 0 := by omega
      subst steps
      let segment := SegmentWitness.wholeCast target
        (Nat.add_zero baseLength)
      let stopToSegment := SegmentWitness.wholeCastLatticeIsometry target
        (Nat.add_zero baseLength)
      refine
        { extraction :=
            { seed := .stop (BONG.nil q L exhausted)
                (target.castLength (Nat.add_zero baseLength))
              baseAmbientVector_eq := ?_ }
          segment := segment
          stopToSegment := stopToSegment
          stopVectors := by
            intro i
            exact SegmentWitness.wholeCastLatticeIsometry_apply_castLength_ambientVector
              target (Nat.add_zero baseLength) i }
      · intro j
        change (target.castLength (Nat.add_zero baseLength)).ambientVector j =
          target.ambientVector (orthogonalProductRightIndex 0 j)
        rw [ambientVector_castLength]
        apply congrArg target.ambientVector
        apply Fin.ext
        simp [orthogonalProductRightIndex]
  | @cons V _ _ q L n x generator anisotropic tail ih =>
      cases steps with
      | zero =>
          let segment := SegmentWitness.wholeCast target
            (Nat.add_zero baseLength)
          let stopToSegment := SegmentWitness.wholeCastLatticeIsometry target
            (Nat.add_zero baseLength)
          refine
            { extraction :=
                { seed := .stop (BONG.cons x generator anisotropic tail)
                    (target.castLength (Nat.add_zero baseLength))
                  baseAmbientVector_eq := ?_ }
              segment := segment
              stopToSegment := stopToSegment
              stopVectors := by
                intro i
                exact SegmentWitness.wholeCastLatticeIsometry_apply_castLength_ambientVector
                  target (Nat.add_zero baseLength) i }
          · intro j
            change
              (target.castLength (Nat.add_zero baseLength)).ambientVector j =
                target.ambientVector (orthogonalProductRightIndex 0 j)
            rw [ambientVector_castLength]
            apply congrArg target.ambientVector
            apply Fin.ext
            simp [orthogonalProductRightIndex]
      | succ k =>
          cases target with
          | @cons _ _ _ _ _ targetTailLength y targetGenerator
              targetAnisotropic targetTail =>
              have hhead : y = (x, 0) := by
                have h := leftVectors (0 : Fin (k + 1))
                have htargetIndex :
                    orthogonalProductLeftIndex baseLength
                        (0 : Fin (k + 1)) =
                      (0 : Fin (baseLength + (k + 1))) := by
                  apply Fin.ext
                  rfl
                have hsourceIndex :
                    prefixSourceIndex hsteps (0 : Fin (k + 1)) =
                      (0 : Fin (n + 1)) := by
                  apply Fin.ext
                  rfl
                rw [htargetIndex, hsourceIndex,
                  ambientVector_cons_zero, ambientVector_cons_zero] at h
                exact h
              subst y
              have han :
                  targetAnisotropic = anisotropic.orthogonalSum_inl :=
                Subsingleton.elim _ _
              subst targetAnisotropic
              let f := q.orthogonalSpaceOrthogonalSumInlIsometry r anisotropic
              let mappedTarget := targetTail.map f
              have hk : k ≤ n := by omega
              have mappedLeftVectors : ∀ i : Fin k,
                  mappedTarget.ambientVector
                      (orthogonalProductLeftIndex baseLength i) =
                    (tail.ambientVector (prefixSourceIndex hk i), 0) := by
                intro i
                have hglobal := leftVectors i.succ
                have htargetIndex :
                    orthogonalProductLeftIndex baseLength i.succ =
                      (orthogonalProductLeftIndex baseLength i).succ := by
                  apply Fin.ext
                  rfl
                have hsourceIndex :
                    prefixSourceIndex hsteps i.succ =
                      (prefixSourceIndex hk i).succ := by
                  apply Fin.ext
                  rfl
                rw [htargetIndex, hsourceIndex,
                  ambientVector_cons_succ, ambientVector_cons_succ] at hglobal
                change
                  (targetTail.ambientVector
                      (orthogonalProductLeftIndex baseLength i) : V × W) =
                    (((tail.ambientVector (prefixSourceIndex hk i) :
                      q.vectorOrthogonal x) : V), 0) at hglobal
                rw [ambientVector_map]
                apply Prod.ext
                · apply Subtype.ext
                  exact congrArg Prod.fst hglobal
                · change
                    (targetTail.ambientVector
                      (orthogonalProductLeftIndex baseLength i)).val.2 = 0
                  simpa using congrArg Prod.snd hglobal
              let tailModel := ih hk mappedTarget mappedLeftVectors
              let tailSegment := tailModel.segment.unmap f
              let segment := tailSegment.liftTail
                (generator := targetGenerator)
              let stopToTailSegment :=
                StopSegmentIsometry.trans tailModel.extraction.seed
                  tailModel.segment tailSegment tailModel.stopToSegment
                  (tailModel.segment.unmapLatticeIsometry f)
              let stopToSegment :=
                StopSegmentIsometry.trans tailModel.extraction.seed
                  tailSegment segment stopToTailSegment
                  (tailSegment.liftTailLatticeIsometry
                    (generator := targetGenerator))
              refine
                { extraction :=
                    { seed := .cons generator anisotropic tail
                        tailModel.extraction.seed
                      baseAmbientVector_eq := ?_ }
                  segment := segment
                  stopToSegment := stopToSegment
                  stopVectors := by
                    let tailVectors := StopBaseVectorEq.trans
                      tailModel.extraction.seed tailModel.segment tailSegment
                      tailModel.stopToSegment
                      (tailModel.segment.unmapLatticeIsometry f)
                      tailModel.stopVectors
                      (fun i =>
                        SegmentWitness.unmapLatticeIsometry_apply_ambientVector
                          f tailModel.segment i)
                    exact StopBaseVectorEq.trans
                      tailModel.extraction.seed tailSegment segment
                      stopToTailSegment
                      (tailSegment.liftTailLatticeIsometry
                        (generator := targetGenerator))
                      tailVectors
                      (fun i =>
                        SegmentWitness.liftTailLatticeIsometry_apply_ambientVector
                          tailSegment i) }
              intro j
              change
                (((Lattice.projectedOrthogonalProductIsometry
                    (q := q) (r := r) (L := L) (M := M)
                    anisotropic).symm.toLinearEquiv
                      (tailModel.extraction.seed.baseAmbientVector j) :
                    (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W) =
                  (BONG.cons (x, 0) targetGenerator
                    anisotropic.orthogonalSum_inl targetTail).ambientVector
                      (orthogonalProductRightIndex (k + 1) j)
              rw [tailModel.extraction.baseAmbientVector_eq j,
                ambientVector_map]
              change
                (((Lattice.projectedOrthogonalProductIsometry
                    (q := q) (r := r) (L := L) (M := M)
                    anisotropic).symm.toLinearEquiv
                      ((Lattice.projectedOrthogonalProductIsometry
                        (q := q) (r := r) (L := L) (M := M)
                        anisotropic).toLinearEquiv
                          (targetTail.ambientVector
                            (orthogonalProductRightIndex k j))) :
                    (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W) = _
              have hindex :
                  orthogonalProductRightIndex (k + 1) j =
                    (orthogonalProductRightIndex k j).succ := by
                apply Fin.ext
                simp only [orthogonalProductRightIndex_val, Fin.val_succ]
                omega
              rw [hindex, ambientVector_cons_succ]
              exact congrArg Subtype.val
                ((Lattice.projectedOrthogonalProductIsometry
                  (q := q) (r := r) (L := L) (M := M)
                  anisotropic).toLinearEquiv.symm_apply_apply
                    (targetTail.ambientVector
                      (orthogonalProductRightIndex k j)))

/-- Paper-facing proposition saying that the automatically extracted literal
suffix segment is the expected stopping orthogonal product. -/
def TargetPrefixSegmentProductEq
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {N : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0)) : Prop :=
  let model := extractTargetPrefixSegment (M := M) source hsteps target
    leftVectors
  model.extraction.seed.StopSegmentProductEq model.segment
    model.stopToSegment

/-- Eliminate the former local `dualStopEq` premise from a concrete
consecutive replacement identity. -/
theorem stopLatticeEq_of_targetPrefixSegmentProductEq
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {N : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0))
    (hproduct : TargetPrefixSegmentProductEq (M := M) source hsteps
      target leftVectors) :
    (extractTargetPrefixSegment (M := M) source hsteps target
      leftVectors).extraction.seed.StopLatticeEq := by
  let model := extractTargetPrefixSegment (M := M) source hsteps target
    leftVectors
  exact model.extraction.seed.stopLatticeEq_of_segmentProductEq
    model.segment model.stopToSegment hproduct

end OrthogonalPrefixRawSeed

namespace OrthogonalPrefixRawSeed.DualEndpointCertificate

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Build the dual stopping certificate from the literal consecutive-segment
product identity.  The hidden stopping equality is now a theorem, not a
caller-supplied interface. -/
noncomputable def stopOfTargetPrefixSegmentProductEq
    {sourceLength dualPrefixLength dualRightLength baseTail dualSteps : Nat}
    {N : Lattice K (V × W)}
    (source : BONG V q L sourceLength)
    (base : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + dualSteps))
    (rightFactorDual : GoodBONG r (Lattice.dualLattice r M)
      dualPrefixLength)
    (hsteps : dualSteps ≤ dualPrefixLength)
    (leftFactorDual : BONG V q (Lattice.dualLattice q L)
      (dualRightLength + 1))
    (targetDual : GoodBONG (r.orthogonalSum q)
      (Lattice.dualLattice (r.orthogonalSum q)
        (Lattice.swapLattice N))
      ((baseTail + 1) + dualSteps))
    (leftVectors : ∀ i : Fin dualSteps,
      targetDual.toBONG.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (rightFactorDual.toBONG.ambientVector
          (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i), 0))
    (segmentProductEq :
      OrthogonalPrefixRawSeed.TargetPrefixSegmentProductEq
        (M := Lattice.dualLattice q L) rightFactorDual.toBONG hsteps
        targetDual.toBONG leftVectors)
    (hlast : ∀ hpos : 0 < dualSteps,
      rightFactorDual.order ⟨dualSteps - 1, by omega⟩ ≤
        leftFactorDual.order 0) :
    OrthogonalPrefixRawSeed.DualEndpointCertificate r M
      (OrthogonalPrefixRawSeed.stop (M := M) source base) := by
  let model := OrthogonalPrefixRawSeed.extractTargetPrefixSegment
    (M := Lattice.dualLattice q L) rightFactorDual.toBONG hsteps
    targetDual.toBONG leftVectors
  let dualStopEq :=
    OrthogonalPrefixRawSeed.stopLatticeEq_of_targetPrefixSegmentProductEq
      (M := Lattice.dualLattice q L) rightFactorDual.toBONG hsteps
      targetDual.toBONG leftVectors segmentProductEq
  let seed := model.extraction.seed.toSeed dualStopEq
  exact .stop source base rightFactorDual hsteps leftFactorDual seed hlast
    targetDual
    (fun i => by
      have hindex : seed.sourceIndex i =
          OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact leftVectors i)
    (fun j => by
      calc
        targetDual.toBONG.ambientVector
            (orthogonalProductRightIndex dualSteps j) =
            model.extraction.seed.baseAmbientVector j :=
          (model.extraction.baseAmbientVector_eq j).symm
        _ = seed.baseAmbientVector j :=
          (model.extraction.seed.baseAmbientVector_toSeed dualStopEq j).symm)

/-- Suffix-vector form of `stopOfTargetPrefixSegmentProductEq`.  Reverse
duality supplies the prefix automatically, leaving only the literal segment
product identity. -/
noncomputable def stopOfSuffixVectorsSegmentProductEq
    {sourceLength dualPrefixLength dualRightLength baseTail dualSteps : Nat}
    {N : Lattice K (V × W)}
    (source : BONG V q L sourceLength)
    (base : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + dualSteps))
    (right : BONG W r M dualPrefixLength)
    (rightFactorDual : GoodBONG r (Lattice.dualLattice r M)
      dualPrefixLength)
    (rightDualVectors : ∀ i,
      rightFactorDual.toBONG.ambientVector i = right.reverseDualVector i)
    (hsteps : dualSteps ≤ dualPrefixLength)
    (leftFactorDual : BONG V q (Lattice.dualLattice q L)
      (dualRightLength + 1))
    (targetDual : GoodBONG (r.orthogonalSum q)
      (Lattice.dualLattice (r.orthogonalSum q)
        (Lattice.swapLattice N))
      ((baseTail + 1) + dualSteps))
    (targetDualVectors : ∀ i,
      targetDual.toBONG.ambientVector i =
        (LinearEquiv.prodComm K V W) (base.reverseDualVector i))
    (suffixVectors : ∀ i : Fin dualSteps,
      base.ambientVector
          (Fin.rev (orthogonalProductLeftIndex (baseTail + 1) i)) =
        (0, right.ambientVector
          (Fin.rev (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i))))
    (segmentProductEq :
      OrthogonalPrefixRawSeed.TargetPrefixSegmentProductEq
        (M := Lattice.dualLattice q L) rightFactorDual.toBONG hsteps
        targetDual.toBONG
        (base.swappedReverseDual_prefixVectors_of_suffixVectors
          right hsteps suffixVectors rightDualVectors targetDualVectors))
    (hlast : ∀ hpos : 0 < dualSteps,
      rightFactorDual.order ⟨dualSteps - 1, by omega⟩ ≤
        leftFactorDual.order 0) :
    OrthogonalPrefixRawSeed.DualEndpointCertificate r M
      (OrthogonalPrefixRawSeed.stop (M := M) source base) := by
  let leftVectors :=
    base.swappedReverseDual_prefixVectors_of_suffixVectors
      right hsteps suffixVectors rightDualVectors targetDualVectors
  exact stopOfTargetPrefixSegmentProductEq source base rightFactorDual hsteps
    leftFactorDual targetDual leftVectors segmentProductEq hlast

end OrthogonalPrefixRawSeed.DualEndpointCertificate

namespace GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n rightLength : Nat}

/-- Paper-facing consecutive-replacement form of Beli (2019), Lemma 7.10.
The unchanged prefix determines the hidden stopping model automatically, and
the one literal segment-product equality supplies its stopping identity. -/
theorem beli2019Lemma710General_of_targetPrefixSegmentProductEq
    {baseTail steps : Nat} {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (hsteps : steps ≤ n)
    (right : BONG W r M (rightLength + 1))
    (target : GoodBONG (q.orthogonalSum r) N
      ((baseTail + 1) + steps))
    (leftVectors : ∀ i : Fin steps,
      target.toBONG.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (b.toBONG.ambientVector
          (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i), 0))
    (segmentProductEq :
      OrthogonalPrefixRawSeed.TargetPrefixSegmentProductEq (M := M)
        b.toBONG hsteps target.toBONG leftVectors)
    (hlast : ∀ hpos : 0 < steps,
      b.order ⟨steps - 1, by omega⟩ ≤ right.order 0) :
    N = Lattice.product L M := by
  let model := OrthogonalPrefixRawSeed.extractTargetPrefixSegment (M := M)
    b.toBONG hsteps target.toBONG leftVectors
  let tailIdentity :=
    OrthogonalPrefixRawSeed.stopLatticeEq_of_targetPrefixSegmentProductEq
      (M := M) b.toBONG hsteps target.toBONG leftVectors segmentProductEq
  let seed := model.extraction.seed.toSeed tailIdentity
  apply b.beli2019Lemma710RightEnd_steps_of_good hsteps right seed hlast
    target.toBONG target.good
  · intro i
    rw [model.extraction.seed.sourceIndex_toSeed tailIdentity]
    have hindex : model.extraction.seed.sourceIndex i =
        OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact leftVectors i
  · intro j
    rw [model.extraction.seed.baseAmbientVector_toSeed tailIdentity]
    exact (model.extraction.baseAmbientVector_eq j).symm

end GoodBONG

end BONG

end Bong
