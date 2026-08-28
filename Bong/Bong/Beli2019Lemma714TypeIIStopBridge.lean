/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIInnerSeed
import Bong.Bong.Beli2019Lemma710StopSource

/-!
# Beli (2019), Lemma 7.14(ii): closing the outer stopping certificate

The inner reverse-dual construction identifies the literal stopping segment
with `πJ ⊥ rightSuffix`.  The first application of Lemma 7.10, however,
expects the left factor at a dependent stopping node hidden behind `s - 2`
successive orthogonal complements.  This file proves that the hidden source
has length two, identifies it canonically with `πJ`, and transports the
concrete stopping-segment isometry into the exact certificate consumed by
Lemma 7.10.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

attribute [local instance]
  BONG.OrthogonalPrefixRawSeed.StopSourceData.addCommGroup
  BONG.OrthogonalPrefixRawSeed.StopSourceData.module

section StopBridge

variable [DyadicDiscriminantClassLaws K]
variable [BONGReverseDualLaws.{u, v} K]
variable [BeliLemma43ConstructionLaws.{u, v} K]
variable (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
variable (D : Lemma714StoppingData b R s)
variable (hfirst : b.order ⟨0, by omega⟩ = R)
variable (hsecond : b.order ⟨1, by omega⟩ =
  R - 2 * (ramificationIndex K : Int))
variable (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
variable (hsCurrent : s < n + 3)
variable (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
variable (S : BONG.TwoBlockSplitWitness b.toBONG 2 (by omega))
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

/-- The final two values of the first Lemma-7.10 source are exactly the
values of the rescaled initial binary BONG. -/
@[simp]
theorem lemma714TypeIILeftProduct_value_binary (j : Fin 2) :
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG.value
        ⟨s - 2 + j.val, by omega⟩ =
      ((b.lemma714InitialBinary S).lemma714RescaledBinary).toBONG.value j := by
  let source :=
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG
  let binary := ((b.lemma714InitialBinary S).lemma714RescaledBinary).toBONG
  let leftForm :=
    ((q.restrict S.right.carrier S.right.nondegenerate).restrict
      U.left.carrier U.left.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)
  let binaryForm := q.restrict S.left.carrier S.left.nondegenerate
  calc
    source.value ⟨s - 2 + j.val, by omega⟩ =
        leftForm.quadratic
          (source.ambientVector ⟨s - 2 + j.val, by omega⟩) :=
      (source.quadratic_ambientVector _).symm
    _ = leftForm.quadratic (0, binary.ambientVector j) := by
      rw [b.lemma714TypeIILeftProduct_ambientVector_binary R s D hfirst
        hsecond hthird S hsFour U j]
    _ = binaryForm.quadratic (binary.ambientVector j) := by
      simp [leftForm, binaryForm,
        QuadraticSpace.orthogonalSum_quadratic_apply]
    _ = binary.value j := binary.quadratic_ambientVector j

/-- The automatically extracted outer prefix and its concrete stopping
segment. -/
noncomputable def lemma714TypeIIOuterModel :=
  BONG.OrthogonalPrefixRawSeed.extractTargetPrefixSegment
    (M := U.right.lattice)
    (b.lemma714TypeIILeftProduct R s D hfirst hsecond hthird S hsFour U).toBONG
    (by omega)
    (b.lemma714TypeIITargetForLemma710 R s D hsCurrent S hsFour U target).toBONG
    (b.lemma714TypeIITargetForLemma710_leftVectors R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors)

/-- Expose the dependent source BONG at the stopping node of the outer
prefix extraction. -/
noncomputable def lemma714TypeIIOuterStopSource :=
  (b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird hsCurrent S hsFour
    U block target htargetVectors).extraction.seed.stopSourceData

/-- Exactly two source vectors remain after discarding the unchanged
`s - 2` prefix. -/
theorem lemma714TypeIIOuterStopSource_length :
    (b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird hsCurrent S
      hsFour U block target htargetVectors).length = 2 := by
  have hlength :=
    (b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird hsCurrent S
      hsFour U block target htargetVectors).length_add_steps
  omega

/-- The stopping source BONG with its length normalized to the literal binary
rank. -/
noncomputable def lemma714TypeIIOuterStopBONG :=
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  E.bong.castLength
    (b.lemma714TypeIIOuterStopSource_length R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors)

/-- The exposed stopping source has the same two scalar values as `πJ`. -/
@[simp]
theorem lemma714TypeIIOuterStopBONG_value (j : Fin 2) :
    (b.lemma714TypeIIOuterStopBONG R s D hfirst hsecond hthird hsCurrent S
      hsFour U block target htargetVectors).value j =
      ((b.lemma714InitialBinary S).lemma714RescaledBinary).toBONG.value j := by
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  rw [lemma714TypeIIOuterStopBONG, BONG.value_castLength]
  rw [E.value_eq]
  exact b.lemma714TypeIILeftProduct_value_binary R s D hfirst hsecond hthird
    hsCurrent S hsFour U j

/-- Canonical lattice isometry from the explicit rescaled binary factor to
the hidden two-dimensional stopping source. -/
noncomputable def lemma714TypeIIBinaryToOuterStop :=
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  ((b.lemma714InitialBinary S).lemma714RescaledBinary).toBONG
    |>.latticeIsometryOfValueEq
      (b.lemma714TypeIIOuterStopBONG R s D hfirst hsecond hthird hsCurrent S
        hsFour U block target htargetVectors)
      (fun j => (b.lemma714TypeIIOuterStopBONG_value R s D hfirst hsecond
        hthird hsCurrent S hsFour U block target htargetVectors j).symm)

set_option maxHeartbeats 3000000 in
/-- In the original first-product coordinates, the canonical binary-to-stop
isometry is exactly inclusion into the second factor. -/
theorem lemma714TypeIIOuterStop_embedding_binaryToStop
    (x : S.left.carrier) :
    let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    E.embedding
        ((b.lemma714TypeIIBinaryToOuterStop R s D hfirst hsecond hthird
          hsCurrent S hsFour U block target htargetVectors).toLinearEquiv x) =
      (0, x) := by
  dsimp only
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let binary := ((b.lemma714InitialBinary S).lemma714RescaledBinary).toBONG
  let f : S.left.carrier →ₗ[K] U.left.carrier × S.left.carrier :=
    E.embedding.comp
      (b.lemma714TypeIIBinaryToOuterStop R s D hfirst hsecond hthird
        hsCurrent S hsFour U block target htargetVectors).toLinearEquiv.toLinearMap
  let g : S.left.carrier →ₗ[K] U.left.carrier × S.left.carrier :=
    LinearMap.inr K U.left.carrier S.left.carrier
  have hfg : f = g := by
    apply binary.basis.ext
    intro j
    change E.embedding
        ((b.lemma714TypeIIBinaryToOuterStop R s D hfirst hsecond hthird
          hsCurrent S hsFour U block target htargetVectors).toLinearEquiv
            (binary.ambientVector j)) =
      (0, binary.ambientVector j)
    have hmap :
        (b.lemma714TypeIIBinaryToOuterStop R s D hfirst hsecond hthird
          hsCurrent S hsFour U block target htargetVectors).toLinearEquiv
            (binary.ambientVector j) =
          (b.lemma714TypeIIOuterStopBONG R s D hfirst hsecond hthird
            hsCurrent S hsFour U block target htargetVectors).ambientVector j := by
      simpa only [lemma714TypeIIBinaryToOuterStop] using
        BONG.latticeIsometryOfValueEq_apply_ambientVector binary
          (b.lemma714TypeIIOuterStopBONG R s D hfirst hsecond hthird
            hsCurrent S hsFour U block target htargetVectors)
          (fun k => (b.lemma714TypeIIOuterStopBONG_value R s D hfirst
            hsecond hthird hsCurrent S hsFour U block target htargetVectors
            k).symm) j
    rw [hmap]
    rw [lemma714TypeIIOuterStopBONG, BONG.ambientVector_castLength]
    rw [E.ambientVector_eq]
    exact b.lemma714TypeIILeftProduct_ambientVector_binary R s D hfirst
      hsecond hthird S hsFour U j
  have hx := congrArg
    (fun h : S.left.carrier →ₗ[K] U.left.carrier × S.left.carrier => h x) hfg
  simp only [f, g, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.inr_apply] at hx
  change E.embedding
      ((b.lemma714TypeIIBinaryToOuterStop R s D hfirst hsecond hthird
        hsCurrent S hsFour U block target htargetVectors).toLinearEquiv x) =
    (0, x)
  exact hx

/-- Any two witnesses for the same literal stopping segment have the same
value sequence; the canonical value isometry therefore identifies the
automatically extracted witness with the explicit reverse-dual witness. -/
noncomputable def lemma714TypeIIOuterSegmentToStopSegment :=
  let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let stop := b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target
  model.segment.bong.latticeIsometryOfValueEq stop.bong (by
    intro i
    rw [BONG.SegmentWitness.value_eq, BONG.SegmentWitness.value_eq]
    apply congrArg
    apply Fin.ext
    rfl)

/-- The segment-witness identification maps each local BONG vector to the
same local vector of the explicit stopping segment. -/
@[simp]
theorem lemma714TypeIIOuterSegmentToStopSegment_apply_ambientVector
    (i : Fin (lemma714TypeIIBaseLength n s)) :
    let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    (b.lemma714TypeIIOuterSegmentToStopSegment R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors).toLinearEquiv
        (model.segment.bong.ambientVector i) =
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).bong.ambientVector i := by
  dsimp only
  unfold lemma714TypeIIOuterSegmentToStopSegment
  exact BONG.latticeIsometryOfValueEq_apply_ambientVector _ _ _ i

/-- First map the automatically extracted segment to the explicit stopping
segment and then apply the completed inner reverse-dual replacement. -/
noncomputable def lemma714TypeIIOuterSegmentToBinaryRight :=
  (b.lemma714TypeIIOuterSegmentToStopSegment R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors).trans
    (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U block
      target htargetVectors hsecond hcurrent)

/-- Replace the explicit binary factor by the hidden source factor and leave
the external right suffix unchanged. -/
noncomputable def lemma714TypeIIBinaryRightToOuterStop :=
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  (b.lemma714TypeIIBinaryToOuterStop R s D hfirst hsecond hthird hsCurrent S
      hsFour U block target htargetVectors).orthogonalProductBasic
    (Lattice.Isometry.refl
      ((q.restrict S.right.carrier S.right.nondegenerate).restrict
        U.right.carrier U.right.nondegenerate)
      U.right.lattice)

set_option maxHeartbeats 1000000 in
/-- The factor-identification isometry applies the binary-to-stop map in the
first coordinate and is the identity on the right suffix. -/
@[simp]
theorem lemma714TypeIIBinaryRightToOuterStop_apply
    (x : S.left.carrier × U.right.carrier) :
    let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    (b.lemma714TypeIIBinaryRightToOuterStop R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors).toLinearEquiv x =
      ((b.lemma714TypeIIBinaryToOuterStop R s D hfirst hsecond hthird
        hsCurrent S hsFour U block target htargetVectors).toLinearEquiv x.1,
        x.2) := by
  dsimp only
  simp [lemma714TypeIIBinaryRightToOuterStop, Lattice.Isometry.refl]

set_option maxHeartbeats 3000000 in
/-- After returning to the original first-product coordinates, the factor
identification is simply `(x,y) ↦ ((0,x),y)`. -/
theorem lemma714TypeIIBinaryRightToOuterStop_productEmbedding
    (x : S.left.carrier × U.right.carrier) :
    let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    E.productEmbedding
        ((b.lemma714TypeIIBinaryRightToOuterStop R s D hfirst hsecond hthird
          hsCurrent S hsFour U block target htargetVectors).toLinearEquiv x) =
      ((0, x.1), x.2) := by
  dsimp only
  rw [b.lemma714TypeIIBinaryRightToOuterStop_apply R s D hfirst hsecond
    hthird hsCurrent S hsFour U block target htargetVectors x]
  rw [BONG.OrthogonalPrefixRawSeed.StopSourceData.productEmbedding_apply]
  rw [b.lemma714TypeIIOuterStop_embedding_binaryToStop R s D hfirst hsecond
    hthird hsCurrent S hsFour U block target htargetVectors]

/-- The concrete isometry from the automatically extracted stopping segment
to the exact hidden product required by the outer Lemma 7.10 call. -/
noncomputable def lemma714TypeIIOuterSegmentToStopProduct :=
  (b.lemma714TypeIIOuterSegmentToBinaryRight R s D hfirst hsecond hthird
      hsCurrent hcurrent S hsFour U block target htargetVectors).trans
    (b.lemma714TypeIIBinaryRightToOuterStop R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors)

set_option maxHeartbeats 3000000 in
/-- The automatic and explicit witnesses for the same stopping interval have
literally equal ambient vectors after their carrier inclusions. -/
theorem lemma714TypeIIOuterSegments_coe_ambientVector
    (i : Fin (lemma714TypeIIBaseLength n s)) :
    let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    (((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).bong.ambientVector i :
          (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
            target).carrier) :
        (U.left.carrier × S.left.carrier) × U.right.carrier) =
      ((model.segment.bong.ambientVector i : model.segment.carrier) :
        (U.left.carrier × S.left.carrier) × U.right.carrier) := by
  dsimp only
  rw [(b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
      target).ambientVector_eq,
    (b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird hsCurrent S hsFour
      U block target htargetVectors).segment.ambientVector_eq]

set_option maxHeartbeats 3000000 in
/-- On each of the three exceptional vectors, the completed outer isometry
agrees with the original ambient-coordinate inclusion of the hidden stopping
product. -/
theorem lemma714TypeIIOuterSegmentToStopProduct_embedded_block (j : Fin 3) :
    let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    E.productEmbedding
        ((b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond
          hthird hsCurrent hcurrent S hsFour U block target
          htargetVectors).toLinearEquiv
            (model.segment.bong.ambientVector
              ⟨j.val, by
                unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
                omega⟩)) =
      ((model.segment.bong.ambientVector
          ⟨j.val, by
            unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
            omega⟩ : model.segment.carrier) :
        (U.left.carrier × S.left.carrier) × U.right.carrier) := by
  dsimp only
  let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let i : Fin (lemma714TypeIIBaseLength n s) :=
    ⟨j.val, by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega⟩
  change E.productEmbedding
      ((b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond
        hthird hsCurrent hcurrent S hsFour U block target
        htargetVectors).toLinearEquiv
          (model.segment.bong.ambientVector i)) =
    ((model.segment.bong.ambientVector i : model.segment.carrier) :
      (U.left.carrier × S.left.carrier) × U.right.carrier)
  simp only [lemma714TypeIIOuterSegmentToStopProduct,
    lemma714TypeIIOuterSegmentToBinaryRight, Lattice.Isometry.trans,
    LinearEquiv.trans_apply]
  rw [b.lemma714TypeIIOuterSegmentToStopSegment_apply_ambientVector R s D
    hfirst hsecond hthird hsCurrent S hsFour U block target htargetVectors i]
  have hblock :
      (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U block
        target htargetVectors hsecond hcurrent).toLinearEquiv
          ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
            target).bong.ambientVector i) =
        ((block.toBONG.ambientVector j).1,
          b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
            (block.toBONG.ambientVector j).2) := by
    simpa only [i] using
      b.lemma714TypeIIStopProductIsometry_apply_block R s D hsCurrent S
        hsFour U block target htargetVectors hsecond hcurrent j
  have hmap := congrArg
    (fun z => E.productEmbedding
      ((b.lemma714TypeIIBinaryRightToOuterStop R s D hfirst hsecond hthird
        hsCurrent S hsFour U block target htargetVectors).toLinearEquiv z))
    hblock
  have hemb :
      E.productEmbedding
          ((b.lemma714TypeIIBinaryRightToOuterStop R s D hfirst hsecond
            hthird hsCurrent S hsFour U block target
            htargetVectors).toLinearEquiv
              ((block.toBONG.ambientVector j).1,
                b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
                  (block.toBONG.ambientVector j).2)) =
        ((0, (block.toBONG.ambientVector j).1),
          b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
            (block.toBONG.ambientVector j).2) := by
    exact b.lemma714TypeIIBinaryRightToOuterStop_productEmbedding R s D hfirst
      hsecond hthird hsCurrent S hsFour U block target htargetVectors
        ((block.toBONG.ambientVector j).1,
          b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
            (block.toBONG.ambientVector j).2)
  have hfinal :
      ((0, (block.toBONG.ambientVector j).1),
          b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
            (block.toBONG.ambientVector j).2) =
        ((model.segment.bong.ambientVector i : model.segment.carrier) :
          (U.left.carrier × S.left.carrier) × U.right.carrier) := by
    rw [← b.lemma714TypeIIOuterSegments_coe_ambientVector R s D hfirst
        hsecond hthird hsCurrent S hsFour U block target htargetVectors i,
      b.lemma714TypeIIStopSegment_ambientVector_block R s D hsCurrent S
        hsFour U block target htargetVectors j]
  exact hmap.trans (hemb.trans hfinal)

set_option maxHeartbeats 3000000 in
/-- On every vector after the exceptional ternary block, the completed outer
isometry agrees with the unchanged right-suffix inclusion. -/
theorem lemma714TypeIIOuterSegmentToStopProduct_embedded_suffix
    (j : Fin (n + 2 - s)) :
    let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    E.productEmbedding
        ((b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond
          hthird hsCurrent hcurrent S hsFour U block target
          htargetVectors).toLinearEquiv
            (model.segment.bong.ambientVector
              ⟨3 + j.val, by
                unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
                omega⟩)) =
      ((model.segment.bong.ambientVector
          ⟨3 + j.val, by
            unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
            omega⟩ : model.segment.carrier) :
        (U.left.carrier × S.left.carrier) × U.right.carrier) := by
  dsimp only
  let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let i : Fin (lemma714TypeIIBaseLength n s) :=
    ⟨3 + j.val, by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega⟩
  let y :=
    (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.ambientVector
      ⟨j.val + 1, by omega⟩
  change E.productEmbedding
      ((b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond
        hthird hsCurrent hcurrent S hsFour U block target
        htargetVectors).toLinearEquiv
          (model.segment.bong.ambientVector i)) =
    ((model.segment.bong.ambientVector i : model.segment.carrier) :
      (U.left.carrier × S.left.carrier) × U.right.carrier)
  simp only [lemma714TypeIIOuterSegmentToStopProduct,
    lemma714TypeIIOuterSegmentToBinaryRight, Lattice.Isometry.trans,
    LinearEquiv.trans_apply]
  rw [b.lemma714TypeIIOuterSegmentToStopSegment_apply_ambientVector R s D
    hfirst hsecond hthird hsCurrent S hsFour U block target htargetVectors i]
  have hsuffix :
      (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U block
        target htargetVectors hsecond hcurrent).toLinearEquiv
          ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
            target).bong.ambientVector i) =
        (0, y) := by
    simpa only [i, y] using
      b.lemma714TypeIIStopProductIsometry_apply_suffix R s D hsCurrent S
        hsFour U block target htargetVectors hsecond hcurrent j
  have hmap := congrArg
    (fun z => E.productEmbedding
      ((b.lemma714TypeIIBinaryRightToOuterStop R s D hfirst hsecond hthird
        hsCurrent S hsFour U block target htargetVectors).toLinearEquiv z))
    hsuffix
  have hemb :
      E.productEmbedding
          ((b.lemma714TypeIIBinaryRightToOuterStop R s D hfirst hsecond
            hthird hsCurrent S hsFour U block target
            htargetVectors).toLinearEquiv (0, y)) =
        ((0, 0), y) := by
    exact b.lemma714TypeIIBinaryRightToOuterStop_productEmbedding R s D hfirst
      hsecond hthird hsCurrent S hsFour U block target htargetVectors (0, y)
  have hfinal :
      ((0, 0), y) =
        ((model.segment.bong.ambientVector i : model.segment.carrier) :
          (U.left.carrier × S.left.carrier) × U.right.carrier) := by
    rw [← b.lemma714TypeIIOuterSegments_coe_ambientVector R s D hfirst
        hsecond hthird hsCurrent S hsFour U block target htargetVectors i,
      b.lemma714TypeIIStopSegment_ambientVector_suffix R s D hsCurrent S
        hsFour U block target htargetVectors j]
  exact hmap.trans (hemb.trans hfinal)

set_option maxHeartbeats 3000000 in
/-- The completed outer stopping isometry commutes with the ambient inclusion
on every vector of the automatically extracted stopping segment. -/
theorem lemma714TypeIIOuterSegmentToStopProduct_embedded
    (i : Fin (lemma714TypeIIBaseLength n s)) :
    let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    E.productEmbedding
        ((b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond
          hthird hsCurrent hcurrent S hsFour U block target
          htargetVectors).toLinearEquiv
            (model.segment.bong.ambientVector i)) =
      ((model.segment.bong.ambientVector i : model.segment.carrier) :
        (U.left.carrier × S.left.carrier) × U.right.carrier) := by
  dsimp only
  let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  change E.productEmbedding
      ((b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond
        hthird hsCurrent hcurrent S hsFour U block target
        htargetVectors).toLinearEquiv
          (model.segment.bong.ambientVector i)) =
    ((model.segment.bong.ambientVector i : model.segment.carrier) :
      (U.left.carrier × S.left.carrier) × U.right.carrier)
  by_cases hi : i.val < 3
  · let j : Fin 3 := ⟨i.val, hi⟩
    have hij :
        (⟨j.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ : Fin (lemma714TypeIIBaseLength n s)) = i := by
      apply Fin.ext
      rfl
    have h :=
      b.lemma714TypeIIOuterSegmentToStopProduct_embedded_block R s D hfirst
        hsecond hthird hsCurrent hcurrent S hsFour U block target
        htargetVectors j
    dsimp only at h
    simpa only [hij] using h
  · let j : Fin (n + 2 - s) :=
      ⟨i.val - 3, by
        have hlt := i.isLt
        unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail at hlt
        omega⟩
    have hij :
        (⟨3 + j.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ : Fin (lemma714TypeIIBaseLength n s)) = i := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h :=
      b.lemma714TypeIIOuterSegmentToStopProduct_embedded_suffix R s D hfirst
        hsecond hthird hsCurrent hcurrent S hsFour U block target
        htargetVectors j
    dsimp only at h
    simpa only [hij] using h

set_option maxHeartbeats 3000000 in
/-- The completed stopping isometry sends every extracted segment vector to
the corresponding literal base vector at the hidden stopping node. -/
theorem lemma714TypeIIOuterSegmentToStopProduct_apply_ambientVector
    (i : Fin (lemma714TypeIIBaseLength n s)) :
    let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
      hsCurrent S hsFour U block target htargetVectors
    (b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond hthird
      hsCurrent hcurrent S hsFour U block target
      htargetVectors).toLinearEquiv
        (model.segment.bong.ambientVector i) =
      E.base.ambientVector i := by
  dsimp only
  let model := b.lemma714TypeIIOuterModel R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  let E := b.lemma714TypeIIOuterStopSource R s D hfirst hsecond hthird
    hsCurrent S hsFour U block target htargetVectors
  change
    (b.lemma714TypeIIOuterSegmentToStopProduct R s D hfirst hsecond hthird
      hsCurrent hcurrent S hsFour U block target
      htargetVectors).toLinearEquiv
        (model.segment.bong.ambientVector i) =
      E.base.ambientVector i
  have hbase :
      E.productEmbedding (E.base.ambientVector i) =
        ((model.segment.bong.ambientVector i : model.segment.carrier) :
          (U.left.carrier × S.left.carrier) × U.right.carrier) := by
    rw [BONG.OrthogonalPrefixRawSeed.StopSourceData.productEmbedding_apply,
      E.baseAmbientVector_eq, model.extraction.baseAmbientVector_eq,
      model.segment.ambientVector_eq]
    apply congrArg
    apply Fin.ext
    rfl
  apply E.productEmbedding_injective
  exact
    (b.lemma714TypeIIOuterSegmentToStopProduct_embedded R s D hfirst hsecond
      hthird hsCurrent hcurrent S hsFour U block target htargetVectors i).trans
        hbase.symm

end StopBridge

end BONG.GoodBONG

end Bong
