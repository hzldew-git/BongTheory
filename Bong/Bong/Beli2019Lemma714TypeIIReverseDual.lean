/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIStopSegment

/-!
# Beli (2019), Lemma 7.14(ii): reverse-dual realizations at the Type-II stop

The general case of Lemma 7.10 reverses and dualizes the stopping suffix.
This file fixes concrete good BONG realizations of all four reverse-dual
families occurring in that argument: the complete stopping suffix, its right
factor, the rescaled binary factor, and the exceptional ternary block.

Each choice is accompanied by its literal vector formula.  Consequently all
later coordinate calculations can rewrite to `BONG.reverseDualVector` rather
than carrying existential witnesses.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private theorem lemma714TypeIIReverseDual_two_le_rank (n : Nat) :
    2 ≤ n + 3 := by
  omega

/-- A quadratic-preserving linear embedding carries a reversed dual vector
to the corresponding right-factor reversed dual vector whenever the reversed
original vectors agree. -/
private theorem map_reverseDualVector_eq_right
    {X Y P : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    [AddCommGroup P] [Module K P]
    {p : QuadraticSpace K P} {qx : QuadraticSpace K X}
    {qy : QuadraticSpace K Y}
    {LP : Lattice K P} {MY : Lattice K Y}
    {aLength rightLength : Nat}
    (a : BONG P p LP aLength) (right : BONG Y qy MY rightLength)
    (embed : P →ₗ[K] X × Y)
    (mapQuadratic : ∀ z, (qx.orthogonalSum qy).quadratic (embed z) =
      p.quadratic z)
    (i : Fin aLength) (j : Fin rightLength)
    (vectors : embed (a.ambientVector (Fin.rev i)) =
      (0, right.ambientVector (Fin.rev j))) :
    embed (a.reverseDualVector i) = (0, right.reverseDualVector j) := by
  have hvalue : a.value (Fin.rev i) = right.value (Fin.rev j) := by
    calc
      a.value (Fin.rev i) = p.quadratic (a.ambientVector (Fin.rev i)) :=
        (a.quadratic_ambientVector (Fin.rev i)).symm
      _ = (qx.orthogonalSum qy).quadratic
          (embed (a.ambientVector (Fin.rev i))) :=
        (mapQuadratic _).symm
      _ = (qx.orthogonalSum qy).quadratic
          (0, right.ambientVector (Fin.rev j)) := by rw [vectors]
      _ = qy.quadratic (right.ambientVector (Fin.rev j)) := by
        simp [QuadraticSpace.orthogonalSum_quadratic_apply]
      _ = right.value (Fin.rev j) :=
        right.quadratic_ambientVector (Fin.rev j)
  have hunit : a.valueUnit (Fin.rev i) = right.valueUnit (Fin.rev j) := by
    apply Units.ext
    simpa only [BONG.coe_valueUnit] using hvalue
  simp only [BONG.reverseDualVector, BONG.dualVector, map_smul]
  rw [vectors, hunit]
  simp

/-- Two quadratic-preserving linear embeddings carry equal reversed original
vectors to equal normalized reversed dual vectors. -/
private theorem map_reverseDualVector_eq_of_maps
    {P Q Z : Type v}
    [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q]
    [AddCommGroup Z] [Module K Z]
    {p : QuadraticSpace K P} {q' : QuadraticSpace K Q}
    {zForm : QuadraticSpace K Z}
    {LP : Lattice K P} {LQ : Lattice K Q}
    {pLength qLength : Nat}
    (a : BONG P p LP pLength) (c : BONG Q q' LQ qLength)
    (f : P →ₗ[K] Z) (g : Q →ₗ[K] Z)
    (fQuadratic : ∀ x, zForm.quadratic (f x) = p.quadratic x)
    (gQuadratic : ∀ y, zForm.quadratic (g y) = q'.quadratic y)
    (i : Fin pLength) (j : Fin qLength)
    (vectors : f (a.ambientVector (Fin.rev i)) =
      g (c.ambientVector (Fin.rev j))) :
    f (a.reverseDualVector i) = g (c.reverseDualVector j) := by
  have hvalue : a.value (Fin.rev i) = c.value (Fin.rev j) := by
    calc
      a.value (Fin.rev i) = p.quadratic (a.ambientVector (Fin.rev i)) :=
        (a.quadratic_ambientVector (Fin.rev i)).symm
      _ = zForm.quadratic (f (a.ambientVector (Fin.rev i))) :=
        (fQuadratic _).symm
      _ = zForm.quadratic (g (c.ambientVector (Fin.rev j))) := by
        rw [vectors]
      _ = q'.quadratic (c.ambientVector (Fin.rev j)) := gQuadratic _
      _ = c.value (Fin.rev j) := c.quadratic_ambientVector (Fin.rev j)
  have hunit : a.valueUnit (Fin.rev i) = c.valueUnit (Fin.rev j) := by
    apply Units.ext
    simpa only [BONG.coe_valueUnit] using hvalue
  simp only [BONG.reverseDualVector, BONG.dualVector, map_smul]
  rw [vectors, hunit]

/-- Any concrete realization of the normalized reversed dual vectors has
the reversed negated order sequence. -/
private theorem order_eq_neg_reverse_of_ambientVector_eq
    {X : Type v} [AddCommGroup X] [Module K X]
    {p : QuadraticSpace K X} {LP : Lattice K X}
    {length : Nat}
    (a : BONG X p LP length)
    {LD : Lattice K X} (dual : GoodBONG p LD length)
    (vectors : ∀ i, dual.toBONG.ambientVector i =
      a.reverseDualVector i)
    (i : Fin length) :
    dual.order i = -a.order (Fin.rev i) := by
  change dual.toBONG.order i = -a.order (Fin.rev i)
  apply WithTop.coe_injective
  rw [BONG.coe_order, ← dual.toBONG.quadratic_ambientVector i,
    vectors i, a.ord_quadratic_reverseDualVector]

section ReverseDual

variable [DyadicDiscriminantClassLaws K]
variable [BONGReverseDualLaws.{u, v} K]
variable (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
variable (D : Lemma714StoppingData b R s)
variable (hsCurrent : s < n + 3)
variable (S : BONG.TwoBlockSplitWitness b.toBONG 2
  (lemma714TypeIIReverseDual_two_le_rank n))
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

/-- The linear embedding of the exceptional ternary block into the literal
stopping-segment ambient space. -/
noncomputable def lemma714TypeIIBlockToStopLinearMap :
    S.left.carrier ×
        (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier →ₗ[K]
      (U.left.carrier × S.left.carrier) × U.right.carrier where
  toFun z :=
    ((0, z.1), b.lemma714TypeIILineToRight S s D.two_le hsCurrent U z.2)
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      rfl
  map_smul' c x := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      rfl

@[simp]
theorem lemma714TypeIIBlockToStopLinearMap_apply
    (z : S.left.carrier ×
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier) :
    b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U z =
      ((0, z.1),
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U z.2) :=
  rfl

/-- The block embedding preserves the quadratic form. -/
theorem lemma714TypeIIBlockToStopLinearMap_quadratic
    (z : S.left.carrier ×
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier) :
    (((((q.restrict S.right.carrier S.right.nondegenerate).restrict
            U.left.carrier U.left.nondegenerate).orthogonalSum
          (q.restrict S.left.carrier S.left.nondegenerate)).orthogonalSum
        ((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate))).quadratic
        (b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U z) =
      ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
        ((q.restrict S.right.carrier S.right.nondegenerate).restrict
          (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier
          (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).nondegenerate)).quadratic
        z := by
  simp only [lemma714TypeIIBlockToStopLinearMap_apply,
    QuadraticSpace.orthogonalSum_quadratic_apply,
    QuadraticSpace.quadratic_zero, zero_add, add_right_inj]
  change (q.restrict S.right.carrier S.right.nondegenerate).quadratic
      ((b.lemma714TypeIILineToRight S s D.two_le hsCurrent U z.2 :
        U.right.carrier) : S.right.carrier) =
    (q.restrict S.right.carrier S.right.nondegenerate).quadratic
      (z.2 : S.right.carrier)
  rw [b.lemma714TypeIILineToRight_coe S s D.two_le hsCurrent U]

/-- A fixed good BONG on the integral dual of the complete stopping suffix. -/
noncomputable def lemma714TypeIIStopReverseDual :=
  Classical.choose
    (b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U
      target).exists_reverseDual

/-- The chosen stopping-suffix dual realizes the normalized reversed dual
vectors literally. -/
@[simp]
theorem lemma714TypeIIStopReverseDual_ambientVector
    (i : Fin (lemma714TypeIIBaseLength n s)) :
    (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
      target).toBONG.ambientVector i =
      (b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U
        target).toBONG.reverseDualVector i :=
  Classical.choose_spec
    (b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U
      target).exists_reverseDual i

/-- A fixed reverse-dual good BONG for the right factor
`x_(s+1), ..., x_N`. -/
noncomputable def lemma714TypeIIRightReverseDual :=
  Classical.choose
    (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).exists_reverseDual

/-- Literal vector formula for the chosen right-factor reverse dual. -/
@[simp]
theorem lemma714TypeIIRightReverseDual_ambientVector
    (i : Fin (n + 3 - s)) :
    (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG.ambientVector i =
      (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.reverseDualVector i :=
  Classical.choose_spec
    (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).exists_reverseDual i

/-- The right-factor reverse dual has the reversed negated order sequence. -/
@[simp]
theorem lemma714TypeIIRightReverseDual_order
    (i : Fin (n + 3 - s)) :
    (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).order i =
      -(b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).order
        (Fin.rev i) :=
  order_eq_neg_reverse_of_ambientVector_eq
    (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG
    (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U)
    (b.lemma714TypeIIRightReverseDual_ambientVector R s D hsCurrent
      S U) i

/-- A fixed reverse-dual good BONG for the rescaled initial binary factor. -/
noncomputable def lemma714TypeIIRescaledBinaryReverseDual :=
  Classical.choose
    ((b.lemma714InitialBinary S).lemma714RescaledBinary).exists_reverseDual

/-- Literal vector formula for the chosen binary reverse dual. -/
@[simp]
theorem lemma714TypeIIRescaledBinaryReverseDual_ambientVector
    (i : Fin 2) :
    (b.lemma714TypeIIRescaledBinaryReverseDual S).toBONG.ambientVector i =
      ((b.lemma714InitialBinary S).lemma714RescaledBinary).toBONG.reverseDualVector i :=
  Classical.choose_spec
    ((b.lemma714InitialBinary S).lemma714RescaledBinary).exists_reverseDual i

/-- The rescaled-binary reverse dual has the reversed negated order
sequence. -/
@[simp]
theorem lemma714TypeIIRescaledBinaryReverseDual_order (i : Fin 2) :
    (b.lemma714TypeIIRescaledBinaryReverseDual S).order i =
      -((b.lemma714InitialBinary S).lemma714RescaledBinary).order
        (Fin.rev i) :=
  order_eq_neg_reverse_of_ambientVector_eq
    ((b.lemma714InitialBinary S).lemma714RescaledBinary).toBONG
    (b.lemma714TypeIIRescaledBinaryReverseDual S)
    (b.lemma714TypeIIRescaledBinaryReverseDual_ambientVector S) i

/-- A fixed reverse-dual good BONG for the unary line generated by
`x_(s+1)`. -/
noncomputable def lemma714TypeIILineReverseDual :=
  Classical.choose
    (b.lemma714TypeIILine S s D.two_le hsCurrent).exists_reverseDual

/-- Literal vector formula for the chosen unary reverse dual. -/
@[simp]
theorem lemma714TypeIILineReverseDual_ambientVector (i : Fin 1) :
    (b.lemma714TypeIILineReverseDual R s D hsCurrent S).toBONG.ambientVector i =
      (b.lemma714TypeIILine S s D.two_le hsCurrent).toBONG.reverseDualVector i :=
  Classical.choose_spec
    (b.lemma714TypeIILine S s D.two_le hsCurrent).exists_reverseDual i

/-- Order formula for the unary reverse dual. -/
@[simp]
theorem lemma714TypeIILineReverseDual_order (i : Fin 1) :
    (b.lemma714TypeIILineReverseDual R s D hsCurrent S).order i =
      -(b.lemma714TypeIILine S s D.two_le hsCurrent).order (Fin.rev i) :=
  order_eq_neg_reverse_of_ambientVector_eq
    (b.lemma714TypeIILine S s D.two_le hsCurrent).toBONG
    (b.lemma714TypeIILineReverseDual R s D hsCurrent S)
    (b.lemma714TypeIILineReverseDual_ambientVector R s D hsCurrent S) i

/-- A fixed reverse-dual good BONG for the exceptional ternary block. -/
noncomputable def lemma714TypeIIBlockReverseDual :=
  Classical.choose block.exists_reverseDual

/-- Literal vector formula for the chosen exceptional-block reverse dual. -/
@[simp]
theorem lemma714TypeIIBlockReverseDual_ambientVector (i : Fin 3) :
    (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
      (D := D) (hsCurrent := hsCurrent) (S := S)
      (block := block)).toBONG.ambientVector i =
      block.toBONG.reverseDualVector i :=
  Classical.choose_spec block.exists_reverseDual i

include block htargetVectors

set_option maxHeartbeats 1000000 in
-- Dependent subspace coercions make this elementary coordinate calculation
-- substantially more expensive to elaborate than its mathematical content.
/-- The unchanged part of the right suffix becomes the initial block of the
reverse dual of the complete stopping segment.  The expanded dependent
subspace types make the final elaboration substantially more expensive than
the underlying coordinate calculation. -/
@[simp]
theorem lemma714TypeIIStopReverseDual_ambientVector_prefix
    (i : Fin (n + 2 - s)) :
    (((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
        target).toBONG.ambientVector
        ⟨i.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ :
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).carrier) :
      (U.left.carrier × S.left.carrier) × U.right.carrier) =
      ((0, 0),
        (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG.ambientVector
          ⟨i.val, by omega⟩) := by
  let iStop : Fin (lemma714TypeIIBaseLength n s) :=
    ⟨i.val, by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega⟩
  let iRight : Fin (n + 3 - s) := ⟨i.val, by omega⟩
  let j : Fin (n + 2 - s) := Fin.rev i
  let stopRev : Fin (lemma714TypeIIBaseLength n s) := Fin.rev iStop
  let rightRev : Fin (n + 3 - s) := Fin.rev iRight
  have hstopRev : stopRev =
      ⟨3 + j.val, by
        unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
        omega⟩ := by
    apply Fin.ext
    simp only [stopRev, iStop, j, Fin.rev, lemma714TypeIIBaseLength,
      lemma714TypeIIBaseTail]
    omega
  have hrightRev : rightRev = ⟨j.val + 1, by omega⟩ := by
    apply Fin.ext
    simp only [rightRev, iRight, j, Fin.rev]
    omega
  have hvectors :
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).carrier.subtype
          ((b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG.ambientVector
            (Fin.rev iStop)) =
        ((0, 0),
          (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.ambientVector
            (Fin.rev iRight)) := by
    rw [show Fin.rev iStop = stopRev by rfl,
      show Fin.rev iRight = rightRev by rfl, hstopRev, hrightRev]
    exact b.lemma714TypeIIStopSegment_ambientVector_suffix R s D hsCurrent
      S hsFour U block target htargetVectors j
  have hreverse :
      (((b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG.reverseDualVector
          iStop :
        (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
          target).carrier) :
        (U.left.carrier × S.left.carrier) × U.right.carrier) =
      ((0, 0),
        (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.reverseDualVector
          iRight) := by
    exact map_reverseDualVector_eq_right
      (b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG
      (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).carrier.subtype
      (fun _ => rfl) iStop iRight hvectors
  calc
    _ = (((b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG.reverseDualVector
          iStop :
        (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
          target).carrier) :
        (U.left.carrier × S.left.carrier) × U.right.carrier) := by
      exact congrArg Subtype.val
        (b.lemma714TypeIIStopReverseDual_ambientVector R s D hsCurrent
          S hsFour U target iStop)
    _ = ((0, 0),
        (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.reverseDualVector
          iRight) := hreverse
    _ = _ := by
      rw [← b.lemma714TypeIIRightReverseDual_ambientVector R s D hsCurrent
        S U iRight]

set_option maxHeartbeats 1000000 in
-- The nested carrier coercions make this finite three-coordinate calculation
-- expensive to elaborate, although the proof is only reversal plus scaling.
/-- The last three vectors of the stopping reverse dual are precisely the
embedded reverse dual of the exceptional ternary block. -/
@[simp]
theorem lemma714TypeIIStopReverseDual_ambientVector_block
    (i : Fin 3) :
    (((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
        target).toBONG.ambientVector
        ⟨n + 2 - s + i.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ :
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).carrier) :
      (U.left.carrier × S.left.carrier) × U.right.carrier) =
      b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U
        ((lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
          (D := D) (hsCurrent := hsCurrent) (S := S)
          (block := block)).toBONG.ambientVector i) := by
  let iStop : Fin (lemma714TypeIIBaseLength n s) :=
    ⟨n + 2 - s + i.val, by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega⟩
  let stopRev : Fin (lemma714TypeIIBaseLength n s) := Fin.rev iStop
  have hstopRev : stopRev =
      ⟨(Fin.rev i).val, by
        unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
        omega⟩ := by
    apply Fin.ext
    simp only [stopRev, iStop, Fin.rev, lemma714TypeIIBaseLength,
      lemma714TypeIIBaseTail]
    omega
  have hvectors :
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).carrier.subtype
          ((b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG.ambientVector
            (Fin.rev iStop)) =
        b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U
          (block.toBONG.ambientVector (Fin.rev i)) := by
    rw [show Fin.rev iStop = stopRev by rfl, hstopRev]
    exact b.lemma714TypeIIStopSegment_ambientVector_block R s D hsCurrent
      S hsFour U block target htargetVectors (Fin.rev i)
  have hreverse :
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).carrier.subtype
          ((b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG.reverseDualVector
            iStop) =
        b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U
          (block.toBONG.reverseDualVector i) := by
    exact map_reverseDualVector_eq_of_maps
      (b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG
      block.toBONG
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).carrier.subtype
      (b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U)
      (fun _ => rfl)
      (b.lemma714TypeIIBlockToStopLinearMap_quadratic R s D hsCurrent
        S U)
      iStop i hvectors
  calc
    _ = (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U target).carrier.subtype
        ((b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG.reverseDualVector
          iStop) := by
      exact congrArg Subtype.val
        (b.lemma714TypeIIStopReverseDual_ambientVector R s D hsCurrent
          S hsFour U target iStop)
    _ = b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U
          (block.toBONG.reverseDualVector i) := hreverse
    _ = _ := by
      exact congrArg
        (b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U)
        (b.lemma714TypeIIBlockReverseDual_ambientVector R s D hsCurrent
          S block i).symm

/-- The quadratic values on the unchanged prefix of the stopping reverse
dual agree with the corresponding right-factor reverse-dual values. -/
theorem lemma714TypeIIStopReverseDual_value_prefix
    (i : Fin (n + 2 - s)) :
    (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U target).value
        ⟨i.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ =
      (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).value
        ⟨i.val, by omega⟩ := by
  let iStop : Fin (lemma714TypeIIBaseLength n s) :=
    ⟨i.val, by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega⟩
  let iRight : Fin (n + 3 - s) := ⟨i.val, by omega⟩
  change
    (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
      target).toBONG.value iStop =
    (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG.value
      iRight
  have h := b.lemma714TypeIIStopReverseDual_ambientVector_prefix R s D
    hsCurrent S hsFour U block target htargetVectors i
  let stopForm :=
    ((((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.left.carrier U.left.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)).orthogonalSum
      ((q.restrict S.right.carrier S.right.nondegenerate).restrict
        U.right.carrier U.right.nondegenerate))
  calc
    _ = (stopForm.restrict
          (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
            target).carrier
          (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
            target).nondegenerate).quadratic
        ((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
          target).toBONG.ambientVector iStop) :=
      (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
        target).toBONG.quadratic_ambientVector iStop |>.symm
    _ = stopForm.quadratic
        ((((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
          target).toBONG.ambientVector iStop :
            (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
              target).carrier) :
          (U.left.carrier × S.left.carrier) × U.right.carrier)) := rfl
    _ = stopForm.quadratic
        ((0, 0),
          (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG.ambientVector
            iRight) := by
      exact congrArg stopForm.quadratic h
    _ = (((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate).quadratic
        ((b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG.ambientVector
          iRight)) := by
      simp [stopForm, QuadraticSpace.orthogonalSum_quadratic_apply]
    _ = _ :=
      (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG.quadratic_ambientVector
        iRight

/-- The last three quadratic values of the stopping reverse dual are the
values of the exceptional-block reverse dual. -/
theorem lemma714TypeIIStopReverseDual_value_block (i : Fin 3) :
    (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U target).value
        ⟨n + 2 - s + i.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ =
      (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
        (D := D) (hsCurrent := hsCurrent) (S := S)
        (block := block)).value i := by
  let iStop : Fin (lemma714TypeIIBaseLength n s) :=
    ⟨n + 2 - s + i.val, by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega⟩
  let blockDual := lemma714TypeIIBlockReverseDual (b := b) (R := R)
    (s := s) (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)
  change
    (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
      target).toBONG.value iStop = blockDual.toBONG.value i
  have h := b.lemma714TypeIIStopReverseDual_ambientVector_block R s D
    hsCurrent S hsFour U block target htargetVectors i
  let stopForm :=
    ((((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.left.carrier U.left.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)).orthogonalSum
      ((q.restrict S.right.carrier S.right.nondegenerate).restrict
        U.right.carrier U.right.nondegenerate))
  calc
    _ = (stopForm.restrict
          (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
            target).carrier
          (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
            target).nondegenerate).quadratic
        ((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
          target).toBONG.ambientVector iStop) :=
      (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
        target).toBONG.quadratic_ambientVector iStop |>.symm
    _ = stopForm.quadratic
        ((((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
          target).toBONG.ambientVector iStop :
            (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
              target).carrier) :
          (U.left.carrier × S.left.carrier) × U.right.carrier)) := rfl
    _ = stopForm.quadratic
        (b.lemma714TypeIIBlockToStopLinearMap R s D hsCurrent S U
          (blockDual.toBONG.ambientVector i)) := by
      exact congrArg stopForm.quadratic h
    _ = ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
          ((q.restrict S.right.carrier S.right.nondegenerate).restrict
            (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier
            (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).nondegenerate)).quadratic
        (blockDual.toBONG.ambientVector i) :=
      b.lemma714TypeIIBlockToStopLinearMap_quadratic R s D hsCurrent
        S U (blockDual.toBONG.ambientVector i)
    _ = _ := blockDual.toBONG.quadratic_ambientVector i

end ReverseDual

end BONG.GoodBONG

end Bong
