/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710General

/-!
# Beli (2019), Lemma 7.10: automatic unchanged-prefix extraction

The paper-facing hypothesis says that the first `steps` vectors of the
candidate BONG are the unchanged vectors `(x_i, 0)`.  This file turns that
literal vector agreement into the dependent `OrthogonalPrefixRawSeed` used
by the general two-endpoint theorem.  At every recursive step the candidate
tail is transported through the canonical identification
`(x,0)⊥ ≃ x⊥ × W`.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w

namespace OrthogonalPrefixRawSeed

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat}

/-- Embed an unchanged-prefix index into the source BONG. -/
def prefixSourceIndex (hsteps : steps ≤ n) (i : Fin steps) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt hsteps⟩

@[simp]
theorem prefixSourceIndex_val (hsteps : steps ≤ n) (i : Fin steps) :
    (prefixSourceIndex hsteps i).val = i.val :=
  rfl

/-- The dependent seed together with its literal stopping-block vectors. -/
structure TargetPrefixExtraction
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {N : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps)) where
  seed : OrthogonalPrefixRawSeed r M baseLength (steps := steps) source
  baseAmbientVector_eq : ∀ j : Fin baseLength,
    seed.baseAmbientVector j =
      target.ambientVector (orthogonalProductRightIndex steps j)

/--
Extract the raw prefix seed directly from literal agreement of the candidate
prefix with the source prefix.  The stopping BONG is the recursively
transported candidate suffix; its lattice is intentionally left unidentified
until the reverse-dual endpoint certificate is applied.
-/
noncomputable def extractTargetPrefix
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {N : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0)) :
    TargetPrefixExtraction (M := M) source hsteps target := by
  induction source generalizing steps with
  | nil q L exhausted =>
      have hzero : steps = 0 := by omega
      subst steps
      refine
        { seed := .stop (BONG.nil q L exhausted)
            (target.castLength (Nat.add_zero baseLength))
          baseAmbientVector_eq := ?_ }
      intro j
      change (target.castLength (Nat.add_zero baseLength)).ambientVector j =
        target.ambientVector (orthogonalProductRightIndex 0 j)
      rw [ambientVector_castLength]
      apply congrArg target.ambientVector
      apply Fin.ext
      simp [orthogonalProductRightIndex]
  | @cons V _ _ q L n x generator anisotropic tail ih =>
      cases steps with
      | zero =>
          refine
            { seed := .stop (BONG.cons x generator anisotropic tail)
                (target.castLength (Nat.add_zero baseLength))
              baseAmbientVector_eq := ?_ }
          intro j
          change (target.castLength (Nat.add_zero baseLength)).ambientVector j =
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
              have han : targetAnisotropic = anisotropic.orthogonalSum_inl :=
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
              let tailExtraction := ih hk mappedTarget mappedLeftVectors
              refine
                { seed := .cons generator anisotropic tail tailExtraction.seed
                  baseAmbientVector_eq := ?_ }
              intro j
              change
                (((Lattice.projectedOrthogonalProductIsometry
                    (q := q) (r := r) (L := L) (M := M)
                    anisotropic).symm.toLinearEquiv
                      (tailExtraction.seed.baseAmbientVector j) :
                    (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W) =
                  (BONG.cons (x, 0) targetGenerator
                    anisotropic.orthogonalSum_inl targetTail).ambientVector
                      (orthogonalProductRightIndex (k + 1) j)
              rw [tailExtraction.baseAmbientVector_eq j, ambientVector_map]
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

/-- The raw seed component of `extractTargetPrefix`. -/
noncomputable def ofTargetPrefix
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {N : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0)) :
    OrthogonalPrefixRawSeed r M baseLength (steps := steps) source :=
  (extractTargetPrefix (M := M) source hsteps target leftVectors).seed

/-- The stopping block extracted from a target prefix transports back to the
literal suffix block of that target. -/
theorem baseAmbientVector_ofTargetPrefix
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {N : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0))
    (j : Fin baseLength) :
    (ofTargetPrefix (M := M) source hsteps target leftVectors).baseAmbientVector j =
      target.ambientVector (orthogonalProductRightIndex steps j) :=
  (extractTargetPrefix (M := M) source hsteps target
    leftVectors).baseAmbientVector_eq j

/-- The single reverse-dual endpoint certificate required at the stopping
node of a raw seed.  Prefix `cons` nodes carry no additional mathematical
data, so this type recursively discards them. -/
def StopDualEndpointData
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    Type (max (u + 1) (v + 1) (w + 1)) := by
  induction S with
  | stop source base =>
      exact OrthogonalPrefixRawSeed.DualEndpointCertificate r M
        (OrthogonalPrefixRawSeed.stop (M := M) source base)
  | cons _ _ _ _ tailData =>
      exact tailData

/-- Lift the unique stopping-node certificate through all unchanged-prefix
constructors. -/
noncomputable def dualEndpointCertificateOfStopData
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    S.StopDualEndpointData →
      OrthogonalPrefixRawSeed.DualEndpointCertificate r M S := by
  induction S with
  | stop source base =>
      exact fun certificate => certificate
  | cons generator anisotropic tail tailSeed ih =>
      exact fun certificate =>
        .cons generator anisotropic tail tailSeed (ih certificate)

end OrthogonalPrefixRawSeed

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Reversing, normalizing, and swapping an unchanged right-suffix vector
turns it into the corresponding left-prefix vector of the swapped dual. -/
theorem swappedReverseDualVector_prefix_eq_of_suffixVectors
    {rightLength baseLength dualSteps : Nat}
    {N : Lattice K (V × W)}
    (base : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + dualSteps))
    (right : BONG W r M rightLength)
    (hsteps : dualSteps ≤ rightLength)
    (suffixVectors : ∀ i : Fin dualSteps,
      base.ambientVector
          (Fin.rev (orthogonalProductLeftIndex baseLength i)) =
        (0, right.ambientVector
          (Fin.rev (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i))))
    (i : Fin dualSteps) :
    (LinearEquiv.prodComm K V W)
        (base.reverseDualVector
          (orthogonalProductLeftIndex baseLength i)) =
      (right.reverseDualVector
        (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i), 0) := by
  let ib : Fin (baseLength + dualSteps) :=
    Fin.rev (orthogonalProductLeftIndex baseLength i)
  let ir : Fin rightLength :=
    Fin.rev (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i)
  have hvalue : base.value ib = right.value ir := by
    calc
      base.value ib = (q.orthogonalSum r).quadratic
          (base.ambientVector ib) := (base.quadratic_ambientVector ib).symm
      _ = (q.orthogonalSum r).quadratic
          (0, right.ambientVector ir) := by
        rw [suffixVectors i]
      _ = r.quadratic (right.ambientVector ir) := by
        simp [QuadraticSpace.orthogonalSum_quadratic_apply]
      _ = right.value ir := right.quadratic_ambientVector ir
  have hunit : base.valueUnit ib = right.valueUnit ir := by
    apply Units.ext
    exact hvalue
  change
    (LinearEquiv.prodComm K V W)
        (((base.valueUnit ib)⁻¹ : K) • base.ambientVector ib) =
      (((right.valueUnit ir)⁻¹ : K) • right.ambientVector ir, 0)
  rw [suffixVectors i, hunit]
  simp [ir]

/-- Literal unchanged suffix vectors produce the complete prefix-vector
premise consumed by `DualEndpointCertificate.stopOfTargetPrefix`. -/
theorem swappedReverseDual_prefixVectors_of_suffixVectors
    {rightLength baseLength dualSteps : Nat}
    {N : Lattice K (V × W)}
    (base : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + dualSteps))
    (right : BONG W r M rightLength)
    (hsteps : dualSteps ≤ rightLength)
    (suffixVectors : ∀ i : Fin dualSteps,
      base.ambientVector
          (Fin.rev (orthogonalProductLeftIndex baseLength i)) =
        (0, right.ambientVector
          (Fin.rev (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i))))
    {rightFactorDual : GoodBONG r (Lattice.dualLattice r M)
      rightLength}
    (rightDualVectors : ∀ i,
      rightFactorDual.toBONG.ambientVector i = right.reverseDualVector i)
    {targetDualLattice : Lattice K (W × V)}
    {targetDual : GoodBONG (r.orthogonalSum q) targetDualLattice
      (baseLength + dualSteps)}
    (targetDualVectors : ∀ i,
      targetDual.toBONG.ambientVector i =
        (LinearEquiv.prodComm K V W) (base.reverseDualVector i)) :
    ∀ i : Fin dualSteps,
      targetDual.toBONG.ambientVector
          (orthogonalProductLeftIndex baseLength i) =
        (rightFactorDual.toBONG.ambientVector
          (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i), 0) := by
  intro i
  rw [targetDualVectors, rightDualVectors]
  exact base.swappedReverseDualVector_prefix_eq_of_suffixVectors
    right hsteps suffixVectors i

namespace OrthogonalPrefixRawSeed.DualEndpointCertificate

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Build the stopping certificate from literal unchanged-prefix agreement
on the swapped dual target.  The dual-side raw seed, its source-index
coherence, and both vector blocks are generated automatically; the only
geometric input left is the stopping product identity for the replaced
block. -/
noncomputable def stopOfTargetPrefix
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
    (dualStopEq :
      (OrthogonalPrefixRawSeed.ofTargetPrefix
        (M := Lattice.dualLattice q L) rightFactorDual.toBONG hsteps
        targetDual.toBONG leftVectors).StopLatticeEq)
    (hlast : ∀ hpos : 0 < dualSteps,
      rightFactorDual.order ⟨dualSteps - 1, by omega⟩ ≤
        leftFactorDual.order 0) :
    OrthogonalPrefixRawSeed.DualEndpointCertificate r M
      (OrthogonalPrefixRawSeed.stop (M := M) source base) := by
  let dualRaw := OrthogonalPrefixRawSeed.ofTargetPrefix
    (M := Lattice.dualLattice q L) rightFactorDual.toBONG hsteps
    targetDual.toBONG leftVectors
  let seed := dualRaw.toSeed dualStopEq
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
            dualRaw.baseAmbientVector j :=
          (OrthogonalPrefixRawSeed.baseAmbientVector_ofTargetPrefix
            (M := Lattice.dualLattice q L) rightFactorDual.toBONG hsteps
            targetDual.toBONG leftVectors j).symm
        _ = seed.baseAmbientVector j :=
          (dualRaw.baseAmbientVector_toSeed dualStopEq j).symm)

/-- Build the stopping certificate directly from the unchanged suffix of the
original candidate.  Reverse-dual vector realizations for the right factor
and for the swapped candidate turn that suffix into the literal prefix
required by `stopOfTargetPrefix`; callers no longer provide a separate
dual-prefix coherence family. -/
noncomputable def stopOfSuffixVectors
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
    (dualStopEq :
      (OrthogonalPrefixRawSeed.ofTargetPrefix
        (M := Lattice.dualLattice q L) rightFactorDual.toBONG hsteps
        targetDual.toBONG
        (base.swappedReverseDual_prefixVectors_of_suffixVectors
          right hsteps suffixVectors rightDualVectors
          targetDualVectors)).StopLatticeEq)
    (hlast : ∀ hpos : 0 < dualSteps,
      rightFactorDual.order ⟨dualSteps - 1, by omega⟩ ≤
        leftFactorDual.order 0) :
    OrthogonalPrefixRawSeed.DualEndpointCertificate r M
      (OrthogonalPrefixRawSeed.stop (M := M) source base) := by
  let leftVectors :=
    base.swappedReverseDual_prefixVectors_of_suffixVectors
      right hsteps suffixVectors rightDualVectors targetDualVectors
  exact stopOfTargetPrefix source base rightFactorDual hsteps leftFactorDual
    targetDual leftVectors dualStopEq hlast

end OrthogonalPrefixRawSeed.DualEndpointCertificate

namespace GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n rightLength : Nat}

/-- Paper-facing general Lemma 7.10 after automatic extraction of the
unchanged prefix.  The caller supplies literal prefix agreement and only the
reverse-dual certificate at the extracted stopping block; all original-side
seed and suffix-vector coherence data are generated internally. -/
theorem beli2019Lemma710General_of_targetPrefix
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
    (dualCertificate :
      OrthogonalPrefixRawSeed.DualEndpointCertificate r M
        (OrthogonalPrefixRawSeed.ofTargetPrefix (M := M)
          b.toBONG hsteps target.toBONG leftVectors))
    (hlast : ∀ hpos : 0 < steps,
      b.order ⟨steps - 1, by omega⟩ ≤ right.order 0) :
    N = Lattice.product L M := by
  let raw := OrthogonalPrefixRawSeed.ofTargetPrefix (M := M)
    b.toBONG hsteps target.toBONG leftVectors
  apply b.beli2019Lemma710General hsteps right raw dualCertificate hlast
    target.toBONG target.good
  · intro i
    have hindex : raw.sourceIndex i =
        OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact leftVectors i
  · intro j
    exact (OrthogonalPrefixRawSeed.baseAmbientVector_ofTargetPrefix
      (M := M) b.toBONG hsteps target.toBONG leftVectors j).symm

/-- The same paper-facing theorem with only the reverse-dual certificate at
the actual stopping suffix.  All certificates along the unchanged prefix are
generated automatically. -/
theorem beli2019Lemma710General_of_targetPrefixStop
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
    (stopCertificate :
      (OrthogonalPrefixRawSeed.ofTargetPrefix (M := M)
        b.toBONG hsteps target.toBONG leftVectors).StopDualEndpointData)
    (hlast : ∀ hpos : 0 < steps,
      b.order ⟨steps - 1, by omega⟩ ≤ right.order 0) :
    N = Lattice.product L M := by
  let raw := OrthogonalPrefixRawSeed.ofTargetPrefix (M := M)
    b.toBONG hsteps target.toBONG leftVectors
  exact b.beli2019Lemma710General_of_targetPrefix hsteps right target
    leftVectors (raw.dualEndpointCertificateOfStopData stopCertificate) hlast

end GoodBONG

end BONG

end Bong
