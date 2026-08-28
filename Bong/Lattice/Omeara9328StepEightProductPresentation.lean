/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightInsertion
import Bong.Bong.Beli2009ComponentwiseAssembly
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Product presentation of O'Meara 93:28, Step 8

The Jordan decomposition constructed in the preceding file has block order

`L₀, s₀ π A(0,0), L₁, ..., Lₜ`.

This file gathers the inserted plane to the left and identifies every raised
old block with the corresponding component of the original decomposition.
The resulting integral isometry presents the enlarged block product as the
orthogonal product of the inserted hyperbolic plane and the original lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

variable (J : JordanDecomposition q L (n + 2))

/-- Coordinatewise identification of the raised old tail with the coordinate
product of the original tail components. -/
noncomputable def stepEightOldTailProductIsometry :
    Isometry
      (BONG.blockOrthogonalForm n
        (fun i : Fin (n + 1) => J.stepEightCarrier i.succ.succ)
        (fun i => J.stepEightForm i.succ.succ))
      (BONG.blockOrthogonalForm n
        (fun i : Fin (n + 1) => (J.component i.succ).carrier)
        (fun i => (J.component i.succ).space))
      (BONG.blockProductLattice n
        (fun i : Fin (n + 1) => J.stepEightCarrier i.succ.succ)
        (fun i => J.stepEightLattice i.succ.succ))
      (BONG.blockProductLattice n
        (fun i : Fin (n + 1) => (J.component i.succ).carrier)
        (fun i => (J.component i.succ).lattice)) :=
  BONG.blockProductLatticeIsometry
    (fun i : Fin (n + 1) => J.stepEightForm i.succ.succ)
    (fun i => (J.component i.succ).space)
    (fun i => J.stepEightLattice i.succ.succ)
    (fun i => (J.component i.succ).lattice)
    J.stepEightOldTailLatticeIsometry

/-- The full Step-8 coordinate product is the inserted hyperbolic plane
orthogonally adjoined to the original lattice. -/
noncomputable def stepEightProductPresentation :
    Isometry
      (BONG.blockOrthogonalForm (n + 2) J.stepEightCarrier J.stepEightForm)
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q)
      (BONG.blockProductLattice (n + 2)
        J.stepEightCarrier J.stepEightLattice)
      (product (hyperbolicPlaneLattice (K := K)) L) := by
  let tailCarrier : Fin (n + 2) → Type (max u v) :=
    fun i => J.stepEightCarrier i.succ
  let tailForm : ∀ i, QuadraticSpace K (tailCarrier i) :=
    fun i => J.stepEightForm i.succ
  let tailLattice : ∀ i, Lattice K (tailCarrier i) :=
    fun i => J.stepEightLattice i.succ
  let restCarrier : Fin (n + 1) → Type (max u v) :=
    fun i => J.stepEightCarrier i.succ.succ
  let restForm : ∀ i, QuadraticSpace K (restCarrier i) :=
    fun i => J.stepEightForm i.succ.succ
  let restLattice : ∀ i, Lattice K (restCarrier i) :=
    fun i => J.stepEightLattice i.succ.succ
  let oldTailCarrier : Fin (n + 1) → Type v :=
    fun i => (J.component i.succ).carrier
  let oldTailForm : ∀ i, QuadraticSpace K (oldTailCarrier i) :=
    fun i => (J.component i.succ).space
  let oldTailLattice : ∀ i, Lattice K (oldTailCarrier i) :=
    fun i => (J.component i.succ).lattice
  let tailBlockForm := BONG.blockOrthogonalForm (n + 1)
    tailCarrier tailForm
  let tailBlockLattice := BONG.blockProductLattice (n + 1)
    tailCarrier tailLattice
  let restBlockForm := BONG.blockOrthogonalForm n restCarrier restForm
  let restBlockLattice := BONG.blockProductLattice n restCarrier restLattice
  let oldTailBlockForm := BONG.blockOrthogonalForm n
    oldTailCarrier oldTailForm
  let oldTailBlockLattice := BONG.blockProductLattice n
    oldTailCarrier oldTailLattice
  let firstSplit := BONG.blockOrthogonalSplitLatticeIsometry
    (n + 1) J.stepEightCarrier J.stepEightForm J.stepEightLattice
  let secondSplit := BONG.blockOrthogonalSplitLatticeIsometry
    n tailCarrier tailForm tailLattice
  let exposeSecond : Isometry
      ((J.stepEightForm 0).orthogonalSum tailBlockForm)
      ((J.stepEightForm 0).orthogonalSum
        ((J.stepEightForm 1).orthogonalSum restBlockForm))
      (product (J.stepEightLattice 0) tailBlockLattice)
      (product (J.stepEightLattice 0)
        (product (J.stepEightLattice 1) restBlockLattice)) :=
    (Isometry.refl (J.stepEightForm 0) (J.stepEightLattice 0))
      |>.orthogonalProductBasic secondSplit
  let rotate : Isometry
      ((J.stepEightForm 0).orthogonalSum
        ((J.stepEightForm 1).orthogonalSum restBlockForm))
      (((J.stepEightForm 1).orthogonalSum (J.stepEightForm 0)).orthogonalSum
        restBlockForm)
      (product (J.stepEightLattice 0)
        (product (J.stepEightLattice 1) restBlockLattice))
      (product (product (J.stepEightLattice 1) (J.stepEightLattice 0))
        restBlockLattice) :=
    orthogonalProductRotateLeft
  let associate : Isometry
      (((J.stepEightForm 1).orthogonalSum (J.stepEightForm 0)).orthogonalSum
        restBlockForm)
      ((J.stepEightForm 1).orthogonalSum
        ((J.stepEightForm 0).orthogonalSum restBlockForm))
      (product (product (J.stepEightLattice 1) (J.stepEightLattice 0))
        restBlockLattice)
      (product (J.stepEightLattice 1)
        (product (J.stepEightLattice 0) restBlockLattice)) :=
    orthogonalProductAssoc
  let identifyOldTail : Isometry restBlockForm oldTailBlockForm
      restBlockLattice oldTailBlockLattice :=
    J.stepEightOldTailProductIsometry
  let identifyOldProduct : Isometry
      ((J.stepEightForm 0).orthogonalSum restBlockForm)
      ((J.component 0).space.orthogonalSum oldTailBlockForm)
      (product (J.stepEightLattice 0) restBlockLattice)
      (product (J.component 0).lattice oldTailBlockLattice) :=
    J.stepEightOldHeadLatticeIsometry.orthogonalProductBasic identifyOldTail
  let identifyAll : Isometry
      ((J.stepEightForm 1).orthogonalSum
        ((J.stepEightForm 0).orthogonalSum restBlockForm))
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        ((J.component 0).space.orthogonalSum oldTailBlockForm))
      (product (J.stepEightLattice 1)
        (product (J.stepEightLattice 0) restBlockLattice))
      (product (hyperbolicPlaneLattice (K := K))
        (product (J.component 0).lattice oldTailBlockLattice)) :=
    J.stepEightInsertedLatticeIsometry.orthogonalProductBasic identifyOldProduct
  let oldSplit := BONG.blockOrthogonalSplitLatticeIsometry n
    (fun i : Fin (n + 2) => (J.component i).carrier)
    (fun i => (J.component i).space)
    (fun i => (J.component i).lattice)
  let regroupOld : Isometry
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        ((J.component 0).space.orthogonalSum oldTailBlockForm))
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        (BONG.blockOrthogonalForm (n + 1)
          (fun i : Fin (n + 2) => (J.component i).carrier)
          (fun i => (J.component i).space)))
      (product (hyperbolicPlaneLattice (K := K))
        (product (J.component 0).lattice oldTailBlockLattice))
      (product (hyperbolicPlaneLattice (K := K))
        (BONG.blockProductLattice (n + 1)
          (fun i : Fin (n + 2) => (J.component i).carrier)
          (fun i => (J.component i).lattice))) :=
    (Isometry.refl (QuadraticSpace.hyperbolicPlane J.stepEightScale)
      (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic oldSplit.symm
  let originalProduct :=
    BONG.orthogonalDecompositionProductIsometry J.toOrthogonalDecomposition
  let returnAmbient : Isometry
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        (BONG.blockOrthogonalForm (n + 1)
          (fun i : Fin (n + 2) => (J.component i).carrier)
          (fun i => (J.component i).space)))
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum q)
      (product (hyperbolicPlaneLattice (K := K))
        (BONG.blockProductLattice (n + 1)
          (fun i : Fin (n + 2) => (J.component i).carrier)
          (fun i => (J.component i).lattice)))
      (product (hyperbolicPlaneLattice (K := K)) L) :=
    (Isometry.refl (QuadraticSpace.hyperbolicPlane J.stepEightScale)
      (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic originalProduct
  exact firstSplit.trans <| exposeSecond.trans <| rotate.trans <|
    associate.trans <| identifyAll.trans <| regroupOld.trans returnAmbient

end Lattice.JordanDecomposition

end Bong
