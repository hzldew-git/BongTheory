/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightGeneratorChoice
import Bong.Lattice.Omeara9328StepEightAlignedPair
import Bong.Lattice.OrthogonalDecompositionFirstPrefix
import Bong.Lattice.OmearaHeadTailPrefix
import Bong.Lattice.OrthogonalDecompositionPrefixProduct

/-!
# Prefix presentations for O'Meara 93:28, Step 8

The first two components of the raw Step-8 splitting are the old head and
the inserted scaled hyperbolic plane.  This file gives the concrete integral
prefix presentation with the inserted plane gathered on the left.  It is
the boundary-one base case for transferring conditions (i)--(iii).
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The first Step-8 prefix is just the old first prefix. -/
noncomputable def stepEightFirstPrefixPresentation
    (J : JordanDecomposition q L (n + 2))
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    Isometry
      ((J.stepEightJordan hscaleGap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1).space
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
      ((J.stepEightJordan hscaleGap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1).lattice
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice := by
  let J₈ := J.stepEightJordan hscaleGap
  let D := J₈.toOrthogonalDecomposition
  let rawHead := BONG.blockProductComponentIsometry
    J.stepEightCarrier J.stepEightForm J.stepEightLattice
      (0 : Fin (n + 3))
  let head : Isometry (D.component 0).space
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
      (D.component 0).lattice
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice :=
    rawHead.symm.trans <| J.stepEightOldHeadLatticeIsometry.trans
      J.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
  exact D.firstComponentPrefixLatticeIsometry.symm.trans head

/-- The first two components after Step-8 insertion are integrally
isometric to the inserted plane orthogonally followed by the old first
prefix. -/
noncomputable def stepEightFirstTwoPrefixPresentation
    (J : JordanDecomposition q L (n + 2))
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    Isometry
      ((J.stepEightJordan hscaleGap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 2).space
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space)
      ((J.stepEightJordan hscaleGap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 2).lattice
      (product (hyperbolicPlaneLattice (K := K))
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice) := by
  let J₈ := J.stepEightJordan hscaleGap
  let D := J₈.toOrthogonalDecomposition
  let rawHead := BONG.blockProductComponentIsometry
    J.stepEightCarrier J.stepEightForm J.stepEightLattice
      (0 : Fin (n + 3))
  let rawInserted := BONG.blockProductComponentIsometry
    J.stepEightCarrier J.stepEightForm J.stepEightLattice
      (1 : Fin (n + 3))
  let head : Isometry (D.component 0).space
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
      (D.component 0).lattice
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice :=
    rawHead.symm.trans <| J.stepEightOldHeadLatticeIsometry.trans
      J.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
  let inserted : Isometry
      (D.tailDecomposition.prefixQuadraticSublattice 1).space
      (QuadraticSpace.hyperbolicPlane J.stepEightScale)
      (D.tailDecomposition.prefixQuadraticSublattice 1).lattice
      (hyperbolicPlaneLattice (K := K)) :=
    D.tailDecomposition.firstComponentPrefixLatticeIsometry.symm |>.trans
      ((D.tailComponentIsometry 0).symm.trans <|
        rawInserted.symm.trans J.stepEightInsertedLatticeIsometry)
  exact (D.headTailPrefixLatticeIsometry 1).symm |>.trans
    ((head.orthogonalProductBasic inserted).trans orthogonalProductSwap)

-- Dependent prefix-product normalization requires substantial elaboration.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The raw product of the first `m+3` Step-8 blocks is the actual prefix
of length `m+3` in the displayed Step-8 decomposition. -/
noncomputable def rawStepEightLaterPrefixIsometry
    (J : JordanDecomposition q L (n + 2))
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (m : Nat) (hk : m + 1 ≤ n + 1) :
    Isometry
      (BONG.blockOrthogonalForm (m + 2)
        (fun i : Fin (m + 3) =>
          J.stepEightCarrier (Fin.castLE (by omega) i))
        (fun i => J.stepEightForm (Fin.castLE (by omega) i)))
      ((J.stepEightJordan hscaleGap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 3)).space
      (BONG.blockProductLattice (m + 2)
        (fun i : Fin (m + 3) =>
          J.stepEightCarrier (Fin.castLE (by omega) i))
        (fun i => J.stepEightLattice (Fin.castLE (by omega) i)))
      ((J.stepEightJordan hscaleGap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 3)).lattice := by
  let hnew : m + 3 ≤ n + 3 := by omega
  let J₈ := J.stepEightJordan hscaleGap
  let D := J₈.toOrthogonalDecomposition
  let C : Fin (m + 3) → Type (max u v) :=
    fun i => J.stepEightCarrier (Fin.castLE hnew i)
  let Q : ∀ i, QuadraticSpace K (C i) :=
    fun i => J.stepEightForm (Fin.castLE hnew i)
  let N : ∀ i, Lattice K (C i) :=
    fun i => J.stepEightLattice (Fin.castLE hnew i)
  let componentIso (i : Fin (m + 3)) : Isometry
      (Q i) (D.prefixBlockSpace hnew i)
      (N i) (D.prefixBlockLattice hnew i) := by
    let ii := Fin.castLE hnew i
    have hidx : (D.prefixIndexEquiv (m + 3) hnew i).1 = ii := by
      apply Fin.ext
      rfl
    cases hidx
    exact BONG.blockProductComponentIsometry
      J.stepEightCarrier J.stepEightForm J.stepEightLattice ii
  let productIso := BONG.blockProductLatticeIsometry
    Q (D.prefixBlockSpace hnew) N (D.prefixBlockLattice hnew)
      componentIso
  exact productIso.trans (D.prefixBlockProductIsometry hnew)

-- The restricted rotation contains several dependent block products.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The raw Step-8 prefix is the inserted scaled hyperbolic plane followed
by the corresponding old prefix. -/
noncomputable def gatherRawStepEightLaterPrefix
    (J : JordanDecomposition q L (n + 2))
    (m : Nat) (hk : m + 1 ≤ n + 1) :
    Isometry
      (BONG.blockOrthogonalForm (m + 2)
        (fun i : Fin (m + 3) =>
          J.stepEightCarrier (Fin.castLE (by omega) i))
        (fun i => J.stepEightForm (Fin.castLE (by omega) i)))
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 2)).space)
      (BONG.blockProductLattice (m + 2)
        (fun i : Fin (m + 3) =>
          J.stepEightCarrier (Fin.castLE (by omega) i))
        (fun i => J.stepEightLattice (Fin.castLE (by omega) i)))
      (product (hyperbolicPlaneLattice (K := K))
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 2)).lattice) := by
  let hnew : m + 3 ≤ n + 3 := by omega
  let hold : m + 2 ≤ n + 2 := by omega
  let newIndex : Fin (m + 3) → Fin (n + 3) := Fin.castLE hnew
  let oldIndex : Fin (m + 2) → Fin (n + 2) := Fin.castLE hold
  let C : Fin (m + 3) → Type (max u v) :=
    fun i => J.stepEightCarrier (newIndex i)
  let Q : ∀ i, QuadraticSpace K (C i) :=
    fun i => J.stepEightForm (newIndex i)
  let N : ∀ i, Lattice K (C i) :=
    fun i => J.stepEightLattice (newIndex i)
  let tailC : Fin (m + 2) → Type (max u v) := fun i => C i.succ
  let tailQ : ∀ i, QuadraticSpace K (tailC i) := fun i => Q i.succ
  let tailN : ∀ i, Lattice K (tailC i) := fun i => N i.succ
  let restC : Fin (m + 1) → Type (max u v) := fun i => C i.succ.succ
  let restQ : ∀ i, QuadraticSpace K (restC i) := fun i => Q i.succ.succ
  let restN : ∀ i, Lattice K (restC i) := fun i => N i.succ.succ
  let oldC : Fin (m + 2) → Type v :=
    fun i => (J.component (oldIndex i)).carrier
  let oldQ : ∀ i, QuadraticSpace K (oldC i) :=
    fun i => (J.component (oldIndex i)).space
  let oldN : ∀ i, Lattice K (oldC i) :=
    fun i => (J.component (oldIndex i)).lattice
  let oldTailC : Fin (m + 1) → Type v := fun i => oldC i.succ
  let oldTailQ : ∀ i, QuadraticSpace K (oldTailC i) := fun i => oldQ i.succ
  let oldTailN : ∀ i, Lattice K (oldTailC i) := fun i => oldN i.succ
  let tailForm := BONG.blockOrthogonalForm (m + 1) tailC tailQ
  let tailLattice := BONG.blockProductLattice (m + 1) tailC tailN
  let restForm := BONG.blockOrthogonalForm m restC restQ
  let restLattice := BONG.blockProductLattice m restC restN
  let oldTailForm := BONG.blockOrthogonalForm m oldTailC oldTailQ
  let oldTailLattice := BONG.blockProductLattice m oldTailC oldTailN
  let firstSplit := BONG.blockOrthogonalSplitLatticeIsometry
    (m + 1) C Q N
  let secondSplit := BONG.blockOrthogonalSplitLatticeIsometry m tailC tailQ tailN
  let exposeSecond : Isometry
      ((Q 0).orthogonalSum tailForm)
      ((Q 0).orthogonalSum ((Q 1).orthogonalSum restForm))
      (product (N 0) tailLattice)
      (product (N 0) (product (N 1) restLattice)) :=
    (Isometry.refl (Q 0) (N 0)).orthogonalProductBasic secondSplit
  let rotate : Isometry
      ((Q 0).orthogonalSum ((Q 1).orthogonalSum restForm))
      (((Q 1).orthogonalSum (Q 0)).orthogonalSum restForm)
      (product (N 0) (product (N 1) restLattice))
      (product (product (N 1) (N 0)) restLattice) :=
    orthogonalProductRotateLeft
  let associate : Isometry
      (((Q 1).orthogonalSum (Q 0)).orthogonalSum restForm)
      ((Q 1).orthogonalSum ((Q 0).orthogonalSum restForm))
      (product (product (N 1) (N 0)) restLattice)
      (product (N 1) (product (N 0) restLattice)) :=
    orthogonalProductAssoc
  let headIso : Isometry (Q 0) (oldQ 0) (N 0) (oldN 0) := by
    have hidx : newIndex 0 =
        (1 : Fin (n + 3)).succAbove (oldIndex 0) := by
      apply Fin.ext
      simp [newIndex, oldIndex]
    cases hidx
    exact J.stepEightOldLatticeIsometry (oldIndex 0)
  let insertedIso : Isometry (Q 1)
      (QuadraticSpace.hyperbolicPlane J.stepEightScale) (N 1)
      (hyperbolicPlaneLattice (K := K)) := by
    have hidx : newIndex 1 = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simp [newIndex]
    cases hidx
    exact J.stepEightInsertedLatticeIsometry
  let oldTailIso : Isometry restForm oldTailForm
      restLattice oldTailLattice :=
    BONG.blockProductLatticeIsometry restQ oldTailQ restN oldTailN
      (fun i => by
        have hidx : newIndex i.succ.succ =
            (1 : Fin (n + 3)).succAbove (oldIndex i.succ) := by
          apply Fin.ext
          simp [newIndex, oldIndex]
        cases hidx
        exact J.stepEightOldLatticeIsometry (oldIndex i.succ))
  let identifyOldProduct : Isometry
      ((Q 0).orthogonalSum restForm)
      ((oldQ 0).orthogonalSum oldTailForm)
      (product (N 0) restLattice)
      (product (oldN 0) oldTailLattice) :=
    headIso.orthogonalProductBasic oldTailIso
  let identifyAll : Isometry
      ((Q 1).orthogonalSum ((Q 0).orthogonalSum restForm))
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        ((oldQ 0).orthogonalSum oldTailForm))
      (product (N 1) (product (N 0) restLattice))
      (product (hyperbolicPlaneLattice (K := K))
        (product (oldN 0) oldTailLattice)) :=
    insertedIso.orthogonalProductBasic identifyOldProduct
  let oldSplit := BONG.blockOrthogonalSplitLatticeIsometry m oldC oldQ oldN
  let regroupOld : Isometry
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        ((oldQ 0).orthogonalSum oldTailForm))
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        (BONG.blockOrthogonalForm (m + 1) oldC oldQ))
      (product (hyperbolicPlaneLattice (K := K))
        (product (oldN 0) oldTailLattice))
      (product (hyperbolicPlaneLattice (K := K))
        (BONG.blockProductLattice (m + 1) oldC oldN)) :=
    (Isometry.refl (QuadraticSpace.hyperbolicPlane J.stepEightScale)
      (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic oldSplit.symm
  let O := J.toOrthogonalDecomposition
  let oldComponentIso (i : Fin (m + 2)) : Isometry
      (oldQ i) (O.prefixBlockSpace hold i)
      (oldN i) (O.prefixBlockLattice hold i) := by
    have hidx : (O.prefixIndexEquiv (m + 2) hold i).1 = oldIndex i := by
      apply Fin.ext
      rfl
    cases hidx
    exact Isometry.refl _ _
  let oldPrefixProductIso := BONG.blockProductLatticeIsometry
    oldQ (O.prefixBlockSpace hold) oldN (O.prefixBlockLattice hold)
      oldComponentIso
  let returnOldPrefix : Isometry
      (BONG.blockOrthogonalForm (m + 1) oldC oldQ)
      (O.prefixQuadraticSublattice (m + 2)).space
      (BONG.blockProductLattice (m + 1) oldC oldN)
      (O.prefixQuadraticSublattice (m + 2)).lattice :=
    oldPrefixProductIso.trans (O.prefixBlockProductIsometry hold)
  let returnAll :=
    (Isometry.refl (QuadraticSpace.hyperbolicPlane J.stepEightScale)
      (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic returnOldPrefix
  exact firstSplit.trans <| exposeSecond.trans <| rotate.trans <|
    associate.trans <| identifyAll.trans <| regroupOld.trans returnAll

/-- Every Step-8 prefix strictly beyond the new middle boundary is the
inserted plane followed by the corresponding old prefix. -/
noncomputable def stepEightLaterPrefixPresentation
    (J : JordanDecomposition q L (n + 2))
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (m : Nat) (hk : m + 1 ≤ n + 1) :
    Isometry
      ((J.stepEightJordan hscaleGap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 3)).space
      ((QuadraticSpace.hyperbolicPlane J.stepEightScale).orthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 2)).space)
      ((J.stepEightJordan hscaleGap).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 3)).lattice
      (product (hyperbolicPlaneLattice (K := K))
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 2)).lattice) :=
  (J.rawStepEightLaterPrefixIsometry hscaleGap m hk).symm.trans
    (J.gatherRawStepEightLaterPrefix m hk)

end Lattice.JordanDecomposition

end Bong
