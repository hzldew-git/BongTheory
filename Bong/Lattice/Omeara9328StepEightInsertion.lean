/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328ScaleOneDispatcher
import Bong.Lattice.OmearaScaledHyperbolicTowerInvariants

/-!
# O'Meara 93:28, Step 8: insertion at the first missing scale

If the first two Jordan scales differ by more than one, Step 8 adjoins the
same lattice `s₀ π A(0,0)` to both sides and places it between the old first
and second components.  This file constructs that enlarged Jordan splitting
as an actual block product.  Its modular, scale, norm and rank data come from
the standard hyperbolic plane; no insertion law is postulated.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

universe x z

/-- Pull a quadratic space back to a universe-raised copy of its carrier. -/
private noncomputable def stepEightULiftForm
    {X : Type x} [AddCommGroup X] [Module K X]
    (r : QuadraticSpace K X) : QuadraticSpace K (ULift.{z} X) where
  bilin := LinearMap.mk₂ K
    (fun a b => r.bilin
      ((ULift.moduleEquiv : ULift.{z} X ≃ₗ[K] X) a)
      ((ULift.moduleEquiv : ULift.{z} X ≃ₗ[K] X) b))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  isSymm := ⟨by intro a b; exact r.isSymm.eq _ _⟩
  nondegenerate := by
    constructor
    · intro a ha
      apply (ULift.moduleEquiv : ULift.{z} X ≃ₗ[K] X).injective
      rw [map_zero]
      apply r.nondegenerate.1
      intro b
      simpa using ha
        ((ULift.moduleEquiv : ULift.{z} X ≃ₗ[K] X).symm b)
    · intro a ha
      apply (ULift.moduleEquiv : ULift.{z} X ≃ₗ[K] X).injective
      rw [map_zero]
      apply r.nondegenerate.2
      intro b
      simpa using ha
        ((ULift.moduleEquiv : ULift.{z} X ≃ₗ[K] X).symm b)

/-- Universe-raised image of a lattice. -/
private noncomputable def stepEightULiftLattice
    {X : Type x} [AddCommGroup X] [Module K X]
    (N : Lattice K X) : Lattice K (ULift.{z} X) :=
  map ULift.moduleEquiv.symm N

/-- Canonical integral isometry from the universe-raised copy back to the
original quadratic lattice. -/
private noncomputable def stepEightULiftIsometry
    {X : Type x} [AddCommGroup X] [Module K X]
    (r : QuadraticSpace K X) (N : Lattice K X) :
    Isometry (stepEightULiftForm r) r
      (stepEightULiftLattice N) N where
  toLinearEquiv := ULift.moduleEquiv
  map_bilin _ _ := by simp [stepEightULiftForm]
  map_mem a := by
    change a ∈ map ULift.moduleEquiv.symm N ↔ ULift.moduleEquiv a ∈ N
    rw [mem_map_iff]
    rfl

private theorem stepEightULift_normIdeal
    {X : Type x} [AddCommGroup X] [Module K X]
    (r : QuadraticSpace K X) (N : Lattice K X) :
    normIdeal (stepEightULiftForm r)
        (stepEightULiftLattice N) = normIdeal r N := by
  let f := stepEightULiftIsometry r N
  calc
    normIdeal (stepEightULiftForm r)
        (stepEightULiftLattice N) =
        normIdeal r
          (map f.toLinearEquiv (stepEightULiftLattice N)) :=
      (normIdeal_map_isometry f.toQuadraticSpaceIsometry _).symm
    _ = normIdeal r N := congrArg (normIdeal r) f.map_eq

private theorem stepEightULift_isModular
    {X : Type x} [AddCommGroup X] [Module K X]
    {r : QuadraticSpace K X} {N : Lattice K X} {s : Kˣ}
    (h : IsModular r N s) :
    IsModular (stepEightULiftForm r)
      (stepEightULiftLattice N) s :=
  h.mapLatticeIsometry (stepEightULiftIsometry r N).symm

/-- The scale inserted by Step 8, one valuation step above the first scale. -/
noncomputable def stepEightScale
    (J : JordanDecomposition q L (n + 2)) : Kˣ :=
  J.scaleGenerator 0 * uniformizerUnit K

/-- A nonzero generator of the norm ideal of the inserted plane. -/
noncomputable def stepEightNormGenerator
    (J : JordanDecomposition q L (n + 2)) : Kˣ :=
  Units.mk0 (2 * (J.stepEightScale : K))
    (mul_ne_zero (by norm_num) (Units.ne_zero J.stepEightScale))

@[simp]
theorem stepEightScale_order
    (J : JordanDecomposition q L (n + 2)) :
    ordUnit K J.stepEightScale = ordUnit K (J.scaleGenerator 0) + 1 := by
  rw [stepEightScale, ordUnit_mul]
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_uniformizerUnit, ord_uniformizer]
    norm_num
  rw [hpi]

variable (J : JordanDecomposition q L (n + 2))

/-! We package each raised block together with the instances and ideal proofs
that belong to it.  This makes the Step-8 family genuinely homogeneous in one
universe and avoids any proof-irrelevant transport across dependent carriers. -/

private structure StepEightBlock (K : Type u) [Field K] [CharZero K]
    [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] where
  carrier : Type (max u v)
  [addCommGroup : AddCommGroup carrier]
  [module : Module K carrier]
  space : QuadraticSpace K carrier
  lattice : Lattice K carrier
  scale : Kˣ
  norm : Kˣ
  rank : Nat
  finrank_eq : finrank K carrier = rank
  finrank_pos : 0 < finrank K carrier
  modular : IsModular space lattice scale
  scaleIdeal_eq : scaleIdeal space lattice =
    principalIdeal (K := K) (scale : K)
  normIdeal_eq : normIdeal space lattice =
    principalIdeal (K := K) (norm : K)

private noncomputable def stepEightInsertedBlock : StepEightBlock K where
  carrier := ULift.{max u v} (Fin 2 → K)
  addCommGroup := inferInstance
  module := inferInstance
  space := stepEightULiftForm
    (QuadraticSpace.hyperbolicPlane J.stepEightScale)
  lattice := stepEightULiftLattice (hyperbolicPlaneLattice (K := K))
  scale := J.stepEightScale
  norm := J.stepEightNormGenerator
  rank := 2
  finrank_eq := by
    rw [(ULift.moduleEquiv :
      ULift.{max u v} (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).finrank_eq]
    simp
  finrank_pos := by
    rw [(ULift.moduleEquiv :
      ULift.{max u v} (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).finrank_eq]
    simp
  modular := stepEightULift_isModular
    (hyperbolicPlaneLattice_isModular (K := K) J.stepEightScale)
  scaleIdeal_eq := by
    exact (stepEightULift_isModular
      (hyperbolicPlaneLattice_isModular (K := K) J.stepEightScale)).scaleIdeal_eq_principal
        (by
          rw [(ULift.moduleEquiv :
            ULift.{max u v} (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).finrank_eq]
          simp)
  normIdeal_eq := by
    rw [stepEightULift_normIdeal,
      normIdeal_hyperbolicPlaneLattice]
    rfl

private noncomputable def stepEightOldBlock (i : Fin (n + 2)) :
    StepEightBlock K where
  carrier := ULift.{max u v} (J.component i).carrier
  addCommGroup := inferInstance
  module := inferInstance
  space := stepEightULiftForm (J.component i).space
  lattice := stepEightULiftLattice (J.component i).lattice
  scale := J.scaleGenerator i
  norm := J.normGenerator i
  rank := J.componentRank i
  finrank_eq := by
    rw [(ULift.moduleEquiv : ULift.{max u v} (J.component i).carrier ≃ₗ[K]
      (J.component i).carrier).finrank_eq]
    rfl
  finrank_pos := by
    rw [(ULift.moduleEquiv : ULift.{max u v} (J.component i).carrier ≃ₗ[K]
      (J.component i).carrier).finrank_eq]
    exact J.component_finrank_pos i
  modular := stepEightULift_isModular (J.modular i)
  scaleIdeal_eq := by
    exact (stepEightULift_isModular (J.modular i)).scaleIdeal_eq_principal
      (by
        rw [(ULift.moduleEquiv : ULift.{max u v} (J.component i).carrier ≃ₗ[K]
          (J.component i).carrier).finrank_eq]
        exact J.component_finrank_pos i)
  normIdeal_eq := by
    rw [stepEightULift_normIdeal]
    exact J.normIdeal_eq i

/-- The homogeneous block family obtained by inserting the Step-8 plane at
index one. -/
private noncomputable def stepEightBlock (i : Fin (n + 3)) :
    StepEightBlock K :=
  Fin.insertNth (α := fun _ => StepEightBlock K) (1 : Fin (n + 3))
    J.stepEightInsertedBlock J.stepEightOldBlock i

@[simp]
private theorem stepEightBlock_inserted :
    J.stepEightBlock (1 : Fin (n + 3)) = J.stepEightInsertedBlock :=
  Fin.insertNth_apply_same _ _ _

@[simp]
private theorem stepEightBlock_old (i : Fin (n + 2)) :
    J.stepEightBlock ((1 : Fin (n + 3)).succAbove i) =
      J.stepEightOldBlock i :=
  Fin.insertNth_apply_succAbove _ _ _ i

/-- Carrier family after inserting the Step-8 plane at index one. -/
def stepEightCarrier (i : Fin (n + 3)) : Type (max u v) :=
  (J.stepEightBlock i).carrier

@[reducible, instance] noncomputable def stepEightAddCommGroup
    (i : Fin (n + 3)) : AddCommGroup (J.stepEightCarrier i) :=
  (J.stepEightBlock i).addCommGroup

@[reducible, instance] noncomputable def stepEightModule
    (i : Fin (n + 3)) : Module K (J.stepEightCarrier i) :=
  (J.stepEightBlock i).module

/-- Quadratic forms on the inserted block family. -/
noncomputable def stepEightForm (i : Fin (n + 3)) :
    QuadraticSpace K (J.stepEightCarrier i) :=
  (J.stepEightBlock i).space

/-- Lattices on the inserted block family. -/
noncomputable def stepEightLattice (i : Fin (n + 3)) :
    Lattice K (J.stepEightCarrier i) :=
  (J.stepEightBlock i).lattice

/-- Scale generators on the inserted block family. -/
noncomputable def stepEightScaleGenerator (i : Fin (n + 3)) : Kˣ :=
  (J.stepEightBlock i).scale

/-- Norm generators on the inserted block family. -/
noncomputable def stepEightNormGeneratorAt (i : Fin (n + 3)) : Kˣ :=
  (J.stepEightBlock i).norm

@[simp]
theorem stepEightCarrier_inserted :
    J.stepEightCarrier (1 : Fin (n + 3)) =
      ULift.{max u v} (Fin 2 → K) := by
  simp [stepEightCarrier, stepEightInsertedBlock]

@[simp]
theorem stepEightCarrier_old (i : Fin (n + 2)) :
    J.stepEightCarrier ((1 : Fin (n + 3)).succAbove i) =
      ULift.{max u v} (J.component i).carrier := by
  simp [stepEightCarrier, stepEightOldBlock]

@[simp]
theorem stepEightScaleGenerator_inserted :
    J.stepEightScaleGenerator (1 : Fin (n + 3)) = J.stepEightScale :=
  by simp [stepEightScaleGenerator, stepEightInsertedBlock]

@[simp]
theorem stepEightScaleGenerator_old (i : Fin (n + 2)) :
    J.stepEightScaleGenerator ((1 : Fin (n + 3)).succAbove i) =
      J.scaleGenerator i :=
  by simp [stepEightScaleGenerator, stepEightOldBlock]

@[simp]
theorem stepEightNormGeneratorAt_inserted :
    J.stepEightNormGeneratorAt (1 : Fin (n + 3)) =
      J.stepEightNormGenerator :=
  by simp [stepEightNormGeneratorAt, stepEightInsertedBlock]

@[simp]
theorem stepEightNormGeneratorAt_old (i : Fin (n + 2)) :
    J.stepEightNormGeneratorAt ((1 : Fin (n + 3)).succAbove i) =
      J.normGenerator i :=
  by simp [stepEightNormGeneratorAt, stepEightOldBlock]

/-- The inserted raised block is integrally isometric to the standard scaled
hyperbolic plane used in O'Meara's Step 8. -/
noncomputable def stepEightInsertedLatticeIsometry :
    Isometry (J.stepEightForm (1 : Fin (n + 3)))
      (QuadraticSpace.hyperbolicPlane J.stepEightScale)
      (J.stepEightLattice (1 : Fin (n + 3)))
      (hyperbolicPlaneLattice (K := K)) := by
  letI : AddCommGroup (J.stepEightBlock (1 : Fin (n + 3))).carrier :=
    (J.stepEightBlock (1 : Fin (n + 3))).addCommGroup
  letI : Module K (J.stepEightBlock (1 : Fin (n + 3))).carrier :=
    (J.stepEightBlock (1 : Fin (n + 3))).module
  change Isometry (J.stepEightBlock (1 : Fin (n + 3))).space
    (QuadraticSpace.hyperbolicPlane J.stepEightScale)
    (J.stepEightBlock (1 : Fin (n + 3))).lattice
    (hyperbolicPlaneLattice (K := K))
  rw [J.stepEightBlock_inserted]
  exact stepEightULiftIsometry
    (QuadraticSpace.hyperbolicPlane J.stepEightScale)
    (hyperbolicPlaneLattice (K := K))

/-- Every raised old block is integrally isometric to the corresponding
component of the original Jordan decomposition. -/
noncomputable def stepEightOldLatticeIsometry (i : Fin (n + 2)) :
    Isometry
      (J.stepEightForm ((1 : Fin (n + 3)).succAbove i))
      (J.component i).space
      (J.stepEightLattice ((1 : Fin (n + 3)).succAbove i))
      (J.component i).lattice := by
  letI : AddCommGroup
      (J.stepEightBlock ((1 : Fin (n + 3)).succAbove i)).carrier :=
    (J.stepEightBlock ((1 : Fin (n + 3)).succAbove i)).addCommGroup
  letI : Module K
      (J.stepEightBlock ((1 : Fin (n + 3)).succAbove i)).carrier :=
    (J.stepEightBlock ((1 : Fin (n + 3)).succAbove i)).module
  change Isometry
    (J.stepEightBlock ((1 : Fin (n + 3)).succAbove i)).space
    (J.component i).space
    (J.stepEightBlock ((1 : Fin (n + 3)).succAbove i)).lattice
    (J.component i).lattice
  rw [J.stepEightBlock_old]
  exact stepEightULiftIsometry (J.component i).space (J.component i).lattice

/-- The block before the insertion is the raised copy of the old first
component. -/
noncomputable def stepEightOldHeadLatticeIsometry :
    Isometry (J.stepEightForm 0) (J.component 0).space
      (J.stepEightLattice 0) (J.component 0).lattice := by
  have hidx : (0 : Fin (n + 3)) =
      (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
    apply Fin.ext
    simp
  rw [hidx]
  exact J.stepEightOldLatticeIsometry (0 : Fin (n + 2))

/-- After removing the old head and the inserted plane, the remaining block
at index `i` is the raised copy of old component `i+1`. -/
noncomputable def stepEightOldTailLatticeIsometry (i : Fin (n + 1)) :
    Isometry (J.stepEightForm i.succ.succ) (J.component i.succ).space
      (J.stepEightLattice i.succ.succ) (J.component i.succ).lattice := by
  have hidx : (i.succ.succ : Fin (n + 3)) =
      (1 : Fin (n + 3)).succAbove (i.succ : Fin (n + 2)) := by
    apply Fin.ext
    simp
  rw [hidx]
  exact J.stepEightOldLatticeIsometry (i.succ : Fin (n + 2))

/-- Old block norm groups are unchanged by the universe-raising copy. -/
theorem stepEightOld_normGroupSet (i : Fin (n + 2)) :
    normGroupSet
        (J.stepEightForm ((1 : Fin (n + 3)).succAbove i))
        (J.stepEightLattice ((1 : Fin (n + 3)).succAbove i)) =
      normGroupSet (J.component i).space (J.component i).lattice :=
  (normGroupSet_eq_of_latticeIsometry
    (J.stepEightOldLatticeIsometry i)).symm

/-- Old block scale ideals are unchanged by the universe-raising copy. -/
theorem stepEightOld_scaleIdeal (i : Fin (n + 2)) :
    scaleIdeal
        (J.stepEightForm ((1 : Fin (n + 3)).succAbove i))
        (J.stepEightLattice ((1 : Fin (n + 3)).succAbove i)) =
      scaleIdeal (J.component i).space (J.component i).lattice := by
  let f := J.stepEightOldLatticeIsometry i
  rw [← f.map_eq]
  exact (scaleIdeal_map_isometry f.toQuadraticSpaceIsometry _).symm

theorem stepEightFinrank_pos (i : Fin (n + 3)) :
    0 < finrank K (J.stepEightCarrier i) :=
  (J.stepEightBlock i).finrank_pos

theorem stepEightModular (i : Fin (n + 3)) :
    IsModular (J.stepEightForm i) (J.stepEightLattice i)
      (J.stepEightScaleGenerator i) :=
  (J.stepEightBlock i).modular

theorem stepEightScaleIdeal_eq (i : Fin (n + 3)) :
    scaleIdeal (J.stepEightForm i) (J.stepEightLattice i) =
      principalIdeal (K := K) (J.stepEightScaleGenerator i : K) :=
  (J.stepEightBlock i).scaleIdeal_eq

theorem stepEightNormIdeal_eq (i : Fin (n + 3)) :
    normIdeal (J.stepEightForm i) (J.stepEightLattice i) =
      principalIdeal (K := K) (J.stepEightNormGeneratorAt i : K) :=
  (J.stepEightBlock i).normIdeal_eq

/-- The inserted scale sequence is strictly increasing whenever the old
first gap is larger than one. -/
theorem stepEightScaleOrder_strict
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    StrictMono (fun i => ordUnit K (J.stepEightScaleGenerator i)) := by
  apply (Fin.strictMono_iff_lt_succ).2
  intro i
  cases i using Fin.cases with
  | zero =>
      change ordUnit K (J.stepEightScaleGenerator
          ((1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)))) <
        ordUnit K (J.stepEightScaleGenerator (1 : Fin (n + 3)))
      rw [J.stepEightScaleGenerator_old, J.stepEightScaleGenerator_inserted,
        stepEightScale_order]
      omega
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          change ordUnit K (J.stepEightScaleGenerator (1 : Fin (n + 3))) <
            ordUnit K (J.stepEightScaleGenerator
              ((1 : Fin (n + 3)).succAbove (1 : Fin (n + 2))))
          rw [J.stepEightScaleGenerator_inserted,
            J.stepEightScaleGenerator_old, stepEightScale_order]
          omega
      | succ i =>
          change ordUnit K (J.stepEightScaleGenerator
              ((1 : Fin (n + 3)).succAbove i.succ.castSucc)) <
            ordUnit K (J.stepEightScaleGenerator
              ((1 : Fin (n + 3)).succAbove i.succ.succ))
          rw [J.stepEightScaleGenerator_old, J.stepEightScaleGenerator_old]
          exact J.scaleOrder_strict Fin.castSucc_lt_succ

/-- The raw Step-8 enlarged Jordan splitting. -/
noncomputable def stepEightJordan
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    JordanDecomposition
      (BONG.blockOrthogonalForm (n + 2) J.stepEightCarrier J.stepEightForm)
      (BONG.blockProductLattice (n + 2) J.stepEightCarrier J.stepEightLattice)
      (n + 3) :=
  BONG.blockProductJordanDecomposition J.stepEightCarrier J.stepEightForm
    J.stepEightLattice J.stepEightScaleGenerator J.stepEightNormGeneratorAt
      J.stepEightModular J.stepEightScaleIdeal_eq J.stepEightNormIdeal_eq
        (J.stepEightScaleOrder_strict hgap)

@[simp]
theorem stepEightJordan_scaleGenerator
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) (i : Fin (n + 3)) :
    (J.stepEightJordan hgap).scaleGenerator i =
      J.stepEightScaleGenerator i :=
  rfl

@[simp]
theorem stepEightJordan_normGenerator
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) (i : Fin (n + 3)) :
    (J.stepEightJordan hgap).normGenerator i =
      J.stepEightNormGeneratorAt i :=
  rfl

@[simp]
theorem stepEightJordan_componentRank
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) (i : Fin (n + 3)) :
    (J.stepEightJordan hgap).componentRank i =
      finrank K (J.stepEightCarrier i) := by
  exact BONG.blockProductJordanDecomposition_componentRank
    J.stepEightCarrier J.stepEightForm J.stepEightLattice
      J.stepEightScaleGenerator J.stepEightNormGeneratorAt J.stepEightModular
        J.stepEightScaleIdeal_eq J.stepEightNormIdeal_eq
          (J.stepEightScaleOrder_strict hgap) i

@[simp]
theorem stepEightJordan_inserted_componentRank
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    (J.stepEightJordan hgap).componentRank 1 = 2 := by
  rw [J.stepEightJordan_componentRank]
  exact (J.stepEightBlock (1 : Fin (n + 3))).finrank_eq.trans <| by
    simp [stepEightBlock, stepEightInsertedBlock]

@[simp]
theorem stepEightJordan_old_componentRank
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) (i : Fin (n + 2)) :
    (J.stepEightJordan hgap).componentRank
        ((1 : Fin (n + 3)).succAbove i) = J.componentRank i := by
  rw [J.stepEightJordan_componentRank]
  exact (J.stepEightBlock ((1 : Fin (n + 3)).succAbove i)).finrank_eq.trans <| by
    simp [stepEightBlock, stepEightOldBlock]

end Lattice.JordanDecomposition

end Bong
