/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328Conditions
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.ModularParameter
import Bong.Lattice.ModularIsometry

/-!
# O'Meara 93:28: classification induction

This file proves the classification theorem from the intrinsic conditions in
`Omeara9328Conditions`.  The one-component case is O'Meara 93:16 after
transporting the two lattices to a common ambient quadratic space.  The
multi-component induction is developed below from 93:14, 93:18 and 93:19.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace JordanDecomposition

/-- For a one-component Jordan decomposition, the intrinsic lattice at its
sole fundamental scale is the original lattice. -/
theorem fundamentalLattice_fin_one
    (J : JordanDecomposition q L 1) :
    J.fundamentalLattice 0 = L := by
  unfold fundamentalLattice fundamentalScaleOrder
  rw [J.scaleTruncation_eq_componentwiseRescaleLattice]
  have hfactor : J.scaleTruncationFactor
      (ordUnit K (J.scaleGenerator 0)) = fun _ ↦ 1 := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact J.scaleTruncationFactor_self 0
  rw [hfactor, J.toOrthogonalDecomposition.componentwiseRescaleLattice_one]

/-- O'Meara 93:28, base case.  With one Jordan component there are no
boundary conditions; equality of fundamental type is exactly the modular
norm-group hypothesis of O'Meara 93:16. -/
noncomputable def omeara9328_singleComponent
    (J : JordanDecomposition q L 1)
    (H : JordanDecomposition r M 1)
    (ambient : q.IsIsometric r)
    (F : SameFundamentalType J H) :
    Lattice.Isometry q r L M := by
  let f : QuadraticSpace.Isometry q r := Classical.choice ambient
  let mappedL : Lattice K W := Lattice.map f.toLinearEquiv L
  let lift : Lattice.Isometry q r L mappedL :=
    Lattice.Isometry.toMap q f L
  have hindex : F.indexEquiv (0 : Fin 1) = 0 :=
    Subsingleton.elim _ _
  have hscaleOrder := F.scaleOrder_eq (0 : Fin 1)
  rw [hindex] at hscaleOrder
  unfold fundamentalScaleOrder at hscaleOrder
  have hscaleIdeal :
      principalIdeal (K := K) ((J.scaleGenerator 0 : Kˣ) : K) =
        principalIdeal (K := K) ((H.scaleGenerator 0 : Kˣ) : K) :=
    (principalIdeal_eq_iff_ordUnit_eq _ _).2 hscaleOrder.symm
  have hsourceModular : IsModular q L (J.scaleGenerator 0) :=
    (J.modular 0).mapLatticeIsometry
      J.toOrthogonalDecomposition.singleComponentLatticeIsometry
  have hmappedModular : IsModular r mappedL (H.scaleGenerator 0) :=
    (hsourceModular.mapLatticeIsometry lift).of_principalIdeal_eq hscaleIdeal
  have htargetModular : IsModular r M (H.scaleGenerator 0) :=
    (H.modular 0).mapLatticeIsometry
      H.toOrthogonalDecomposition.singleComponentLatticeIsometry
  have horiginalGroup : normGroupSet r M = normGroupSet q L := by
    have h := F.normGroup_eq (0 : Fin 1)
    rw [hindex] at h
    unfold fundamentalNormGroup at h
    rw [fundamentalLattice_fin_one J, fundamentalLattice_fin_one H] at h
    exact h
  have hmappedGroup : normGroupSet r mappedL = normGroupSet r M := by
    calc
      normGroupSet r mappedL = normGroupSet q L :=
        normGroupSet_eq_of_latticeIsometry lift
      _ = normGroupSet r M := horiginalGroup.symm
  exact lift.trans <|
    omeara9316_of_modular_normGroupSet_eq (H.scaleGenerator 0)
      hmappedModular htargetModular hmappedGroup

/-- Equivalence form of the one-component case.  The three 93:28 boundary
conditions are vacuous because `Fin 0` is empty. -/
theorem omeara9328_singleComponent_iff
    (J : JordanDecomposition q L 1)
    (H : JordanDecomposition r M 1)
    (ambient : q.IsIsometric r)
    (F : SameFundamentalType J H) :
    Lattice.IsIsometric q r L M ↔ J.Omeara9328Conditions H := by
  constructor
  · intro _
    refine ⟨?_, ?_, ?_⟩ <;> intro i
    all_goals exact Fin.elim0 i
  · intro _
    exact ⟨omeara9328_singleComponent J H ambient F⟩

end JordanDecomposition

end Lattice

end Bong
