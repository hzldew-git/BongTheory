/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318DeterminantOne
import Bong.Lattice.OmearaSaturationGeometry
import Bong.Lattice.OrthogonalDecompositionDeterminant

/-!
# Invariants of the complement in O'Meara 93:18(v)

Once a scaled hyperbolic plane is split from a positive-rank modular
lattice, its norm group is absorbed by the modular complement.  Consequently
the complement has exactly the same norm group as the original lattice.
This elementary fact is used repeatedly in 93:18, 93:19, and the
normalization step of 93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

namespace Omeara9318vData

variable (D : Omeara9318vData q L s)

/-- Splitting one displayed hyperbolic plane lowers the ambient rank by
exactly two.  This rank formula is independent of any lower bound on the
complement and is the termination measure for the repeated 93:18(v)
reduction used in 93:28. -/
theorem complement_finrank :
    finrank K (D.decomposition.component 1).carrier =
      finrank K V - 2 := by
  let H := D.decomposition.component 0
  let C := D.decomposition.component 1
  letI : Module.Finite K H.carrier := H.lattice.moduleFinite
  letI : Module.Finite K C.carrier := C.lattice.moduleFinite
  have hHrank : finrank K H.carrier = 2 := by
    calc
      finrank K H.carrier = finrank K (Fin 2 → K) :=
        D.hyperbolic.toLinearEquiv.finrank_eq
      _ = 2 := by simp
  have htotal :=
    D.decomposition.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
  change finrank K (H.carrier × C.carrier) = finrank K V at htotal
  rw [Module.finrank_prod, hHrank] at htotal
  have htotal' : finrank K C.carrier + 2 = finrank K V := by
    simpa only [Nat.add_comm] using htotal
  exact Nat.eq_sub_of_add_eq htotal'

/-- In ambient rank four, the complement of the displayed hyperbolic plane
has rank two. -/
theorem complement_finrank_of_rank_four
    (hrank : finrank K V = 4) :
    finrank K (D.decomposition.component 1).carrier = 2 := by
  rw [D.complement_finrank, hrank]

/-- A displayed scaled hyperbolic summand contributes no new norm-group
elements once its modular complement has positive rank. -/
theorem complement_normGroupSet_eq
    (hpos : 0 < finrank K (D.decomposition.component 1).carrier) :
    normGroupSet (D.decomposition.component 1).space
        (D.decomposition.component 1).lattice =
      normGroupSet q L := by
  let C := D.decomposition.component 1
  have habsorb :
      normGroupSet (QuadraticSpace.hyperbolicPlane s)
          (hyperbolicPlaneLattice (K := K)) ⊆
        normGroupSet C.space C.lattice :=
    normGroupSet_scaledHyperbolic_subset_of_modular
      D.complement_modular hpos
  have hproduct :
      normGroupSet
          ((QuadraticSpace.hyperbolicPlane s).orthogonalSum C.space)
          (product (hyperbolicPlaneLattice (K := K)) C.lattice) =
        normGroupSet C.space C.lattice := by
    ext z
    rw [mem_normGroupSet_orthogonalProduct_iff]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact add_mem_normGroupSet C.space C.lattice (habsorb ha) hb
    · intro hz
      exact ⟨0, zero_mem_normGroupSet
        (QuadraticSpace.hyperbolicPlane s)
        (hyperbolicPlaneLattice (K := K)), z, hz, by simp⟩
  calc
    normGroupSet C.space C.lattice =
        normGroupSet
          ((QuadraticSpace.hyperbolicPlane s).orthogonalSum C.space)
          (product (hyperbolicPlaneLattice (K := K)) C.lattice) :=
      hproduct.symm
    _ = normGroupSet q L :=
      normGroupSet_eq_of_latticeIsometry D.displayedIsometry

end Omeara9318vData

end Lattice

end Bong
