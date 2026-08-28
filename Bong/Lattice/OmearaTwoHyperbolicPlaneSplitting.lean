/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318OddRankFiveSix
import Bong.Lattice.OrthogonalDecompositionCons

/-!
# Two hyperbolic planes in a modular lattice of rank at least seven

The first step of O'Meara 93:21 applies 93:18(v) twice to every sufficiently
large modular component.  This file packages that iteration as an actual
three-component orthogonal decomposition.  Its first two components are
scaled hyperbolic planes and its last component remains modular at the same
scale.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

/-- Concrete output of applying O'Meara 93:18(v) twice. -/
structure OmearaTwoHyperbolicPlaneData
    (q : QuadraticSpace K V) (L : Lattice K V) (s : Kˣ) where
  decomposition : OrthogonalDecomposition q L 3
  firstHyperbolic : Isometry
    (decomposition.component 0).space (QuadraticSpace.hyperbolicPlane s)
    (decomposition.component 0).lattice
    (hyperbolicPlaneLattice (K := K))
  secondHyperbolic : Isometry
    (decomposition.component 1).space (QuadraticSpace.hyperbolicPlane s)
    (decomposition.component 1).lattice
    (hyperbolicPlaneLattice (K := K))
  complement_modular : IsModular
    (decomposition.component 2).space
    (decomposition.component 2).lattice s
  /-- Removing two displayed planes lowers the ambient rank by four. -/
  complement_finrank :
    finrank K (decomposition.component 2).carrier = finrank K V - 4

set_option maxHeartbeats 1000000 in
/-- O'Meara 93:18(v), iterated twice. -/
noncomputable def omearaTwoHyperbolicPlaneData
    (hmodular : IsModular q L s)
    (hrank : 7 ≤ finrank K V) :
    OmearaTwoHyperbolicPlaneData q L s := by
  letI : Module.Finite K V := L.moduleFinite
  let D₀ : Omeara9318vData q L s :=
    omeara9318vDataOfOddRankFiveOrSix
      (omeara9318vOddRankFiveOrSix (K := K)) q L s hmodular (by omega)
  let C := D₀.decomposition.component 1
  letI : Module.Finite K C.carrier := C.lattice.moduleFinite
  have hCfinrank : finrank K C.carrier = finrank K V - 2 := by
    let P := D₀.decomposition.component 0
    letI : Module.Finite K P.carrier := P.lattice.moduleFinite
    have hP : finrank K P.carrier = 2 := by
      have h := D₀.hyperbolic.toLinearEquiv.finrank_eq
      simpa only [Module.finrank_fin_fun] using h
    have htotal := D₀.decomposition.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
    change finrank K (P.carrier × C.carrier) = finrank K V at htotal
    rw [Module.finrank_prod, hP] at htotal
    omega
  have hCrank : 5 ≤ finrank K C.carrier := by omega
  let D₁ : Omeara9318vData C.space C.lattice s :=
    omeara9318vDataOfOddRankFiveOrSix
      (omeara9318vOddRankFiveOrSix (K := K)) C.space C.lattice s
        D₀.complement_modular hCrank
  have hD₁finrank :
      finrank K (D₁.decomposition.component 1).carrier =
        finrank K C.carrier - 2 := by
    let P := D₁.decomposition.component 0
    let R := D₁.decomposition.component 1
    letI : Module.Finite K P.carrier := P.lattice.moduleFinite
    letI : Module.Finite K R.carrier := R.lattice.moduleFinite
    have hP : finrank K P.carrier = 2 := by
      have h := D₁.hyperbolic.toLinearEquiv.finrank_eq
      simpa only [Module.finrank_fin_fun] using h
    have htotal := D₁.decomposition.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
    change finrank K (P.carrier × R.carrier) = finrank K C.carrier at htotal
    rw [Module.finrank_prod, hP] at htotal
    change finrank K R.carrier = finrank K C.carrier - 2
    omega
  let T : OrthogonalDecomposition q L 3 :=
    D₀.decomposition.prependNested D₁.decomposition
  refine {
    decomposition := T
    firstHyperbolic := ?_
    secondHyperbolic := ?_
    complement_modular := ?_
    complement_finrank := ?_
  }
  · change Isometry (D₀.decomposition.component 0).space
      (QuadraticSpace.hyperbolicPlane s)
      (D₀.decomposition.component 0).lattice
      (hyperbolicPlaneLattice (K := K))
    exact D₀.hyperbolic
  · let lift := C.liftNestedIsometry (D₁.decomposition.component 0)
    have h : Isometry
        (C.liftNested (D₁.decomposition.component 0)).space
        (QuadraticSpace.hyperbolicPlane s)
        (C.liftNested (D₁.decomposition.component 0)).lattice
        (hyperbolicPlaneLattice (K := K)) :=
      lift.symm.trans D₁.hyperbolic
    change Isometry
      (C.liftNested (D₁.decomposition.component 0)).space
      (QuadraticSpace.hyperbolicPlane s)
      (C.liftNested (D₁.decomposition.component 0)).lattice
      (hyperbolicPlaneLattice (K := K))
    exact h
  · let lift := C.liftNestedIsometry (D₁.decomposition.component 1)
    have h := D₁.complement_modular.mapLatticeIsometry lift
    change IsModular
      (C.liftNested (D₁.decomposition.component 1)).space
      (C.liftNested (D₁.decomposition.component 1)).lattice s
    exact h
  · change finrank K (C.liftNested
        (D₁.decomposition.component 1)).carrier = finrank K V - 4
    rw [C.finrank_liftNested, hD₁finrank, hCfinrank]
    omega

end Lattice

end Bong
