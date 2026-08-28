/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanEffectiveNorm
import Bong.Lattice.JordanAmalgamation
import Bong.Lattice.OrthogonalDecompositionPrefixComponentwise

/-!
# Prefix determinants under adjacent Jordan amalgamation

Replacing two adjacent equal-scale weak Jordan components by their
orthogonal sum does not change the refined determinant square class of the
prefix through that pair.  Both the quotient-class identity and an explicit
valuation-unit square witness are provided.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.WeakJordanDecomposition

/-- The carrier of the empty prefix of an orthogonal decomposition is
subsingleton. -/
theorem prefixCarrier_zero_subsingleton
    {t : Nat} (D : Lattice.OrthogonalDecomposition q L t) :
    Subsingleton (D.prefixCarrier 0) := by
  letI : IsEmpty (D.PrefixIndex 0) :=
    ⟨fun i ↦ (Nat.not_lt_zero i.1.val) i.property⟩
  have hcarrier : D.prefixCarrier 0 = ⊥ := by
    unfold Lattice.OrthogonalDecomposition.prefixCarrier
    exact iSup_of_empty _
  constructor
  intro x y
  apply Subtype.ext
  have hx : (x : V) = 0 := by
    have hx' : (x : V) ∈ (⊥ : Submodule K V) := by
      rw [← hcarrier]
      exact x.property
    simpa only [Submodule.mem_bot] using hx'
  have hy : (y : V) = 0 := by
    have hy' : (y : V) ∈ (⊥ : Submodule K V) := by
      rw [← hcarrier]
      exact y.property
    simpa only [Submodule.mem_bot] using hy'
  rw [hx, hy]

/-- Merging at `k` leaves the refined determinant class of the prefix
strictly before `k` unchanged. -/
theorem unitSquareClass_mergeAdjacentAt_prefixBefore
    {t : Nat} (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    unitSquareClass K
        (((W.mergeAdjacentAt k heq).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.val
          |>.refinedDeterminantUnit)) =
      unitSquareClass K
        ((W.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.val
          |>.refinedDeterminantUnit)) := by
  let P := (W.mergeAdjacentAt k heq).toOrthogonalDecomposition
  let Q := W.toOrthogonalDecomposition
  by_cases hk0 : k.val = 0
  · have hPsub : Subsingleton
        (P.prefixQuadraticSublattice k.val).carrier := by
      rw [hk0]
      exact prefixCarrier_zero_subsingleton P
    have hQsub : Subsingleton
        (Q.prefixQuadraticSublattice k.val).carrier := by
      rw [hk0]
      exact prefixCarrier_zero_subsingleton Q
    have hPone := Lattice.determinantClass_eq_one_of_subsingleton
      (P.prefixQuadraticSublattice k.val).space
      (P.prefixQuadraticSublattice k.val).lattice hPsub
    have hQone := Lattice.determinantClass_eq_one_of_subsingleton
      (Q.prefixQuadraticSublattice k.val).space
      (Q.prefixQuadraticSublattice k.val).lattice hQsub
    change unitSquareClass K
      (P.prefixQuadraticSublattice k.val |>.refinedDeterminantUnit) = 1
      at hPone
    change unitSquareClass K
      (Q.prefixQuadraticSublattice k.val |>.refinedDeterminantUnit) = 1
      at hQone
    exact hPone.trans hQone.symm
  · let cut := k.val
    have hcut : cut - 1 + 1 = cut := by
      dsimp only [cut]
      omega
    have hP : cut - 1 + 1 ≤ t := by
      rw [hcut]
      exact k.isLt.le
    have hQ : cut - 1 + 1 ≤ t + 1 := hP.trans (Nat.le_succ t)
    let F := P.prefixComponentwiseIsometryOfDifferentCounts Q hP hQ
      (fun z ↦ by
        let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
        let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
        have hjPVal : jP.val = z.val :=
          P.prefixIndexEquiv_val (cut - 1 + 1) hP z
        have hjQVal : jQ.val = z.val :=
          Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
        have hjPLt : jP < k := by
          change jP.val < k.val
          rw [hjPVal]
          have hz := z.isLt
          dsimp only [cut] at hz
          omega
        have hjEq : jP.castSucc = jQ := by
          apply Fin.ext
          change jP.val = jQ.val
          exact hjPVal.trans hjQVal.symm
        change Lattice.Isometry (P.component jP).space
          (Q.component jQ).space (P.component jP).lattice
          (Q.component jQ).lattice
        rw [show P.component jP = W.component jP.castSucc by
          simpa only [P] using
            W.mergeAdjacentAt_component_of_lt k heq jP hjPLt]
        rw [hjEq]
        exact Lattice.Isometry.refl _ _)
    have hdet := Lattice.determinantClass_eq_of_isometry F
    change unitSquareClass K
        (P.prefixQuadraticSublattice (cut - 1 + 1)
          |>.refinedDeterminantUnit) =
      unitSquareClass K
        (Q.prefixQuadraticSublattice (cut - 1 + 1)
          |>.refinedDeterminantUnit) at hdet
    rw [hcut] at hdet
    simpa only [P, Q, cut] using hdet

/-- Witness form for the unchanged prefix before an amalgamated pair. -/
theorem exists_mergeAdjacentAt_prefixBefore_mul_square
    {t : Nat} (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    ∃ s : Kˣ,
      (W.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.val
          |>.refinedDeterminantUnit) * s ^ 2 =
        ((W.mergeAdjacentAt k heq).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.val
          |>.refinedDeterminantUnit) := by
  exact BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq _ _
    (W.unitSquareClass_mergeAdjacentAt_prefixBefore k heq).symm

/-- Merging an adjacent pair does not change the refined determinant class
of the prefix through that pair. -/
theorem unitSquareClass_mergeAdjacentAt_prefixThrough
    {t : Nat} (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    unitSquareClass K
        (((W.mergeAdjacentAt k heq).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (k.val + 1)
          |>.refinedDeterminantUnit)) =
      unitSquareClass K
        ((W.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (k.val + 2)
          |>.refinedDeterminantUnit)) := by
  let P := (W.mergeAdjacentAt k heq).toOrthogonalDecomposition
  let Q := W.toOrthogonalDecomposition
  let dP0 : Kˣ :=
    (P.prefixQuadraticSublattice k.val).refinedDeterminantUnit
  let dQ0 : Kˣ :=
    (Q.prefixQuadraticSublattice k.val).refinedDeterminantUnit
  let dLeft : Kˣ := (Q.component k.castSucc).refinedDeterminantUnit
  let dRight : Kˣ := (Q.component k.succ).refinedDeterminantUnit
  let dMerged : Kˣ := (P.component k).refinedDeterminantUnit
  have hbefore : unitSquareClass K dP0 = unitSquareClass K dQ0 := by
    by_cases hk0 : k.val = 0
    · have hPsub : Subsingleton
          (P.prefixQuadraticSublattice k.val).carrier := by
        rw [hk0]
        exact prefixCarrier_zero_subsingleton P
      have hQsub : Subsingleton
          (Q.prefixQuadraticSublattice k.val).carrier := by
        rw [hk0]
        exact prefixCarrier_zero_subsingleton Q
      have hPone := Lattice.determinantClass_eq_one_of_subsingleton
        (P.prefixQuadraticSublattice k.val).space
        (P.prefixQuadraticSublattice k.val).lattice hPsub
      have hQone := Lattice.determinantClass_eq_one_of_subsingleton
        (Q.prefixQuadraticSublattice k.val).space
        (Q.prefixQuadraticSublattice k.val).lattice hQsub
      change unitSquareClass K dP0 = 1 at hPone
      change unitSquareClass K dQ0 = 1 at hQone
      exact hPone.trans hQone.symm
    · let cut := k.val
      have hcut : cut - 1 + 1 = cut := by
        dsimp only [cut]
        omega
      have hP : cut - 1 + 1 ≤ t := by
        rw [hcut]
        exact k.isLt.le
      have hQ : cut - 1 + 1 ≤ t + 1 := hP.trans (Nat.le_succ t)
      let F := P.prefixComponentwiseIsometryOfDifferentCounts Q hP hQ
        (fun z ↦ by
          let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
          let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
          have hjPVal : jP.val = z.val :=
            P.prefixIndexEquiv_val (cut - 1 + 1) hP z
          have hjQVal : jQ.val = z.val :=
            Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
          have hjPLt : jP < k := by
            change jP.val < k.val
            rw [hjPVal]
            have hz := z.isLt
            dsimp only [cut] at hz
            omega
          have hjEq : jP.castSucc = jQ := by
            apply Fin.ext
            change jP.val = jQ.val
            exact hjPVal.trans hjQVal.symm
          change Lattice.Isometry (P.component jP).space
            (Q.component jQ).space (P.component jP).lattice
            (Q.component jQ).lattice
          rw [show P.component jP = W.component jP.castSucc by
            simpa only [P] using W.mergeAdjacentAt_component_of_lt k heq jP hjPLt]
          rw [hjEq]
          exact Lattice.Isometry.refl _ _)
      have hdet := Lattice.determinantClass_eq_of_isometry F
      change unitSquareClass K
          (P.prefixQuadraticSublattice (cut - 1 + 1)
            |>.refinedDeterminantUnit) =
        unitSquareClass K
          (Q.prefixQuadraticSublattice (cut - 1 + 1)
            |>.refinedDeterminantUnit) at hdet
      rw [hcut] at hdet
      simpa only [dP0, dQ0, cut] using hdet
  have hmerged : unitSquareClass K dMerged =
      unitSquareClass K dLeft * unitSquareClass K dRight := by
    have hdet := Lattice.determinantClass_eq_of_isometry
      (Q.orthogonalSupLatticeIsometry k.castSucc_lt_succ.ne)
    rw [Lattice.determinantClass_orthogonalProduct] at hdet
    change unitSquareClass K dLeft * unitSquareClass K dRight =
      unitSquareClass K
        ((Q.orthogonalSup k.castSucc_lt_succ.ne).refinedDeterminantUnit)
      at hdet
    have hcomponent : P.component k =
        Q.orthogonalSup k.castSucc_lt_succ.ne := by
      simpa only [P, Q] using W.mergeAdjacentAt_component_self k heq
    change unitSquareClass K
      ((P.component k).refinedDeterminantUnit) =
        unitSquareClass K dLeft * unitSquareClass K dRight
    rw [hcomponent]
    exact hdet.symm
  have hPstep := P.unitSquareClass_prefix_succ_eq_mul_component k
  have hQleft := Q.unitSquareClass_prefix_succ_eq_mul_component k.castSucc
  have hQright := Q.unitSquareClass_prefix_succ_eq_mul_component k.succ
  rw [unitSquareClass_mul] at hPstep hQleft hQright
  change unitSquareClass K
      (P.prefixQuadraticSublattice (k.val + 1)
        |>.refinedDeterminantUnit) =
    unitSquareClass K dP0 * unitSquareClass K dMerged at hPstep
  change unitSquareClass K
      (Q.prefixQuadraticSublattice (k.val + 1)
        |>.refinedDeterminantUnit) =
    unitSquareClass K dQ0 * unitSquareClass K dLeft at hQleft
  change unitSquareClass K
      (Q.prefixQuadraticSublattice (k.val + 2)
        |>.refinedDeterminantUnit) =
    unitSquareClass K
        (Q.prefixQuadraticSublattice (k.val + 1)
          |>.refinedDeterminantUnit) *
      unitSquareClass K dRight at hQright
  calc
    unitSquareClass K
        (P.prefixQuadraticSublattice (k.val + 1)
          |>.refinedDeterminantUnit) =
        unitSquareClass K dP0 * unitSquareClass K dMerged := hPstep
    _ = unitSquareClass K dQ0 *
        (unitSquareClass K dLeft * unitSquareClass K dRight) := by
      rw [hbefore, hmerged]
    _ = (unitSquareClass K dQ0 * unitSquareClass K dLeft) *
        unitSquareClass K dRight := by ac_rfl
    _ = unitSquareClass K
        (Q.prefixQuadraticSublattice (k.val + 1)
          |>.refinedDeterminantUnit) * unitSquareClass K dRight := by
      rw [← hQleft]
    _ = unitSquareClass K
        (Q.prefixQuadraticSublattice (k.val + 2)
          |>.refinedDeterminantUnit) := hQright.symm

/-- Witness form of `unitSquareClass_mergeAdjacentAt_prefixThrough`. -/
theorem exists_mergeAdjacentAt_prefixThrough_mul_square
    {t : Nat} (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    ∃ s : Kˣ,
      (W.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (k.val + 2)
          |>.refinedDeterminantUnit) * s ^ 2 =
        ((W.mergeAdjacentAt k heq).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (k.val + 1)
          |>.refinedDeterminantUnit) := by
  exact BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq _ _
    (W.unitSquareClass_mergeAdjacentAt_prefixThrough k heq).symm

end Lattice.WeakJordanDecomposition

end Bong
