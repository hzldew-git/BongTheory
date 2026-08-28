/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma32ProfileSeeds
import Bong.Bong.Beli2019PrefixChange

/-!
# Determinant approximations at the right end of a Jordan component

The determinant seed of Beli (2019), Lemma 3.2 is stated at the left end of
a strict Jordan component.  This file records the equivalent right-end form:
the determinant of the prefix through a component is a prefix approximation
at that component's stop.  At an internal boundary this is the next
component's O'Meara 93:28 seed; at the final boundary it follows from the
determinant class of the whole lattice.
-/

namespace Bong

open Dyadic Module
open scoped BigOperators

universe u v

namespace BONG.WeakJordanOrderProfileWitness

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

set_option maxHeartbeats 0 in
/-- The determinant of the strict Jordan prefix through `p` approximates
the good-BONG prefix at the numerical stop of `p`.  The final-component
case includes the full-prefix endpoint, where the prefix cap is infinite. -/
theorem prefixThrough_isPrefixApproximation
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    {n t : Nat} (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t) :
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    a.IsPrefixApproximation C.stop
      ((W.toJordan hstrict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)
        |>.refinedDeterminantUnit) := by
  classical
  dsimp only
  let w := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  let J := W.toJordan hstrict
  let Q := J.toOrthogonalDecomposition
  let dP : Kˣ :=
    (Q.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit
  change a.IsPrefixApproximation C.stop dP
  by_cases hnext : p.val + 1 < t
  · let pNext : Fin t := ⟨p.val + 1, hnext⟩
    let Cnext := w.jordanBlockCoordinates hW pNext
    have hIio : Finset.Iio pNext = insert p (Finset.Iio p) := by
      ext j
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change (j.val < p.val + 1 ↔ j = p ∨ j.val < p.val)
      constructor
      · intro hj
        by_cases heq : j.val = p.val
        · exact Or.inl (Fin.ext heq)
        · exact Or.inr (by omega)
      · rintro (rfl | hj)
        · omega
        · omega
    have hstart : Cnext.start = C.stop := by
      change
        (∑ k ∈ Finset.Iio pNext,
          finrank K (W.component k).carrier) =
        (∑ k ∈ Finset.Iio p,
          finrank K (W.component k).carrier) +
            finrank K (W.component p).carrier
      rw [hIio, Finset.sum_insert (by simp)]
      omega
    let determinant := strictDeterminantSeedDataAny
      W hW hstrict P pNext
    have hseed := determinant.evenSeed
    have hpNextNe : pNext.val ≠ 0 := by
      dsimp only [pNext]
      omega
    have hleft :=
      strictDeterminantSeedDataAny_leftDet_of_component_ne_zero
        W hW hstrict P pNext hpNextNe
    change a.IsPrefixApproximation Cnext.start determinant.leftDet at hseed
    change determinant.leftDet =
      (Q.prefixQuadraticSublattice pNext.val).refinedDeterminantUnit at hleft
    rw [hstart, hleft] at hseed
    simpa only [dP, pNext] using hseed
  · have hpLast : p.val + 1 = t := by
      have hp := p.isLt
      omega
    have hUniv : (Finset.univ : Finset (Fin t)) =
        insert p (Finset.Iio p) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_Iio,
        true_iff]
      by_cases heq : j = p
      · exact Or.inl heq
      · exact Or.inr (by
          have hj := j.isLt
          have hneVal : j.val ≠ p.val := by
            intro h
            exact heq (Fin.ext h)
          omega)
    have hsum := w.sum_componentRank_eq_length
    rw [hUniv, Finset.sum_insert (by simp)] at hsum
    have hstop : C.stop = n + 2 := by
      change
        (∑ k ∈ Finset.Iio p,
          finrank K (W.component k).carrier) +
            finrank K (W.component p).carrier = n + 2
      omega
    have hfullClassRaw :=
      Lattice.determinantClass_eq_of_isometry Q.fullPrefixLatticeIsometry
    have hfullClass : unitSquareClass K dP =
        Lattice.determinantClass q L := by
      change Lattice.determinantClass
          (Q.prefixQuadraticSublattice (p.val + 1)).space
          (Q.prefixQuadraticSublattice (p.val + 1)).lattice =
        Lattice.determinantClass q L
      rw [hpLast]
      exact hfullClassRaw
    have hprefixFull : a.prefixProduct (n + 2) =
        a.toBONG.valueProduct :=
      a.prefixProduct_eq_valueProduct_of_rank_le (n + 2) le_rfl
    have hvalueClass := a.toBONG.determinantClass_eq_valueProduct
    have hclass : unitSquareClass K (a.prefixProduct (n + 2)) =
        unitSquareClass K dP := by
      calc
        unitSquareClass K (a.prefixProduct (n + 2)) =
            unitSquareClass K a.toBONG.valueProduct :=
          congrArg (unitSquareClass K) hprefixFull
        _ = Lattice.determinantClass q L := hvalueClass.symm
        _ = unitSquareClass K dP := hfullClass.symm
    obtain ⟨s, hs⟩ :=
      BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq
        (a.prefixProduct (n + 2)) dP hclass
    have hcanonical := a.isPrefixApproximation_prefixProduct (n + 2)
    have happrox : a.IsPrefixApproximation (n + 2) dP := by
      rw [← hs]
      exact (a.isPrefixApproximation_mul_square_iff
        (n + 2) (a.prefixProduct (n + 2)) s).2 hcanonical
    rw [hstop]
    exact happrox

end BONG.WeakJordanOrderProfileWitness

end Bong
