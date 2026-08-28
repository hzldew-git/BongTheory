/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaBinaryModularSplitting
import Bong.Lattice.OmearaNormPreservingBinarySplitting
import Bong.Lattice.RankOneNormScale

/-!
# Odd-rank modular lattices are proper

O'Meara 93:15 says that an improper modular lattice has even rank.  The
contrapositive needed in 93:18(iv)--(v) is proved here by repeatedly
splitting a binary modular summand.  An odd-rank remainder terminates in
rank one, where norm and scale ideals coincide.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- O'Meara 93:15, odd-rank form: an odd-rank modular lattice has equal
norm and scale ideals. -/
theorem normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hmodular : IsModular q L a)
    (hrankOdd : Odd (finrank K V)) :
    normIdeal q L = scaleIdeal q L := by
  letI : Module.Finite K V := L.moduleFinite
  have hpos : 0 < finrank K V := by
    rcases hrankOdd with ⟨k, hk⟩
    omega
  by_cases hone : finrank K V = 1
  · exact normIdeal_eq_scaleIdeal_of_finrank_eq_one q L hone
  · have hthree : 3 ≤ finrank K V := by
      rcases hrankOdd with ⟨k, hk⟩
      omega
    let D := binaryModularSplittingData q L a hmodular (by omega)
    let J := D.decomposition.component 0
    let C := D.decomposition.component 1
    letI : Module.Finite K J.carrier := J.lattice.moduleFinite
    letI : Module.Finite K C.carrier := C.lattice.moduleFinite
    have htotal :=
      D.decomposition.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
    have hCrank : finrank K C.carrier = finrank K V - 2 := by
      change finrank K (J.carrier × C.carrier) = finrank K V at htotal
      rw [Module.finrank_prod, D.first_rank] at htotal
      omega
    have hCOdd : Odd (finrank K C.carrier) := by
      rcases hrankOdd with ⟨k, hk⟩
      have hkpos : 0 < k := by omega
      refine ⟨k - 1, ?_⟩
      rw [hCrank]
      omega
    have hCProper := normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
      C.space C.lattice a D.complement_modular hCOdd
    have hCpos : 0 < finrank K C.carrier := by
      rcases hCOdd with ⟨k, hk⟩
      omega
    have hCnorm : normIdeal C.space C.lattice =
        principalIdeal (K := K) (a : K) :=
      hCProper.trans
        (D.complement_modular.scaleIdeal_eq_principal hCpos)
    have hJle : normIdeal J.space J.lattice ≤
        principalIdeal (K := K) (a : K) := by
      exact (normIdeal_le_scaleIdeal J.space J.lattice).trans_eq
        (D.first_modular.scaleIdeal_eq_principal (by
          rw [D.first_rank]
          omega))
    calc
      normIdeal q L =
          normIdeal J.space J.lattice ⊔
            normIdeal C.space C.lattice :=
        NormPreservingBinaryModularSplittingData.normIdeal_eq_sup_components
          D.decomposition
      _ = principalIdeal (K := K) (a : K) := by
        rw [hCnorm]
        exact sup_eq_right.mpr hJle
      _ = scaleIdeal q L :=
        (hmodular.scaleIdeal_eq_principal hpos).symm
termination_by finrank K V
decreasing_by
  rw [hCrank]
  omega

/-- A represented valuation unit in a positive odd-rank unimodular
lattice.  This is the choice denoted by `epsilon in Q(L)` in 93:18(iv). -/
structure OddRankUnimodularUnitValueData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) where
  vector : V
  vector_mem : vector ∈ L
  value_ne : q.quadratic vector ≠ 0
  valueUnit : Kˣ
  valueUnit_eq : (valueUnit : K) = q.quadratic vector
  value_isValuationUnit : IsValuationUnit K (valueUnit : K)

/-- Construct the represented unit supplied by odd-rank properness. -/
noncomputable def oddRankUnimodularUnitValueData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrankOdd : Odd (finrank K V)) :
    OddRankUnimodularUnitValueData q L := by
  letI : Module.Finite K V := L.moduleFinite
  have hpos : 0 < finrank K V := by
    rcases hrankOdd with ⟨k, hk⟩
    omega
  let hexists := exists_isNormGenerator_of_finrank_pos q L hpos
  let x : V := Classical.choose hexists
  have hx : IsNormGenerator q L x :=
    (Classical.choose_spec hexists).1
  have hxne : q.quadratic x ≠ 0 :=
    (Classical.choose_spec hexists).2
  let epsilon : Kˣ := Units.mk0 (q.quadratic x) hxne
  have hideal : principalIdeal (K := K) (epsilon : K) =
      principalIdeal (K := K) (1 : K) := by
    calc
      principalIdeal (K := K) (epsilon : K) = normIdeal q L := by
        simpa only [epsilon, Units.val_mk0] using hx.normIdeal_eq.symm
      _ = scaleIdeal q L :=
        normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
          q L (1 : Kˣ) hmodular hrankOdd
      _ = principalIdeal (K := K) (1 : K) :=
        hmodular.scaleIdeal_eq_principal hpos
  have horder : ordUnit K epsilon = 0 := by
    have h := (principalIdeal_eq_iff_ordUnit_eq epsilon (1 : Kˣ)).mp
      (by simpa using hideal)
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have honeMul := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at honeMul
      omega
    rwa [hone] at h
  exact
    { vector := x
      vector_mem := hx.mem
      value_ne := hxne
      valueUnit := epsilon
      valueUnit_eq := rfl
      value_isValuationUnit :=
        (isValuationUnit_iff_ordUnit_eq_zero K epsilon).2 horder }

end Lattice

end Bong
