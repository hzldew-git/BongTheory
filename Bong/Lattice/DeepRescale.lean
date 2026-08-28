/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DeterminantBasis
import Bong.Lattice.PowerIdeal
import Mathlib.Data.Finset.Order

/-!
# Deep containment of lattices

This file isolates the part of O'Meara, Proposition 81:1, used by the
deep-complement argument in Beli (2019): a lattice can be multiplied deeply
enough into any full target lattice.  Over the discretely valued field used
here, the multiplier may be chosen to be an arbitrarily high power of the
fixed uniformizer.

The proof is the finite-coordinate proof from O'Meara: write one integral
basis in the other, then clear the finitely many negative coordinate orders.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

private noncomputable def coordinateDepth
    (A L : Lattice K V)
    (ij : Fin (finrank K V) × Fin (finrank K V)) : Int := by
  classical
  let x := L.standardAmbientBasis.repr (A.standardAmbientBasis ij.1) ij.2
  exact if hx : x = 0 then 0 else -ordUnit K (Units.mk0 x hx)

/-- Given two full lattices and any prescribed depth, a sufficiently high
uniformizer power sends the first lattice into the second.  This is the DVR
form of the containment direction of O'Meara, Proposition 81:1. -/
theorem exists_uniformizerPower_rescale_le
    (A L : Lattice K V) (k₀ : Int) :
    ∃ k : Int, k₀ ≤ k ∧
      rescale (uniformizerPowerUnit K k) A ≤ L := by
  classical
  let depths : Finset Int :=
    Finset.univ.image (coordinateDepth A L)
  obtain ⟨k₁, hk₁⟩ := Finset.exists_le depths
  let k := max k₀ k₁
  refine ⟨k, le_max_left _ _, ?_⟩
  rw [← basisLattice_standardAmbientBasis A,
    rescale_basisLattice,
    ← basisLattice_standardAmbientBasis L]
  intro x hx
  change x ∈ Submodule.span (IntegerRing K)
    (Set.range ((uniformizerPowerUnit K k) • A.standardAmbientBasis)) at hx
  change x ∈ basisLattice L.standardAmbientBasis
  refine Submodule.span_induction
    (p := fun x _ ↦ x ∈ basisLattice L.standardAmbientBasis) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [Basis.smul_apply]
    apply (mem_basisLattice_iff_repr_mem_integerRing
      L.standardAmbientBasis _).2
    intro j
    change L.standardAmbientBasis.repr
      ((uniformizerPowerUnit K k : K) • A.standardAmbientBasis i) j ∈
        IntegerRing K
    rw [map_smul]
    let c : K :=
      L.standardAmbientBasis.repr (A.standardAmbientBasis i) j
    change (uniformizerPowerUnit K k : K) * c ∈ IntegerRing K
    by_cases hc : c = 0
    · simp [hc]
    rw [mem_integerRing_iff, Dyadic.IsIntegral, ord_mul,
      ← coe_ordUnit K (uniformizerPowerUnit K k),
      ordUnit_uniformizerPowerUnit]
    have hordc : ord K c =
        (ordUnit K (Units.mk0 c hc) : WithTop Int) := by
      simpa using (coe_ordUnit K (Units.mk0 c hc)).symm
    rw [hordc, ← WithTop.coe_add]
    have hdepth : coordinateDepth A L (i, j) ≤ k₁ := by
      apply hk₁
      simp [depths]
    simp [coordinateDepth, c, hc] at hdepth
    change -ordUnit K (Units.mk0 c hc) ≤ k₁ at hdepth
    have hInt : 0 ≤ k + ordUnit K (Units.mk0 c hc) := by
      dsimp [k]
      omega
    exact_mod_cast hInt
  · exact (basisLattice L.standardAmbientBasis).zero_mem
  · intro y z _ _ hy hz
    exact (basisLattice L.standardAmbientBasis).add_mem hy hz
  · intro c y _ hy
    exact (basisLattice L.standardAmbientBasis).smul_mem c hy

end Lattice

end Bong
