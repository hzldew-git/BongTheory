/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Modular
import Bong.Lattice.NormGeneratorValues

/-!
# Changing the chosen modular parameter

The parameter of a modular lattice is a generator of its scale ideal, so it
may be multiplied by a valuation unit without changing modularity.  This is
the normalization used when equal-scale raw Jordan blocks are amalgamated.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Rescaling a lattice by a valuation unit does not change it. -/
theorem rescale_eq_self_of_isValuationUnit
    (L : Lattice K V) (u : Kˣ)
    (hu : IsValuationUnit K (u : K)) :
    rescale u L = L := by
  apply Lattice.ext
  apply le_antisymm
  · exact rescale_le_self_of_mem_integerRing u L
      ((mem_integerRing_iff K).2 (by
        rw [Dyadic.IsIntegral]
        exact hu.ge))
  · intro x hx
    have huInv : IsValuationUnit K ((u⁻¹ : Kˣ) : K) := by
      simpa [IsValuationUnit, AddValuation.map_inv, hu]
    have huInvIntegral : ((u⁻¹ : Kˣ) : K) ∈ IntegerRing K :=
      (mem_integerRing_iff K).2 (by
        rw [Dyadic.IsIntegral]
        exact huInv.ge)
    let uInvO : IntegerRing K := ⟨((u⁻¹ : Kˣ) : K), huInvIntegral⟩
    have hmem : ((u⁻¹ : Kˣ) : K) • x ∈ L := L.smul_mem uInvO hx
    change x ∈ rescale u L
    rw [mem_rescale_iff]
    refine ⟨((u⁻¹ : Kˣ) : K) • x, hmem, ?_⟩
    simp [smul_smul]

/-- Equal nonzero principal ideals give the same lattice rescaling. -/
theorem rescale_eq_of_principalIdeal_eq
    (L : Lattice K V) (a b : Kˣ)
    (h : principalIdeal (K := K) (a : K) =
      principalIdeal (K := K) (b : K)) :
    rescale a L = rescale b L := by
  obtain ⟨u, hu, hua⟩ :=
    exists_valuationUnit_mul_eq_of_principalIdeal_eq a b h
  rw [← hua]
  calc
    rescale a L = rescale a (rescale u L) :=
      congrArg (Lattice.rescale a)
        (rescale_eq_self_of_isValuationUnit L u hu).symm
    _ = rescale (a * u) L := (rescale_mul a u L).symm
    _ = rescale (u * a) L := by rw [mul_comm]

/-- A modular lattice may be expressed using any generator of the same
principal scale ideal. -/
theorem IsModular.of_principalIdeal_eq
    {q : QuadraticSpace K V} {L : Lattice K V} {a b : Kˣ}
    (hmodular : IsModular q L a)
    (h : principalIdeal (K := K) (a : K) =
      principalIdeal (K := K) (b : K)) :
    IsModular q L b := by
  rw [IsModular, hmodular]
  obtain ⟨u, hu, hua⟩ :=
    exists_valuationUnit_mul_eq_of_principalIdeal_eq a b h
  have huInv : IsValuationUnit K ((u⁻¹ : Kˣ) : K) := by
    simpa [IsValuationUnit, AddValuation.map_inv, hu]
  have hinv : b⁻¹ = u⁻¹ * a⁻¹ := by
    rw [← hua]
    simp [mul_comm]
  rw [hinv]
  calc
    Lattice.rescale a⁻¹ L =
        Lattice.rescale a⁻¹ (Lattice.rescale u⁻¹ L) :=
      congrArg (Lattice.rescale a⁻¹)
        (rescale_eq_self_of_isValuationUnit L u⁻¹ huInv).symm
    _ = Lattice.rescale (a⁻¹ * u⁻¹) L :=
      (rescale_mul a⁻¹ u⁻¹ L).symm
    _ = Lattice.rescale (u⁻¹ * a⁻¹) L := by rw [mul_comm]

end Lattice

end Bong
