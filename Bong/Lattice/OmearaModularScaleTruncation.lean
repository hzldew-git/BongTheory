/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.OmearaNormGroupShift

/-!
# Scale truncations of modular lattices

For an `s`-modular lattice, O'Meara's scale truncation at `s O` is the
whole lattice.  This elementary normalization is used in 93:19 to feed a
norm-group element of the modular complement directly into 93:13.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

/-- If `L` is `s`-modular, then `L_{s O} = L`. -/
theorem omearaScaleTruncation_eq_of_isModular
    (hL : IsModular q L s) :
    omearaScaleTruncation q L s = L := by
  unfold omearaScaleTruncation
  rw [dualLattice_rescaleQuadraticUnit, hL]
  rw [inv_inv, rescale_rescale_inv]
  apply Lattice.ext
  ext x
  change (x ∈ L ∧ x ∈ L) ↔ x ∈ L
  simp

/-- On an `s`-modular lattice, the norm group of the scale truncation is
literally the original norm group. -/
theorem normGroupSet_omearaScaleTruncation_eq_of_isModular
    (hL : IsModular q L s) :
    normGroupSet q (omearaScaleTruncation q L s) = normGroupSet q L := by
  rw [omearaScaleTruncation_eq_of_isModular hL]

/-- Every norm-group element of an `s`-modular lattice is divisible by
the modular scale.  The quotient is integral and is the coefficient used in
the middle line of O'Meara 93:19. -/
theorem exists_integral_factor_of_mem_normGroupSet_of_isModular
    (hL : IsModular q L s) {delta : K}
    (hdelta : delta ∈ normGroupSet q L) :
    ∃ gamma : K, gamma ∈ IntegerRing K ∧
      delta = (s : K) * gamma := by
  have hprincipal : delta ∈ principalIdeal (K := K) (s : K) :=
    hL.scaleIdeal_le_principal
      (normIdeal_le_scaleIdeal q L
        (normGroupSet_subset_normIdeal q L hdelta))
  rw [principalIdeal, Submodule.mem_span_singleton] at hprincipal
  rcases hprincipal with ⟨gamma, hgamma⟩
  refine ⟨gamma, gamma.property, ?_⟩
  simpa [Algebra.smul_def, mul_comm] using hgamma.symm

/-- The integral quotient of a norm-group element can be fed directly into
93:13 because the modular scale truncation is the whole lattice. -/
theorem integral_factor_mem_truncationNormGroup_of_isModular
    (hL : IsModular q L s) {delta gamma : K}
    (hdelta : delta ∈ normGroupSet q L)
    (hfactor : delta = (s : K) * gamma) :
    (s : K) * gamma ∈
      normGroupSet q (omearaScaleTruncation q L s) := by
  rw [omearaScaleTruncation_eq_of_isModular hL, ← hfactor]
  exact hdelta

end Lattice

end Bong
