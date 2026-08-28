/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.HilbertSymbol
import Bong.Lattice.Projection
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The base dyadic field `ℚ_[2]`

This file is both the first concrete instance and an executable smoke test for
the M0 interface.
-/

namespace BongTest.Q2

open Bong
open Bong.Dyadic

noncomputable section

noncomputable instance q2ValuativeRel : ValuativeRel ℚ_[2] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[2]))

instance q2NormCompatible :
    (NormedField.valuation (K := ℚ_[2])).Compatible :=
  Valuation.Compatible.ofValuation _

instance q2IsValuativeTopology : IsValuativeTopology ℚ_[2] :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (NormedField.valuation (K := ℚ_[2])) fun {s} ↦
      @Valued.is_topological_valuation ℚ_[2] _ NNReal _
        (NormedField.toValued (K := ℚ_[2])) s

instance q2IsNontrivial : ValuativeRel.IsNontrivial ℚ_[2] := by
  rw [ValuativeRel.isNontrivial_iff_isNontrivial
    (NormedField.valuation (K := ℚ_[2]))]
  infer_instance

noncomputable instance q2LocalField : IsNonarchimedeanLocalField ℚ_[2] := by
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

private theorem addValuation_isEquiv_norm :
    (AddValuation.toValuation (Padic.addValuation (p := 2))).IsEquiv
      (NormedField.valuation (K := ℚ_[2])) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  change 0 ≤ Padic.addValuation x ↔ NormedField.valuation x ≤ 1
  by_cases hx : x = 0
  · simp [hx]
  · rw [Padic.addValuation.apply hx, NormedField.valuation_apply]
    simpa only [WithTop.coe_nonneg, ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm] using
      (Padic.norm_le_one_iff_val_nonneg x).symm

private instance q2OrdCompatible :
    (AddValuation.toValuation (Padic.addValuation (p := 2))).Compatible where
  vle_iff_le x y :=
    (Valuation.vle_iff_le (NormedField.valuation (K := ℚ_[2]))).trans
      (addValuation_isEquiv_norm x y).symm

private theorem addValuation_two : Padic.addValuation (2 : ℚ_[2]) = 1 := by
  simp [Padic.addValuation.apply]

noncomputable instance q2DyadicContext : DyadicContext ℚ_[2] where
  ord := Padic.addValuation
  ordCompatible := q2OrdCompatible
  uniformizer := 2
  ordUniformizer := addValuation_two
  ordTwoPos := by
    rw [addValuation_two]
    exact zero_lt_one

example : DyadicContext ℚ_[2] := inferInstance

example : ord ℚ_[2] (0 : ℚ_[2]) = ⊤ := by simp

@[simp]
theorem ord_two : ord ℚ_[2] (2 : ℚ_[2]) = 1 := by
  change Padic.addValuation (2 : ℚ_[2]) = 1
  exact addValuation_two

example : 0 < ord ℚ_[2] (2 : ℚ_[2]) :=
  ord_two_pos ℚ_[2]

example : ord ℚ_[2] ((2 : ℚ_[2]) * 2) = 2 := by
  rw [ord_mul, ord_two]
  norm_num

@[simp]
theorem ramificationIndex_q2 : ramificationIndex ℚ_[2] = 1 := by
  have h := ramificationIndex_spec ℚ_[2]
  rw [ord_two] at h
  exact_mod_cast h

example : quadraticDefect ℚ_[2] (1 : ℚ_[2]ˣ) = ⊤ := by
  apply quadraticDefect_eq_top_of_isSquare
  exact ⟨1, by simp⟩

example : hilbertSymbol ℚ_[2] (1 : ℚ_[2]ˣ) (-1 : ℚ_[2]ˣ) = 1 := by
  simp

noncomputable def unaryLattice : Lattice ℚ_[2] ℚ_[2] :=
  Lattice.ofFinset {1} (by simp)

example : (1 : ℚ_[2]) ∈ unaryLattice := by
  apply Lattice.subset_ofFinset
  simp

example (x : ℚ_[2]) : (QuadraticSpace.line ℚ_[2]).quadratic x = x ^ 2 := by
  simp

example : (1 : ℚ_[2]) ∈ Lattice.scaleIdeal (QuadraticSpace.line ℚ_[2]) unaryLattice := by
  have h1 : (1 : ℚ_[2]) ∈ unaryLattice := by
    apply Lattice.subset_ofFinset
    simp
  simpa using Lattice.bilin_mem_scaleIdeal_of_mem
    (QuadraticSpace.line ℚ_[2]) unaryLattice h1 h1

example : (1 : ℚ_[2]) ∈ Lattice.normIdeal (QuadraticSpace.line ℚ_[2]) unaryLattice := by
  have h1 : (1 : ℚ_[2]) ∈ unaryLattice := by
    apply Lattice.subset_ofFinset
    simp
  simpa using Lattice.quadratic_mem_normIdeal_of_mem
    (QuadraticSpace.line ℚ_[2]) unaryLattice h1

example : (2 : ℚ_[2]) ∈ Lattice.normIdeal (QuadraticSpace.line ℚ_[2]) unaryLattice := by
  have hs : (1 : ℚ_[2]) ∈ Lattice.scaleIdeal (QuadraticSpace.line ℚ_[2]) unaryLattice := by
    have h1 : (1 : ℚ_[2]) ∈ unaryLattice := by
      apply Lattice.subset_ofFinset
      simp
    simpa using Lattice.bilin_mem_scaleIdeal_of_mem
      (QuadraticSpace.line ℚ_[2]) unaryLattice h1 h1
  simpa only [Algebra.smul_def, map_ofNat, mul_one] using Lattice.two_smul_mem_normIdeal
    (QuadraticSpace.line ℚ_[2]) unaryLattice hs

example (y : ℚ_[2]) :
    (QuadraticSpace.line ℚ_[2]).orthogonalProjection 1 y = 0 := by
  rw [QuadraticSpace.orthogonalProjection_apply]
  simp

noncomputable def projectedUnaryLattice :
    Lattice ℚ_[2] ((QuadraticSpace.line ℚ_[2]).vectorOrthogonal 1) :=
  Lattice.projectedLattice (QuadraticSpace.line ℚ_[2]) unaryLattice 1 (by
    simp [QuadraticSpace.IsAnisotropic])

end

end BongTest.Q2
