/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.He2023ADCNonDyadicTheorem110

/-!
# He (2025), non-dyadic Proposition 4.16

This module separates the finite case split in the publisher's proof from
the remaining local-lattice realization facts.  The row dichotomy is proved
in `He2023ADCNonDyadicTable`; the structure below lists only the bridges from
those symbolic blocks to actual representation and integral isometry.
-/

namespace Bong

universe u

namespace HeADC2025NonDyadicSystem

variable (S : HeADC2025NonDyadicSystem.{u})

/-- Realization and transport facts needed to interpret the symbolic
quaternary table as Proposition 4.16. -/
structure QuaternaryTableRealizationLaws
    (isometric : S.Lattice → S.Lattice → Prop) where
  hyperbolicPlane : S.Lattice
  anisotropicPlane : S.Lattice
  scaledAnisotropicPlane : S.Lattice
  orthogonalSum : S.Lattice → S.Lattice → S.Lattice
  isometric_trans {L M N : S.Lattice} :
    isometric L M → isometric M N → isometric L N
  represents_of_isometric_left {L M N : S.Lattice} :
    isometric L M → S.represents M N → S.represents L N
  target_represents_hyperbolic_of_mem
      (nu : HeADC2025NonDyadicColumn)
      (c : HeADC2025NonDyadicSquareClass) :
    .hyperbolic ∈ heADC2025NonDyadicEvenTableRow 2 nu c →
      S.represents (S.target nu 4 c) hyperbolicPlane
  exceptional_target_isometric :
    isometric (S.target .two 4 .one)
      (orthogonalSum anisotropicPlane scaledAnisotropicPlane)

namespace QuaternaryTableRealizationLaws

variable {S : HeADC2025NonDyadicSystem.{u}}
  {I : S.Lemma45InvariantData}
  {P : S.Proposition42InvariantData I}
  {isometric : S.Lattice → S.Lattice → Prop}

/-- He (2025), Proposition 4.16 over a non-dyadic local field, with the
actual realization and maximal-lattice classification inputs explicit. -/
theorem heADC2025Proposition416NonDyadic
    (H : S.CatalogueLaws I P isometric)
    (R : S.QuaternaryTableRealizationLaws isometric)
    (N : S.Lattice) (hRank : S.rank N = 4) (hMaximal : S.isMaximal N) :
    (isometric N (S.target .two 4 .one) ∧
      isometric N
        (R.orthogonalSum R.anisotropicPlane R.scaledAnisotropicPlane)) ∨
      S.represents N R.hyperbolicPlane := by
  obtain ⟨nu, c, _, hN⟩ :=
    H.maximal_complete N 4 (by omega) hRank hMaximal
  rcases heADC2025NonDyadicQuaternaryRow_dichotomy nu c with
    hExceptional | hHyperbolic
  · rcases hExceptional with ⟨rfl, rfl, _⟩
    exact Or.inl ⟨hN, R.isometric_trans hN R.exceptional_target_isometric⟩
  · exact Or.inr (R.represents_of_isometric_left hN
      (R.target_represents_hyperbolic_of_mem nu c hHyperbolic))

/-- Outside the unique exceptional table class, a maximal quaternary lattice
represents the hyperbolic plane. -/
theorem heADC2025Proposition416NonDyadic_represents
    (H : S.CatalogueLaws I P isometric)
    (R : S.QuaternaryTableRealizationLaws isometric)
    (N : S.Lattice) (hRank : S.rank N = 4) (hMaximal : S.isMaximal N)
    (hNotExceptional : ¬ isometric N (S.target .two 4 .one)) :
    S.represents N R.hyperbolicPlane := by
  rcases R.heADC2025Proposition416NonDyadic H N hRank hMaximal with
    hExceptional | hRepresents
  · exact False.elim (hNotExceptional hExceptional.1)
  · exact hRepresents

end QuaternaryTableRealizationLaws

end HeADC2025NonDyadicSystem

end Bong
