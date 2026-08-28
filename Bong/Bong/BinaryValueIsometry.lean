/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryShearIsometry
import Bong.Bong.BeliLemma317

/-!
# Isometry of binary BONG lattices with equal values

The adapted integral bases of two binary BONGs may have different mixed
coefficients.  Their diagonal values nevertheless determine the same binary
parameter, and the two admissible mixed coefficients differ integrally.
Consequently an integral shear identifies the two model lattices.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Two binary BONG lattices with the same two nonzero quadratic values are
isometric.  The proof is explicit through their adapted binary models and an
integral shear; it does not use the general classification theorem. -/
theorem binary_isIsometric_of_valueUnit_eq
    (a : BONG V q L 2) (b : BONG W r M 2)
    (hzero : a.valueUnit 0 = b.valueUnit 0)
    (hone : a.valueUnit 1 = b.valueUnit 1) :
    Lattice.IsIsometric q r L M := by
  have hparameter : a.binaryParameter = b.binaryParameter := by
    simp only [binaryParameter, hzero, hone]
  have haAdmissible := a.binaryModelCoefficient_isAdmissibleWitness
  have hbAdmissible := b.binaryModelCoefficient_isAdmissibleWitness
  have hbAdmissible' :
      (2 : K) * b.binaryModelCoefficient ∈ IntegerRing K ∧
        b.binaryModelCoefficient ^ 2 + (a.binaryParameter : K) ∈
          IntegerRing K := by
    simpa only [hparameter] using hbAdmissible
  have hshear :
      a.binaryModelCoefficient - b.binaryModelCoefficient ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing a.binaryParameter
      a.binaryModelCoefficient b.binaryModelCoefficient
      haAdmissible.1 haAdmissible.2
      hbAdmissible'.1 hbAdmissible'.2
  have hmodelsRaw :=
    rescaledBinaryModel_isIsometric_of_shear_sub_integral
      (a.valueUnit 0) a.binaryParameter
      a.binaryModelCoefficient b.binaryModelCoefficient hshear
  have hmodels :
      Lattice.IsIsometric a.normalizedBinaryModelSpace
        b.normalizedBinaryModelSpace
        (binaryModelLattice (K := K)) (binaryModelLattice (K := K)) := by
    simpa only [normalizedBinaryModelSpace, hzero, hparameter] using hmodelsRaw
  rcases a.normalizedBinaryModel_isIsometric with ⟨fa⟩
  rcases b.normalizedBinaryModel_isIsometric with ⟨fb⟩
  rcases hmodels with ⟨g⟩
  exact ⟨fa.symm.trans (g.trans fb)⟩

end BONG

end Bong
