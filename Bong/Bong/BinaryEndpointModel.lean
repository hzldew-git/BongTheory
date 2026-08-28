/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryEndpointClass
import Bong.Bong.BinaryModelIsometry
import Bong.Bong.BinarySpinorGroupInvariant

/-!
# Concrete models for binary endpoint classes

Equality modulo valuation-unit squares is realized by scaling the second
standard coordinate of the binary Gram model.  Combining this with the
adapted-basis model theorem gives an actual lattice isometry for each endpoint
class, not only an equality in the square-class quotient.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The model with prescribed parameter representative `d` obtained by a
valuation-unit change of the second coordinate. -/
noncomputable def squareClassRepresentativeModelSpace
    (b : BONG V q L 2) (d s : Kˣ) : QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.rescaleUnit (b.valueUnit 0)
    (QuadraticSpace.binaryModel d (b.binaryModelCoefficient / (s : K)))

/-- A chosen representative of the refined square class gives a concrete
binary model lattice isometric to the original BONG lattice. -/
theorem isIsometric_squareClassRepresentativeModel
    (b : BONG V q L 2) (d : Kˣ)
    (hclass : b.binaryUnitSquareClass = unitSquareClass K d) :
    ∃ s : Kˣ, IsValuationUnit K (s : K) ∧
      Lattice.IsIsometric q (b.squareClassRepresentativeModelSpace d s)
        L (binaryModelLattice (K := K)) := by
  rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
      K hclass.symm with ⟨s, hs, hparameter⟩
  rcases b.normalizedBinaryModel_isIsometric with ⟨f⟩
  rcases rescaledBinaryModel_isIsometric_mul_valuationUnit_square
      (b.valueUnit 0) b.binaryParameter d s b.binaryModelCoefficient
      hs hparameter with ⟨g⟩
  exact ⟨s, hs, ⟨f.symm.trans g⟩⟩

/-- A binary BONG at relative order `-2e` is concretely isometric to a model
with parameter `-1/4` or to one with parameter `-Δ/4`. -/
theorem endpointModel_cases [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L 2)
    (hgap : b.binaryOrderGap =
      -(2 * (ramificationIndex K : Int))) :
    (∃ s : Kˣ, IsValuationUnit K (s : K) ∧
      Lattice.IsIsometric q
        (b.squareClassRepresentativeModelSpace (negativeQuarterUnit K) s)
        L (binaryModelLattice (K := K))) ∨
    (∃ s : Kˣ, IsValuationUnit K (s : K) ∧
      Lattice.IsIsometric q
        (b.squareClassRepresentativeModelSpace
          (negativeQuarterUnit K * laws.discriminantUnit) s)
        L (binaryModelLattice (K := K))) := by
  have hparameterOrder : ordUnit K b.binaryParameter =
      -(2 * (ramificationIndex K : Int)) := by
    change b.binaryParameterOrder = _
    rw [b.binaryParameterOrder_eq_orderGap]
    exact hgap
  rcases laws.endpoint_parameter_class b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible hparameterOrder with
    hquarter | hdiscriminant
  · left
    exact b.isIsometric_squareClassRepresentativeModel
      (negativeQuarterUnit K) hquarter
  · right
    exact b.isIsometric_squareClassRepresentativeModel
      (negativeQuarterUnit K * laws.discriminantUnit) hdiscriminant

end BONG

end Bong
