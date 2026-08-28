/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328SourceFirstDeterminant
import Bong.Lattice.Omeara9328RankFourConditionTransfer
import Bong.Lattice.OrthogonalDecompositionFirstPrefix
import Bong.Lattice.DeterminantFormRescaleClass
import Bong.Dyadic.UnitsCongruentModuloAlgebra

/-!
# The first determinant congruence after scale normalization

Condition 93:28(i) is stated for the unnormalized first prefixes.  Both
rank-four components have the same scale, so the common fourth power of
that scale cancels.  Since the normalized source component has determinant
class one, the normalized target determinant is congruent to one modulo the
first fundamental ideal.  This is the exact input used in Steps 4--7 of
O'Meara's proof.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The first source prefix has the determinant class of the common fourth
power of the first Jordan scale. -/
theorem sourceFirstPrefix_determinantClass :
    determinantClass
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      unitSquareClass K (S.firstScale ^ 4) := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  have hcomponent :
      determinantClass (S.sourceJordan.component 0).space
          (S.sourceJordan.component 0).lattice =
        unitSquareClass K (S.firstScale ^ 4) := by
    calc
      determinantClass (S.sourceJordan.component 0).space
          (S.sourceJordan.component 0).lattice =
          unitSquareClass K
              (S.firstScale ^
                finrank K (S.sourceJordan.component 0).carrier) *
            determinantClass S.sourceFirstNormalized
              (S.sourceJordan.component 0).lattice :=
        determinantClass_eq_scalePow_mul_rescaleInverse
          (S.sourceJordan.component 0).space
          (S.sourceJordan.component 0).lattice S.firstScale
      _ = unitSquareClass K (S.firstScale ^ 4) := by
        rw [S.sourceFirstNormalized_finrank,
          S.sourceFirstNormalized_determinantClass]
        exact mul_one (unitSquareClass K (S.firstScale ^ 4))
  have hisometry := determinantClass_eq_of_isometry
    D.firstComponentPrefixLatticeIsometry
  exact hisometry.symm.trans hcomponent

/-- The target first-prefix determinant is the common scale factor times
the determinant class of the normalized target head. -/
theorem targetFirstPrefix_determinantClass :
    determinantClass
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      unitSquareClass K (S.firstScale ^ 4) *
        determinantClass S.targetFirstNormalized
          (S.targetJordan.component 0).lattice := by
  let D := S.targetJordan.toOrthogonalDecomposition
  have hcomponent :
      determinantClass (S.targetJordan.component 0).space
          (S.targetJordan.component 0).lattice =
        unitSquareClass K (S.firstScale ^ 4) *
          determinantClass S.targetFirstNormalized
            (S.targetJordan.component 0).lattice := by
    calc
      determinantClass (S.targetJordan.component 0).space
          (S.targetJordan.component 0).lattice =
          unitSquareClass K
              (S.firstScale ^
                finrank K (S.targetJordan.component 0).carrier) *
            determinantClass S.targetFirstNormalized
              (S.targetJordan.component 0).lattice :=
        determinantClass_eq_scalePow_mul_rescaleInverse
          (S.targetJordan.component 0).space
          (S.targetJordan.component 0).lattice S.firstScale
      _ = unitSquareClass K (S.firstScale ^ 4) *
          determinantClass S.targetFirstNormalized
            (S.targetJordan.component 0).lattice := by
        rw [S.targetFirstNormalized_finrank]
  have hisometry := determinantClass_eq_of_isometry
    D.firstComponentPrefixLatticeIsometry
  exact hisometry.symm.trans hcomponent

/-- After cancelling the common scale factor, condition 93:28(i) says
that the normalized target determinant is congruent to one modulo the
first fundamental ideal. -/
theorem targetFirstNormalized_determinantCongruentOne
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A) :
    BONG.GoodBONG.UnitsCongruentModulo
      (determinantUnit S.targetFirstNormalized
        (S.targetJordan.component 0).lattice)
      (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0) := by
  let c : Kˣ := S.firstScale ^ 4
  let x : Kˣ := determinantUnit S.targetFirstNormalized
    (S.targetJordan.component 0).lattice
  let sourcePrefix : Kˣ := S.sourceJordan.prefixDeterminantUnit 0
  let targetPrefix : Kˣ := S.targetJordan.prefixDeterminantUnit 0
  have htargetClass :
      unitSquareClass K targetPrefix = unitSquareClass K (c * x) := by
    change determinantClass
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      unitSquareClass K (c * x)
    rw [S.targetFirstPrefix_determinantClass]
    exact (unitSquareClass_mul K c x).symm
  have hsourceClass :
      unitSquareClass K sourcePrefix =
        unitSquareClass K (c * (1 : Kˣ)) := by
    change determinantClass
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      unitSquareClass K (c * (1 : Kˣ))
    rw [S.sourceFirstPrefix_determinantClass, mul_one]
  have hscaled : BONG.GoodBONG.UnitsCongruentModulo
      (c * x) (c * (1 : Kˣ))
      (S.sourceJordan.fundamentalIdeal 0) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      targetPrefix (c * x) sourcePrefix (c * (1 : Kˣ))
      (S.sourceJordan.fundamentalIdeal 0)
      htargetClass hsourceClass (conditions.1 0)
  exact (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
    c x (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0)).1 hscaled

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
