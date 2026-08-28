import Bong.Dyadic.UnitsCongruentModuloAlgebra
import Bong.Lattice.Omeara9328GeneratorChoice
import Bong.Lattice.OrthogonalDecompositionFirstPrefix
import Bong.QuadraticSpace.OrthogonalSumDiagonal

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}

/-- The three clauses of O'Meara 93:28 at the first proper boundary.  A
replacement of the first two target components only has to re-establish
these clauses; every later prefix contains the whole replaced pair. -/
structure Omeara9328BoundaryZeroConditionsWith
    (J : JordanDecomposition q L (m + 2))
    (T : JordanDecomposition r M (m + 2))
    (A : FundamentalNormGeneratorChoice J) : Prop where
  conditionI : BONG.GoodBONG.UnitsCongruentModulo
    (T.prefixDeterminantUnit 0) (J.prefixDeterminantUnit 0)
    (J.fundamentalIdeal 0)
  conditionII : J.fundamentalIdeal 0 <
      J.fourNormOverWeightIdealWith A (boundaryRightIndex 0) →
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1)
      (T.toOrthogonalDecomposition.prefixQuadraticSublattice 1)
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex 0)))
  conditionIII : J.fundamentalIdeal 0 <
      J.fourNormOverWeightIdealWith A (boundaryLeftIndex 0) →
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1)
      (T.toOrthogonalDecomposition.prefixQuadraticSublattice 1)
      (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex 0)))

/-- Once the two head lattices are integrally isometric, all three clauses
at the first boundary hold automatically.  The representation triggers are
irrelevant because the length-one prefixes are already isometric. -/
theorem omeara9328BoundaryZeroConditionsWith_of_headIsometry
    (J : JordanDecomposition q L (m + 2))
    (T : JordanDecomposition r M (m + 2))
    (A : FundamentalNormGeneratorChoice J)
    (head : Isometry (J.component 0).space (T.component 0).space
      (J.component 0).lattice (T.component 0).lattice) :
    Omeara9328BoundaryZeroConditionsWith J T A := by
  let sourcePrefix :=
    J.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
  let targetPrefix :=
    T.toOrthogonalDecomposition.firstComponentPrefixLatticeIsometry
  let prefixIso : Isometry
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
      (T.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice
      (T.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice :=
    sourcePrefix.symm.trans (head.trans targetPrefix)
  refine ⟨?_, ?_, ?_⟩
  · apply unitsCongruentModulo_of_unitSquareClass_eq
    change determinantClass
        (T.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
        (T.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice =
      determinantClass
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice
    exact (determinantClass_eq_of_isometry prefixIso).symm
  · intro _
    exact prefixIso.toQuadraticSpaceIsometry.embedsInto_orthogonalSum_target
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex 0)))
  · intro _
    exact prefixIso.toQuadraticSpaceIsometry.embedsInto_orthogonalSum_target
      (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex 0)))

/-- Conditions 93:28(i)--(iii) survive a target-splitting replacement once
the first boundary is checked and all later target prefixes are integrally
isometric. -/
theorem omeara9328ConditionsWith_of_boundaryZero_and_laterPrefixIsometry
    (J : JordanDecomposition q L (m + 2))
    (H T : JordanDecomposition r M (m + 2))
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A)
    (boundary : Omeara9328BoundaryZeroConditionsWith J T A)
    (later : ∀ (i : Fin (m + 1)), i ≠ 0 →
      Isometry
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (T.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice
        (T.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice) :
    J.Omeara9328ConditionsWith T A := by
  rcases conditions with ⟨conditionI, conditionII, conditionIII⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      exact boundary.conditionI
    · let g := later i hi
      have hdet : unitSquareClass K (H.prefixDeterminantUnit i) =
          unitSquareClass K (T.prefixDeterminantUnit i) := by
        change determinantClass
            (H.toOrthogonalDecomposition.prefixQuadraticSublattice
              (i.val + 1)).space
            (H.toOrthogonalDecomposition.prefixQuadraticSublattice
              (i.val + 1)).lattice =
          determinantClass
            (T.toOrthogonalDecomposition.prefixQuadraticSublattice
              (i.val + 1)).space
            (T.toOrthogonalDecomposition.prefixQuadraticSublattice
              (i.val + 1)).lattice
        exact determinantClass_eq_of_isometry g
      exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
        (H.prefixDeterminantUnit i) (T.prefixDeterminantUnit i)
        (J.prefixDeterminantUnit i) (J.prefixDeterminantUnit i)
        (J.fundamentalIdeal i) hdet rfl (conditionI i)
  · intro i htrigger
    by_cases hi : i = 0
    · subst i
      exact boundary.conditionII htrigger
    · rcases conditionII i htrigger with ⟨f⟩
      let g := later i hi
      let targetReframe :=
        g.toQuadraticSpaceIsometry.orthogonalSum
          (QuadraticSpace.Isometry.refl
            (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i))))
      exact ⟨targetReframe.toRepresentation.trans f⟩
  · intro i htrigger
    by_cases hi : i = 0
    · subst i
      exact boundary.conditionIII htrigger
    · rcases conditionIII i htrigger with ⟨f⟩
      let g := later i hi
      let targetReframe :=
        g.toQuadraticSpaceIsometry.orthogonalSum
          (QuadraticSpace.Isometry.refl
            (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i))))
      exact ⟨targetReframe.toRepresentation.trans f⟩

end Lattice.JordanDecomposition

end Bong
