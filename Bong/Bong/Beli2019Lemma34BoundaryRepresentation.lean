/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma34Jordan

/-!
# Direct boundary representations in Beli (2019), Lemma 3.4

For a prescribed strict Jordan decomposition, an active O'Meara 93:28(iii)
boundary gives the left representation clause of a full-space
approximation, while an active 93:28(ii) boundary gives the right clause.
The proof uses the coherent-generator form of 93:28 and chooses the boundary
generator to be the exact endpoint value of the adapted good BONG.  Beli's
Lemma 3.5(i) then removes the resulting hyperbolic pair on the left.

Both results are unconditional consequences of the already proved dyadic
classification layer; no representation-law instance is introduced.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness.PrescribedJordanComparison

set_option maxHeartbeats 0 in
theorem leftRepresentation_of_conditionIII
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hcontainment : J.fundamentalIdeal z <
      J.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    DiagonalRepresents
      (a.prefixValues (P.boundaryIndex z).val (by omega))
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) := by
  change DiagonalRepresents
    (diagonalUnitCoefficients
      (a.prefixValueUnits (P.boundaryIndex z).val (by omega)))
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
  let S := C.adapted
  let h := C.componentCount_eq
  let Js := S.sourceJordanSucc h
  let Ps := S.sourceProfileSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let B : Kˣ := Ps.boundaryLeftValue z
  have hB : Lattice.IsNormGeneratorValue q (Js.fundamentalLattice li) B := by
    simpa only [Js, Ps, B] using
      S.sourceBoundaryLeftValue_isNormGeneratorValue h z
  let As0 :=
    Lattice.JordanDecomposition.canonicalFundamentalNormGeneratorChoice Js
  let As := As0.replaceAt li B hB
  let A := As.ofSameFundamentalType C.sameType
  have hAvalue : A.value li = B := by
    simp [A, As]
  have htrigger : J.fundamentalIdeal z <
      J.fourNormOverWeightIdealWith A li := by
    rw [J.fourNormOverWeightIdealWith_eq_canonical]
    exact hcontainment
  have hembedding := (C.conditionsFromPrescribed A).2.2 z htrigger
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
    C.boundaryIndex_eq P z
  let targetIso := (S.sourcePrefixExactDiagonalIsometry h z).symm
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (diagonalUnitCoefficients
        (Fin.snoc
          (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega)) B)) := by
    have hgeometry := boundaryEmbedding_iff_diagonal
      (P.boundaryPrefixDiagonalUnits z)
      (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega)) B
      (P.boundaryPrefixDiagonalizationIsometry z) targetIso
    apply hgeometry.1
    change J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1) |>.EmbedsIntoOrthogonalSum
      (Js.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1)) (QuadraticSpace.scaledLine B)
    change J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1) |>.EmbedsIntoOrthogonalSum
      (Js.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1)) (QuadraticSpace.scaledLine (A.value li)) at hembedding
    rw [hAvalue] at hembedding
    exact hembedding
  let terminal : Kˣ := a.valueUnit (Ps.boundaryIndex z).castSucc
  have hsquareRaw :=
    BONG.StrictJordanAdaptedAlignment.boundaryLeftValue_mul_neg_valueUnit_isSquare
      (a := a) Ps z
  have hsquare : IsSquare (B * (-terminal)) := by
    simpa only [B, terminal] using hsquareRaw
  have hreplace := diagonalRepresents_snoc_iff_of_isSquare_mul
    (P.boundaryPrefixDiagonalUnits z)
    (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega))
    B (-terminal) hsquare
  have hextended := hreplace.1 hdiag
  let shorter :=
    a.prefixValueUnits (Ps.boundaryIndex z).val (by omega)
  have hprefix :
      a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega) =
        Fin.snoc shorter terminal := by
    have hraw := a.prefixValueUnits_succ_eq_snoc
      (Ps.boundaryIndex z).val (by omega)
    calc
      a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega) =
          Fin.snoc shorter
            (a.valueUnit ⟨(Ps.boundaryIndex z).val, by omega⟩) := by
        simpa only [shorter] using hraw
      _ = Fin.snoc shorter terminal := by
        congr 2
  rw [hprefix] at hextended
  have hlength : (Ps.boundaryIndex z).val + 1 =
      (P.boundaryIndex z).val + 1 := by rw [hboundary]
  have hresult := (beli2009Lemma35i_diagonal_of_rank_eq
    (P.boundaryPrefixDiagonalUnits z) shorter terminal hlength).2 hextended
  exact GoodBONG.sourcePrefixRepresents_cast
    (sourceBound := by omega) (sourceBound' := by omega) a
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
    (congrArg Fin.val hboundary) hresult

set_option maxHeartbeats 0 in
theorem rightRepresentation_of_conditionII
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hcontainment : J.fundamentalIdeal z <
      J.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (a.prefixValues ((P.boundaryIndex z).val + 2) (by omega)) := by
  change DiagonalRepresents
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
    (diagonalUnitCoefficients
      (a.prefixValueUnits ((P.boundaryIndex z).val + 2) (by omega)))
  let S := C.adapted
  let h := C.componentCount_eq
  let Js := S.sourceJordanSucc h
  let Ps := S.sourceProfileSucc h
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let B : Kˣ := Ps.boundaryRightValue z
  have hB : Lattice.IsNormGeneratorValue q (Js.fundamentalLattice ri) B := by
    simpa only [Js, Ps, B] using
      S.sourceBoundaryRightValue_isNormGeneratorValue h z
  let As0 :=
    Lattice.JordanDecomposition.canonicalFundamentalNormGeneratorChoice Js
  let As := As0.replaceAt ri B hB
  let A := As.ofSameFundamentalType C.sameType
  have hAvalue : A.value ri = B := by
    simp [A, As]
  have htrigger : J.fundamentalIdeal z <
      J.fourNormOverWeightIdealWith A ri := by
    rw [J.fourNormOverWeightIdealWith_eq_canonical]
    exact hcontainment
  have hembedding := (C.conditionsFromPrescribed A).2.1 z htrigger
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
    C.boundaryIndex_eq P z
  let targetIso := (S.sourcePrefixExactDiagonalIsometry h z).symm
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (diagonalUnitCoefficients
        (Fin.snoc
          (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega)) B)) := by
    have hgeometry := boundaryEmbedding_iff_diagonal
      (P.boundaryPrefixDiagonalUnits z)
      (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega)) B
      (P.boundaryPrefixDiagonalizationIsometry z) targetIso
    apply hgeometry.1
    change J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1) |>.EmbedsIntoOrthogonalSum
      (Js.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1)) (QuadraticSpace.scaledLine B)
    change J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1) |>.EmbedsIntoOrthogonalSum
      (Js.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1)) (QuadraticSpace.scaledLine (A.value ri)) at hembedding
    rw [hAvalue] at hembedding
    exact hembedding
  have hBvalue : B = a.valueUnit (Ps.boundaryIndex z).succ :=
    Ps.boundaryRightValue_eq_valueUnit_succ z
  have hprefix :
      Fin.snoc
          (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega)) B =
        a.prefixValueUnits ((Ps.boundaryIndex z).val + 2) (by omega) := by
    have hraw := a.prefixValueUnits_succ_eq_snoc
      ((Ps.boundaryIndex z).val + 1) (by omega)
    calc
      Fin.snoc
          (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega)) B =
          Fin.snoc
            (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega))
            (a.valueUnit ⟨(Ps.boundaryIndex z).val + 1, by omega⟩) := by
              rw [hBvalue]
              congr 2
      _ = a.prefixValueUnits ((Ps.boundaryIndex z).val + 2) (by omega) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hraw.symm
  rw [hprefix] at hdiag
  exact GoodBONG.targetPrefixRepresents_cast
    (targetBound := by omega) (targetBound' := by omega)
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) a
    (by rw [hboundary]) hdiag

/-- A full Jordan prefix is a two-sided space approximation once the two
Definition 10 triggers have been converted to the corresponding current
O'Meara boundary containments.  The scalar determinant approximation is
kept explicit so this theorem can be used with either a strict or a merged
weak Jordan decomposition. -/
theorem boundary_isSpaceApproximation_of_currentContainments
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hdet : a.IsPrefixApproximation ((P.boundaryIndex z).val + 1)
      (diagonalUnitDeterminant (P.boundaryPrefixDiagonalUnits z)))
    (hleft : a.leftApproximationTrigger (P.boundaryIndex z) →
      J.fundamentalIdeal z < J.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hright : a.rightApproximationTrigger (P.boundaryIndex z) →
      J.fundamentalIdeal z < J.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    a.IsSpaceApproximation (P.boundaryIndex z)
      (P.boundaryPrefixDiagonalUnits z) := by
  constructor
  · exact ⟨hdet, fun htrigger ↦
      C.leftRepresentation_of_conditionIII P z (hleft htrigger)⟩
  · exact ⟨hdet, fun htrigger ↦
      C.rightRepresentation_of_conditionII P z (hright htrigger)⟩

end BONG.JordanOrderProfileWitness.PrescribedJordanComparison

end Bong
