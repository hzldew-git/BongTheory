/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalBoundaryWitt
import Bong.Lattice.BinaryDeterminantHyperbolic
import Bong.QuadraticSpace.OrthogonalSumDiagonal

/-!
# The hyperbolic quaternary boundary maneuver

This is the coordinate-free form of the Witt step used in O'Meara 93:28,
Step 2.  If a split quaternary space embeds in `q ⊥ [-a]`, then `q`
embeds in that split quaternary space with `[a]` adjoined.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace QuadraticSpace

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {U : Type v} [AddCommGroup U] [Module K U]
  {V : Type w} [AddCommGroup V] [Module K V]

/-- The fixed diagonal model `[1,-1,1,-1]` of two hyperbolic planes. -/
noncomputable def twoHyperbolicPairsDiagonalForm :
    QuadraticSpace K (Fin 4 → K) :=
  finiteDiagonal
    (diagonalUnitCoefficients (twoHyperbolicPairsUnits (K := K)))
    (diagonalUnitCoefficients_ne_zero
      (twoHyperbolicPairsUnits (K := K)))

/-- Coordinate-free reversal of the last-boundary representation in
O'Meara 93:28, Step 2.  The quaternary target has rank four, the source is
split, and the line changes from `[-a]` to `[a]`. -/
theorem reverseHyperbolicQuaternaryBoundary
    [FiniteDimensional K V]
    (p : QuadraticSpace K U) (q : QuadraticSpace K V) (a : Kˣ)
    (hqrank : finrank K V = 4)
    (hp : p.IsIsometric (twoHyperbolicPairsDiagonalForm (K := K)))
    (h : EmbedsInto p (q.orthogonalSum (scaledLine (-a)))) :
    EmbedsInto q (p.orthogonalSum (scaledLine a)) := by
  let pToPairs := hp.some
  rcases h with ⟨f⟩
  let pairsInTarget :
      Representation (twoHyperbolicPairsDiagonalForm (K := K))
        (q.orthogonalSum (scaledLine (-a))) :=
    f.trans pToPairs.symm.toRepresentation
  let e : Fin 4 ≃ Fin (finrank K V) := finCongr hqrank.symm
  let t : Fin 4 → Kˣ := fun i ↦ q.diagonalUnits (e i)
  let qToT : Isometry q
      (finiteDiagonal (diagonalUnitCoefficients t)
        (diagonalUnitCoefficients_ne_zero t)) :=
    q.diagonalizationIsometry.trans
      (finiteDiagonalReindexIsometry
        (diagonalUnitCoefficients q.diagonalUnits)
        (diagonalUnitCoefficients_ne_zero q.diagonalUnits) e)
  let targetDiagonal : Isometry
      (q.orthogonalSum (scaledLine (-a)))
      (finiteDiagonal
        (diagonalUnitCoefficients (Fin.snoc t (-a)))
        (diagonalUnitCoefficients_ne_zero (Fin.snoc t (-a)))) := by
    let raw :=
      (qToT.orthogonalSum (scaledLineDiagonalizationIsometry (-a))).trans
        (finiteDiagonalOrthogonalSumIsometry
          t (fun _ : Fin 1 ↦ -a))
    simpa only [Fin.append_right_eq_snoc] using raw
  have hdiagSpace :
      (finiteDiagonal
        (diagonalUnitCoefficients (Fin.snoc t (-a)))
        (diagonalUnitCoefficients_ne_zero
          (Fin.snoc t (-a)))).Represents
        (twoHyperbolicPairsDiagonalForm (K := K)) :=
    ⟨targetDiagonal.toRepresentation.trans pairsInTarget⟩
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients (twoHyperbolicPairsUnits (K := K)))
      (diagonalUnitCoefficients (Fin.snoc t (-a))) :=
    (finiteDiagonal_represents_iff_diagonalRepresents
      (twoHyperbolicPairsUnits (K := K)) (Fin.snoc t (-a))).mp
        hdiagSpace
  have hreverse := diagonalRankFour_reverseHyperbolicBoundary t a hdiag
  have hreverseSpace :
      (finiteDiagonal
        (diagonalUnitCoefficients
          (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a))
        (diagonalUnitCoefficients_ne_zero
          (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a))).Represents
        (finiteDiagonal (diagonalUnitCoefficients t)
          (diagonalUnitCoefficients_ne_zero t)) :=
    (finiteDiagonal_represents_iff_diagonalRepresents
      t (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a)).mpr hreverse
  rcases hreverseSpace with ⟨g⟩
  let pairsPlusLineToDiagonal : Isometry
      ((twoHyperbolicPairsDiagonalForm (K := K)).orthogonalSum
        (scaledLine a))
      (finiteDiagonal
        (diagonalUnitCoefficients
          (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a))
        (diagonalUnitCoefficients_ne_zero
          (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a))) := by
    let raw :=
      ((Isometry.refl (twoHyperbolicPairsDiagonalForm (K := K)))
          |>.orthogonalSum (scaledLineDiagonalizationIsometry a)).trans
        (finiteDiagonalOrthogonalSumIsometry
          (twoHyperbolicPairsUnits (K := K)) (fun _ : Fin 1 ↦ a))
    simpa only [Fin.append_right_eq_snoc] using raw
  let diagonalToPPlusLine : Isometry
      (finiteDiagonal
        (diagonalUnitCoefficients
          (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a))
        (diagonalUnitCoefficients_ne_zero
          (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a)))
      (p.orthogonalSum (scaledLine a)) :=
    pairsPlusLineToDiagonal.symm.trans
      (pToPairs.symm.orthogonalSum (Isometry.refl (scaledLine a)))
  exact ⟨diagonalToPPlusLine.toRepresentation.trans
    (g.trans qToT.toRepresentation)⟩

end QuadraticSpace

end Bong
