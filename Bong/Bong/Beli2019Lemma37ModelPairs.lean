/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37Models

/-!
# Elementary representation pairs between the models of Lemma 3.7

The two non-exceptional adjacencies used in Beli (2019), Section 5 are
formal consequences of the geometric meanings of Lemma 3.7(ii) and (iii).
A Jordan prefix is represented by the same prefix with one line appended,
and the complement of a represented line is represented by the complete
Jordan prefix.  These facts do not use a local classification law.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

namespace Lattice.QuadraticSublattice

/-- Two nondegenerate quadratic sublattices with the same ambient carrier
have canonically isometric restricted quadratic spaces. -/
noncomputable def spaceIsometryOfCarrierEq
    (C D : Lattice.QuadraticSublattice q)
    (hcarrier : C.carrier = D.carrier) :
    QuadraticSpace.Isometry C.space D.space := by
  let e : C.carrier ≃ₗ[K] D.carrier :=
    LinearEquiv.ofEq _ _ hcarrier
  refine
    { toLinearEquiv := e
      map_bilin := ?_ }
  intro x y
  change q.bilin (((e x : D.carrier) : V)) (((e y : D.carrier) : V)) =
    q.bilin (x : V) (y : V)
  simp [e]

end Lattice.QuadraticSublattice

namespace Lattice.JordanDecomposition

/-- Equal ambient carriers identify the corresponding Jordan prefix
quadratic spaces by the identity on ambient vectors. -/
noncomputable def prefixSpaceIsometryOfCarrierEq
    {s t : Nat} (J : Lattice.JordanDecomposition q L (s + 1))
    (H : Lattice.JordanDecomposition q M (t + 1))
    (z : Fin s) (w : Fin t)
    (hcarrier : J.toOrthogonalDecomposition.prefixCarrier (z.val + 1) =
      H.toOrthogonalDecomposition.prefixCarrier (w.val + 1)) :
    QuadraticSpace.Isometry (J.prefixSpace (z.val + 1))
      (H.prefixSpace (w.val + 1)) := by
  let e : J.toOrthogonalDecomposition.prefixCarrier (z.val + 1) ≃ₗ[K]
      H.toOrthogonalDecomposition.prefixCarrier (w.val + 1) :=
    LinearEquiv.ofEq _ _ hcarrier
  refine
    { toLinearEquiv := e
      map_bilin := ?_ }
  intro x y
  change q.bilin
      (((e x : H.toOrthogonalDecomposition.prefixCarrier (w.val + 1)) : V))
      (((e y : H.toOrthogonalDecomposition.prefixCarrier (w.val + 1)) : V)) =
    q.bilin (x : V) (y : V)
  simp [e]

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness

/-- An isometry between two Jordan prefix spaces transports their canonical
Lemma 3.7(i) diagonal presentations.  The Jordan decompositions, BONGs, and
component counts on the two sides may all be different. -/
theorem boundaryPrefix_diagonalRepresents_boundaryPrefix_of_isometry
    {n m s t : Nat}
    {a : BONG.GoodBONG q L (n + 2)}
    {b : BONG.GoodBONG q M (m + 2)}
    {J : Lattice.JordanDecomposition q L (s + 1)}
    {H : Lattice.JordanDecomposition q M (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (Q : JordanOrderProfileWitness b.toBONG H)
    (z : Fin s) (w : Fin t)
    (h : QuadraticSpace.Isometry (J.prefixSpace (z.val + 1))
      (H.prefixSpace (w.val + 1))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (diagonalUnitCoefficients (Q.boundaryPrefixDiagonalUnits w)) := by
  let source := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (P.boundaryPrefixDiagonalUnits z))
  let target := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients (Q.boundaryPrefixDiagonalUnits w))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (Q.boundaryPrefixDiagonalUnits w))
  let represented : QuadraticSpace.Representation source target :=
    (Q.boundaryPrefixDiagonalizationIsometry w).toRepresentation.trans <|
      h.toRepresentation.trans <|
        (P.boundaryPrefixDiagonalizationIsometry z).symm.toRepresentation
  apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    (P.boundaryPrefixDiagonalUnits z)
    (Q.boundaryPrefixDiagonalUnits w)).1
  exact ⟨represented⟩

/-- The Lemma 3.7(i) boundary-prefix model is represented by the
Lemma 3.7(ii) model obtained by adjoining one abstract line. -/
theorem boundaryPrefix_diagonalRepresents_oneAfter
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) (A : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A)) := by
  let target :=
    diagonalUnitCoefficients (P.boundaryOneAfterDiagonalUnits z A)
  let hle : (P.boundaryIndex z).val + 1 ≤
      (P.boundaryIndex z).val + 2 := by omega
  have h := DiagonalRepresents.prefixOfLE target hle
  have hsource :
      (fun i : Fin ((P.boundaryIndex z).val + 1) ↦
        target ⟨i.val, i.isLt.trans_le hle⟩) =
      diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z) := by
    funext i
    have hi : (⟨i.val, i.isLt.trans_le hle⟩ :
        Fin ((P.boundaryIndex z).val + 2)) = i.castSucc := by
      apply Fin.ext
      rfl
    rw [hi]
    simp only [target, boundaryOneAfterDiagonalUnits,
      diagonalUnitCoefficients, Fin.snoc_castSucc]
  rw [hsource] at h
  exact h

/-- A source boundary prefix is represented by a target prefix with one
line appended whenever the two boundary prefix spaces are isometric. -/
theorem boundaryPrefix_diagonalRepresents_oneAfter_of_prefixIsometry
    {n m s t : Nat}
    {a : BONG.GoodBONG q L (n + 2)}
    {b : BONG.GoodBONG q M (m + 2)}
    {J : Lattice.JordanDecomposition q L (s + 1)}
    {H : Lattice.JordanDecomposition q M (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (Q : JordanOrderProfileWitness b.toBONG H)
    (z : Fin s) (w : Fin t) (A : Kˣ)
    (h : QuadraticSpace.Isometry (J.prefixSpace (z.val + 1))
      (H.prefixSpace (w.val + 1))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
      (diagonalUnitCoefficients (Q.boundaryOneAfterDiagonalUnits w A)) :=
  (P.boundaryPrefix_diagonalRepresents_boundaryPrefix_of_isometry Q z w h).trans
    (Q.boundaryPrefix_diagonalRepresents_oneAfter w A)

namespace BoundaryOneBeforeModel

/-- The Lemma 3.7(iii) complement model is represented by the complete
Lemma 3.7(i) boundary prefix from which its defining line was removed. -/
theorem diagonalRepresents_boundaryPrefix
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    {P : JordanOrderProfileWitness a.toBONG J} {z : Fin t} {A : Kˣ}
    (M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (M.approximationUnits hrank))
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) := by
  let e := M.rankEquiv hrank
  let source := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients (M.approximationUnits hrank))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (M.approximationUnits hrank))
  let middle := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units)
  let target := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (P.boundaryPrefixDiagonalUnits z))
  let reindex : QuadraticSpace.Isometry source middle := by
    change QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (fun i ↦ (M.units (e i) : K))
        (fun i ↦ Units.ne_zero (M.units (e i)))) middle
    exact (QuadraticSpace.finiteDiagonalReindexIsometry
      (diagonalUnitCoefficients M.units)
      (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units) e).symm
  let line := QuadraticSpace.scaledLine A
  let inclusionMap : QuadraticSpace.Representation middle
      (middle.orthogonalSum line) :=
    QuadraticSpace.Representation.orthogonalSumInl middle line
  let assembled : QuadraticSpace.Representation source target :=
    (P.boundaryPrefixDiagonalizationIsometry z).toRepresentation.trans <|
      M.splitIsometry.toRepresentation.trans <|
        inclusionMap.trans reindex.toRepresentation
  apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    (M.approximationUnits hrank)
    (P.boundaryPrefixDiagonalUnits z)).1
  exact ⟨assembled⟩

/-- A one-before complement on the source side is represented by a target
boundary prefix whenever the complete source and target prefixes are
isometric. -/
theorem diagonalRepresents_boundaryPrefix_of_prefixIsometry
    {n m s t : Nat}
    {a : BONG.GoodBONG q L (n + 2)}
    {b : BONG.GoodBONG q M (m + 2)}
    {J : Lattice.JordanDecomposition q L (s + 1)}
    {H : Lattice.JordanDecomposition q M (t + 1)}
    {P : JordanOrderProfileWitness a.toBONG J}
    (Q : JordanOrderProfileWitness b.toBONG H)
    {z : Fin s} (w : Fin t) {A : Kˣ}
    (B : BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (h : QuadraticSpace.Isometry (J.prefixSpace (z.val + 1))
      (H.prefixSpace (w.val + 1))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (B.approximationUnits hrank))
      (diagonalUnitCoefficients (Q.boundaryPrefixDiagonalUnits w)) :=
  (B.diagonalRepresents_boundaryPrefix hrank).trans
    (P.boundaryPrefix_diagonalRepresents_boundaryPrefix_of_isometry Q z w h)

end BoundaryOneBeforeModel

end BONG.JordanOrderProfileWitness

end Bong
