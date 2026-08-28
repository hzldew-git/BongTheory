/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37Models
import Bong.Bong.DiagonalCodimensionTwoRepresentationProof

/-!
# Universal line models for Beli 2019, Lemma 3.7(iii)

The expression `F L_(k) ⊤ [A_k]` only requires the fundamental norm
generator to be represented by the complete Jordan prefix.  It need not be
represented integrally by the displayed Jordan component.  Once that prefix
has rank at least four, quaternary universality over the dyadic field supplies
the represented line unconditionally.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A nonzero value of an arbitrary nonempty diagonal form gives a
representation of the corresponding line. -/
theorem diagonalUnaryRepresents_of_exists_value_general
    {m : Nat} (target : Fin m → Kˣ) (A : Kˣ) (hm : 0 < m)
    (hvalue : ∃ x : Fin m → K,
      diagonalQuadratic (diagonalUnitCoefficients target) x = (A : K)) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (A : K))
      (diagonalUnitCoefficients target) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨x, hx⟩ := hvalue
  obtain ⟨tail, hsplit, _⟩ :=
    exists_diagonal_split_first (K := K) r target A x hx
  have hline : DiagonalRepresents
      (fun _ : Fin 1 ↦ (A : K))
      (diagonalUnitCoefficients (Fin.cons A tail)) := by
    convert DiagonalRepresents.prefixOfLE
      (k := 1) (diagonalUnitCoefficients (Fin.cons A tail)) (by omega)
    simp [diagonalUnitCoefficients]
  exact hline.trans hsplit

namespace QuadraticSpace

/-- Every nondegenerate quadratic space of rank at least four over the
dyadic field represents every nonzero line. -/
theorem represents_scaledLine_of_four_le_finrank
    {U : Type v} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (Q : QuadraticSpace K U) (A : Kˣ) (hfour : 4 ≤ finrank K U) :
    Q.Represents (scaledLine A) := by
  obtain ⟨x, hx⟩ := diagonalUnit_exists_value_of_four_le
    Q.diagonalUnits hfour A
  have hdiag : DiagonalRepresents (fun _ : Fin 1 ↦ (A : K))
      (diagonalUnitCoefficients Q.diagonalUnits) :=
    diagonalUnaryRepresents_of_exists_value_general Q.diagonalUnits A
      (by omega) ⟨x, hx⟩
  have hfinite :
      (finiteDiagonal
          (diagonalUnitCoefficients Q.diagonalUnits)
          (diagonalUnitCoefficients_ne_zero Q.diagonalUnits)).Represents
        (finiteDiagonal
          (diagonalUnitCoefficients (fun _ : Fin 1 ↦ A))
          (diagonalUnitCoefficients_ne_zero (fun _ : Fin 1 ↦ A))) :=
    (finiteDiagonal_represents_iff_diagonalRepresents
      (fun _ : Fin 1 ↦ A) Q.diagonalUnits).2 hdiag
  let lineToFinite := (scaledLineDiagonalizationIsometry A).toRepresentation
  let finiteToQ := Q.diagonalizationIsometry.symm.toRepresentation
  exact ⟨finiteToQ.trans ((Classical.choice hfinite).trans lineToFinite)⟩

end QuadraticSpace

namespace BONG.JordanOrderProfileWitness

/-- Every Jordan prefix of rank at least four represents every nonzero
line.  This is the precise high-rank existence statement needed in
Lemma 3.7(iii). -/
theorem boundaryPrefix_represents_scaledLine_of_four_le
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) (A : Kˣ)
    (hfour : 4 ≤ (P.boundaryIndex z).val + 1) :
    (J.prefixSpace (z.val + 1)).Represents
      (QuadraticSpace.scaledLine A) := by
  let target := P.boundaryPrefixDiagonalUnits z
  obtain ⟨x, hx⟩ :=
    diagonalUnit_exists_value_of_four_le target hfour A
  have hdiag : DiagonalRepresents (fun _ : Fin 1 ↦ (A : K))
      (diagonalUnitCoefficients target) :=
    diagonalUnaryRepresents_of_exists_value_general target A (by omega) ⟨x, hx⟩
  have hfinite :
      (QuadraticSpace.finiteDiagonal
          (diagonalUnitCoefficients target)
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero target)).Represents
        (QuadraticSpace.finiteDiagonal
          (diagonalUnitCoefficients (fun _ : Fin 1 ↦ A))
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero
            (fun _ : Fin 1 ↦ A))) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (fun _ : Fin 1 ↦ A) target).2 hdiag
  let lineToFinite := (QuadraticSpace.scaledLineDiagonalizationIsometry A).toRepresentation
  let finiteToPrefix := (P.boundaryPrefixDiagonalizationIsometry z).symm.toRepresentation
  exact ⟨finiteToPrefix.trans ((Classical.choice hfinite).trans lineToFinite)⟩

/-- Quaternary universality supplies the concrete complement datum used in
Lemma 3.7(iii). -/
noncomputable def boundaryOneBeforeModel_of_four_le
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) (A : Kˣ)
    (hfour : 4 ≤ (P.boundaryIndex z).val + 1) :
    BoundaryOneBeforeModel P z A :=
  BoundaryOneBeforeModel.ofLineRepresentation
    (P.boundaryPrefix_represents_scaledLine_of_four_le z A hfour)

end BONG.JordanOrderProfileWitness

end Bong
