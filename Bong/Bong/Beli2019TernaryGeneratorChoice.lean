/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37ResolvedModels
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Bong.BeliDiscriminantNormGenerator
import Bong.Bong.DiagonalTernaryRepresentationObstructionProof

/-!
# The discriminant-twisted generator choice in rank three

The remark following Beli (2019), Lemma 3.7 replaces a fundamental norm
generator `A` by `Delta * A` when the former is the unique scalar class not
represented by a ternary prefix.  This file proves both ingredients of that
choice: the discriminant twist remains a norm generator, and a nondegenerate
ternary space represents at least one of the two lines.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {U : Type w} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.IsNormGeneratorValue

/-- Multiplication by the distinguished discriminant unit preserves an
O'Meara norm-generator value.  The error `(Delta - 1)A = -4 rho A` lies in
`2 A O`, hence in `2 sL`, while `Delta` has valuation zero. -/
theorem discriminant_mul (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q L A) :
    Lattice.IsNormGeneratorValue q L (laws.discriminantUnit * A) := by
  have hcoefficientIntegral :
      (-(2 : K) * laws.rho) ∈ IntegerRing K := by
    exact (IntegerRing K).toSubring.mul_mem
      ((IntegerRing K).toSubring.neg_mem (by norm_num))
      ((mem_integerRing_iff K).2 laws.rho_isValuationUnit.ge)
  have hprincipal : (-(2 : K) * laws.rho) * (A : K) ∈
      Lattice.principalIdeal (K := K) (A : K) := by
    convert Lattice.mul_mem_principalIdeal_of_mem_integerRing
      (A : K) (-(2 : K) * laws.rho) hcoefficientIntegral using 1 <;> ring
  have htwice :
      ((laws.discriminantUnit * A : Kˣ) : K) - (A : K) ∈
        Lattice.twiceIdeal (Lattice.principalIdeal (K := K) (A : K)) := by
    change _ ∈ (Lattice.principalIdeal (K := K) (A : K)).map
      (Lattice.twoMulLinearMap (K := K))
    refine ⟨(-(2 : K) * laws.rho) * (A : K), hprincipal, ?_⟩
    rw [Lattice.twoMulLinearMap_apply]
    simp only [Algebra.smul_def, map_ofNat, Units.val_mul]
    rw [laws.discriminant_eq_one_sub_four_mul_rho]
    ring
  have hweight :
      ((laws.discriminantUnit * A : Kˣ) : K) - (A : K) ∈
        Lattice.weightIdeal q L := by
    exact Lattice.twoScaleIdeal_le_weightIdeal q L
      (Lattice.OrthogonalDecomposition.twicePrincipalIdeal_le_twoScaleIdeal
        A hA htwice)
  have hcoset : ((laws.discriminantUnit * A : Kˣ) : K) ∈
      Lattice.integralSquareCoset (A : K) (Lattice.weightIdeal q L) := by
    refine ⟨(1 : IntegerRing K),
      ((laws.discriminantUnit * A : Kˣ) : K) - (A : K), hweight, ?_⟩
    simp
  have hgroup : ((laws.discriminantUnit * A : Kˣ) : K) ∈
      Lattice.normGroupSet q L := by
    rw [Lattice.normGroupSet_eq_integralSquareCoset_weightIdeal A hA]
    exact hcoset
  refine ⟨hgroup, ?_⟩
  calc
    Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (A : K) := hA.2
    _ = Lattice.principalIdeal (K := K)
        ((laws.discriminantUnit * A : Kˣ) : K) := by
      apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
        A (laws.discriminantUnit * A)).2
      rw [ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K
          laws.discriminantUnit).1 laws.discriminant_isValuationUnit]
      omega

end Lattice.IsNormGeneratorValue

/-- A nondegenerate ternary diagonal form represents either `A` or its
discriminant twist.  If both failed, the ternary obstruction would make both
signed determinant products squares, forcing `Delta` itself to be a square. -/
theorem diagonalTernary_represents_line_or_discriminant_mul
    (a : Fin 3 → Kˣ) (A : Kˣ) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (A : K))
        (diagonalUnitCoefficients a) ∨
      DiagonalRepresents
        (fun _ : Fin 1 ↦ ((laws.discriminantUnit * A : Kˣ) : K))
        (diagonalUnitCoefficients a) := by
  by_cases hA : DiagonalRepresents (fun _ : Fin 1 ↦ (A : K))
      (diagonalUnitCoefficients a)
  · exact Or.inl hA
  · right
    by_contra hDeltaA
    have hASquare :=
      (DyadicTernaryRepresentationObstructionLaws.obstruction a A hA).2
    have hDeltaASquare :=
      (DyadicTernaryRepresentationObstructionLaws.obstruction
        a (laws.discriminantUnit * A) hDeltaA).2
    have hDeltaSquare : IsSquare laws.discriminantUnit := by
      have hquotient := hDeltaASquare.div hASquare
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hquotient
    have hDeltaNotSquare : ¬ IsSquare laws.discriminantUnit := by
      simpa [Dyadic.discriminantValuationUnit] using
        (Dyadic.discriminantValuationUnit_not_isSquare (K := K))
    exact hDeltaNotSquare hDeltaSquare

/-- Coordinate-free form of the ternary generator choice. -/
theorem QuadraticSpace.represents_scaledLine_or_discriminant_mul_of_finrank_eq_three
    [FiniteDimensional K U] (Q : QuadraticSpace K U)
    (hrank : finrank K U = 3) (A : Kˣ) :
    Q.Represents (QuadraticSpace.scaledLine A) ∨
      Q.Represents
        (QuadraticSpace.scaledLine (laws.discriminantUnit * A)) := by
  let e : Fin 3 ≃ Fin (finrank K U) := finCongr hrank.symm
  let target : Fin 3 → Kˣ := Q.diagonalUnits ∘ e
  have hchoice := diagonalTernary_represents_line_or_discriminant_mul target A
  let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (diagonalUnitCoefficients Q.diagonalUnits)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero Q.diagonalUnits) e
  let targetToQ : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients target)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero target)) Q := by
    have hraw := reindex.symm.trans Q.diagonalizationIsometry.symm
    change QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (fun i ↦ (Q.diagonalUnits (e i) : K))
        (fun i ↦ Units.ne_zero (Q.diagonalUnits (e i)))) Q
    simpa only [reindex, target, Function.comp_apply,
      diagonalUnitCoefficients, QuadraticSpace.diagonalModel] using hraw
  rcases hchoice with hA | hDeltaA
  · left
    have hfinite :=
      (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
        (fun _ : Fin 1 ↦ A) target).2 hA
    let lineToFinite := QuadraticSpace.scaledLineDiagonalizationIsometry A
    exact ⟨targetToQ.toRepresentation.trans
      ((Classical.choice hfinite).trans lineToFinite.toRepresentation)⟩
  · right
    let B := laws.discriminantUnit * A
    have hfinite :=
      (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
        (fun _ : Fin 1 ↦ B) target).2 hDeltaA
    let lineToFinite := QuadraticSpace.scaledLineDiagonalizationIsometry B
    exact ⟨targetToQ.toRepresentation.trans
      ((Classical.choice hfinite).trans lineToFinite.toRepresentation)⟩

/-- A ternary space and an unrelated lattice carrying `A` admit a common
choice of norm-generator scalar which is represented by the ternary space. -/
theorem QuadraticSpace.exists_normGeneratorValue_represents_scaledLine_of_finrank_eq_three
    [FiniteDimensional K U] (Q : QuadraticSpace K U)
    (hrank : finrank K U = 3) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q L A) :
    ∃ B : Kˣ, Lattice.IsNormGeneratorValue q L B ∧
      Q.Represents (QuadraticSpace.scaledLine B) := by
  rcases Q.represents_scaledLine_or_discriminant_mul_of_finrank_eq_three
      hrank A with hrep | hrep
  · exact ⟨A, hA, hrep⟩
  · exact ⟨laws.discriminantUnit * A,
      hA.discriminant_mul A, hrep⟩

end Bong
