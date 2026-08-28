/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Binary
import Bong.Bong.DiagonalBinaryRepresentation
import Bong.Bong.DiagonalOrthogonalBasis
import Bong.Bong.DiagonalDeterminantExtension
import Bong.Bong.DiagonalCodimensionOneCancellationProof

/-!
# The binary first-scaling law

This file discharges the local-space input left abstract in the binary branch
of Beli (2019), Lemma 8.8.  The Hilbert-symbol hypothesis first gives a
represented unary line.  Codimension-one cancellation then completes that
line to the binary diagonal form

`[epsilon * a_1, epsilon^-1 * a_2]`.

The resulting orthogonal basis has the same orders and adjacent defect as the
original binary good BONG, while its first mixed prefix has defect
`d(epsilon)`.  These identities give the complete
`BinaryFirstScalingCertificate`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The explicit binary coefficient change used in Lemma 8.8. -/
noncomputable def binaryFirstScaledValues
    (b : GoodBONG q L 2) (epsilon : Kˣ) : Fin 2 → Kˣ :=
  ![epsilon * b.valueUnit (0 : Fin 2),
    epsilon⁻¹ * b.valueUnit (1 : Fin 2)]

@[simp]
theorem binaryFirstScaledValues_zero
    (b : GoodBONG q L 2) (epsilon : Kˣ) :
    b.binaryFirstScaledValues epsilon (0 : Fin 2) =
      epsilon * b.valueUnit (0 : Fin 2) := by
  rfl

@[simp]
theorem binaryFirstScaledValues_one
    (b : GoodBONG q L 2) (epsilon : Kˣ) :
    b.binaryFirstScaledValues epsilon (1 : Fin 2) =
      epsilon⁻¹ * b.valueUnit (1 : Fin 2) := by
  rfl

/-- The scaled binary form has the same determinant square class. -/
theorem binaryFirstScaledValues_determinantSquare
    (b : GoodBONG q L 2) (epsilon : Kˣ) :
    IsSquare
      (diagonalUnitDeterminant (b.binaryFirstScaledValues epsilon) *
        diagonalUnitDeterminant b.valueUnit) := by
  refine ⟨diagonalUnitDeterminant b.valueUnit, ?_⟩
  apply Units.ext
  simp only [diagonalUnitDeterminant, Fin.prod_univ_two,
    binaryFirstScaledValues_zero, binaryFirstScaledValues_one,
    Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero epsilon]

/-- The Hilbert condition represents the required first line. -/
theorem binaryFirstScaled_prefixRepresents
    (b : GoodBONG q L 2) (epsilon : Kˣ)
    (hhilbert : hilbertSymbol K epsilon (b.adjacentProduct 0) = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (diagonalUnitPrefix (b.binaryFirstScaledValues epsilon)))
      (diagonalUnitCoefficients b.valueUnit) := by
  have hline :=
    (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
      (b.valueUnit (0 : Fin 1).castSucc)
      (b.valueUnit (0 : Fin 1).succ)
      (epsilon * b.valueUnit (0 : Fin 1).castSucc)).2 (by
        have hratio' :
            (epsilon * b.valueUnit (0 : Fin 1).castSucc) *
                (b.valueUnit (0 : Fin 1).castSucc)⁻¹ = epsilon := by
          group
        rw [hratio']
        simpa only [adjacentProduct] using hhilbert)
  convert hline using 1 <;> funext i
  · fin_cases i
    rfl
  · fin_cases i <;> rfl

/-- The completed scaled binary diagonal form is represented by the source
binary form. -/
theorem binaryFirstScaled_diagonalRepresents
    (b : GoodBONG q L 2) (epsilon : Kˣ)
    (hhilbert : hilbertSymbol K epsilon (b.adjacentProduct 0) = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients (b.binaryFirstScaledValues epsilon))
      (diagonalUnitCoefficients b.valueUnit) := by
  exact diagonalRepresents_of_prefix_of_determinant_square
    (b.binaryFirstScaledValues epsilon) b.valueUnit
    (b.binaryFirstScaled_prefixRepresents epsilon hhilbert)
    (b.binaryFirstScaledValues_determinantSquare epsilon)

/-- The represented binary diagonal form gives an orthogonal basis of the
original ambient quadratic space. -/
theorem exists_binaryFirstScaledOrthogonalBasis
    (b : GoodBONG q L 2) (epsilon : Kˣ)
    (hhilbert : hilbertSymbol K epsilon (b.adjacentProduct 0) = 1) :
    ∃ X : BONG.OrthogonalBasisData q 2,
      ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i := by
  exact DiagonalRepresents.exists_orthogonalBasisData b
    (b.binaryFirstScaledValues epsilon)
    (b.binaryFirstScaled_diagonalRepresents epsilon hhilbert)

/-- The only proper mixed prefix is `epsilon` times a square. -/
theorem binaryFirstScaled_comparisonPrefixUnit_one
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i) :
    X.comparisonPrefixUnit b 1 =
      epsilon * (b.valueUnit (0 : Fin 2)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change b.toBONG.prefixProduct 1 * X.prefixProduct 1 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 2 => j.1 < 1) = {0} by
    decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The full mixed comparison product is a square. -/
theorem binaryFirstScaled_comparisonPrefixUnit_full
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i) :
    X.comparisonPrefixUnit b 2 =
      (diagonalUnitDeterminant b.valueUnit) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change b.toBONG.prefixProduct 2 * X.prefixProduct 2 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
    diagonalUnitDeterminant
  rw [show Finset.univ.filter (fun j : Fin 2 => j.1 < 2) =
      Finset.univ by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro j.isLt]
  simp [hvalues, Fin.prod_univ_two, pow_two]
  unfold GoodBONG.valueUnit
  calc
    _ = (epsilon * epsilon⁻¹) *
        (b.toBONG.valueUnit 0 * b.toBONG.valueUnit 1 *
          b.toBONG.valueUnit 0 * b.toBONG.valueUnit 1) := by
      ac_rfl
    _ = _ := by
      rw [mul_inv_cancel, one_mul]
      ac_rfl

/-- Valuation-unit scaling preserves both binary orders. -/
theorem binaryFirstScaled_sameOrders
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hunit : IsValuationUnit K (epsilon : K))
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i) :
    X.SameOrders b := by
  have hepsilonOrder : ordUnit K epsilon = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K epsilon).1 hunit
  intro i
  fin_cases i
  · change ordUnit K (X.valueUnit (0 : Fin 2)) =
      b.toBONG.order (0 : Fin 2)
    rw [hvalues, binaryFirstScaledValues_zero,
      b.toBONG.order_eq_ordUnit, ordUnit_mul, hepsilonOrder]
    simp
    unfold GoodBONG.valueUnit
    rfl
  · change ordUnit K (X.valueUnit (1 : Fin 2)) =
      b.toBONG.order (1 : Fin 2)
    rw [hvalues, binaryFirstScaledValues_one,
      b.toBONG.order_eq_ordUnit, ordUnit_mul, ordUnit_inv,
      hepsilonOrder]
    simp
    unfold GoodBONG.valueUnit
    rfl

/-- The scaled binary pair has exactly the same adjacent product. -/
theorem binaryFirstScaled_adjacentProduct
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i) :
    X.adjacentProduct (0 : Fin 1) = b.adjacentProduct (0 : Fin 1) := by
  unfold BONG.OrthogonalBasisData.adjacentProduct adjacentProduct
  rw [hvalues (0 : Fin 1).castSucc, hvalues (0 : Fin 1).succ]
  have hzero : (0 : Fin 1).castSucc = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hone : (0 : Fin 1).succ = (1 : Fin 2) := by
    apply Fin.ext
    rfl
  rw [hzero, hone]
  apply Units.ext
  simp only [binaryFirstScaledValues_zero, binaryFirstScaledValues_one,
    Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero epsilon]

/-- Consequently the unique adjacent defect is unchanged. -/
theorem binaryFirstScaled_adjacentDefect
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i) :
    X.adjacentDefect (0 : Fin 1) = b.adjacentDefect (0 : Fin 1) := by
  unfold BONG.OrthogonalBasisData.adjacentDefect adjacentDefect
  rw [b.binaryFirstScaled_adjacentProduct X epsilon hvalues]

/-- The defect bound on `epsilon` is precisely the binary prefix bound. -/
theorem binaryFirstScaled_prefixDefectBounds
    [QuadraticDefectLaws K]
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i)
    (hdefect : (b.alphaValue (0 : Fin 1) : WithTop ℚ) ≤
      defectOrder (K := K) epsilon) :
    X.PrefixDefectBounds b := by
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change (b.alphaValue (0 : Fin 1) : WithTop ℚ) ≤
    X.comparisonPrefixDefect b 1
  unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
  rw [b.binaryFirstScaled_comparisonPrefixUnit_one X epsilon hvalues,
    defectOrder_mul_square]
  exact hdefect

/-- The final comparison condition is automatic for the scaled pair. -/
theorem binaryFirstScaled_fullComparisonSquare
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i) :
    IsSquare (X.comparisonPrefixUnit b 2) := by
  rw [b.binaryFirstScaled_comparisonPrefixUnit_full X epsilon hvalues]
  exact ⟨diagonalUnitDeterminant b.valueUnit, by simp [pow_two]⟩

/-- The unique binary alpha candidate set is unchanged by the scaling. -/
theorem binaryFirstScaled_alphaCandidates_eq
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hunit : IsValuationUnit K (epsilon : K))
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i) :
    X.alphaCandidates (0 : Fin 1) = b.alphaCandidates (0 : Fin 1) := by
  have horders := b.binaryFirstScaled_sameOrders X epsilon hunit hvalues
  have hadjacent := b.binaryFirstScaled_adjacentDefect X epsilon hvalues
  have hhalf : X.halfGapCandidate (0 : Fin 1) =
      b.halfGapCandidate (0 : Fin 1) := by
    unfold BONG.OrthogonalBasisData.halfGapCandidate halfGapCandidate
    rw [horders (0 : Fin 1).succ, horders (0 : Fin 1).castSucc]
  have hleft : X.leftDefectCandidate (0 : Fin 1) =
      b.leftDefectCandidate (0 : Fin 1) := by
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    unfold BONG.OrthogonalBasisData.leftDefectCandidate leftDefectCandidate
    rw [horders (0 : Fin 1).succ, horders (0 : Fin 1).castSucc,
      hadjacent]
  have hright : X.rightDefectCandidate (0 : Fin 1) =
      b.rightDefectCandidate (0 : Fin 1) := by
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    unfold BONG.OrthogonalBasisData.rightDefectCandidate rightDefectCandidate
    rw [horders (0 : Fin 1).succ, horders (0 : Fin 1).castSucc,
      hadjacent]
  unfold BONG.OrthogonalBasisData.alphaCandidates alphaCandidates
  rw [hhalf, hleft, hright]

/-- The unique rational binary alpha is unchanged. -/
theorem binaryFirstScaled_alphaValue_eq
    (b : GoodBONG q L 2) (X : BONG.OrthogonalBasisData q 2)
    (epsilon : Kˣ)
    (hunit : IsValuationUnit K (epsilon : K))
    (hvalues : ∀ i, X.valueUnit i = b.binaryFirstScaledValues epsilon i) :
    X.alphaValue (0 : Fin 1) = b.alphaValue (0 : Fin 1) := by
  apply WithTop.coe_injective
  rw [X.coe_alphaValue, b.coe_alphaValue]
  have hcandidates :=
    b.binaryFirstScaled_alphaCandidates_eq X epsilon hunit hvalues
  unfold BONG.OrthogonalBasisData.alpha alpha
  simpa only [hcandidates]

end BONG.GoodBONG

/-- The explicit binary construction supplies the global default first-
scaling instance used by the Beli (2019) development. -/
noncomputable instance dyadicBinaryFirstScalingLawsProved
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [QuadraticDefectLaws K] :
    DyadicBinaryFirstScalingLaws.{u, v} K where
  exists_basisCertificate b epsilon hunit hdefect hhilbert := by
    rcases b.exists_binaryFirstScaledOrthogonalBasis epsilon hhilbert with
      ⟨X, hvalues⟩
    exact ⟨{
      basisData := X
      firstValue_eq := hvalues (0 : Fin 2)
      sameOrders := b.binaryFirstScaled_sameOrders X epsilon hunit hvalues
      prefixDefectBounds :=
        b.binaryFirstScaled_prefixDefectBounds X epsilon hvalues hdefect
      fullComparisonSquare :=
        b.binaryFirstScaled_fullComparisonSquare X epsilon hvalues
      firstAlpha_eq :=
        b.binaryFirstScaled_alphaValue_eq X epsilon hunit hvalues
    }⟩

end Bong
