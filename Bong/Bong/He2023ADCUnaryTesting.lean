/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCCorollary721
import Bong.Bong.He2023ADCPublishedProfiles

/-!
# He (2025), the unary maximal-lattice testing table

This file closes the rank-one boundary in Definition 4.1, Proposition 4.2,
Remark 4.3, and Lemma 4.9(ii).  The published unary table has only the first
column `N_1^1(c)`.  Its parameters are the finite square-class representatives
`delta` and `delta*pi`, with `delta` in the chosen unit representative system.

The proof constructs the exact ternary witness `W_2^3(c)` which misses the
selected unary space and represents every other unary square class.  Thus the
result is literal deletion-minimality, not merely minimality after quotienting
duplicate table presentations.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The finite unary part of the published maximal-lattice table. -/
abbrev HeADC2025PublishedUnaryTestingIndex (I : Type u) :=
  HeHuPublishedSquareClassIndex I

namespace HeADC2025PublishedUnaryTestingIndex

variable {I : Type u} (U : I → Kˣ)

/-- The normalized square-class parameter attached to a unary table row. -/
noncomputable def parameter (i : HeADC2025PublishedUnaryTestingIndex I) : Kˣ :=
  HeHuPublishedSquareClassIndex.parameter (K := K) U i

/-- The chosen maximal lattice `N_1^1(c)` in a unary table row. -/
noncomputable def model (i : HeADC2025PublishedUnaryTestingIndex I) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heADCN1Unary (parameter (K := K) U i)

@[simp]
theorem model_rank (i : HeADC2025PublishedUnaryTestingIndex I) :
    (model (K := K) U i).rank = 1 :=
  heHuOMaximalModel_rank _

theorem model_isOMaximal (i : HeADC2025PublishedUnaryTestingIndex I) :
    (model (K := K) U i).IsOMaximal :=
  heHuOMaximalModel_isOMaximal _

/-- The unary table has two valuation parities for every unit square class. -/
theorem card_index (I : Type u) [Fintype I] :
    Fintype.card (HeADC2025PublishedUnaryTestingIndex I) =
      2 * Fintype.card I := by
  simp [HeADC2025PublishedUnaryTestingIndex,
    HeHuPublishedSquareClassIndex, Nat.mul_comm]

end HeADC2025PublishedUnaryTestingIndex

namespace Lattice.QuadraticLatticeModel

private theorem heADCUnary_represents_of_mul_square
    (c d s : Kˣ) (h : c = d * s ^ 2) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heADCW1Unary c))
      (diagonalUnitCoefficients (heADCW1Unary d)) := by
  apply Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    (heADCW1Unary c) (heADCW1Unary d) ![s]
  intro i
  fin_cases i
  simpa [heADCW1Unary] using h

/-- Every unary quadratic space occurs in the finite published table. -/
theorem exists_heADC2025PublishedUnaryIndex_for_model
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (X : QuadraticLatticeModel (K := K)) (hRank : X.rank = 1) :
    ∃ i : HeADC2025PublishedUnaryTestingIndex I,
      X.IsAmbientlyIsometric
        (HeADC2025PublishedUnaryTestingIndex.model (K := K) U i) := by
  let w := X.diagonalUnitsCast 1 hRank
  have hXw := ambientlyIsometric_heHuOMaximalModel_diagonalUnitsCast X 1 hRank
  obtain ⟨i, s, hfactor⟩ :=
    HeHuPublishedSquareClassIndex.exists_parameter_mul_square
      U hU (w 0)
  refine ⟨i, hXw.trans ?_⟩
  apply heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
  have hw : w = heADCW1Unary (w 0) := by
    funext j
    fin_cases j
    rfl
  have hrep := heADCUnary_represents_of_mul_square
    (w 0)
    (HeADC2025PublishedUnaryTestingIndex.parameter (K := K) U i)
    s hfactor
  rw [← hw] at hrep
  exact hrep

/-- Different unary table indices give different ambient isometry classes. -/
theorem heADC2025PublishedUnary_model_eq_of_ambientlyIsometric
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {i j : HeADC2025PublishedUnaryTestingIndex I}
    (hiso :
      (HeADC2025PublishedUnaryTestingIndex.model (K := K) U i).IsAmbientlyIsometric
        (HeADC2025PublishedUnaryTestingIndex.model (K := K) U j)) :
    i = j := by
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients
        (heADCW1Unary
          (HeADC2025PublishedUnaryTestingIndex.parameter (K := K) U i)))
      (diagonalUnitCoefficients
        (heADCW1Unary
          (HeADC2025PublishedUnaryTestingIndex.parameter (K := K) U j))) := by
    apply diagonalRepresents_of_heHuOMaximalModel_ambientlyIsometric
    simpa only [HeADC2025PublishedUnaryTestingIndex.model, heADCN1Unary]
      using hiso
  have hdet := DiagonalIsometryInvariantLaws.determinant_square _ _ hdiag
  apply publishedParameter_eq_of_square U hU
  simpa [HeADC2025PublishedUnaryTestingIndex.parameter,
    heADCW1Unary, diagonalUnitDeterminant, Fin.prod_univ_one]
    using hdet

private theorem heADCUnary_sameDeterminantClass_represents
    (c : Kˣ) (w : Fin 1 → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant w *
        diagonalUnitDeterminant (heADCW1Unary c))) :
    DiagonalRepresents
      (diagonalUnitCoefficients w)
      (diagonalUnitCoefficients (heADCW1Unary c)) := by
  rcases hdet with ⟨s, hs⟩
  let t : Kˣ := s * c⁻¹
  apply Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    w (heADCW1Unary c) ![t]
  intro i
  fin_cases i
  change w 0 = c * t ^ 2
  have hs' : w 0 * c = s * s := by
    simpa [heADCW1Unary, diagonalUnitDeterminant,
      Fin.prod_univ_one] using hs
  dsimp only [t]
  calc
    w 0 = (w 0 * c) * c⁻¹ := by group
    _ = (s * s) * c⁻¹ := by rw [hs']
    _ = c * (s * c⁻¹) ^ 2 := by
      rw [pow_two]
      calc
        s * s * c⁻¹ = (c * c⁻¹) * (s * s * c⁻¹) := by simp
        _ = c * (s * c⁻¹) * (s * c⁻¹) := by ac_rfl
        _ = c * (s * c⁻¹ * (s * c⁻¹)) := by rw [mul_assoc]

/-- Proposition 4.2(iii) in rank one: `W_2^3(c)` is the unique ternary
space which misses `W_1^1(c)` and represents every other unary space. -/
theorem heADC2025Proposition42iiiUnary (c : Kˣ) :
    HeHuUniqueExcludingTarget
      (heADCW1Unary c) (heHuOddSecond 0 c) := by
  have hpair := heHu2022Definition34Proposition35Odd (K := K) 0 c
  have hlift : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append (heADCW1Unary c) (heHuHyperbolicPair (K := K))))
      (diagonalUnitCoefficients (heHuOddFirst 0 c)) := by
    have hcomm := diagonalRepresents_append_comm
      (diagonalUnitCoefficients (heADCW1Unary c))
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
    have hfamily : heHuOddFirst 0 c =
        Fin.append (heHuHyperbolicPair (K := K)) (heADCW1Unary c) := by
      funext i
      fin_cases i <;> rfl
    have htarget :
        diagonalUnitCoefficients (heHuOddFirst 0 c) =
          Fin.append
            (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
            (diagonalUnitCoefficients (heADCW1Unary c)) := by
      rw [hfamily, diagonalUnitCoefficients_append]
    rw [diagonalUnitCoefficients_append, htarget]
    exact hcomm
  exact heHuUniqueExcludingOnlyClass_of_hyperbolicPair
    (heADCW1Unary c) (heHuOddFirst 0 c) (heHuOddSecond 0 c)
    hpair hlift (heADCUnary_sameDeterminantClass_represents c)

/-- The finite unary table is a literal deletion-minimal universality
testing family, including the rank-one boundary of He, Lemma 4.9(ii). -/
theorem heADC2025Lemma49iiUnary
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    IsLiteralMinimalUniversalityTestingFamily
      (HeADC2025PublishedUnaryTestingIndex.model (K := K) U) 1 := by
  refine ⟨completeMaximalFamily_isUniversalityTestingFamily _ _
    (HeADC2025PublishedUnaryTestingIndex.model_isOMaximal U)
    (fun X hRank ↦
      exists_heADC2025PublishedUnaryIndex_for_model U hU X hRank), ?_⟩
  intro i
  let c := HeADC2025PublishedUnaryTestingIndex.parameter (K := K) U i
  let W := heHuOMaximalModel (heHuOddSecond 0 c)
  letI : AddCommGroup W.Carrier := W.addCommGroup
  letI : Module K W.Carrier := W.module
  have hWmaximal : W.IsOMaximal :=
    heHuOMaximalModel_isOMaximal (heHuOddSecond 0 c)
  refine ⟨W, hWmaximal.isIntegral, ?_, ?_⟩
  · intro hrep
    apply (heADC2025Proposition42iiiUnary c).exactness.misses
    apply (heHuOMaximalModel_represents_iff
      (heHuOddSecond 0 c) (heADCW1Unary c)).mp
    simpa only [W, c, HeADC2025PublishedUnaryTestingIndex.model,
      heADCN1Unary] using hrep
  · intro j hji
    apply (heHuOMaximalModel_represents_iff
      (heHuOddSecond 0 c)
      (heADCW1Unary
        (HeADC2025PublishedUnaryTestingIndex.parameter (K := K) U j))).mpr
    apply (heADC2025Proposition42iiiUnary c).exactness.represents_other
    intro hdiag
    apply hji
    apply heADC2025PublishedUnary_model_eq_of_ambientlyIsometric U hU
    apply heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
    simpa only [c, HeADC2025PublishedUnaryTestingIndex.model, heADCN1Unary]
      using hdiag

end Lattice.QuadraticLatticeModel

/-- Remark 4.3 in rank one, before substituting O'Meara's unit-square-class
count: the exact number of maximal unary classes is `2 * |U|`. -/
theorem heADC2025Remark43UnaryCard
    (I : Type u) [Fintype I] :
    Fintype.card (HeADC2025PublishedUnaryTestingIndex I) =
      2 * Fintype.card I :=
  HeADC2025PublishedUnaryTestingIndex.card_index I

/-- The printed `4 * (N p)^e` unary count, relative to the same O'Meara
63:9 cardinality input isolated for Corollary 7.21. -/
theorem heADC2025Remark43UnaryCardPublished
    {I : Type u} [Fintype I] (U : I → Kˣ)
    [HeADC2025Corollary721CountingLaw (K := K)]
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeADC2025PublishedUnaryTestingIndex I) =
      4 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  rw [heADC2025Remark43UnaryCard I,
    HeADC2025Corollary721CountingLaw.card_unit_representatives
      (K := K) U hU]
  ring

end Bong
