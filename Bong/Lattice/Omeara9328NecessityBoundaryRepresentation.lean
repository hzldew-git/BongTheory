/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NecessityBoundaryDiscriminant
import Bong.Bong.Beli2009ClassificationPropagation
import Bong.Bong.DiagonalBoundaryWitt
import Bong.Bong.DiagonalRepresentationParity
import Bong.Bong.DiagonalHasseSymbol
import Bong.Lattice.BasisIsometry
import Bong.Lattice.RankFourDeterminantHyperbolic

/-!
# O'Meara 93:28 necessity: the strict first-boundary representation

At a strict left boundary, the two binary discriminants constructed from
the projected rank-four head are one valuation step more congruent to `-1`
than the printed threshold.  The resulting defect estimates make the two
successive ternary Hilbert symbols trivial and split two hyperbolic planes.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace Lattice

universe u

variable {K : Type u} [Field K]

/-- Independent shears inside the first and last pair of a four-vector
basis preserve linear independence. -/
theorem linearIndependent_finFour_pairShear
    {X : Type*} [AddCommGroup X] [Module K X]
    (b : Basis (Fin 4) K X) (s t : K) :
    LinearIndependent K ![b 0, b 1 + s • b 0,
      b 2, b 3 + t • b 2] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := congrArg b.repr hg
  have h₀ := congrArg (fun v ↦ v (0 : Fin 4)) hr
  have h₁ := congrArg (fun v ↦ v (1 : Fin 4)) hr
  have h₂ := congrArg (fun v ↦ v (2 : Fin 4)) hr
  have h₃ := congrArg (fun v ↦ v (3 : Fin 4)) hr
  simp [Fin.sum_univ_four] at h₀ h₁ h₂ h₃
  fin_cases i
  · simpa [h₁] using h₀
  · exact h₁
  · simpa [h₃] using h₂
  · exact h₃

end Lattice

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

/-- The exponent of the left threshold after normalizing the first scale. -/
noncomputable def firstBoundaryThresholdExponent : Int :=
  2 * (ramificationIndex K : Int) + ordUnit K S.firstNormGenerator -
    weightIdealOrder S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice

/-- The normalized first-boundary threshold is the corresponding power
ideal. -/
theorem firstBoundary_fourNormOverWeightIdeal_eq_powerIdeal :
    S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0) =
      powerIdeal (K := K) S.firstBoundaryThresholdExponent := by
  unfold firstBoundaryThresholdExponent fourNormOverWeightIdeal
  rw [show boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) by ext; rfl,
    S.firstNormGenerator_order,
    S.sourceFirstNormalized_weightIdealOrder_eq_fundamental]
  congr 1
  omega

/-- The threshold exponent is at least the ramification index. -/
theorem ramificationIndex_le_firstBoundaryThresholdExponent :
    (ramificationIndex K : Int) ≤ S.firstBoundaryThresholdExponent := by
  have hu : 0 ≤ ordUnit K S.firstNormGenerator :=
    ordUnit_nonneg_of_mem_integerRing S.firstNormGenerator
      S.firstNormGenerator_integral
  have hw := S.sourceFirstNormalized_weightIdealOrder_le_ramificationIndex
  unfold firstBoundaryThresholdExponent
  omega

/-- In particular the successor threshold is a nonnegative exponent. -/
theorem firstBoundaryThresholdExponent_add_one_nonneg :
    0 ≤ S.firstBoundaryThresholdExponent + 1 := by
  have he : 0 ≤ (ramificationIndex K : Int) := by omega
  have h := S.ramificationIndex_le_firstBoundaryThresholdExponent
  omega

/-- Proper containment upgrades a square-class congruence modulo the first
fundamental ideal to congruence modulo the successor of the threshold
power.  This is the discrete-valuation step hidden in O'Meara's strict
containment sign. -/
theorem unitsCongruentModulo_powerIdeal_threshold_add_one_of_strict
    (d : Kˣ)
    (hcongruent : BONG.GoodBONG.UnitsCongruentModulo d (-1 : Kˣ)
      (S.sourceJordan.fundamentalIdeal 0))
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0)) :
    BONG.GoodBONG.UnitsCongruentModulo d (-1 : Kˣ)
      (powerIdeal (K := K) (S.firstBoundaryThresholdExponent + 1)) := by
  rcases hcongruent with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [mem_powerIdeal_iff]
  apply coe_int_add_one_le_of_lt
  have htrigger' : S.sourceJordan.fundamentalIdeal 0 <
      powerIdeal (K := K) S.firstBoundaryThresholdExponent := by
    rw [← S.firstBoundary_fourNormOverWeightIdeal_eq_powerIdeal]
    exact htrigger
  have hlt := ordUnit_lt_ord_of_mem_of_lt_principalIdeal
    (Dyadic.uniformizerPowerUnit K S.firstBoundaryThresholdExponent)
    (S.sourceJordan.fundamentalIdeal 0) hs (by
      simpa only [powerIdeal] using htrigger')
  simpa using hlt

/-- The first projected binary discriminant has defect at least one more
than the strict threshold. -/
theorem firstBoundaryThreshold_add_one_le_projectedDiscriminantDefect
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0)) :
    ((((S.firstBoundaryThresholdExponent + 1 : Int) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (-S.projectedAdaptedFirstGramUnit f)) := by
  have hdeep :=
    S.unitsCongruentModulo_powerIdeal_threshold_add_one_of_strict
      (S.projectedAdaptedFirstGramUnit f)
      (S.projectedAdaptedFirstGramUnit_congruent_negOne_of_strictNormOrder
        f hgap) htrigger
  have h :=
    BONG.GoodBONG.intCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
      (S.projectedAdaptedFirstGramUnit f) (-1 : Kˣ)
      (S.firstBoundaryThresholdExponent + 1)
      S.firstBoundaryThresholdExponent_add_one_nonneg
      (by
        have hd : IsValuationUnit K
            (S.projectedAdaptedFirstGramUnit f : K) := by
          simpa only [S.coe_projectedAdaptedFirstGramUnit] using
            S.projectedAdaptedFirstGramDet_isValuationUnit f
        rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1 hd,
          ordUnit_neg]
        exact ((isValuationUnit_iff_ordUnit_eq_zero K (1 : Kˣ)).1
          (by simp [IsValuationUnit])).symm)
      hdeep
  simpa only [mul_neg, mul_one] using h

/-- The second orthogonal binary discriminant satisfies the same strict
defect estimate. -/
theorem firstBoundaryThreshold_add_one_le_secondDiscriminantDefect
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0)) :
    ((((S.firstBoundaryThresholdExponent + 1 : Int) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (-S.orthogonalizedSecondGramUnit f)) := by
  have hdeep :=
    S.unitsCongruentModulo_powerIdeal_threshold_add_one_of_strict
      (S.orthogonalizedSecondGramUnit f)
      (S.orthogonalizedSecondGramUnit_congruent_negOne_of_strictNormOrder
        f hgap) htrigger
  have h :=
    BONG.GoodBONG.intCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
      (S.orthogonalizedSecondGramUnit f) (-1 : Kˣ)
      (S.firstBoundaryThresholdExponent + 1)
      S.firstBoundaryThresholdExponent_add_one_nonneg
      (by
        have hd : IsValuationUnit K
            (S.orthogonalizedSecondGramUnit f : K) := by
          simpa only [S.coe_orthogonalizedSecondGramUnit] using
            S.orthogonalizedSecondGramDet_isValuationUnit f
        rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1 hd,
          ordUnit_neg]
        exact ((isValuationUnit_iff_ordUnit_eq_zero K (1 : Kˣ)).1
          (by simp [IsValuationUnit])).symm)
      hdeep
  simpa only [mul_neg, mul_one] using h

/-- The first projected norm generator differs from the chosen source norm
generator by defect at least `w-u`. -/
theorem firstBoundaryWeightGap_le_projectedNormRatioDefect
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    ((((weightIdealOrder S.targetFirstNormalized
          (S.targetJordan.component 0).lattice -
        ordUnit K S.firstNormGenerator : Int) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (-(S.firstNormGenerator /
          S.projectedAdaptedFirstGramZeroUnit f hgap))) := by
  exact Lattice.weightIdealOrder_sub_ordUnit_le_defectOrder_neg_div_of_normGenerators
    S.firstNormGenerator (S.projectedAdaptedFirstGramZeroUnit f hgap)
    S.firstNormGenerator_target
    (S.projectedAdaptedFirstGramZeroUnit_isNormGeneratorValue f hgap)
    (S.projectedAdaptedFirstGramZeroUnit_order_eq f hgap)

/-- The norm generator from the orthogonalized second binary block obeys
the same relative defect estimate. -/
theorem firstBoundaryWeightGap_le_secondNormRatioDefect
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    ((((weightIdealOrder S.targetFirstNormalized
          (S.targetJordan.component 0).lattice -
        ordUnit K S.firstNormGenerator : Int) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (-(S.firstNormGenerator /
          S.orthogonalizedSecondGramZeroUnit f hgap))) := by
  exact Lattice.weightIdealOrder_sub_ordUnit_le_defectOrder_neg_div_of_normGenerators
    S.firstNormGenerator (S.orthogonalizedSecondGramZeroUnit f hgap)
    S.firstNormGenerator_target
    (S.orthogonalizedSecondGramZeroUnit_isNormGeneratorValue f hgap)
    (S.orthogonalizedSecondGramZeroUnit_order_eq f hgap)

/-- The projected-block defect estimate with an arbitrary coherent norm
generator of the normalized target head. -/
theorem firstBoundaryWeightGap_le_projectedNormRatioDefectFor
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (a : Kˣ)
    (ha : IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice a)
    (hord : ordUnit K a = ordUnit K S.firstNormGenerator) :
    ((((weightIdealOrder S.targetFirstNormalized
          (S.targetJordan.component 0).lattice -
        ordUnit K S.firstNormGenerator : Int) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (-(a / S.projectedAdaptedFirstGramZeroUnit f hgap))) := by
  have h :=
    Lattice.weightIdealOrder_sub_ordUnit_le_defectOrder_neg_div_of_normGenerators
      a (S.projectedAdaptedFirstGramZeroUnit f hgap) ha
      (S.projectedAdaptedFirstGramZeroUnit_isNormGeneratorValue f hgap)
      (by
        rw [S.projectedAdaptedFirstGramZeroUnit_order_eq f hgap, hord])
  simpa only [hord] using h

/-- The second-block defect estimate with an arbitrary coherent norm
generator of the normalized target head. -/
theorem firstBoundaryWeightGap_le_secondNormRatioDefectFor
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (a : Kˣ)
    (ha : IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice a)
    (hord : ordUnit K a = ordUnit K S.firstNormGenerator) :
    ((((weightIdealOrder S.targetFirstNormalized
          (S.targetJordan.component 0).lattice -
        ordUnit K S.firstNormGenerator : Int) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (-(a / S.orthogonalizedSecondGramZeroUnit f hgap))) := by
  have h :=
    Lattice.weightIdealOrder_sub_ordUnit_le_defectOrder_neg_div_of_normGenerators
      a (S.orthogonalizedSecondGramZeroUnit f hgap) ha
      (S.orthogonalizedSecondGramZeroUnit_isNormGeneratorValue f hgap)
      (by
        rw [S.orthogonalizedSecondGramZeroUnit_order_eq f hgap, hord])
  simpa only [hord] using h

/-- The two complementary lower bounds add to `2e+1`. -/
theorem twoRamification_lt_thresholdSuccessor_add_weightGap :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      ((((S.firstBoundaryThresholdExponent + 1 : Int) : ℚ) : WithTop ℚ) +
        (((weightIdealOrder S.targetFirstNormalized
              (S.targetJordan.component 0).lattice -
            ordUnit K S.firstNormGenerator : Int) : ℚ) : WithTop ℚ)) := by
  rw [← S.firstNormalized_weightIdealOrder_eq]
  norm_cast
  unfold firstBoundaryThresholdExponent
  push_cast
  omega

/-- The first binary block and the adjoined norm-generator line form an
isotropic ternary space. -/
theorem projectedDiscriminant_normRatio_hilbert_eq_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0)) :
    hilbertSymbol K (-S.projectedAdaptedFirstGramUnit f)
      (-(S.firstNormGenerator /
        S.projectedAdaptedFirstGramZeroUnit f hgap)) = 1 := by
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  exact S.twoRamification_lt_thresholdSuccessor_add_weightGap.trans_le
    (add_le_add
      (S.firstBoundaryThreshold_add_one_le_projectedDiscriminantDefect
        f hgap htrigger)
      (S.firstBoundaryWeightGap_le_projectedNormRatioDefect f hgap))

/-- The analogous Hilbert symbol for the second orthogonal binary block is
also trivial. -/
theorem secondDiscriminant_normRatio_hilbert_eq_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0)) :
    hilbertSymbol K (-S.orthogonalizedSecondGramUnit f)
      (-(S.firstNormGenerator /
        S.orthogonalizedSecondGramZeroUnit f hgap)) = 1 := by
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  exact S.twoRamification_lt_thresholdSuccessor_add_weightGap.trans_le
    (add_le_add
      (S.firstBoundaryThreshold_add_one_le_secondDiscriminantDefect
        f hgap htrigger)
      (S.firstBoundaryWeightGap_le_secondNormRatioDefect f hgap))

/-- The first ternary Hilbert symbol vanishes for every coherent normalized
first norm generator of the correct order. -/
theorem projectedDiscriminant_normRatio_hilbert_eq_one_for
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0))
    (a : Kˣ)
    (ha : IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice a)
    (hord : ordUnit K a = ordUnit K S.firstNormGenerator) :
    hilbertSymbol K (-S.projectedAdaptedFirstGramUnit f)
      (-(a / S.projectedAdaptedFirstGramZeroUnit f hgap)) = 1 := by
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  exact S.twoRamification_lt_thresholdSuccessor_add_weightGap.trans_le
    (add_le_add
      (S.firstBoundaryThreshold_add_one_le_projectedDiscriminantDefect
        f hgap htrigger)
      (S.firstBoundaryWeightGap_le_projectedNormRatioDefectFor
        f hgap a ha hord))

/-- The second ternary Hilbert symbol vanishes for every coherent normalized
first norm generator of the correct order. -/
theorem secondDiscriminant_normRatio_hilbert_eq_one_for
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0))
    (a : Kˣ)
    (ha : IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice a)
    (hord : ordUnit K a = ordUnit K S.firstNormGenerator) :
    hilbertSymbol K (-S.orthogonalizedSecondGramUnit f)
      (-(a / S.orthogonalizedSecondGramZeroUnit f hgap)) = 1 := by
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  exact S.twoRamification_lt_thresholdSuccessor_add_weightGap.trans_le
    (add_le_add
      (S.firstBoundaryThreshold_add_one_le_secondDiscriminantDefect
        f hgap htrigger)
      (S.firstBoundaryWeightGap_le_secondNormRatioDefectFor
        f hgap a ha hord))

/-- The two negative binary discriminants are mutually Hilbert-orthogonal.
Here both strict bounds are at least `e+1`. -/
theorem binaryDiscriminants_hilbert_eq_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0)) :
    hilbertSymbol K (-S.projectedAdaptedFirstGramUnit f)
      (-S.orthogonalizedSecondGramUnit f) = 1 := by
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  apply lt_of_lt_of_le _
    (add_le_add
      (S.firstBoundaryThreshold_add_one_le_projectedDiscriminantDefect
        f hgap htrigger)
      (S.firstBoundaryThreshold_add_one_le_secondDiscriminantDefect
        f hgap htrigger))
  norm_cast
  have hT := S.ramificationIndex_le_firstBoundaryThresholdExponent
  omega

/-- The four nonzero diagonal coefficients obtained by completing the
square separately in the two orthogonal binary Gram blocks. -/
noncomputable def firstBoundaryDiagonalUnits
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) : Fin 4 → Kˣ :=
  ![S.projectedAdaptedFirstGramZeroUnit f hgap,
    S.projectedAdaptedFirstGramUnit f /
      S.projectedAdaptedFirstGramZeroUnit f hgap,
    S.orthogonalizedSecondGramZeroUnit f hgap,
    S.orthogonalizedSecondGramUnit f /
      S.orthogonalizedSecondGramZeroUnit f hgap]

@[simp] theorem firstBoundaryDiagonalUnits_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.firstBoundaryDiagonalUnits f hgap 0 =
      S.projectedAdaptedFirstGramZeroUnit f hgap := by
  rfl

@[simp] theorem firstBoundaryDiagonalUnits_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.firstBoundaryDiagonalUnits f hgap 1 =
      S.projectedAdaptedFirstGramUnit f /
        S.projectedAdaptedFirstGramZeroUnit f hgap := by
  rfl

@[simp] theorem firstBoundaryDiagonalUnits_two
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.firstBoundaryDiagonalUnits f hgap 2 =
      S.orthogonalizedSecondGramZeroUnit f hgap := by
  rfl

@[simp] theorem firstBoundaryDiagonalUnits_three
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.firstBoundaryDiagonalUnits f hgap 3 =
      S.orthogonalizedSecondGramUnit f /
        S.orthogonalizedSecondGramZeroUnit f hgap := by
  rfl

/-- The pairwise shear which diagonalizes the projected rank-four basis. -/
noncomputable def firstBoundaryDiagonalizingFamily
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    Fin 4 → (S.targetJordan.component 0).carrier :=
  let b := S.orthogonalizedProjectedAdaptedBasis f
  let a : K := S.projectedAdaptedFirstGramMatrix f 0 0
  let p : K := S.projectedAdaptedFirstGramMatrix f 0 1
  let z : K := S.orthogonalizedSecondGramMatrix f 0 0
  let t : K := S.orthogonalizedSecondGramMatrix f 0 1
  ![b 0, b 1 + (-(p / a)) • b 0,
    b 2, b 3 + (-(t / z)) • b 2]

@[simp] theorem firstBoundaryDiagonalizingFamily_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.firstBoundaryDiagonalizingFamily f hgap 0 =
      S.orthogonalizedProjectedAdaptedBasis f 0 := by
  rfl

@[simp] theorem firstBoundaryDiagonalizingFamily_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.firstBoundaryDiagonalizingFamily f hgap 1 =
      S.orthogonalizedProjectedAdaptedBasis f 1 +
        (-((S.projectedAdaptedFirstGramMatrix f 0 1) /
          (S.projectedAdaptedFirstGramMatrix f 0 0))) •
            S.orthogonalizedProjectedAdaptedBasis f 0 := by
  rfl

@[simp] theorem firstBoundaryDiagonalizingFamily_two
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.firstBoundaryDiagonalizingFamily f hgap 2 =
      S.orthogonalizedProjectedAdaptedBasis f 2 := by
  rfl

@[simp] theorem firstBoundaryDiagonalizingFamily_three
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.firstBoundaryDiagonalizingFamily f hgap 3 =
      S.orthogonalizedProjectedAdaptedBasis f 3 +
        (-((S.orthogonalizedSecondGramMatrix f 0 1) /
          (S.orthogonalizedSecondGramMatrix f 0 0))) •
            S.orthogonalizedProjectedAdaptedBasis f 2 := by
  rfl

/-- The diagonalizing family is a basis. -/
noncomputable def firstBoundaryDiagonalizingBasis
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    Basis (Fin 4) K (S.targetJordan.component 0).carrier := by
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  apply basisOfLinearIndependentOfCardEqFinrank'
    (S.firstBoundaryDiagonalizingFamily f hgap)
  · simpa only [firstBoundaryDiagonalizingFamily] using
      Lattice.linearIndependent_finFour_pairShear
        (S.orthogonalizedProjectedAdaptedBasis f)
        (-((S.projectedAdaptedFirstGramMatrix f 0 1) /
          (S.projectedAdaptedFirstGramMatrix f 0 0)))
        (-((S.orthogonalizedSecondGramMatrix f 0 1) /
          (S.orthogonalizedSecondGramMatrix f 0 0)))
  · simpa using S.targetFirstNormalized_finrank.symm

@[simp]
theorem firstBoundaryDiagonalizingBasis_apply
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) (i : Fin 4) :
    S.firstBoundaryDiagonalizingBasis f hgap i =
      S.firstBoundaryDiagonalizingFamily f hgap i := by
  simp [firstBoundaryDiagonalizingBasis]

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_zero_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 0)
        (S.orthogonalizedProjectedAdaptedBasis f 0) =
      S.projectedAdaptedFirstGramMatrix f 0 0 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_zero]
  rfl

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_zero_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 0)
        (S.orthogonalizedProjectedAdaptedBasis f 1) =
      S.projectedAdaptedFirstGramMatrix f 0 1 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_zero,
    S.orthogonalizedProjectedAdaptedBasis_one]
  rfl

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_one_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 1)
        (S.orthogonalizedProjectedAdaptedBasis f 0) =
      S.projectedAdaptedFirstGramMatrix f 0 1 := by
  rw [S.targetFirstNormalized.isSymm.eq]
  exact S.orthogonalizedProjectedAdaptedBasis_bilin_zero_one f

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_one_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 1)
        (S.orthogonalizedProjectedAdaptedBasis f 1) =
      S.projectedAdaptedFirstGramMatrix f 1 1 := by
  rw [S.orthogonalizedProjectedAdaptedBasis_one]
  rfl

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_two_two
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 2)
        (S.orthogonalizedProjectedAdaptedBasis f 2) =
      S.orthogonalizedSecondGramMatrix f 0 0 := by
  rfl

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_two_three
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 2)
        (S.orthogonalizedProjectedAdaptedBasis f 3) =
      S.orthogonalizedSecondGramMatrix f 0 1 := by
  rfl

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_three_two
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 3)
        (S.orthogonalizedProjectedAdaptedBasis f 2) =
      S.orthogonalizedSecondGramMatrix f 0 1 := by
  rw [S.targetFirstNormalized.isSymm.eq]
  exact S.orthogonalizedProjectedAdaptedBasis_bilin_two_three f

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_three_three
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 3)
        (S.orthogonalizedProjectedAdaptedBasis f 3) =
      S.orthogonalizedSecondGramMatrix f 1 1 := by
  rfl

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_two_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 2)
        (S.orthogonalizedProjectedAdaptedBasis f 0) = 0 := by
  rw [S.targetFirstNormalized.isSymm.eq]
  exact S.orthogonalizedProjectedAdaptedBasis_bilin_zero_two f

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_three_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 3)
        (S.orthogonalizedProjectedAdaptedBasis f 0) = 0 := by
  rw [S.targetFirstNormalized.isSymm.eq]
  exact S.orthogonalizedProjectedAdaptedBasis_bilin_zero_three f

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_two_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 2)
        (S.orthogonalizedProjectedAdaptedBasis f 1) = 0 := by
  rw [S.targetFirstNormalized.isSymm.eq]
  exact S.orthogonalizedProjectedAdaptedBasis_bilin_one_two f

@[simp] theorem orthogonalizedProjectedAdaptedBasis_bilin_three_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.targetFirstNormalized.bilin
        (S.orthogonalizedProjectedAdaptedBasis f 3)
        (S.orthogonalizedProjectedAdaptedBasis f 1) = 0 := by
  rw [S.targetFirstNormalized.isSymm.eq]
  exact S.orthogonalizedProjectedAdaptedBasis_bilin_one_three f

set_option maxHeartbeats 2000000 in
/-- Gram equality between the pair-sheared basis and its explicit finite
diagonal model. -/
theorem firstBoundaryDiagonalizingBasis_gram
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) (i j : Fin 4) :
    S.targetFirstNormalized.bilin
        (S.firstBoundaryDiagonalizingBasis f hgap i)
        (S.firstBoundaryDiagonalizingBasis f hgap j) =
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients
          (S.firstBoundaryDiagonalUnits f hgap))
        (fun k ↦ Units.ne_zero (S.firstBoundaryDiagonalUnits f hgap k))).bilin
          (Pi.basisFun K (Fin 4) i) (Pi.basisFun K (Fin 4) j) := by
  let d := S.firstBoundaryDiagonalUnits f hgap
  let b := S.firstBoundaryDiagonalizingFamily f hgap
  have hmodel (x y : Fin 4) :
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients d)
        (fun k ↦ Units.ne_zero (d k))).bilin
          (Pi.basisFun K (Fin 4) x) (Pi.basisFun K (Fin 4) y) =
        if x = y then (d x : K) else 0 := by
    rw [QuadraticSpace.finiteDiagonal_bilin_apply]
    classical
    rw [Finset.sum_eq_single x]
    · by_cases hxy : x = y
      · subst y
        simp [Pi.basisFun_apply,
          BONG.GoodBONG.diagonalUnitCoefficients]
      · simp [Pi.basisFun_apply, hxy, Ne.symm hxy,
          BONG.GoodBONG.diagonalUnitCoefficients]
    · intro z _ hzx
      simp [Pi.basisFun_apply, hzx]
    · simp
  have h00 : S.targetFirstNormalized.bilin (b 0) (b 0) = (d 0 : K) := by
    simp only [b, d, firstBoundaryDiagonalizingFamily_zero,
      firstBoundaryDiagonalUnits_zero,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_zero,
      S.coe_projectedAdaptedFirstGramZeroUnit]
  have h01 : S.targetFirstNormalized.bilin (b 0) (b 1) = 0 := by
    simp only [b, firstBoundaryDiagonalizingFamily_zero,
      firstBoundaryDiagonalizingFamily_one,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_one,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_zero]
    field_simp [S.projectedAdaptedFirstGram_zero_zero_ne_zero f hgap]
    ring
  have h02 : S.targetFirstNormalized.bilin (b 0) (b 2) = 0 := by
    simp only [b, firstBoundaryDiagonalizingFamily_zero,
      firstBoundaryDiagonalizingFamily_two,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_two]
  have h03 : S.targetFirstNormalized.bilin (b 0) (b 3) = 0 := by
    simp only [b, firstBoundaryDiagonalizingFamily_zero,
      firstBoundaryDiagonalizingFamily_three,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_three,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_two,
      mul_zero, add_zero]
  have h11 : S.targetFirstNormalized.bilin (b 1) (b 1) = (d 1 : K) := by
    simp only [b, d, firstBoundaryDiagonalizingFamily_one,
      firstBoundaryDiagonalUnits_one,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_zero,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_one,
      S.orthogonalizedProjectedAdaptedBasis_bilin_one_zero,
      S.orthogonalizedProjectedAdaptedBasis_bilin_one_one,
      S.coe_projectedAdaptedFirstGramZeroUnit]
    rw [Units.val_div_eq_div_val,
      S.coe_projectedAdaptedFirstGramUnit,
      S.coe_projectedAdaptedFirstGramZeroUnit]
    field_simp [S.projectedAdaptedFirstGram_zero_zero_ne_zero f hgap]
    have hdet : (S.projectedAdaptedFirstGramMatrix f).det =
        S.projectedAdaptedFirstGramMatrix f 0 0 *
          S.projectedAdaptedFirstGramMatrix f 1 1 -
        S.projectedAdaptedFirstGramMatrix f 0 1 ^ 2 := by
      rw [Matrix.det_fin_two]
      have hsymm : S.projectedAdaptedFirstGramMatrix f 1 0 =
          S.projectedAdaptedFirstGramMatrix f 0 1 := by
        unfold projectedAdaptedFirstGramMatrix
        exact S.targetFirstNormalized.isSymm.eq _ _
      rw [hsymm]
      ring
    rw [hdet]
    ring
  have h12 : S.targetFirstNormalized.bilin (b 1) (b 2) = 0 := by
    simp only [b, firstBoundaryDiagonalizingFamily_one,
      firstBoundaryDiagonalizingFamily_two,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      S.orthogonalizedProjectedAdaptedBasis_bilin_one_two,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_two,
      mul_zero, zero_add]
  have h13 : S.targetFirstNormalized.bilin (b 1) (b 3) = 0 := by
    simp only [b, firstBoundaryDiagonalizingFamily_one,
      firstBoundaryDiagonalizingFamily_three,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      S.orthogonalizedProjectedAdaptedBasis_bilin_one_three,
      S.orthogonalizedProjectedAdaptedBasis_bilin_one_two,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_three,
      S.orthogonalizedProjectedAdaptedBasis_bilin_zero_two,
      mul_zero, zero_add, add_zero]
  have h22 : S.targetFirstNormalized.bilin (b 2) (b 2) = (d 2 : K) := by
    simp only [b, d, firstBoundaryDiagonalizingFamily_two,
      firstBoundaryDiagonalUnits_two,
      S.orthogonalizedProjectedAdaptedBasis_bilin_two_two,
      S.coe_orthogonalizedSecondGramZeroUnit]
  have h23 : S.targetFirstNormalized.bilin (b 2) (b 3) = 0 := by
    simp only [b, firstBoundaryDiagonalizingFamily_two,
      firstBoundaryDiagonalizingFamily_three,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      S.orthogonalizedProjectedAdaptedBasis_bilin_two_three,
      S.orthogonalizedProjectedAdaptedBasis_bilin_two_two]
    field_simp [S.orthogonalizedSecondGram_zero_zero_ne_zero f hgap]
    ring
  have h33 : S.targetFirstNormalized.bilin (b 3) (b 3) = (d 3 : K) := by
    simp only [b, d, firstBoundaryDiagonalizingFamily_three,
      firstBoundaryDiagonalUnits_three,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      S.orthogonalizedProjectedAdaptedBasis_bilin_two_two,
      S.orthogonalizedProjectedAdaptedBasis_bilin_two_three,
      S.orthogonalizedProjectedAdaptedBasis_bilin_three_two,
      S.orthogonalizedProjectedAdaptedBasis_bilin_three_three,
      S.coe_orthogonalizedSecondGramZeroUnit]
    rw [Units.val_div_eq_div_val,
      S.coe_orthogonalizedSecondGramUnit,
      S.coe_orthogonalizedSecondGramZeroUnit]
    field_simp [S.orthogonalizedSecondGram_zero_zero_ne_zero f hgap]
    rw [S.orthogonalizedSecondGramDet_formula]
    ring
  rw [hmodel]
  fin_cases i <;> fin_cases j
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h00
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h01
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h02
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h03
  · rw [S.targetFirstNormalized.isSymm.eq]
    simpa [firstBoundaryDiagonalizingBasis_apply, b] using h01
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h11
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h12
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h13
  · rw [S.targetFirstNormalized.isSymm.eq]
    simpa [firstBoundaryDiagonalizingBasis_apply, b] using h02
  · rw [S.targetFirstNormalized.isSymm.eq]
    simpa [firstBoundaryDiagonalizingBasis_apply, b] using h12
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h22
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h23
  · rw [S.targetFirstNormalized.isSymm.eq]
    simpa [firstBoundaryDiagonalizingBasis_apply, b] using h03
  · rw [S.targetFirstNormalized.isSymm.eq]
    simpa [firstBoundaryDiagonalizingBasis_apply, b] using h13
  · rw [S.targetFirstNormalized.isSymm.eq]
    simpa [firstBoundaryDiagonalizingBasis_apply, b] using h23
  · simpa [firstBoundaryDiagonalizingBasis_apply, b] using h33

/-- The explicit four-entry diagonal model obtained above is isometric to
the normalized target head. -/
noncomputable def firstBoundaryDiagonalModelIsometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (S.firstBoundaryDiagonalUnits f hgap))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (S.firstBoundaryDiagonalUnits f hgap)))
      S.targetFirstNormalized := by
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  exact (Classical.choice
    (Lattice.basisLattice_isIsometric_of_gram_eq
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (S.firstBoundaryDiagonalUnits f hgap))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (S.firstBoundaryDiagonalUnits f hgap)))
      S.targetFirstNormalized (Pi.basisFun K (Fin 4))
      (S.firstBoundaryDiagonalizingBasis f hgap)
      (S.firstBoundaryDiagonalizingBasis_gram f hgap)))
    |>.toQuadraticSpaceIsometry

/-- In the strict norm-order branch, the normalized target head with the
fixed left fundamental line represents the normalized source head.  This
is the field-theoretic content of O'Meara 93:28(iii), Step 1. -/
theorem normalizedStrictConditionIIIWith_of_ltNormOrder
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    (S.targetFirstNormalized.orthogonalSum
        (QuadraticSpace.scaledLine
          (S.firstNormalizedNormGeneratorWith A))).Represents
      S.sourceFirstNormalized := by
  let a := S.firstNormalizedNormGeneratorWith A
  let d := S.firstBoundaryDiagonalUnits f hgap
  let pair : Fin 2 → Kˣ := ![(1 : Kˣ), -1]
  let pairs : Fin 4 → Kˣ := ![(1 : Kˣ), -1, 1, -1]
  change (S.targetFirstNormalized.orthogonalSum
      (QuadraticSpace.scaledLine a)).Represents S.sourceFirstNormalized
  have ha : IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice a :=
    S.firstNormalizedNormGeneratorWith_target A
  have haord : ordUnit K a = ordUnit K S.firstNormGenerator :=
    S.firstNormalizedNormGeneratorWith_order_eq A
  have htriggerCanonical : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0) := by
    rw [← fourNormOverWeightIdealWith_canonical]
    unfold fourNormOverWeightIdealWith at htrigger ⊢
    rw [(canonicalFundamentalNormGeneratorChoice
      S.sourceJordan).value_order_eq_fundamentalNormGenerator]
    rw [A.value_order_eq_fundamentalNormGenerator] at htrigger
    exact htrigger
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients pairs)
      (diagonalUnitCoefficients (Fin.snoc d a)) := by
    have h := diagonalQuinary_represents_twoHyperbolicPairs_of_hilbert
      (d 0) (S.projectedAdaptedFirstGramUnit f)
      (d 2) (S.orthogonalizedSecondGramUnit f) a
      (by
        simpa [d] using
          (S.projectedDiscriminant_normRatio_hilbert_eq_one_for
            f hgap htriggerCanonical a ha haord))
      (by
        simpa [d] using
          (S.secondDiscriminant_normRatio_hilbert_eq_one_for
            f hgap htriggerCanonical a ha haord))
      (S.binaryDiscriminants_hilbert_eq_one f hgap htriggerCanonical)
    convert h using 1 <;> funext i <;> fin_cases i <;> rfl
  have hdiagSpace :
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (Fin.snoc d a))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (Fin.snoc d a))).Represents
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients pairs)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero pairs)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      pairs (Fin.snoc d a)).mpr hdiag
  have hpairSquare : IsSquare (-(pair 0 / pair 1)) := by
    refine ⟨1, ?_⟩
    simp [pair]
  rcases
      QuadraticSpace.finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
        (pair 0) (pair 1) hpairSquare with
    ⟨pairToHyperbolicRaw⟩
  have hpairCoefficients : diagonalUnitCoefficients pair =
      ![(pair 0 : K), (pair 1 : K)] := by
    funext i
    fin_cases i <;> rfl
  let pairToHyperbolic : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal (diagonalUnitCoefficients pair)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero pair))
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
    simpa only [hpairCoefficients] using pairToHyperbolicRaw
  have hpairsCoefficients : diagonalUnitCoefficients pairs =
      diagonalUnitCoefficients (Fin.append pair pair) := by
    funext i
    fin_cases i <;> rfl
  let pairsToHyperbolic : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal (diagonalUnitCoefficients pairs)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero pairs))
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (QuadraticSpace.hyperbolicPlane (1 : Kˣ))) := by
    have h := (QuadraticSpace.finiteDiagonalOrthogonalSumIsometry
      pair pair).symm.trans
        (pairToHyperbolic.orthogonalSum pairToHyperbolic)
    simpa only [hpairsCoefficients] using h
  let hyperbolicToZero :=
    (scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry
  let pairToTower :=
    (hyperbolicToZero.orthogonalSum hyperbolicToZero).trans
      (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))
  let sourceToPairs : QuadraticSpace.Isometry S.sourceFirstNormalized
      (QuadraticSpace.finiteDiagonal (diagonalUnitCoefficients pairs)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero pairs)) :=
    S.sourceFirstNormalizedHyperbolicTowerIsometry.trans
      (pairToTower.symm.trans pairsToHyperbolic.symm)
  let line : Fin 1 → Kˣ := fun _ ↦ a
  let diagonalTargetToNormalized : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (Fin.snoc d a))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (Fin.snoc d a)))
      (S.targetFirstNormalized.orthogonalSum
        (QuadraticSpace.scaledLine a)) := by
    have h := (QuadraticSpace.finiteDiagonalOrthogonalSumIsometry
      d line).symm.trans
        ((S.firstBoundaryDiagonalModelIsometry f hgap).orthogonalSum
          (QuadraticSpace.scaledLineDiagonalizationIsometry a).symm)
    simpa only [line, Fin.append_right_eq_snoc] using h
  rcases hdiagSpace with ⟨diagRep⟩
  exact ⟨diagonalTargetToNormalized.toRepresentation.trans
    (diagRep.trans sourceToPairs.toRepresentation)⟩

/-- O'Meara 93:28(iii) at the first boundary in the strict norm-order
branch, restored from normalized heads to the actual Jordan prefixes and
the fixed fundamental norm generator. -/
theorem firstBoundary_strictConditionIIIWith_of_ltNormOrder
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator)
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    S.sourceJordan.fundamentalIdeal 0 <
        S.sourceJordan.fourNormOverWeightIdealWith A
          (boundaryLeftIndex 0) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (QuadraticSpace.scaledLine
          (A.value (boundaryLeftIndex 0))) := by
  intro htrigger
  let a := S.firstNormalizedNormGeneratorWith A
  have hindex : boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) := by
    apply Fin.ext
    simp [boundaryLeftIndex]
  change
    ((S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
        |>.orthogonalSum
          (QuadraticSpace.scaledLine
            (A.value 0))).Represents
      (S.sourceJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1).space
  rcases S.normalizedStrictConditionIIIWith_of_ltNormOrder
      f hgap A htrigger with
    ⟨normalized⟩
  let scaled := normalized.rescaleUnitBoth S.firstScale
  have hscale : S.firstScale * S.firstScale⁻¹ = (1 : Kˣ) := by simp
  let sourceCollapse := rescaleUnitMulLatticeIsometry
    (S.sourceJordan.component 0).space
    (S.sourceJordan.component 0).lattice S.firstScale⁻¹ S.firstScale
  let sourceFinish : Lattice.Isometry
      ((S.sourceJordan.component 0).space.rescaleUnit
        (S.firstScale * S.firstScale⁻¹))
      (S.sourceJordan.component 0).space
      (S.sourceJordan.component 0).lattice
      (S.sourceJordan.component 0).lattice := by
    simpa only [hscale] using Lattice.Isometry.rescaleUnitOne
      (S.sourceJordan.component 0).space
      (S.sourceJordan.component 0).lattice
  let sourceUndo : QuadraticSpace.Isometry
      (S.sourceFirstNormalized.rescaleUnit S.firstScale)
      (S.sourceJordan.component 0).space := by
    simpa only [sourceFirstNormalized] using
      (sourceCollapse.trans sourceFinish).toQuadraticSpaceIsometry
  let sourcePrefixIso :=
    S.sourceJordan.toOrthogonalDecomposition
      |>.firstComponentPrefixLatticeIsometry.toQuadraticSpaceIsometry
  let sourceToPrefix := sourceUndo.trans sourcePrefixIso
  let targetCollapse := rescaleUnitMulLatticeIsometry
    (S.targetJordan.component 0).space
    (S.targetJordan.component 0).lattice S.firstScale⁻¹ S.firstScale
  let targetFinish : Lattice.Isometry
      ((S.targetJordan.component 0).space.rescaleUnit
        (S.firstScale * S.firstScale⁻¹))
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
      (S.targetJordan.component 0).lattice := by
    simpa only [hscale] using Lattice.Isometry.rescaleUnitOne
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
  let targetUndo : QuadraticSpace.Isometry
      (S.targetFirstNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 0).space := by
    simpa only [targetFirstNormalized] using
      (targetCollapse.trans targetFinish).toQuadraticSpaceIsometry
  let targetPrefixIso :=
    S.targetJordan.toOrthogonalDecomposition
      |>.firstComponentPrefixLatticeIsometry.toQuadraticSpaceIsometry
  let targetToPrefix := targetUndo.trans targetPrefixIso
  have haRaw : S.firstScale * a =
      A.value 0 := by
    simp [a, firstNormalizedNormGeneratorWith]
  let lineUndo : QuadraticSpace.Isometry
      ((QuadraticSpace.scaledLine a).rescaleUnit S.firstScale)
      (QuadraticSpace.scaledLine
        (A.value 0)) := by
    simpa only [haRaw] using
      QuadraticSpace.scaledLineRescaleUnitIsometry S.firstScale a
  let distribute := QuadraticSpace.rescaleUnitOrthogonalSumIsometry
    S.targetFirstNormalized (QuadraticSpace.scaledLine a) S.firstScale
  let targetToRaw := distribute.trans
    (targetToPrefix.orthogonalSum lineUndo)
  exact ⟨targetToRaw.toRepresentation.trans
    (scaled.trans sourceToPrefix.symm.toRepresentation)⟩

/-- Canonical-generator specialization of the strict first-boundary
representation theorem. -/
theorem firstBoundary_strictConditionIII_of_ltNormOrder
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.sourceJordan.fundamentalIdeal 0 <
        S.sourceJordan.fourNormOverWeightIdeal (boundaryLeftIndex 0) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (QuadraticSpace.scaledLine
          (S.sourceJordan.fundamentalNormGenerator
            (boundaryLeftIndex 0))) := by
  intro htrigger
  have h := S.firstBoundary_strictConditionIIIWith_of_ltNormOrder f hgap
    (canonicalFundamentalNormGeneratorChoice S.sourceJordan)
  apply h
  simpa only [fourNormOverWeightIdealWith_canonical] using htrigger

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
