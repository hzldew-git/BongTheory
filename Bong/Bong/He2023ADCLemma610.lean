/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma69
import Bong.Bong.He2023ADCEvenCentralPrefix
import Bong.Bong.He2023ADCCorankOneAmbient
import Bong.Bong.Beli2009ClassificationProof

/-!
# He (2025), Lemma 6.10

The exceptional order profile in the ambient space `W_1^4(Delta)` determines
the lattice constructed in Lemma 6.12.  The proof below verifies the four
conditions of Beli's good-BONG classification theorem, as in the published
proof.
-/

namespace Bong

open Dyadic Module

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The exceptional order sequence forces the alpha sequence `(0,2e,1)`. -/
theorem heADCLemma610_alphaProfile (a : GoodBONG q L 4)
    (ha : HeADCExceptionalQuaternaryOrders a) (i : Fin 3) :
    a.alphaValue i =
      (![0, 2 * (ramificationIndex K : ℚ), 1] : Fin 3 → ℚ) i := by
  fin_cases i
  · apply (a.heADC2025Proposition34 0).alphaZero.mpr
    unfold orderGap
    change a.order 1 - a.order 0 = _
    rw [ha 0, ha 1]
    norm_num
  · simpa using a.heADCExceptional_middleAlpha ha
  · apply (a.heADC2025Proposition34 2).alphaOne.mpr
    left
    left
    unfold orderGap
    change a.order 3 - a.order 2 = _
    rw [ha 2, ha 3]
    simp

/-- The first two displayed coefficients of the constructed exceptional
lattice are an explicit square rescaling of the standard hyperbolic pair. -/
theorem heADCExceptionalQuaternaryCandidate_firstTwo_represents_hyperbolic :
    DiagonalRepresents
      ((heADCExceptionalQuaternaryCandidate (K := K)).prefixValues 2 (by omega))
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))) := by
  let c := heADCExceptionalQuaternaryCandidate (K := K)
  let s : Fin 2 → Kˣ :=
    ![1, uniformizerPowerUnit K (-(ramificationIndex K : Int))]
  have hvalues := heHu2022Lemma310HyperbolicValues
    (heADCExceptionalTail (K := K))
    (heADCExceptionalTail_integral (K := K)) 1 0
  change c.valueUnit 0 = 1 ∧ c.valueUnit 1 =
    -(uniformizerPowerUnit K (-(2 * (ramificationIndex K : Int)))) at hvalues
  have hpower : uniformizerPowerUnit K (-(2 * (ramificationIndex K : Int))) =
      uniformizerPowerUnit K (-(ramificationIndex K : Int)) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    ring
  have hrep :=
    Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
      (c.prefixValueUnits 2 (by omega)) (heHuHyperbolicPair (K := K)) s (by
        intro i
        fin_cases i
        · change c.valueUnit 0 = _
          simpa [s, heHuHyperbolicPair] using hvalues.1
        · change c.valueUnit 1 = _
          simpa [s, heHuHyperbolicPair, hpower] using hvalues.2)
  simpa only [c.diagonalUnitCoefficients_prefixValueUnits] using hrep

/-- The standard hyperbolic pair is the first two coordinates of
`W_1^3(epsilon)`. -/
theorem heADCLemma610_hyperbolic_represents_oddFirst (ε : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
      (diagonalUnitCoefficients (heADCW1Odd 0 ε)) := by
  simpa [heADCW1Even, heHuEvenFirst, heHuBinaryFirst,
    heHuHyperbolicPair] using
      heADCEvenFirstOne_represents_oddFirst (K := K) 0 ε

/-- Condition (iii) of Beli's classification theorem for Lemma 6.10. -/
theorem heADCLemma610_prefixDefectBounds (a : GoodBONG q L 4)
    (ha : HeADCExceptionalQuaternaryOrders a) :
    a.PrefixDefectBounds (heADCExceptionalQuaternaryCandidate (K := K)) := by
  let c := heADCExceptionalQuaternaryCandidate (K := K)
  intro i
  fin_cases i
  · change (a.alphaValue 0 : WithTop ℚ) ≤ comparisonPrefixDefect a c 1
    rw [a.heADCLemma610_alphaProfile ha 0]
    unfold comparisonPrefixDefect
    exact defectOrder_nonneg _
  · change (a.alphaValue 1 : WithTop ℚ) ≤ comparisonPrefixDefect a c 2
    rw [a.heADCLemma610_alphaProfile ha 1]
    have haGap : a.orderGap 0 = -(2 * (ramificationIndex K : Int)) := by
      unfold orderGap
      change a.order 1 - a.order 0 = _
      rw [ha 0, ha 1]
      norm_num
    have hcGap : c.orderGap 0 = -(2 * (ramificationIndex K : Int)) := by
      unfold orderGap
      change c.order 1 - c.order 0 = _
      rw [heADCExceptionalQuaternaryCandidate_orders,
        heADCExceptionalQuaternaryCandidate_orders]
      norm_num
    have haDefect := (a.heADC2025Corollary32ii 0 haGap).rawDefectLower
    have hcDefect := (c.heADC2025Corollary32ii 0 hcGap).rawDefectLower
    have hdom := comparisonPrefixDefect_add_two a c 0 (by omega)
    have hzero : comparisonPrefixDefect a c 0 = ⊤ :=
      comparisonPrefixDefect_zero a c
    calc
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
          min (comparisonPrefixDefect a c 0)
            (min (a.adjacentDefect 0) (c.adjacentDefect 0)) := by
        rw [hzero]
        exact le_min le_top (le_min haDefect hcDefect)
      _ ≤ comparisonPrefixDefect a c 2 := hdom
  · change (a.alphaValue 2 : WithTop ℚ) ≤ comparisonPrefixDefect a c 3
    rw [a.heADCLemma610_alphaProfile ha 2]
    have haEven : Even (ordUnit K (a.prefixProduct 3)) := by
      rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega)]
      simp only [BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_zero,
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 4),
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 4),
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 4)]
      change Even (0 + a.order 0 + a.order 1 + a.order 2)
      rw [ha 0, ha 1, ha 2]
      simp
    have hcEven : Even (ordUnit K (c.prefixProduct 3)) := by
      rw [c.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega)]
      simp only [BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_zero,
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 4),
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 4),
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 4)]
      change Even (0 + c.order 0 + c.order 1 + c.order 2)
      rw [heADCExceptionalQuaternaryCandidate_orders,
        heADCExceptionalQuaternaryCandidate_orders,
        heADCExceptionalQuaternaryCandidate_orders]
      simp
    unfold comparisonPrefixDefect comparisonPrefixUnit
    exact defectOrder_one_le_of_even _ (by
      rw [ordUnit_mul]
      exact haEven.add hcEven)

/-- Condition (iv) of Beli's classification theorem for Lemma 6.10. -/
theorem heADCLemma610_internalRepresentations (a : GoodBONG q L 4)
    (hIntegral : Lattice.IsIntegral q L)
    (ha : HeADCExceptionalQuaternaryOrders a) :
    a.InternalRepresentationConditions
      (heADCExceptionalQuaternaryCandidate (K := K)) := by
  let c := heADCExceptionalQuaternaryCandidate (K := K)
  intro i hi htrigger
  fin_cases i
  · norm_num at hi
  · change 2 * (ramificationIndex K : ℚ) <
      a.alphaValue 0 + a.alphaValue 1 at htrigger
    rw [a.heADCLemma610_alphaProfile ha 0,
      a.heADCLemma610_alphaProfile ha 1] at htrigger
    norm_num at htrigger
  · change DiagonalRepresents (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega))
    have hhead : ∀ i : Fin 2, a.order ⟨i.val, by omega⟩ =
        if Even i.val then 0 else -(2 * (ramificationIndex K : Int)) := by
      intro j
      fin_cases j
      · simpa using ha 0
      · have hodd : ¬ Even 1 := by decide
        simpa [hodd] using ha 1
    have hcase : Even (a.order (2 : Fin 4)) := by
      rw [ha 2]
      simp
    have hHtoA := a.heADCEvenCentral_prefix_represents_first 0 hIntegral hhead
      (1 : Kˣ) (Or.inl rfl) (Or.inl hcase)
    have hHtoA' : DiagonalRepresents
        (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
        (a.prefixValues 3 (by omega)) := by
      simpa [heHuEvenFirst, heHuBinaryFirst, heHuHyperbolicPair] using hHtoA
    exact (heADCExceptionalQuaternaryCandidate_firstTwo_represents_hyperbolic
      (K := K)).trans hHtoA'

/-- He (2025), Lemma 6.10.  The conclusion identifies the lattice with the
constructed exceptional model, not merely with another lattice having the
same order sequence. -/
theorem heADC2025Lemma610 (a : GoodBONG q L 4)
    (ha : HeADCExceptionalQuaternaryOrders a)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even 1
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))) :
    Lattice.IsIsometric q (heADCExceptionalQuaternaryForm (K := K)) L
      (heADCExceptionalQuaternaryLattice (K := K)) := by
  let c := heADCExceptionalQuaternaryCandidate (K := K)
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hfirst : 0 ≤ a.order 0 := by
    rw [ha 0]
    norm_num
  have hIntegral : Lattice.IsIntegral q L :=
    (a.toBONG.beliUniversalLemma22).2 hfirst
  have hcAmbient : (heADCExceptionalQuaternaryForm (K := K)).IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW1Even 1 δ)) :=
    c.ambientIsometric_of_diagonalRepresents (heADCW1Even 1 δ) rfl
      (heADCExceptionalQuaternaryCandidate_represents_first (K := K))
  have hacAmbient : q.IsIsometric (heADCExceptionalQuaternaryForm (K := K)) :=
    ⟨(Classical.choice ambient).trans (Classical.choice hcAmbient).symm⟩
  apply (a.beli2009Theorem31_concrete hacAmbient c).mpr
  refine
    { sameOrders := ?_
      sameAlphas := ?_
      prefixDefectBounds := a.heADCLemma610_prefixDefectBounds ha
      internalRepresentations := a.heADCLemma610_internalRepresentations hIntegral ha }
  · intro i
    rw [ha i, heADCExceptionalQuaternaryCandidate_orders]
  · intro i
    rw [a.heADCLemma610_alphaProfile ha i,
      c.heADCLemma610_alphaProfile
        (heADCExceptionalQuaternaryCandidate_hasOrders (K := K)) i]

end BONG.GoodBONG

end Bong
