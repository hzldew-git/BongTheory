/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022SectionFive

/-!
# He--Hu 2022, Lemma 5.7

This file formalizes the exceptional odd-rank obstruction in Lemma 5.7.
For `n = 3`, the test lattice is the published
`N_2^3(delta*pi)`.  Its BONG has orders `[0,-2e,1]`.  When the first four
source coefficients have square product and the fifth source order is
strictly larger than one, the revised central trigger at paper index `4`
holds, but the required ternary prefix is not represented.
-/

namespace Bong

open Dyadic AlternatingEndpointTower

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The paper parameter `delta*pi` in the exceptional ternary test. -/
noncomputable def heHuLemma57Parameter (delta : Kˣ) : Kˣ :=
  delta * uniformizerPowerUnit K 1

@[simp]
theorem heHuLemma57Parameter_order (delta : Kˣ)
    (hdelta : IsValuationUnit K (delta : K)) :
    ordUnit K (heHuLemma57Parameter delta) = 1 := by
  rw [heHuLemma57Parameter, ordUnit_mul, ordUnit_uniformizerPowerUnit,
    (isValuationUnit_iff_ordUnit_eq_zero K delta).mp hdelta]
  norm_num

/-- Coordinate squares identifying the literal BONG of
`N_2^3(delta*pi)` with the second Table 1 space `W_2^3(delta*pi)`. -/
noncomputable def heHuLemma57TargetFactors : Fin 3 → Kˣ :=
  ![1, uniformizerPowerUnit K (-(ramificationIndex K : Int)), 1]

/-- The literal values of the exceptional test BONG differ from the
Table 1 row `[1,-Delta,Delta*delta*pi]` by the displayed squares. -/
theorem heHuLemma57TargetValues_eq_oddSecond_mul_square
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) (i : Fin 3) :
    (heHuLemma311OddSecondUnitUniformizerTail delta hdelta).valueUnit i =
      heHuOddSecondTailOdd (heHuLemma57Parameter delta) i *
        heHuLemma57TargetFactors (K := K) i ^ 2 := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · change
      (heHuDiscriminantEndpointGoodBONG (K := K) 0
        |>.orthogonalProductRight_of_orderBounds
          (BONG.unaryModelGoodBONG
            (heHuLemma311OddSecondUnitUniformizerValue delta))
          (heHuLemma311OddSecondUnitUniformizer_orderBound delta hdelta)
          (heHuLemma311OddSecondUnitUniformizer_lastSecondBound delta hdelta)).valueUnit
            (BONG.orthogonalProductLeftIndex 1 (0 : Fin 2)) = _
    rw [valueUnit_orthogonalProductRight_of_orderBounds_left,
      heHuDiscriminantEndpointGoodBONG_valueUnit]
    simp [heHuDiscriminantEndpointValues, heHuOddSecondTailOdd,
      heHuLemma57TargetFactors, uniformizerPowerUnit]
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · change
      (heHuDiscriminantEndpointGoodBONG (K := K) 0
        |>.orthogonalProductRight_of_orderBounds
          (BONG.unaryModelGoodBONG
            (heHuLemma311OddSecondUnitUniformizerValue delta))
          (heHuLemma311OddSecondUnitUniformizer_orderBound delta hdelta)
          (heHuLemma311OddSecondUnitUniformizer_lastSecondBound delta hdelta)).valueUnit
            (BONG.orthogonalProductLeftIndex 1 (1 : Fin 2)) = _
      rw [valueUnit_orthogonalProductRight_of_orderBounds_left,
        heHuDiscriminantEndpointGoodBONG_valueUnit]
      simp only [Fin.isValue, heHuDiscriminantEndpointValues_one, zero_sub,
        Fin.succ_zero_eq_one, heHuOddSecondTailOdd_one, neg_mul, neg_inj,
        mul_right_inj]
      change uniformizerPowerUnit K (-(2 * (ramificationIndex K : Int))) =
        uniformizerPowerUnit K (-(ramificationIndex K : Int)) ^ 2
      unfold uniformizerPowerUnit
      rw [pow_two, ← zpow_add]
      congr 1
      ring
    · refine Fin.cases ?_ (fun k ↦ Fin.elim0 k) j
      change
        (heHuDiscriminantEndpointGoodBONG (K := K) 0
          |>.orthogonalProductRight_of_orderBounds
            (BONG.unaryModelGoodBONG
              (heHuLemma311OddSecondUnitUniformizerValue delta))
            (heHuLemma311OddSecondUnitUniformizer_orderBound delta hdelta)
            (heHuLemma311OddSecondUnitUniformizer_lastSecondBound delta hdelta)).valueUnit
              (BONG.orthogonalProductRightIndex 2 (0 : Fin 1)) = _
      rw [valueUnit_orthogonalProductRight_of_orderBounds_right]
      change (BONG.unaryModelBONG
        (heHuLemma311OddSecondUnitUniformizerValue delta)).valueUnit 0 = _
      rw [BONG.unaryModelBONG_valueUnit]
      simp [heHuLemma311OddSecondUnitUniformizerValue,
        heHuOddSecondTailOdd, heHuLemma57TargetFactors,
        heHuLemma57Parameter, mul_assoc]

/-- Equal-rank isometry between the exceptional test BONG and the second
odd-dimensional Table 1 space. -/
theorem heHuLemma57Target_represents_oddSecond
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma311OddSecondUnitUniformizerTail delta hdelta).valueUnit)
      (diagonalUnitCoefficients
        (heHuOddSecond 0 (heHuLemma57Parameter delta))) := by
  have hodd : Odd (ordUnit K (heHuLemma57Parameter delta)) := by
    rw [heHuLemma57Parameter_order delta hdelta]
    exact odd_one
  have hnotEven : ¬ Even (ordUnit K (heHuLemma57Parameter delta)) :=
    Int.not_even_iff_odd.mpr hodd
  rw [heHuOddSecond_of_not_even 0 _ hnotEven]
  have hpoint := heHuLemma57TargetValues_eq_oddSecond_mul_square
    (K := K) delta hdelta
  have hrep :=
    Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
      (heHuLemma311OddSecondUnitUniformizerTail delta hdelta).valueUnit
      (heHuOddSecondTailOdd (heHuLemma57Parameter delta))
      (heHuLemma57TargetFactors (K := K)) hpoint
  convert hrep using 1
  funext i
  fin_cases i <;> rfl

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- A split quaternary space represents the first ternary space
`W_1^3(c)=H orthogonalSum <c>` for every nonzero `c`. -/
theorem heHuLemma57_oddFirst_represents_split (c : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst (K := K) 0 c))
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) 2)) := by
  have hline : DiagonalRepresents
      (fun _ : Fin 1 ↦ (c : K))
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))) := by
    apply (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
      (K := K) (1 : Kˣ) (-1) c).2
    simp
  have hhead : DiagonalRepresents
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))) :=
    diagonalRepresents_refl _
  have happend := DiagonalRepresents.appendBoth hhead hline
  convert happend using 1 <;> funext i <;> fin_cases i <;> rfl

/-- A four-entry endpoint prefix with square product is the split
quaternary space. -/
theorem heHuLemma57_split_represents_sourcePrefix
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m : Nat} (a : GoodBONG q L (m + 2))
    (hm : 2 ≤ m)
    (hfirst : a.order 0 = 0)
    (hlast : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hdet : IsSquare (a.prefixProduct 4)) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) 2))
      (a.prefixValues 4 (by omega)) := by
  let source : Fin 4 → Kˣ := a.prefixValueUnits 4 (by omega)
  let split : Fin 4 → Kˣ :=
    standardHyperbolicEndpointTower (K := K) 2
  have hlast' : a.order ⟨2 * 2 - 1, by omega⟩ =
      0 - 2 * (ramificationIndex K : Int) := by
    convert hlast using 1
    all_goals norm_num
  have hsourceClasses :
      AlternatingEndpointPairClasses (pairs := 2) source := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    simpa only [source] using
      a.lemma79_endpointTower_pairClasses 0 2 (by omega) (by omega)
        hfirst hlast'
  have hsourceOrders :
      AlternatingEndpointLeadingOrdersAt (pairs := 2) source (1 : Kˣ) := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    intro t
    have h := a.lemma79_endpointTower_leadingOrders 0 2 (by omega)
      (by omega) hfirst hlast' t
    rw [hone]
    simpa only [source] using h
  have hsplitClasses :
      AlternatingEndpointPairClasses (pairs := 2) split := by
    simpa only [split] using
      standardHyperbolicEndpointTower_pairClasses (K := K) 2
  have hsplitOrders :
      AlternatingEndpointLeadingOrdersAt (pairs := 2) split (1 : Kˣ) := by
    simpa only [split] using
      standardHyperbolicEndpointTower_leadingOrders (K := K) 2
  have hdet' : IsSquare
      (diagonalUnitDeterminant source * diagonalUnitDeterminant split) := by
    rw [show diagonalUnitDeterminant source = a.prefixProduct 4 by
      simpa only [source] using
        a.diagonalUnitDeterminant_prefixValueUnits 4 (by omega)]
    rw [show diagonalUnitDeterminant split = 1 by
      simpa [split] using
        diagonalUnitDeterminant_standardHyperbolicEndpointTower
          (K := K) 2]
    simpa only [mul_one] using hdet
  have hrep :=
    alternatingEndpointTower_equalDeterminantRepresentation (pairs := 2)
      source split (1 : Kˣ) hsourceClasses hsplitClasses hsourceOrders
        hsplitOrders hdet'
  simpa only [source, split, diagonalUnitCoefficients_prefixValueUnits]
    using hrep

/-- Paper index `i=4` in the exceptional rank-three central test. -/
def heHuLemma57CentralIndex {m : Nat} (hm : 4 ≤ m) :
    CentralRepresentationIndex (m + 2) 3 where
  val := 4
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- The first capped defect in the exceptional central trigger is at least
`2e`.  This is the domination step from the two alternating binary
prefixes in the published proof. -/
theorem heHuLemma57_centralPreviousDefect_ge
    {m : Nat} (a : GoodBONG q L (m + 2)) (hm : 4 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.centralPreviousDefect
        (heHuLemma311OddSecondUnitUniformizerTail delta hdelta)
        (heHuLemma57CentralIndex hm) := by
  let b := heHuLemma311OddSecondUnitUniformizerTail delta hdelta
  let sourceLast : Fin (m + 2) := ⟨3, by omega⟩
  have hsourceLastOdd : Odd sourceLast.val := ⟨1, by simp [sourceLast]⟩
  have hsource : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a (1 : Kˣ) 0 4 := by
    have h := (a.heHu2022Proposition27iiiiv hAIntegral sourceLast
      hsourceLastOdd (by simpa only [sourceLast] using hR4))
        |>.alternatingPrefixDefect
    simpa [sourceLast] using h
  have hsourceReverse : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a (1 : Kˣ) 4 0 := by
    rw [a.truncatedPrefixDefect_comm a 1 4 0]
    exact hsource
  have hbIntegral : Lattice.IsIntegral _ _ :=
    heHuIntegral_of_firstOrder_nonneg b (by
      change 0 ≤ b.order 0
      rw [show b.order 0 = 0 by simp [b]])
  let targetLast : Fin 3 := ⟨1, by omega⟩
  have htargetLastOdd : Odd targetLast.val := ⟨0, by simp [targetLast]⟩
  have htargetLast : b.order targetLast =
      -(2 * (ramificationIndex K : Int)) := by
    simp [b, targetLast]
  have htarget : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b (-1 : Kˣ) 0 2 := by
    have h := (b.heHu2022Proposition27iiiiv hbIntegral targetLast
      htargetLastOdd htargetLast) |>.alternatingPrefixDefect
    simpa [targetLast] using h
  have htargetCross : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1 : Kˣ) 0 2 := by
    simpa only [truncatedPrefixDefect, a.prefixAlphaCap_zero,
      b.prefixAlphaCap_zero, GoodBONG.prefixProduct,
      BONG.prefixProduct_zero, mul_one] using htarget
  have hdomination :
      min (a.truncatedPrefixDefect a (1 : Kˣ) 4 0)
          (a.truncatedPrefixDefect b (-1 : Kˣ) 0 2) ≤
        a.truncatedPrefixDefect b (-1 : Kˣ) 4 2 := by
    simpa only [one_mul] using
      a.truncatedPrefixDefect_domination a b (1 : Kˣ) (-1 : Kˣ)
        4 0 2
  have hcombined : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1 : Kˣ) 4 2 :=
    (le_min hsourceReverse htargetCross).trans hdomination
  simpa only [centralPreviousDefect, heHuLemma57CentralIndex, b] using
    hcombined

/-- The hypotheses of Lemma 5.7 activate the revised condition-(iii')
test at paper index `4`. -/
theorem heHuLemma57_defectTrigger
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (hm : 4 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    a.centralDefectTrigger
      (heHuLemma311OddSecondUnitUniformizerTail delta hdelta)
      (heHuLemma57CentralIndex hm) := by
  let b := heHuLemma311OddSecondUnitUniformizerTail delta hdelta
  let i := heHuLemma57CentralIndex hm
  let sourceFive : Fin (m + 2) := ⟨4, by omega⟩
  unfold centralDefectTrigger
  constructor
  · change b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ < a.order ⟨i.val, i.lt_large⟩
    have htargetIndex : (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin 3) = 2 := by
      apply Fin.ext
      simp [i, heHuLemma57CentralIndex]
    have hsourceIndex :
        (⟨i.val, i.lt_large⟩ : Fin (m + 2)) = sourceFive := by
      apply Fin.ext
      simp [i, sourceFive, heHuLemma57CentralIndex]
    rw [htargetIndex, hsourceIndex]
    have htarget : b.order (2 : Fin 3) = 1 := by
      simp [b]
    rw [htarget]
    simpa only [sourceFive] using hR5
  · have hprevious : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        a.centralPreviousDefect b i := by
      simpa only [b, i] using
        a.heHuLemma57_centralPreviousDefect_ge hm hAIntegral hR4 delta hdelta
    have hcurrent : (0 : WithTop ℚ) ≤ a.centralCurrentDefect b i := by
      unfold centralCurrentDefect
      exact a.truncatedPrefixDefect_nonneg
        (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
        b (-1) (i.val + 1) (i.val - 1)
    have hsum : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
      exact hprevious.trans
        (by simpa only [add_zero] using
          add_le_add_right hcurrent (a.centralPreviousDefect b i))
    change
      ((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : ℚ) -
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) <
          a.centralPreviousDefect b i + a.centralCurrentDefect b i
    have htargetIndex : (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin 3) = 2 := by
      apply Fin.ext
      simp [i, heHuLemma57CentralIndex]
    have hsourceIndex :
        (⟨i.val, i.lt_large⟩ : Fin (m + 2)) = sourceFive := by
      apply Fin.ext
      simp [i, sourceFive, heHuLemma57CentralIndex]
    rw [htargetIndex, hsourceIndex]
    have htarget : b.order (2 : Fin 3) = 1 := by
      simp [b]
    rw [htarget]
    have hR5' : 1 < a.order sourceFive := by
      simpa only [sourceFive] using hR5
    have hthreshold :
        ((2 * (ramificationIndex K : ℚ) + ((1 : Int) : ℚ) -
          (a.order sourceFive : ℚ) : ℚ) : WithTop ℚ) <
            ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
      apply WithTop.coe_lt_coe.mpr
      have hR5Q : (1 : ℚ) <
          (a.order sourceFive : ℚ) := by
        exact_mod_cast hR5'
      norm_num
      linarith
    exact hthreshold.trans_le hsum

/-- The ternary target `N_2^3(delta*pi)` is not represented by the first
four source coefficients when that source prefix has square product. -/
theorem heHuLemma57_not_represents
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (hm : 4 ≤ m)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤)
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    ¬ DiagonalRepresents
      ((heHuLemma311OddSecondUnitUniformizerTail delta hdelta).prefixValues
        3 le_rfl)
      (a.prefixValues 4 (by omega)) := by
  let b := heHuLemma311OddSecondUnitUniformizerTail delta hdelta
  let c := heHuLemma57Parameter delta
  have hfirst : a.order 0 = 0 := by
    exact hI1.oddOrder (0 : Fin 3) odd_one
  have hdet : IsSquare (a.prefixProduct 4) := by
    apply isSquare_of_two_mul_e_lt_defectOrder (K := K)
    rw [hprefix]
    exact (show
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) < ⊤ from
        WithTop.coe_lt_top (((2 * ramificationIndex K : Nat) : ℚ)))
  have hsplit : DiagonalRepresents
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) 2))
      (a.prefixValues 4 (by omega)) :=
    heHuLemma57_split_represents_sourcePrefix sourceLaws a (by omega)
      hfirst hR4 hdet
  have hfirstRep : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst (K := K) 0 c))
      (a.prefixValues 4 (by omega)) :=
    (heHuLemma57_oddFirst_represents_split (K := K) c).trans hsplit
  let source : Fin 4 → Kˣ := a.prefixValueUnits 4 (by omega)
  have hfirstRepUnits : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst (K := K) 0 c))
      (diagonalUnitCoefficients source) := by
    simpa only [source, diagonalUnitCoefficients_prefixValueUnits] using
      hfirstRep
  have hexact := heHu2022Lemma313CodimensionOne
    (heHuOddFirst (K := K) 0 c) (heHuOddSecond (K := K) 0 c)
    (heHu2022Definition34Proposition35Odd (K := K) 0 c) source
  have hnotSecond : ¬ DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddSecond (K := K) 0 c))
      (diagonalUnitCoefficients source) := by
    rcases hexact with hleft | hright
    · exact hleft.2
    · exact (hright.1 hfirstRepUnits).elim
  intro hrep
  have hbFull : b.prefixValueUnits 3 le_rfl = b.valueUnit := by
    funext j
    rfl
  have hrepUnits : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (diagonalUnitCoefficients (b.prefixValueUnits 3 le_rfl))
      (diagonalUnitCoefficients source) at hrep
    rwa [hbFull] at hrep
  have hsecondB : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddSecond (K := K) 0 c))
      (diagonalUnitCoefficients b.valueUnit) := by
    exact (heHuLemma57Target_represents_oddSecond
      (K := K) delta hdelta).symm_of_sameRank
  exact hnotSecond (hsecondB.trans hrepUnits)

/-- He--Hu, Lemma 5.7: the revised central condition fails for the
published test lattice `N_2^3(delta*pi)`. -/
theorem heHu2022Lemma57
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (hm : 4 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤)
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    a.centralDefectTrigger
        (heHuLemma311OddSecondUnitUniformizerTail delta hdelta)
        (heHuLemma57CentralIndex hm) ∧
      ¬ DiagonalRepresents
        ((heHuLemma311OddSecondUnitUniformizerTail delta hdelta).prefixValues
          3 le_rfl)
        (a.prefixValues 4 (by omega)) := by
  exact ⟨a.heHuLemma57_defectTrigger hm hAIntegral hR4 hR5 delta hdelta,
    a.heHuLemma57_not_represents hm hI1 hR4 hprefix delta hdelta⟩

/-- Direct logical form: condition `(iii')` cannot hold for the test
lattice isolated by Lemma 5.7. -/
theorem heHu2022Lemma57_not_centralRepresentationConditionsPrime
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m : Nat} (a : GoodBONG q L (m + 2)) (hm : 4 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤)
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    ¬ a.CentralRepresentationConditionsPrime
      (heHuLemma311OddSecondUnitUniformizerTail delta hdelta) := by
  intro hprime
  have h := a.heHu2022Lemma57 hm hAIntegral hI1 hR4 hR5 hprefix
    delta hdelta
  exact h.2 (hprime (heHuLemma57CentralIndex hm) h.1)

end BONG.GoodBONG

end Bong
