/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCPublishedProfiles

/-!
# He (2025), Lemma 4.11(iii): the nonexceptional square classes

The finite defect, its parity, and the unit property of the sharp partner
are derived from the published parameter domain. The final criteria use
Definition 4.1's `W/N` families, not an assumed model identification.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The defect of a nonexceptional unit is a finite nonnegative odd
integer below `2e`. The integer is the actual quadratic-defect index. -/
theorem heADCUnitSharpDefectData (c : Kˣ) (hc : IsValuationUnit K (c : K))
    (hs : HeHuSharpDomain c) :
    let d : Int := (quadraticDefect K c).toNat
    Odd d ∧ 0 ≤ d ∧ d < 2 * (ramificationIndex K : Int) ∧
      defectOrder (K := K) c = ((d : ℚ) : WithTop ℚ) := by
  let d : Int := (quadraticDefect K c).toNat
  let D := heHuSharpData c hs
  have hsource : D.sourceDefect = (d : ℚ) := by simp only [D, d, heHuSharpData, Int.cast_natCast]
  have hdefect : defectOrder (K := K) c = ((d : ℚ) : WithTop ℚ) := by
    rw [← hsource]
    exact D.source_defectOrder
  have hdlt : (d : ℚ) < 2 * (ramificationIndex K : ℚ) := by
    rw [← hsource]
    exact D.sourceDefect_lt_twoE
  have heven : Even (ordUnit K c) := by
    rw [(isValuationUnit_iff_ordUnit_eq_zero K c).1 hc]
    exact ⟨0, by omega⟩
  obtain ⟨z, hz, hdz⟩ := isOddRationalInteger_of_even_ordUnit_of_defectOrder_eq
    c (d : ℚ) heven hdefect hdlt
  have hdzInt : d = z := by exact_mod_cast hdz
  have hodd : Odd d := by rw [hdzInt]; exact hz
  have hnonneg : 0 ≤ d := Int.natCast_nonneg _
  have hlt : d < 2 * (ramificationIndex K : Int) := by exact_mod_cast hdlt
  exact ⟨hodd, hnonneg, hlt, hdefect⟩

/-- Remove the coordinate square `π^(1-d)` from the generic unit tail. -/
theorem heADCUnitDefectTail_represents_twist (a c : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K)) (hc : IsValuationUnit K (c : K))
    (hdOdd : Odd d) (hdNonneg : 0 ≤ d) (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c = ((d : ℚ) : WithTop ℚ)) :
    DiagonalRepresents (diagonalUnitCoefficients
      (heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt hcDefect).valueUnit)
      (diagonalUnitCoefficients (heHuBinaryTwist c a)) := by
  obtain ⟨z, hz⟩ := hdOdd
  have hpower : uniformizerPowerUnit K (1 - d) = uniformizerPowerUnit K (-z) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  apply Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square _ _
    (![1, uniformizerPowerUnit K (-z)] : Fin 2 → Kˣ)
  intro i
  rw [heHuLemma45_unitDefectTailGoodBONG_valueUnit]
  fin_cases i <;> simp [heHuUnitDefectTailValues, heHuBinaryTwist, hpower, mul_assoc]

/-- The second-column space for a nonexceptional square class is a
standard hyperbolic tower followed by its chosen binary sharp twist. -/
theorem heADCEvenSecond_eq_sharpTower (k : Nat) (c : Kˣ) (hc : HeHuSharpDomain c) :
    heADCW2Even k c (Or.inr hc.notSquare) =
      Fin.append (AlternatingEndpointTower.standardHyperbolicEndpointTower (K := K) k)
        (heHuBinarySecond c hc) := by
  cases k with
  | zero =>
      rw [heADCW2Even, heHuEvenSecond_zero_of_sharp c _ hc.notSquare hc.notDiscriminantSquare]
      funext i
      fin_cases i <;> rfl
  | succ k =>
      rw [heADCW2Even,
        heHuEvenSecond_succ_of_sharp k c _ hc.notSquare hc.notDiscriminantSquare]
      simpa only [heHuEvenSharpTail] using
        heHuFinFamilyCast_tower_hyperbolic_tail (K := K) k (heHuBinarySecond c hc)

/-- The binary sharp identification lifts to the entire published `W_2`. -/
theorem heADCBinaryTower_represents_evenSecond (b : GoodBONG r M 2)
    (hM : Lattice.IsIntegral r M) (k : Nat) (c : Kˣ) (hc : HeHuSharpDomain c)
    (htail : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuBinarySecond c hc))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHu2022Lemma310BONG b hM k).valueUnit)
      (diagonalUnitCoefficients (heADCW2Even k c (Or.inr hc.notSquare))) := by
  rw [heADCEvenSecond_eq_sharpTower k c hc]
  exact heADCTower_represents b hM k _ htail

/-- Lemma 4.11(iii), nonexceptional unit first column. All finite-defect
and parity facts are derived, not extra hypotheses of the public criterion. -/
theorem heADC2025Lemma411iiiUnitFirstPublished (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) (hs : HeHuSharpDomain c)
    (k : Nat) (a : GoodBONG q L (2 + 2 * k)) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even k c))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even k c))
        L (heADCN1Even k c).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![0, 1 - ((quadraticDefect K c).toNat : Int)] i := by
  let d : Int := (quadraticDefect K c).toNat
  obtain ⟨hdOdd, hdNonneg, hdLt, hdefect⟩ := heADCUnitSharpDefectData c hc hs
  have hone : IsValuationUnit K ((1 : Kˣ) : K) := by simp [IsValuationUnit]
  let b := heHuUnitDefectTailGoodBONG 1 c d hone hc hdOdd hdNonneg hdLt hdefect
  have hM := heHu2022Proposition37EvenGeneric 1 c d hone hc hdOdd hdNonneg hdLt hdefect 0
  have htail := heADCUnitDefectTail_represents_twist 1 c d hone hc hdOdd hdNonneg hdLt hdefect
  have hfirst : heHuBinaryTwist c 1 = heHuBinaryFirst c := by
    simp [heHuBinaryTwist, heHuBinaryFirst]
  rw [hfirst] at htail
  exact isIsometric_publishedModel_iff_orderProfile b hM _
    (heHuUnitDefectTailGoodBONG_order 1 c d hone hc hdOdd hdNonneg hdLt hdefect)
    k _ (by omega) (heADCBinaryTower_represents_evenFirst b hM.isIntegral k c htail) a hL ambient

/-- Lemma 4.11(iii), nonexceptional unit second column. The sharp unit and
all its required arithmetic properties are supplied by proved results. -/
theorem heADC2025Lemma411iiiUnitSecondPublished (c : Kˣ)
    (hc : IsValuationUnit K (c : K)) (hs : HeHuSharpDomain c)
    (k : Nat) (a : GoodBONG q L (2 + 2 * k)) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Even k c (Or.inr hs.notSquare)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Even k c (Or.inr hs.notSquare)))
        L (heADCN2Even k c (Or.inr hs.notSquare)).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![0, 1 - ((quadraticDefect K c).toNat : Int)] i := by
  let d : Int := (quadraticDefect K c).toNat
  obtain ⟨hdOdd, hdNonneg, hdLt, hdefect⟩ := heADCUnitSharpDefectData c hc hs
  let eta := heHuSharp c hs
  have heta : IsValuationUnit K (eta : K) := (heHu2022Proposition32 c hs).1
  let b := heHuUnitDefectTailGoodBONG eta c d heta hc hdOdd hdNonneg hdLt hdefect
  have hM := heHu2022Proposition37EvenGeneric eta c d heta hc hdOdd hdNonneg hdLt hdefect 0
  have htail := heADCUnitDefectTail_represents_twist eta c d heta hc hdOdd hdNonneg hdLt hdefect
  exact isIsometric_publishedModel_iff_orderProfile b hM _
    (heHuUnitDefectTailGoodBONG_order eta c d heta hc hdOdd hdNonneg hdLt hdefect)
    k _ (by omega) (heADCBinaryTower_represents_evenSecond b hM.isIntegral k c hs htail)
    a hL ambient

/-- A unit times one uniformizer is automatically outside the two
exceptional square classes, since its quadratic defect is zero. -/
theorem heADCUnitUniformizerSharpDomain (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) :
    HeHuSharpDomain (δ * uniformizerPowerUnit K 1) := by
  have hodd : Odd (ordUnit K (δ * uniformizerPowerUnit K 1)) := by
    rw [ordUnit_mul, (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
      ordUnit_uniformizerPowerUnit]
    exact odd_one
  have hdefect : defectOrder (K := K) (δ * uniformizerPowerUnit K 1) = 0 := by
    unfold defectOrder
    rw [quadraticDefect_eq_zero_of_odd_ordUnit _ hodd]
    rfl
  apply heHuLemma45_sharpDomain_of_defect_lt_twoE _ 0 hdefect
  have he := ramificationIndex_pos (K := K)
  omega

/-- Lemma 4.11(iii), unit-uniformizer first column on the named `W_1/N_1`. -/
theorem heADC2025Lemma411iiiUniformizerFirstPublished
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat)
    (a : GoodBONG q L (2 + 2 * k)) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW1Even k (δ * uniformizerPowerUnit K 1)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW1Even k (δ * uniformizerPowerUnit K 1)))
        L (heADCN1Even k (δ * uniformizerPowerUnit K 1)).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k ![0, 1] i := by
  have hone : IsValuationUnit K ((1 : Kˣ) : K) := by simp [IsValuationUnit]
  let b := heHuUnitUniformizerPairGoodBONG 1 δ hone hδ
  have hM := heHu2022Proposition37EvenUnitUniformizer 1 δ hone hδ 0
  have hvalues : b.valueUnit = heHuBinaryFirst (δ * uniformizerPowerUnit K 1) := by
    funext i
    rw [heHuUnitUniformizerPairGoodBONG_valueUnit]
    fin_cases i <;> simp [heHuUnitUniformizerPairValues, heHuBinaryFirst]
  have htail : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuBinaryFirst (δ * uniformizerPowerUnit K 1))) := by
    rw [hvalues]
    exact diagonalRepresents_refl _
  exact isIsometric_publishedModel_iff_orderProfile b hM _
    (heHuUnitUniformizerPairGoodBONG_orders 1 δ hone hδ) k _ (by omega)
    (heADCBinaryTower_represents_evenFirst b hM.isIntegral k _ htail) a hL ambient

/-- Lemma 4.11(iii), unit-uniformizer second column. Choosing the proved
sharp unit gives the very same space as Definition 4.1; uniqueness then
identifies its maximal lattice with the published `N_2`. -/
theorem heADC2025Lemma411iiiUniformizerSecondPublished
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat)
    (a : GoodBONG q L (2 + 2 * k)) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW2Even k (δ * uniformizerPowerUnit K 1)
        (Or.inr (heADCUnitUniformizerSharpDomain δ hδ).notSquare)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Even k (δ * uniformizerPowerUnit K 1)
          (Or.inr (heADCUnitUniformizerSharpDomain δ hδ).notSquare)))
        L (heADCN2Even k (δ * uniformizerPowerUnit K 1)
          (Or.inr (heADCUnitUniformizerSharpDomain δ hδ).notSquare)).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k ![0, 1] i := by
  let c := δ * uniformizerPowerUnit K 1
  let hs := heADCUnitUniformizerSharpDomain δ hδ
  let eta := heHuSharp c hs
  have heta : IsValuationUnit K (eta : K) := (heHu2022Proposition32 c hs).1
  let b := heHuUnitUniformizerPairGoodBONG eta δ heta hδ
  have hM := heHu2022Proposition37EvenUnitUniformizer eta δ heta hδ 0
  have hvalues : b.valueUnit = heHuBinarySecond c hs := by
    funext i
    rw [heHuUnitUniformizerPairGoodBONG_valueUnit]
    fin_cases i <;> simp [heHuUnitUniformizerPairValues, heHuBinarySecond,
      heHuBinaryTwist, c, eta, mul_assoc]
  have htail : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuBinarySecond c hs)) := by
    rw [hvalues]
    exact diagonalRepresents_refl _
  exact isIsometric_publishedModel_iff_orderProfile b hM _
    (heHuUnitUniformizerPairGoodBONG_orders eta δ heta hδ) k _ (by omega)
    (heADCBinaryTower_represents_evenSecond b hM.isIntegral k c hs htail) a hL ambient

end BONG.GoodBONG

end Bong
