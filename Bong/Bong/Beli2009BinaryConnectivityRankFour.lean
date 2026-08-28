/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009BinaryConnectivityCore

namespace Bong

open Dyadic
open BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

/-- Sharp dynamic form of the quaternary braid `0 -> 1 -> 2 -> 1 -> 0`.
The conclusion is exactly the coefficient scaling used in Beli (2019),
Lemma 9.2.  Every hypothesis is a concrete depth or Hilbert condition for
one of the five literal binary edges. -/
theorem reachable_rankFour_fiveStep_scaling_of_dynamic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (mu theta eta epsilon : valuationUnitSubgroup K)
    (hmuAlpha : a.adjacentBinaryAlpha (0 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hmuHilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (mu : Kˣ) = 1)
    (hthetaAlpha : rankFourSecondBinaryAlphaAfterFirstMultiplier
        a (mu : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaHilbert : hilbertSymbol K
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3)) (theta : Kˣ) = 1)
    (hetaAlpha : rankFourThirdBinaryAlphaAfterSecondMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hetaHilbert : hilbertSymbol K
      ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) (eta : Kˣ) = 1)
    (hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
        a (mu : Kˣ) (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)))
    (hkappaHilbert : hilbertSymbol K
      (((mu : Kˣ) * (eta : Kˣ)) * a.adjacentProduct (1 : Fin 3))
      (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) = 1)
    (hnuAlpha : rankFourFirstBinaryAlphaAfterRightMultiplier
        a (epsilon : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) ((mu : Kˣ)⁻¹))
    (hnuHilbert : hilbertSymbol K
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3))
      ((mu : Kˣ)⁻¹) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i)
      ![a.valueUnit 0,
        (epsilon : Kˣ) * a.valueUnit 1,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 2,
        (eta : Kˣ) * a.valueUnit 3] := by
  have hmuGroup : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 4) / a.valueUnit (0 : Fin 4)) := by
    exact valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 3) mu hmuAlpha hmuHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 3)
      mu hmuGroup with ⟨c, hcValues⟩
  have hmuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => a.valueUnit i) (fun i => c.valueUnit i) :=
    ⟨0, mu, hmuGroup, hcValues⟩
  have hcSecondAdjacent : c.adjacentProduct (1 : Fin 3) =
      (mu : Kˣ) * a.adjacentProduct (1 : Fin 3) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (1 : Fin 3).castSucc,
      congrFun hcValues (1 : Fin 3).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
    exact mul_comm _ _
  have hcSecondAlpha : c.adjacentBinaryAlpha (1 : Fin 3) =
      rankFourSecondBinaryAlphaAfterFirstMultiplier a (mu : Kˣ) := by
    have horders := a.order_invariant c
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourSecondBinaryAlphaAfterFirstMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (1 : Fin 3).succ).symm,
      (horders (1 : Fin 3).castSucc).symm, hcSecondAdjacent]
  have hthetaGroup : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (c.valueUnit (2 : Fin 4) / c.valueUnit (1 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (1 : Fin 3) theta
    · rw [hcSecondAlpha]
      exact hthetaAlpha
    · rw [hcSecondAdjacent]
      exact hthetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (1 : Fin 3)
      theta hthetaGroup with ⟨d, hdValues⟩
  have hthetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => c.valueUnit i) (fun i => d.valueUnit i) :=
    ⟨1, theta, hthetaGroup, hdValues⟩
  have hdThirdAdjacent : d.adjacentProduct (2 : Fin 3) =
      (theta : Kˣ) * a.adjacentProduct (2 : Fin 3) := by
    have hdTwo : d.valueUnit (2 : Fin 4) =
        (theta : Kˣ) * c.valueUnit (2 : Fin 4) := by
      rw [congrFun hdValues (2 : Fin 4)]
      rfl
    have hdThree : d.valueUnit (3 : Fin 4) =
        c.valueUnit (3 : Fin 4) := by
      rw [congrFun hdValues (3 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    have hcTwo : c.valueUnit (2 : Fin 4) = a.valueUnit (2 : Fin 4) := by
      rw [congrFun hcValues (2 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    have hcThree : c.valueUnit (3 : Fin 4) = a.valueUnit (3 : Fin 4) := by
      rw [congrFun hcValues (3 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    unfold BONG.GoodBONG.adjacentProduct
    change -(d.valueUnit (2 : Fin 4) * d.valueUnit (3 : Fin 4)) = _
    rw [hdTwo, hdThree, hcTwo, hcThree]
    apply Units.ext
    simp
    ring
  have hdThirdAlpha : d.adjacentBinaryAlpha (2 : Fin 3) =
      rankFourThirdBinaryAlphaAfterSecondMultiplier a (theta : Kˣ) := by
    have horders := a.order_invariant d
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourThirdBinaryAlphaAfterSecondMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (2 : Fin 3).succ).symm,
      (horders (2 : Fin 3).castSucc).symm, hdThirdAdjacent]
  have hetaGroup : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (d.valueUnit (3 : Fin 4) / d.valueUnit (2 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (2 : Fin 3) eta
    · rw [hdThirdAlpha]
      exact hetaAlpha
    · rw [hdThirdAdjacent]
      exact hetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact d (2 : Fin 3)
      eta hetaGroup with ⟨e, heValues⟩
  have hetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => d.valueUnit i) (fun i => e.valueUnit i) :=
    ⟨2, eta, hetaGroup, heValues⟩
  have heSecondAdjacent : e.adjacentProduct (1 : Fin 3) =
      (((mu : Kˣ) * (eta : Kˣ)) * a.adjacentProduct (1 : Fin 3)) *
        (theta : Kˣ) ^ 2 := by
    have heOne : e.valueUnit (1 : Fin 4) = d.valueUnit (1 : Fin 4) := by
      rw [congrFun heValues (1 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    have heTwo : e.valueUnit (2 : Fin 4) =
        (eta : Kˣ) * d.valueUnit (2 : Fin 4) := by
      rw [congrFun heValues (2 : Fin 4)]
      rfl
    have hdOne : d.valueUnit (1 : Fin 4) =
        (theta : Kˣ) * c.valueUnit (1 : Fin 4) := by
      rw [congrFun hdValues (1 : Fin 4)]
      rfl
    have hdTwo : d.valueUnit (2 : Fin 4) =
        (theta : Kˣ) * c.valueUnit (2 : Fin 4) := by
      rw [congrFun hdValues (2 : Fin 4)]
      rfl
    have hcOne : c.valueUnit (1 : Fin 4) =
        (mu : Kˣ) * a.valueUnit (1 : Fin 4) := by
      rw [congrFun hcValues (1 : Fin 4)]
      rfl
    have hcTwo : c.valueUnit (2 : Fin 4) = a.valueUnit (2 : Fin 4) := by
      rw [congrFun hcValues (2 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    unfold BONG.GoodBONG.adjacentProduct
    change -(e.valueUnit (1 : Fin 4) * e.valueUnit (2 : Fin 4)) = _
    rw [heOne, heTwo, hdOne, hdTwo, hcOne, hcTwo]
    apply Units.ext
    simp [pow_two]
    ring
  have heSecondAlpha : e.adjacentBinaryAlpha (1 : Fin 3) =
      rankFourSecondBinaryAlphaAfterOuterMultipliers
        a (mu : Kˣ) (eta : Kˣ) := by
    have horders := a.order_invariant e
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourSecondBinaryAlphaAfterOuterMultipliers
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (1 : Fin 3).succ).symm,
      (horders (1 : Fin 3).castSucc).symm, heSecondAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  let kappa : valuationUnitSubgroup K := epsilon / theta
  have hkappaGroup : valuationUnitClassHom K kappa ∈
      beliNormGeneratorGroup K
        (e.valueUnit (2 : Fin 4) / e.valueUnit (1 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      e (1 : Fin 3) kappa
    · rw [heSecondAlpha]
      simpa only [kappa] using hkappaAlpha
    · rw [heSecondAdjacent, hilbertSymbol_mul_square_left]
      simpa only [kappa] using hkappaHilbert
  rcases exists_goodBONG_binaryTransformation_exact e (1 : Fin 3)
      kappa hkappaGroup with ⟨f, hfValues⟩
  have hkappaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => e.valueUnit i) (fun i => f.valueUnit i) :=
    ⟨1, kappa, hkappaGroup, hfValues⟩
  have hfFirstAdjacent : f.adjacentProduct (0 : Fin 3) =
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3)) *
        (mu : Kˣ) ^ 2 := by
    have hfZero : f.valueUnit (0 : Fin 4) = e.valueUnit (0 : Fin 4) := by
      rw [congrFun hfValues (0 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    have hfOne : f.valueUnit (1 : Fin 4) =
        (kappa : Kˣ) * e.valueUnit (1 : Fin 4) := by
      rw [congrFun hfValues (1 : Fin 4)]
      rfl
    have heZero : e.valueUnit (0 : Fin 4) = d.valueUnit (0 : Fin 4) := by
      rw [congrFun heValues (0 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    have heOne : e.valueUnit (1 : Fin 4) = d.valueUnit (1 : Fin 4) := by
      rw [congrFun heValues (1 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    have hdZero : d.valueUnit (0 : Fin 4) = c.valueUnit (0 : Fin 4) := by
      rw [congrFun hdValues (0 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    have hdOne : d.valueUnit (1 : Fin 4) =
        (theta : Kˣ) * c.valueUnit (1 : Fin 4) := by
      rw [congrFun hdValues (1 : Fin 4)]
      rfl
    have hcZero : c.valueUnit (0 : Fin 4) =
        (mu : Kˣ) * a.valueUnit (0 : Fin 4) := by
      rw [congrFun hcValues (0 : Fin 4)]
      rfl
    have hcOne : c.valueUnit (1 : Fin 4) =
        (mu : Kˣ) * a.valueUnit (1 : Fin 4) := by
      rw [congrFun hcValues (1 : Fin 4)]
      rfl
    unfold BONG.GoodBONG.adjacentProduct
    change -(f.valueUnit (0 : Fin 4) * f.valueUnit (1 : Fin 4)) = _
    rw [hfZero, hfOne, heZero, heOne, hdZero, hdOne, hcZero, hcOne]
    dsimp only [kappa]
    apply Units.ext
    simp [div_eq_mul_inv, pow_two]
    ring
  have hfFirstAlpha : f.adjacentBinaryAlpha (0 : Fin 3) =
      rankFourFirstBinaryAlphaAfterRightMultiplier a (epsilon : Kˣ) := by
    have horders := a.order_invariant f
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (0 : Fin 3).succ).symm,
      (horders (0 : Fin 3).castSucc).symm, hfFirstAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  let nu : valuationUnitSubgroup K := mu⁻¹
  have hnuGroup : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (f.valueUnit (1 : Fin 4) / f.valueUnit (0 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      f (0 : Fin 3) nu
    · rw [hfFirstAlpha]
      simpa only [nu, Subgroup.coe_inv] using hnuAlpha
    · rw [hfFirstAdjacent, hilbertSymbol_mul_square_left]
      simpa only [nu, Subgroup.coe_inv] using hnuHilbert
  rcases exists_goodBONG_binaryTransformation_exact f (0 : Fin 3)
      nu hnuGroup with ⟨g, hgValues⟩
  have hnuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => f.valueUnit i) (fun i => g.valueUnit i) :=
    ⟨0, nu, hnuGroup, hgValues⟩
  have hgValuesRaw : (fun i => g.valueUnit i) =
      rankFourBraidFive (fun i => a.valueUnit i)
        (mu : Kˣ) (theta : Kˣ) (eta : Kˣ) (kappa : Kˣ) (nu : Kˣ) := by
    rw [hgValues, hfValues, heValues, hdValues, hcValues]
    rfl
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => g.valueUnit i) :=
    hmuStep.reachable.trans <| hthetaStep.reachable.trans <|
      hetaStep.reachable.trans <| hkappaStep.reachable.trans hnuStep.reachable
  rw [hgValuesRaw] at hreach
  have hreach' : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i)
      (rankFourBraidFive (fun i => a.valueUnit i)
        (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ))
        ((mu : Kˣ)⁻¹)) := by
    simpa only [kappa, nu, Subgroup.coe_inv] using hreach
  rw [binaryTransform_fiveStep_zero_one_two_one_zero
    (K := K) (fun i => a.valueUnit i) mu theta eta epsilon] at hreach'
  exact hreach'

/-- The last Hilbert condition in the three-step braid follows from the first
two edge conditions and the Hilbert identity in Beli's Lemma 8.2. -/
theorem hilbertSymbol_threeStep_closure
    [HilbertSymbolLaws K]
    (A₁ A₂ epsilon theta eta : Kˣ)
    (htheta : hilbertSymbol K A₁ theta = 1)
    (heta : hilbertSymbol K (theta * A₂) eta = 1)
    (hchoice : hilbertSymbol K (epsilon * A₂) eta =
      hilbertSymbol K epsilon A₁) :
    hilbertSymbol K (eta * A₁) (epsilon / theta) = 1 := by
  have hthetaInv : hilbertSymbol K (eta * A₁) theta⁻¹ =
      hilbertSymbol K (eta * A₁) theta := by
    have hmap := map_inv (hilbertCharacter K (eta * A₁)) theta
    change hilbertSymbol K (eta * A₁) theta⁻¹ =
      (hilbertSymbol K (eta * A₁) theta)⁻¹ at hmap
    rw [hmap]
    rcases Int.units_eq_one_or (hilbertSymbol K (eta * A₁) theta) with h | h <;>
      rw [h] <;> norm_num
  rw [div_eq_mul_inv, hilbertSymbol_mul_right, hthetaInv,
    hilbertSymbol_mul_left, hilbertSymbol_mul_left,
    hilbertSymbol_comm K eta epsilon,
    hilbertSymbol_comm K A₁ epsilon,
    hilbertSymbol_comm K eta theta, htheta]
  rw [hilbertSymbol_mul_left] at heta hchoice
  rcases Int.units_eq_one_or (hilbertSymbol K theta eta) with hthetaEta | hthetaEta <;>
    rcases Int.units_eq_one_or (hilbertSymbol K A₂ eta) with hA₂Eta | hA₂Eta <;>
    rcases Int.units_eq_one_or (hilbertSymbol K epsilon eta) with hepsilonEta | hepsilonEta <;>
    rcases Int.units_eq_one_or (hilbertSymbol K epsilon A₁) with hepsilonA₁ | hepsilonA₁ <;>
    simp [hthetaEta, hA₂Eta, hepsilonEta, hepsilonA₁] at heta hchoice ⊢

/-- The quaternary braid with trivial outer multipliers.  The five formal
edges reduce to the three genuinely nontrivial moves `1 -> 2 -> 1`; the two
outer identity edges are discharged by the infinite defect of `1`. -/
theorem reachable_rankFour_threeStep_scaling_of_dynamic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (theta eta epsilon : valuationUnitSubgroup K)
    (hthetaAlpha : rankFourSecondBinaryAlphaAfterFirstMultiplier
        a (1 : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaHilbert : hilbertSymbol K
      (a.adjacentProduct (1 : Fin 3)) (theta : Kˣ) = 1)
    (hetaAlpha : rankFourThirdBinaryAlphaAfterSecondMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hetaHilbert : hilbertSymbol K
      ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) (eta : Kˣ) = 1)
    (hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
        a (1 : Kˣ) (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)))
    (hkappaHilbert : hilbertSymbol K
      ((eta : Kˣ) * a.adjacentProduct (1 : Fin 3))
      (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i)
      ![a.valueUnit 0,
        (epsilon : Kˣ) * a.valueUnit 1,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 2,
        (eta : Kˣ) * a.valueUnit 3] := by
  apply reachable_rankFour_fiveStep_scaling_of_dynamic
      a (1 : valuationUnitSubgroup K) theta eta epsilon
  · simpa only [Subgroup.coe_one, BONG.GoodBONG.defectOrder_one] using
      (show a.adjacentBinaryAlpha (0 : Fin 3) ≤ (⊤ : WithTop ℚ) from le_top)
  · simp
  · simpa only [Subgroup.coe_one] using hthetaAlpha
  · simpa only [Subgroup.coe_one, one_mul] using hthetaHilbert
  · exact hetaAlpha
  · exact hetaHilbert
  · simpa only [Subgroup.coe_one] using hkappaAlpha
  · simpa only [Subgroup.coe_one, one_mul] using hkappaHilbert
  · simpa only [Subgroup.coe_one, inv_one,
        BONG.GoodBONG.defectOrder_one] using
      (show rankFourFirstBinaryAlphaAfterRightMultiplier a (epsilon : Kˣ) ≤
          (⊤ : WithTop ℚ) from le_top)
  · simp

/-- A directly usable three-step version: Beli's Lemma 8.2 Hilbert identity
replaces the otherwise separate legality condition for the final edge. -/
theorem reachable_rankFour_threeStep_scaling_of_choice
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (theta eta epsilon : valuationUnitSubgroup K)
    (hthetaAlpha : rankFourSecondBinaryAlphaAfterFirstMultiplier
        a (1 : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaHilbert : hilbertSymbol K
      (a.adjacentProduct (1 : Fin 3)) (theta : Kˣ) = 1)
    (hetaAlpha : rankFourThirdBinaryAlphaAfterSecondMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hetaHilbert : hilbertSymbol K
      ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) (eta : Kˣ) = 1)
    (hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
        a (1 : Kˣ) (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)))
    (hchoice : hilbertSymbol K
        ((epsilon : Kˣ) * a.adjacentProduct (2 : Fin 3)) (eta : Kˣ) =
      hilbertSymbol K (epsilon : Kˣ)
        (a.adjacentProduct (1 : Fin 3))) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i)
      ![a.valueUnit 0,
        (epsilon : Kˣ) * a.valueUnit 1,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 2,
        (eta : Kˣ) * a.valueUnit 3] := by
  apply reachable_rankFour_threeStep_scaling_of_dynamic
      a theta eta epsilon hthetaAlpha hthetaHilbert hetaAlpha hetaHilbert
      hkappaAlpha
  exact hilbertSymbol_threeStep_closure
    (a.adjacentProduct (1 : Fin 3))
    (a.adjacentProduct (2 : Fin 3))
    (epsilon : Kˣ) (theta : Kˣ) (eta : Kˣ)
    hthetaHilbert hetaHilbert hchoice

/-! ## Specialization to the first rank-four branch of Lemma 9.2 -/

/-- Equality of the right endpoints in the `FirstData` certificate gives the
recursion at the middle boundary. -/
theorem lemma92RankFourFirstData_secondAlpha_recursion
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.alphaValue (1 : Fin 3) =
      (a.orderGap (1 : Fin 3) : ℚ) +
        a.alphaValue (0 : Fin 3) := by
  have h := D.commonRightEndpoint (1 : Fin 3)
  unfold BONG.GoodBONG.alphaRightEndpoint at h
  unfold BONG.GoodBONG.orderGap
  push_cast at h ⊢
  linarith

/-- In the `FirstData` branch the literal first binary alpha is the global
first alpha.  This is the exact normalization needed by the outer two moves
of the five-step braid. -/
theorem lemma92RankFourFirstData_firstBinaryAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.adjacentBinaryAlpha (0 : Fin 3) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
  have hleft : a.leftDefectCandidate (0 : Fin 3) (0 : Fin 3) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    simpa [BONG.GoodBONG.leftDefectCandidate,
      BONG.GoodBONG.orderGap] using D.firstAlpha_candidate
  unfold BONG.GoodBONG.adjacentBinaryAlpha
  rw [hleft]
  apply min_eq_right
  rw [← a.coe_halfGapValue]
  exact_mod_cast a.alphaValue_le_halfGapValue (0 : Fin 3)

/-- The branch called `R₁ < R₃` in the paper really has strict outer
orders.  The strictness is already encoded in `FirstData`: after writing the
finite first adjacent defect as a rational, the first-candidate equality and
the common-right-endpoint recursion cancel that defect. -/
theorem lemma92RankFourFirstData_firstOrder_lt_thirdOrder
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.order (0 : Fin 4) < a.order (2 : Fin 4) := by
  have hfinite : a.adjacentDefect (0 : Fin 3) ≠ ⊤ :=
    ne_top_of_lt D.firstAdjacent_lt_secondAlpha
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hcandidate := D.firstAlpha_candidate
  have hstrict := D.firstAdjacent_lt_secondAlpha
  have hrecursion := lemma92RankFourFirstData_secondAlpha_recursion a D
  rw [← hd] at hcandidate hstrict
  norm_cast at hcandidate hstrict
  unfold BONG.GoodBONG.orderGap at hcandidate hrecursion
  push_cast at hcandidate hrecursion
  by_contra hnot
  have hle : a.order (2 : Fin 4) ≤ a.order (0 : Fin 4) :=
    le_of_not_gt hnot
  have hleQ : (a.order (2 : Fin 4) : ℚ) ≤
      (a.order (0 : Fin 4) : ℚ) := by
    exact_mod_cast hle
  linarith

/-- Consequently the canonical initial ternary segment has property A. -/
theorem lemma92RankFourFirstData_initialThree_hasPropertyA
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.lemma814InitialThree.toBONG.HasPropertyA := by
  intro i hi
  have hiZero : i = (0 : Fin 3) := by
    apply Fin.ext
    omega
  subst i
  change a.lemma814InitialThree.order (0 : Fin 3) <
    a.lemma814InitialThree.order (2 : Fin 3)
  rw [a.lemma814InitialThree_order_eq,
    a.lemma814InitialThree_order_eq]
  exact lemma92RankFourFirstData_firstOrder_lt_thirdOrder a D

/-- The first alpha of the canonical initial ternary segment is the ambient
first alpha. -/
theorem lemma92RankFourFirstData_initialThree_firstAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.lemma814InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin 3) := by
  apply a.lemma814InitialThree_firstAlpha_eq
  simpa only [a.adjacentBinaryAlpha_zero] using
    lemma92RankFourFirstData_firstBinaryAlpha_eq a D

/-- The second alpha of the initial ternary segment is also the ambient
second alpha.  For the reverse inequality, the local left candidate starting
at the first adjacent pair is exactly
`(R₃-R₂)+alpha₁ = alpha₂`; this avoids any extra literal-binary
normalization hypothesis. -/
theorem lemma92RankFourFirstData_initialThree_secondAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.lemma814InitialThree.alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin 3) := by
  let p := BONG.GoodBONG.prefixPairLocalization (N := 2) (1 : Fin 3)
  let w : BONG.SegmentWitness a.toBONG p.start p.length p.bound :=
    a.lemma814InitialThreeSegment
  have hpivot : p.pivotFin = (1 : Fin 3) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have hlowerRaw := a.beli2009Lemma21_le_segmentAlpha p w
  change a.alpha (1 : Fin 3) ≤
    a.lemma814InitialThree.alpha (1 : Fin 2) at hlowerRaw
  have hlower : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      (a.lemma814InitialThree.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    rw [a.coe_alphaValue, a.lemma814InitialThree.coe_alphaValue]
    exact hlowerRaw
  have hlocalUpper := a.lemma814InitialThree.alpha_le_leftDefectCandidate
    (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide)
  rw [← a.lemma814InitialThree.coe_alphaValue] at hlocalUpper
  have hcandidate : a.lemma814InitialThree.leftDefectCandidate
      (1 : Fin 2) (0 : Fin 2) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    unfold BONG.GoodBONG.leftDefectCandidate
    change
      (((((a.lemma814InitialThree.order (2 : Fin 3) -
        a.lemma814InitialThree.order (0 : Fin 3) : Int) : ℚ)) :
          WithTop ℚ)) +
        a.lemma814InitialThree.adjacentDefect (0 : Fin 2) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ)
    rw [a.lemma814InitialThree_order_eq,
      a.lemma814InitialThree_order_eq,
      a.lemma814InitialThree_adjacentDefect_eq]
    change
      (((((a.order (2 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ)) :
          WithTop ℚ)) + a.adjacentDefect (0 : Fin 3) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ)
    have hsplit :
        (((((a.order (2 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ)) :
            WithTop ℚ)) =
          (((((a.order (2 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ)) :
              WithTop ℚ)) +
            (((((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ)) :
              WithTop ℚ)) := by
      norm_cast
      push_cast
      ring
    have hfirst := D.firstAlpha_candidate
    unfold BONG.GoodBONG.orderGap at hfirst
    change
      (((((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ)) :
          WithTop ℚ)) + a.adjacentDefect (0 : Fin 3) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) at hfirst
    have hrecursion := lemma92RankFourFirstData_secondAlpha_recursion a D
    unfold BONG.GoodBONG.orderGap at hrecursion
    change a.alphaValue (1 : Fin 3) =
      ((a.order (2 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
        a.alphaValue (0 : Fin 3) at hrecursion
    rw [hsplit, add_assoc, hfirst, ← WithTop.coe_add]
    exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hrecursion.symm
  rw [hcandidate] at hlocalUpper
  have heqTop :
      (a.lemma814InitialThree.alphaValue (1 : Fin 2) : WithTop ℚ) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) :=
    le_antisymm hlocalUpper hlower
  exact WithTop.coe_injective heqTop

/-- The Hilbert condition for the fourth edge of the full braid is forced by
the first two edge conditions, Beli's Lemma 8.2 identity, and the condition
that the outer auxiliary multiplier pairs trivially with `epsilon`. -/
theorem hilbertSymbol_fiveStep_middle_closure
    [HilbertSymbolLaws K]
    (A₁ A₂ mu epsilon theta eta : Kˣ)
    (hmuEpsilon : hilbertSymbol K epsilon mu = 1)
    (htheta : hilbertSymbol K (mu * A₁) theta = 1)
    (heta : hilbertSymbol K (theta * A₂) eta = 1)
    (hchoice : hilbertSymbol K (epsilon * A₂) eta =
      hilbertSymbol K epsilon A₁) :
    hilbertSymbol K ((mu * eta) * A₁) (epsilon / theta) = 1 := by
  have hchoice' : hilbertSymbol K (epsilon * A₂) eta =
      hilbertSymbol K epsilon (mu * A₁) := by
    rw [hilbertSymbol_mul_right, hmuEpsilon, one_mul]
    exact hchoice
  have hclosed := hilbertSymbol_threeStep_closure
    (K := K) (mu * A₁) A₂ epsilon theta eta
      htheta heta hchoice'
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hclosed

/-- The first and last Hilbert conditions of the full braid are compatible
exactly when `mu` pairs trivially with both the first adjacent product and
`epsilon`. -/
theorem hilbertSymbol_fiveStep_outer_closure
    [HilbertSymbolLaws K]
    (A₀ mu epsilon : Kˣ)
    (hfirst : hilbertSymbol K A₀ mu = 1)
    (hmuEpsilon : hilbertSymbol K epsilon mu = 1) :
    hilbertSymbol K (epsilon * A₀) mu⁻¹ = 1 := by
  rw [hilbertSymbol_inv_right_eq_local,
    hilbertSymbol_mul_left, hmuEpsilon, hfirst]
  norm_num

/-- A positive-sign version of the fixed-layer neighbour construction.
The chosen class has defect at least that of `a`, while multiplication by
`a` returns to the exact defect layer of `a`.  If the first positive Hilbert
partner cancels with `a`, Lemma 8.1 supplies a second neighbour and a short
four-case correction. -/
theorem exists_product_preserving_hilbert_one_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (z a : Kˣ)
    (haFinite : quadraticDefect K a ≠ ⊤)
    (haNonzero : quadraticDefect K a ≠ 0)
    (haNotTwoE : quadraticDefect K a ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ mu : Kˣ,
      quadraticDefect K a ≤ quadraticDefect K mu ∧
        quadraticDefect K (a * mu) = quadraticDefect K a ∧
        hilbertSymbol K z mu = 1 := by
  have hnotPair : ¬BONG.IsZeroTwoEDefectPair (K := K) z a := by
    rintro (h | h)
    · exact haNotTwoE h.2
    · exact haNonzero h.2
  rcases (BONG.beli2019Lemma82_ii hres z a).2 hnotPair with
    ⟨w, hwDefect, hwHilbert⟩
  have haLeProduct : quadraticDefect K a ≤
      quadraticDefect K (a * w) := by
    have h := quadraticDefect_mul_ge_min K a w
    rw [hwDefect, min_self] at h
    exact h
  by_cases haw : quadraticDefect K (a * w) = quadraticDefect K a
  · exact ⟨w, hwDefect.symm.le, haw, hwHilbert⟩
  have haLtProduct : quadraticDefect K a <
      quadraticDefect K (a * w) :=
    lt_of_le_of_ne haLeProduct (Ne.symm haw)
  rcases Int.units_eq_one_or (hilbertSymbol K z a) with hza | hza
  · refine ⟨a * w, haLeProduct, ?_, ?_⟩
    · have hsquare : a * (a * w) = w * a ^ 2 := by
        simp only [pow_two]
        ac_rfl
      rw [hsquare, quadraticDefect_mul_square, hwDefect]
    · rw [hilbertSymbol_mul_right, hza, hwHilbert]
      norm_num
  · rcases BONG.beli2019Lemma81_i hres a haNonzero haNotTwoE with
      ⟨c, hcDefect, hacDefect⟩
    rcases Int.units_eq_one_or (hilbertSymbol K z c) with hzc | hzc
    · exact ⟨c, hcDefect.symm.le, hacDefect, hzc⟩
    · refine ⟨a * c, hacDefect.symm.le, ?_, ?_⟩
      · have hsquare : a * (a * c) = c * a ^ 2 := by
          simp only [pow_two]
          ac_rfl
        rw [hsquare, quadraticDefect_mul_square, hcDefect]
      · rw [hilbertSymbol_mul_right, hza, hzc]
        norm_num

/-- Valuation-unit normalization of the preceding positive neighbour.  The
square removed from the raw class preserves both the product defect and its
Hilbert sign. -/
theorem exists_valuationUnit_product_preserving_hilbert_one_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (z a : Kˣ)
    (haFinite : quadraticDefect K a ≠ ⊤)
    (haNonzero : quadraticDefect K a ≠ 0)
    (haNotTwoE : quadraticDefect K a ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ mu : valuationUnitSubgroup K,
      quadraticDefect K a ≤ quadraticDefect K (mu : Kˣ) ∧
        quadraticDefect K (a * (mu : Kˣ)) = quadraticDefect K a ∧
        hilbertSymbol K z (mu : Kˣ) = 1 := by
  rcases exists_product_preserving_hilbert_one_of_largeResidue
      hres z a haFinite haNonzero haNotTwoE with
    ⟨x, hax, hproduct, hxHilbert⟩
  have hxNonzero : quadraticDefect K x ≠ 0 := by
    intro hxZero
    have haZero : quadraticDefect K a = 0 :=
      le_antisymm (hxZero ▸ hax) (bot_le : 0 ≤ quadraticDefect K a)
    exact haNonzero haZero
  have hxEven : Even (ordUnit K x) := by
    rcases Int.even_or_odd (ordUnit K x) with heven | hodd
    · exact heven
    · exact (hxNonzero
        (quadraticDefect_eq_zero_of_odd_ordUnit x hodd)).elim
  rcases BONG.GoodBONG.exists_valuationUnit_eq_mul_square_of_even_order
      x hxEven with ⟨u, t, huUnit, huFactor⟩
  let mu : valuationUnitSubgroup K := ⟨u, huUnit⟩
  refine ⟨mu, ?_, ?_, ?_⟩
  · have huDefect : quadraticDefect K u = quadraticDefect K x := by
      rw [huFactor, quadraticDefect_mul_square]
    simpa only [mu, Subgroup.coe_mk, huDefect] using hax
  · change quadraticDefect K (a * u) = quadraticDefect K a
    rw [huFactor]
    have hsquare : a * (x * t ^ 2) = (a * x) * t ^ 2 := by ac_rfl
    rw [hsquare, quadraticDefect_mul_square, hproduct]
  · change hilbertSymbol K z u = 1
    rw [huFactor, hilbertSymbol_mul_square_right, hxHilbert]

/-- On every non-boundary defect layer over a residue field with more than
two elements there is a valuation-unit representative pairing positively
with a prescribed square class.  Lemma 8.1 supplies three classes
`a`, `c`, and `a*c` on the same layer.  Since the Hilbert character is
multiplicative, at least one of those three has sign `+1`; removing the
even-order square then gives a valuation unit without changing either the
defect or the sign. -/
theorem exists_valuationUnit_same_defect_hilbert_one_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [UnitQuadraticDefectParityLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (z a : Kˣ)
    (haNonzero : quadraticDefect K a ≠ 0)
    (haNotTwoE : quadraticDefect K a ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ mu : valuationUnitSubgroup K,
      quadraticDefect K (mu : Kˣ) = quadraticDefect K a ∧
        hilbertSymbol K z (mu : Kˣ) = 1 := by
  rcases BONG.beli2019Lemma81_i hres a haNonzero haNotTwoE with
    ⟨c, hcDefect, hacDefect⟩
  have hraw : ∃ x : Kˣ,
      quadraticDefect K x = quadraticDefect K a ∧
        hilbertSymbol K z x = 1 := by
    rcases Int.units_eq_one_or (hilbertSymbol K z a) with hza | hza
    · exact ⟨a, rfl, hza⟩
    · rcases Int.units_eq_one_or (hilbertSymbol K z c) with hzc | hzc
      · exact ⟨c, hcDefect, hzc⟩
      · refine ⟨a * c, hacDefect, ?_⟩
        rw [hilbertSymbol_mul_right, hza, hzc]
        norm_num
  rcases hraw with ⟨x, hxDefect, hxHilbert⟩
  have hxNonzero : quadraticDefect K x ≠ 0 := by
    rw [hxDefect]
    exact haNonzero
  have hxEven : Even (ordUnit K x) := by
    rcases Int.even_or_odd (ordUnit K x) with heven | hodd
    · exact heven
    · exact (hxNonzero
        (quadraticDefect_eq_zero_of_odd_ordUnit x hodd)).elim
  rcases BONG.GoodBONG.exists_valuationUnit_eq_mul_square_of_even_order
      x hxEven with ⟨u, t, huUnit, huFactor⟩
  let mu : valuationUnitSubgroup K := ⟨u, huUnit⟩
  refine ⟨mu, ?_, ?_⟩
  · change quadraticDefect K u = quadraticDefect K a
    rw [huFactor, quadraticDefect_mul_square, hxDefect]
  · change hilbertSymbol K z u = 1
    rw [huFactor, hilbertSymbol_mul_square_right, hxHilbert]

/-- Concrete path-refinement of the `R₁ < R₃` rank-four construction
in Lemma 9.2.  Only the two genuinely auxiliary choices `mu` and `theta`
remain as hypotheses.  All dynamic alpha bounds for the return moves, and
both closure Hilbert signs, are derived from `FirstData` and the unit-choice
certificate rather than being postulated separately. -/
theorem reachable_rankFour_firstData_scaling_of_auxiliaryChoices
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a)
    (U : BONG.GoodBONG.Lemma92TernaryUnitChoiceData a.tail
      (a.alphaValue (1 : Fin 3)) (a.alphaValue (2 : Fin 3)))
    (mu theta : valuationUnitSubgroup K)
    (hmuDepth : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hmuFirst : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (mu : Kˣ) = 1)
    (hmuEpsilon : hilbertSymbol K U.epsilon (mu : Kˣ) = 1)
    (hmuMiddleProduct : BONG.GoodBONG.defectOrder (K := K)
        ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3)) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hmuEtaMiddleProduct : BONG.GoodBONG.defectOrder (K := K)
        (((mu : Kˣ) * U.eta) * a.adjacentProduct (1 : Fin 3)) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hthetaDepth : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaMiddle : hilbertSymbol K
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3))
      (theta : Kˣ) = 1)
    (hthetaLastProduct : BONG.GoodBONG.defectOrder (K := K)
        ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hthetaEta : hilbertSymbol K
      ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) U.eta = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i)
      ![a.valueUnit 0,
        U.epsilon * a.valueUnit 1,
        U.epsilon * U.eta * a.valueUnit 2,
        U.eta * a.valueUnit 3] := by
  let epsilon : valuationUnitSubgroup K :=
    ⟨U.epsilon, U.epsilon_isValuationUnit⟩
  let eta : valuationUnitSubgroup K :=
    ⟨U.eta, U.eta_isValuationUnit⟩
  have hsecondRecursion :=
    lemma92RankFourFirstData_secondAlpha_recursion a D
  have hsecondTop :
      (((((a.order (1 : Fin 3).succ -
        a.order (1 : Fin 3).castSucc : Int) : ℚ)) : WithTop ℚ) +
          (a.alphaValue (0 : Fin 3) : WithTop ℚ)) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
      hsecondRecursion.symm
  have hthirdTop :
      (((((a.order (2 : Fin 3).succ -
        a.order (2 : Fin 3).castSucc : Int) : ℚ)) : WithTop ℚ) +
          (a.alphaValue (1 : Fin 3) : WithTop ℚ)) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
      D.thirdAlpha_recursion.symm
  have hmuAlpha : a.adjacentBinaryAlpha (0 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
    rw [lemma92RankFourFirstData_firstBinaryAlpha_eq a D]
    exact hmuDepth
  have hthetaAlpha : rankFourSecondBinaryAlphaAfterFirstMultiplier
      a (mu : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
    refine (min_le_right _ _).trans ?_
    rw [hmuMiddleProduct, hsecondTop]
    exact hthetaDepth
  have hetaAlpha : rankFourThirdBinaryAlphaAfterSecondMultiplier
      a (theta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
    refine (min_le_right _ _).trans ?_
    change _ ≤ BONG.GoodBONG.defectOrder (K := K) U.eta
    rw [hthetaLastProduct, hthirdTop, U.eta_defect]
  have hkappaDepth : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) := by
    have hthetaInv : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) ((theta : Kˣ)⁻¹) := by
      rw [BONG.GoodBONG.defectOrder_inv]
      exact hthetaDepth
    have hmin : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        min (BONG.GoodBONG.defectOrder (K := K) U.epsilon)
          (BONG.GoodBONG.defectOrder (K := K) ((theta : Kˣ)⁻¹)) := by
      apply le_min
      · rw [U.epsilon_defect]
      · exact hthetaInv
    calc
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤ _ := hmin
      _ ≤ BONG.GoodBONG.defectOrder (K := K)
          (U.epsilon * (theta : Kˣ)⁻¹) :=
        BONG.GoodBONG.defectOrder_mul_ge_min _ _
      _ = BONG.GoodBONG.defectOrder (K := K)
          (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) := by
        rfl
  have hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
      a (mu : Kˣ) (eta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K)
          (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) := by
    refine (min_le_right _ _).trans ?_
    change _ ≤ _
    rw [show ((eta : valuationUnitSubgroup K) : Kˣ) = U.eta by rfl,
      hmuEtaMiddleProduct, hsecondTop]
    exact hkappaDepth
  have hchoice : hilbertSymbol K
        (U.epsilon * a.adjacentProduct (2 : Fin 3)) U.eta =
      hilbertSymbol K U.epsilon
        (a.adjacentProduct (1 : Fin 3)) := by
    calc
      hilbertSymbol K
          (U.epsilon * a.adjacentProduct (2 : Fin 3)) U.eta =
          hilbertSymbol K
            (U.epsilon * a.tail.adjacentProduct (1 : Fin 2)) U.eta := by
              congr 2
              rw [a.adjacentProduct_tail]
              congr 1
      _ = hilbertSymbol K U.epsilon
          (a.tail.adjacentProduct (0 : Fin 2)) := U.hilbert_choice
      _ = hilbertSymbol K U.epsilon
          (a.adjacentProduct (1 : Fin 3)) := by
            congr 1
            rw [a.adjacentProduct_tail]
            congr 1
  have hkappaHilbert : hilbertSymbol K
      (((mu : Kˣ) * (eta : Kˣ)) *
        a.adjacentProduct (1 : Fin 3))
      (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) = 1 := by
    exact hilbertSymbol_fiveStep_middle_closure
      (a.adjacentProduct (1 : Fin 3))
      (a.adjacentProduct (2 : Fin 3))
      (mu : Kˣ) U.epsilon (theta : Kˣ) U.eta
      hmuEpsilon hthetaMiddle hthetaEta hchoice
  have hnuAlpha : rankFourFirstBinaryAlphaAfterRightMultiplier
      a (epsilon : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) ((mu : Kˣ)⁻¹) := by
    have hmuInvDepth : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) ((mu : Kˣ)⁻¹) := by
      rw [BONG.GoodBONG.defectOrder_inv]
      exact hmuDepth
    refine (min_le_right _ _).trans ?_
    change _ ≤ _
    have hcandidate := D.firstCandidate U
    have hproduct :
        -(U.epsilon * a.valueUnit (0 : Fin 4) *
            a.valueUnit (1 : Fin 4)) =
          U.epsilon * a.adjacentProduct (0 : Fin 3) := by
      unfold BONG.GoodBONG.adjacentProduct
      have hz : Fin.castSucc (0 : Fin 3) = (0 : Fin 4) := Fin.ext rfl
      have ho : Fin.succ (0 : Fin 3) = (1 : Fin 4) := Fin.ext rfl
      rw [hz, ho]
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul]
      ring
    rw [hproduct] at hcandidate
    change (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (U.epsilon * a.adjacentProduct (0 : Fin 3)) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) at hcandidate
    calc
      _ = (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
        simpa only [epsilon, Subgroup.coe_mk,
          BONG.GoodBONG.orderGap] using hcandidate
      _ ≤ _ := hmuInvDepth
  have hnuHilbert : hilbertSymbol K
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3))
      ((mu : Kˣ)⁻¹) = 1 := by
    exact hilbertSymbol_fiveStep_outer_closure
      (a.adjacentProduct (0 : Fin 3)) (mu : Kˣ) U.epsilon
      hmuFirst hmuEpsilon
  have hreach := reachable_rankFour_fiveStep_scaling_of_dynamic
    a mu theta eta epsilon hmuAlpha hmuFirst hthetaAlpha hthetaMiddle
      hetaAlpha hthetaEta hkappaAlpha hkappaHilbert hnuAlpha hnuHilbert
  simpa only [epsilon, eta, Subgroup.coe_mk] using hreach

/-! ## Numerical consequences of the first rank-four branch -/

/-- The last alpha in the first rank-four branch is strictly below its
half-gap.  Equality would turn the final recursion into
`alpha_2 + alpha_3 = 2e`, contradicting the strict sum in `FirstData`. -/
theorem lemma92RankFourFirstData_thirdAlpha_lt_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.alphaValue (2 : Fin 3) < a.halfGapValue (2 : Fin 3) := by
  apply lt_of_le_of_ne (a.alphaValue_le_halfGapValue (2 : Fin 3))
  intro heq
  have hrec := D.thirdAlpha_recursion
  have hsum := D.secondThird_sum_lt_twoE
  unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap at heq
  unfold BONG.GoodBONG.orderGap at hrec
  push_cast at heq hrec hsum
  linarith

/-- The common right-endpoint plateau propagates the preceding strictness
back to the first alpha. -/
theorem lemma92RankFourFirstData_firstAlpha_lt_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.alphaValue (0 : Fin 3) < a.halfGapValue (0 : Fin 3) := by
  have hthird := lemma92RankFourFirstData_thirdAlpha_lt_halfGap a D
  have hthirdNe : a.alphaValue (2 : Fin 3) ≠
      a.halfGapValue (2 : Fin 3) := ne_of_lt hthird
  apply lt_of_le_of_ne (a.alphaValue_le_halfGapValue (0 : Fin 3))
  intro heq
  have hpropagate := a.beli2019Lemma84_iii
    (0 : Fin 3) (2 : Fin 3) (0 : Fin 3)
    (Fin.zero_le _) le_rfl (Fin.zero_le _)
    (D.commonRightEndpoint (2 : Fin 3)).symm heq
  exact hthirdNe
    (hpropagate.2 (2 : Fin 3) (Fin.zero_le _) le_rfl)

/-- The first alpha is no larger than the third alpha.  This follows from
the common right endpoint and goodness (`R_2 <= R_4`). -/
theorem lemma92RankFourFirstData_firstAlpha_le_thirdAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.alphaValue (0 : Fin 3) ≤ a.alphaValue (2 : Fin 3) := by
  have hright := D.commonRightEndpoint (2 : Fin 3)
  have horders : a.order (1 : Fin 4) ≤ a.order (3 : Fin 4) :=
    a.good (1 : Fin 4) (by omega)
  have hordersQ : (a.order (1 : Fin 4) : ℚ) ≤
      (a.order (3 : Fin 4) : ℚ) := by
    exact_mod_cast horders
  unfold BONG.GoodBONG.alphaRightEndpoint at hright
  push_cast at hright
  linarith

/-- The two local alphas of the initial ternary segment stay below `2e` in
sum, as required by the property-A exact scaling construction. -/
theorem lemma92RankFourFirstData_initialThree_alphaSum_le_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    a.lemma814InitialThree.alphaValue (0 : Fin 2) +
        a.lemma814InitialThree.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
  rw [lemma92RankFourFirstData_initialThree_firstAlpha_eq a D,
    lemma92RankFourFirstData_initialThree_secondAlpha_eq a D]
  have hfirstLeThird :=
    lemma92RankFourFirstData_firstAlpha_le_thirdAlpha a D
  linarith [D.secondThird_sum_lt_twoE]

/-- The middle adjacent defect contains the first alpha layer.  The proof
cancels the finite middle order gap from the local left-candidate inequality
using the right-endpoint recursion. -/
theorem lemma92RankFourFirstData_firstAlpha_le_middleAdjacentDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      a.adjacentDefect (1 : Fin 3) := by
  have hbound := a.alpha_le_leftDefectCandidate
    (i := (1 : Fin 3)) (j := (1 : Fin 3)) le_rfl
  rw [← a.coe_alphaValue, BONG.GoodBONG.leftDefectCandidate] at hbound
  have hrecTop := congrArg (fun z : ℚ => (z : WithTop ℚ))
    (lemma92RankFourFirstData_secondAlpha_recursion a D)
  rw [WithTop.coe_add] at hrecTop
  rw [hrecTop] at hbound
  exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp hbound

/-- The first alpha of `FirstData` is an interior odd defect layer and hence
is represented by a valuation unit. -/
theorem lemma92RankFourFirstData_exists_firstAlphaUnit
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    ∃ x : Kˣ, IsValuationUnit K (x : K) ∧
      BONG.GoodBONG.defectOrder (K := K) x =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
  exact a.exists_firstAlphaUnit_of_lt_halfGap
    (lemma92RankFourFirstData_firstAlpha_lt_halfGap a D)

/-- In the first rank-four branch one can choose the first braid multiplier
at (or above) the first alpha layer, with positive first Hilbert sign, while
forcing its product with the middle adjacent product back to the exact first
alpha layer.  The equal-layer case uses the positive product-preserving
neighbour construction; in the strict case ordinary defect domination is
already sharp. -/
theorem lemma92RankFourFirstData_exists_firstMultiplier
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    ∃ mu : valuationUnitSubgroup K,
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) ∧
        BONG.GoodBONG.defectOrder (K := K)
            ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3)) =
          (a.alphaValue (0 : Fin 3) : WithTop ℚ) ∧
        hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
            (mu : Kˣ) = 1 := by
  let A₀ := a.adjacentProduct (0 : Fin 3)
  let A₁ := a.adjacentProduct (1 : Fin 3)
  have hfirstLtTwoE : a.alphaValue (0 : Fin 3) <
      2 * (ramificationIndex K : ℚ) := by
    have hfirstLeThird :=
      lemma92RankFourFirstData_firstAlpha_le_thirdAlpha a D
    linarith [D.secondAlpha_nonnegative, D.secondThird_sum_lt_twoE]
  rcases lemma92RankFourFirstData_exists_firstAlphaUnit a D with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hA₁Le : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) A₁ := by
    simpa only [A₁, BONG.GoodBONG.adjacentDefect] using
      lemma92RankFourFirstData_firstAlpha_le_middleAdjacentDefect a D
  by_cases hA₁Eq : BONG.GoodBONG.defectOrder (K := K) A₁ =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ)
  · have hA₁Reference : BONG.GoodBONG.defectOrder (K := K) A₁ =
        BONG.GoodBONG.defectOrder (K := K) reference := by
      rw [hA₁Eq, hrefDefect]
    have hA₁Quadratic : quadraticDefect K A₁ =
        quadraticDefect K reference :=
      BONG.GoodBONG.quadraticDefect_eq_of_defectOrder_eq
        A₁ reference hA₁Reference
    have hA₁Finite : quadraticDefect K A₁ ≠ ⊤ := by
      rw [hA₁Quadratic]
      exact BONG.GoodBONG.quadraticDefect_ne_top_of_defectOrder_eq_coe
        reference (a.alphaValue (0 : Fin 3)) hrefDefect
    have hA₁Nonzero : quadraticDefect K A₁ ≠ 0 := by
      rw [hA₁Quadratic]
      exact quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
    have hA₁OrderLt : BONG.GoodBONG.defectOrder (K := K) A₁ <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hA₁Eq]
      exact_mod_cast hfirstLtTwoE
    have hA₁NotTwoE : quadraticDefect K A₁ ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_ne_twoE_of_defectOrder_lt_twoE A₁ hA₁OrderLt
    rcases exists_valuationUnit_product_preserving_hilbert_one_of_largeResidue
        hres A₀ A₁ hA₁Finite hA₁Nonzero hA₁NotTwoE with
      ⟨mu, hA₁Mu, hproduct, hhilbert⟩
    have hmap : Monotone
        (WithTop.map (fun n : Nat ↦ (n : ℚ))) :=
      WithTop.monotone_map_iff.mpr (by
        intro m n hmn
        change (m : ℚ) ≤ (n : ℚ)
        exact_mod_cast hmn)
    have hdepth : BONG.GoodBONG.defectOrder (K := K) A₁ ≤
        BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
      unfold BONG.GoodBONG.defectOrder
      exact hmap hA₁Mu
    refine ⟨mu, hA₁Eq ▸ hdepth, ?_, ?_⟩
    · have hproduct' : quadraticDefect K ((mu : Kˣ) * A₁) =
          quadraticDefect K A₁ := by
        simpa only [mul_comm] using hproduct
      exact (BONG.defectOrder_eq_of_quadraticDefect_eq
          ((mu : Kˣ) * A₁) A₁ hproduct').trans hA₁Eq
    · simpa only [A₀] using hhilbert
  · have hfirstLtA₁ : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
        BONG.GoodBONG.defectOrder (K := K) A₁ :=
      lt_of_le_of_ne hA₁Le (Ne.symm hA₁Eq)
    have hrefOrderLt : BONG.GoodBONG.defectOrder (K := K) reference <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hrefDefect]
      exact_mod_cast hfirstLtTwoE
    have hrefNonzero : quadraticDefect K reference ≠ 0 :=
      quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
    have hrefNotTwoE : quadraticDefect K reference ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_ne_twoE_of_defectOrder_lt_twoE
        reference hrefOrderLt
    have hnotPair : ¬BONG.IsZeroTwoEDefectPair
        (K := K) A₀ reference := by
      rintro (⟨_, hrefEndpoint⟩ | ⟨_, hrefZero⟩)
      · exact hrefNotTwoE hrefEndpoint
      · exact hrefNonzero hrefZero
    rcases BONG.beli2019Lemma82_ii_unit hres A₀ reference
        hrefUnit hnotPair with
      ⟨muRaw, hmuUnit, hmuQuadratic, hmuHilbert⟩
    let mu : valuationUnitSubgroup K := ⟨muRaw, hmuUnit⟩
    have hmuOrder : BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
      change BONG.GoodBONG.defectOrder (K := K) muRaw = _
      exact (BONG.defectOrder_eq_of_quadraticDefect_eq
        muRaw reference hmuQuadratic).trans hrefDefect
    refine ⟨mu, hmuOrder.ge, ?_, ?_⟩
    · change BONG.GoodBONG.defectOrder (K := K) (muRaw * A₁) = _
      exact (BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right
        (hmuOrder ▸ hfirstLtA₁)).trans hmuOrder
    · simpa only [mu, Subgroup.coe_mk, A₀] using hmuHilbert

/-- Variant of the Lemma 9.2 ternary unit certificate with its first unit
already fixed.  Only the final unit is chosen; the strict defect-sum bound
allows the Hilbert sign dictated by the fixed first unit. -/
theorem exists_lemma92TernaryUnitChoiceData_of_fixedEpsilon
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    (s : BONG.GoodBONG r M 3)
    (previousDepth finalDepth : ℚ)
    (epsilon : valuationUnitSubgroup K)
    (hepsilonDefect : BONG.GoodBONG.defectOrder (K := K)
        (epsilon : Kˣ) = (previousDepth : WithTop ℚ))
    (hfinalOdd : IsOddRationalInteger finalDepth)
    (hfinalNonnegative : 0 ≤ finalDepth)
    (hfinalLt : finalDepth < 2 * (ramificationIndex K : ℚ))
    (hlastAdjacent : (previousDepth : WithTop ℚ) <
      s.adjacentDefect (1 : Fin 2))
    (hsum : previousDepth + finalDepth <
      2 * (ramificationIndex K : ℚ)) :
    ∃ U : BONG.GoodBONG.Lemma92TernaryUnitChoiceData s
        previousDepth finalDepth,
      U.epsilon = (epsilon : Kˣ) := by
  rcases BONG.DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      finalDepth hfinalOdd hfinalNonnegative hfinalLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hepsilonLt : BONG.GoodBONG.defectOrder (K := K) (epsilon : Kˣ) <
      BONG.GoodBONG.defectOrder (K := K)
        (s.adjacentProduct (1 : Fin 2)) := by
    rw [hepsilonDefect]
    simpa only [BONG.GoodBONG.adjacentDefect] using hlastAdjacent
  have hscaled : BONG.GoodBONG.defectOrder (K := K)
      ((epsilon : Kˣ) * s.adjacentProduct (1 : Fin 2)) =
        (previousDepth : WithTop ℚ) := by
    rw [BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right hepsilonLt,
      hepsilonDefect]
  have hsumTop : BONG.GoodBONG.defectOrder (K := K)
        ((epsilon : Kˣ) * s.adjacentProduct (1 : Fin 2)) +
        BONG.GoodBONG.defectOrder (K := K) reference <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hscaled, hrefDefect]
    norm_cast
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsum
  let requested := hilbertSymbol K (epsilon : Kˣ)
    (s.adjacentProduct (0 : Fin 2))
  rcases BONG.exists_valuationUnit_same_defect_hilbert_eq_of_defectOrder_add_lt_twoE
      ((epsilon : Kˣ) * s.adjacentProduct (1 : Fin 2))
      reference hrefUnit requested hsumTop with
    ⟨eta, hetaUnit, hetaQuadratic, hetaHilbert⟩
  have hetaDefect : BONG.GoodBONG.defectOrder (K := K) eta =
      (finalDepth : WithTop ℚ) :=
    (BONG.defectOrder_eq_of_quadraticDefect_eq
      eta reference hetaQuadratic).trans hrefDefect
  have hadjacent := s.ternaryScaled_adjacentHilbert_eq_of_choice
    (epsilon : Kˣ) eta hetaHilbert
  refine ⟨{
    epsilon := (epsilon : Kˣ)
    eta := eta
    epsilon_isValuationUnit := epsilon.property
    eta_isValuationUnit := hetaUnit
    epsilon_defect := hepsilonDefect
    eta_defect := hetaDefect
    scaledLastAdjacent_defect := hscaled
    hilbert_choice := hetaHilbert
    adjacent_hilbert := hadjacent
  }, rfl⟩

/-- The legal first binary move which normalizes the tail in the strict
rank-four branch.  Besides retaining the exact path, the package records
that the two alpha values of the new ternary tail are precisely the ambient
second and third alpha values. -/
structure Lemma92RankFourFirstTailNormalizationData
    (a : BONG.GoodBONG q L 4) where
  mu : valuationUnitSubgroup K
  muDepth : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
    BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ)
  muFirstHilbert : hilbertSymbol K
    (a.adjacentProduct (0 : Fin 3)) (mu : Kˣ) = 1
  muMiddleProduct : BONG.GoodBONG.defectOrder (K := K)
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3)) =
    (a.alphaValue (0 : Fin 3) : WithTop ℚ)
  transformed : BONG.GoodBONG q L 4
  values : (fun i ↦ transformed.valueUnit i) =
    beli2009BinaryTransformAt (fun i ↦ a.valueUnit i) (0 : Fin 3) mu
  reachable : Beli2009BinaryReachable (K := K)
    (fun i ↦ a.valueUnit i) (fun i ↦ transformed.valueUnit i)
  tailFirstAlpha_eq : transformed.tail.alphaValue (0 : Fin 2) =
    a.alphaValue (1 : Fin 3)
  tailSecondAlpha_eq : transformed.tail.alphaValue (1 : Fin 2) =
    a.alphaValue (2 : Fin 3)

/-- Construction of the tail normalization package.  The first local tail
alpha is the normalized middle left candidate.  For the second, the left
candidate beginning at that same normalized edge and the two right-endpoint
recursions give the reverse inequality to alpha localization. -/
theorem exists_lemma92RankFourFirstTailNormalizationData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    Nonempty (Lemma92RankFourFirstTailNormalizationData a) := by
  rcases lemma92RankFourFirstData_exists_firstMultiplier hres a D with
    ⟨mu, hmuDepth, hmuMiddleProduct, hmuFirstHilbert⟩
  have hmuAlpha : a.adjacentBinaryAlpha (0 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
    rw [lemma92RankFourFirstData_firstBinaryAlpha_eq a D]
    exact hmuDepth
  have hmuGroup : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 4) / a.valueUnit (0 : Fin 4)) := by
    exact valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 3) mu hmuAlpha hmuFirstHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 3)
      mu hmuGroup with ⟨c, hcValues⟩
  have hstep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨0, mu, hmuGroup, hcValues⟩
  have horders : a.SameOrders c := a.order_invariant c
  have halphas : a.SameAlphas c := a.alpha_invariant c
  have hcMiddleAdjacent : c.adjacentProduct (1 : Fin 3) =
      (mu : Kˣ) * a.adjacentProduct (1 : Fin 3) := by
    unfold BONG.GoodBONG.adjacentProduct
    change -(c.valueUnit (1 : Fin 4) * c.valueUnit (2 : Fin 4)) =
      (mu : Kˣ) *
        -(a.valueUnit (1 : Fin 4) * a.valueUnit (2 : Fin 4))
    rw [congrFun hcValues (1 : Fin 4), congrFun hcValues (2 : Fin 4)]
    simp [beli2009BinaryTransformAt, mul_assoc]
  have hcMiddleDefect : c.adjacentDefect (1 : Fin 3) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    unfold BONG.GoodBONG.adjacentDefect
    rw [hcMiddleAdjacent, hmuMiddleProduct]
  have hcMiddleLeft : c.leftDefectCandidate
      (1 : Fin 3) (1 : Fin 3) =
        (c.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    unfold BONG.GoodBONG.leftDefectCandidate
    change
      (((c.order (2 : Fin 4) - c.order (1 : Fin 4) : Int) : ℚ) :
          WithTop ℚ) + c.adjacentDefect (1 : Fin 3) =
        (c.alphaValue (1 : Fin 3) : WithTop ℚ)
    rw [← horders (2 : Fin 4), ← horders (1 : Fin 4),
      hcMiddleDefect, ← halphas (1 : Fin 3), ← WithTop.coe_add]
    exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
      (lemma92RankFourFirstData_secondAlpha_recursion a D).symm
  have hcMiddleBinary : c.adjacentBinaryAlpha (1 : Fin 3) =
      (c.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    unfold BONG.GoodBONG.adjacentBinaryAlpha
    rw [hcMiddleLeft]
    apply min_eq_right
    rw [← c.coe_halfGapValue]
    exact_mod_cast c.alphaValue_le_halfGapValue (1 : Fin 3)
  have htailFirstRaw :=
    alphaValue_succ_eq_tail_of_adjacentBinaryAlpha_succ
      c (0 : Fin 2) (by simpa using hcMiddleBinary)
  have htailFirst : c.tail.alphaValue (0 : Fin 2) =
      a.alphaValue (1 : Fin 3) := by
    rw [← htailFirstRaw]
    exact (halphas (1 : Fin 3)).symm
  have htailSecondLower :
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
        (c.tail.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    rw [halphas (2 : Fin 3)]
    exact c.alphaValue_shift_le_tail (1 : Fin 2)
  have hcandidateRat :
      ((a.order (3 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
          a.alphaValue (0 : Fin 3) =
        a.alphaValue (2 : Fin 3) := by
    have hsecond := lemma92RankFourFirstData_secondAlpha_recursion a D
    have hthird := D.thirdAlpha_recursion
    unfold BONG.GoodBONG.orderGap at hsecond hthird
    push_cast at hsecond hthird ⊢
    linarith
  have htailSecondCandidate : c.tail.leftDefectCandidate
      (1 : Fin 2) (0 : Fin 2) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    rw [c.leftDefectCandidate_tail]
    unfold BONG.GoodBONG.leftDefectCandidate
    change
      (((c.order (3 : Fin 4) - c.order (1 : Fin 4) : Int) : ℚ) :
          WithTop ℚ) + c.adjacentDefect (1 : Fin 3) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ)
    rw [← horders (3 : Fin 4), ← horders (1 : Fin 4), hcMiddleDefect,
      ← WithTop.coe_add]
    exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hcandidateRat
  have htailSecondUpper :
      (c.tail.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    have h := c.tail.alpha_le_leftDefectCandidate
      (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide)
    rw [← c.tail.coe_alphaValue, htailSecondCandidate] at h
    exact h
  have htailSecond : c.tail.alphaValue (1 : Fin 2) =
      a.alphaValue (2 : Fin 3) := by
    apply WithTop.coe_injective
    exact le_antisymm htailSecondUpper htailSecondLower
  exact ⟨{
    mu := mu
    muDepth := hmuDepth
    muFirstHilbert := hmuFirstHilbert
    muMiddleProduct := hmuMiddleProduct
    transformed := c
    values := hcValues
    reachable := hstep.reachable
    tailFirstAlpha_eq := htailFirst
    tailSecondAlpha_eq := htailSecond
  }⟩

/-- The two ternary scaling units chosen after tail normalization.  The
first one is additionally required to pair trivially with the multiplier
which normalized the head edge; this is the sole condition needed to make
the final inverse head move legal. -/
structure Lemma92RankFourFirstTailUnitChoiceData
    (a : BONG.GoodBONG q L 4)
    (N : Lemma92RankFourFirstTailNormalizationData a) where
  epsilon : valuationUnitSubgroup K
  epsilonMuHilbert : hilbertSymbol K (N.mu : Kˣ) (epsilon : Kˣ) = 1
  choice : BONG.GoodBONG.Lemma92TernaryUnitChoiceData
    N.transformed.tail (a.alphaValue (1 : Fin 3))
      (a.alphaValue (2 : Fin 3))
  choiceEpsilon : choice.epsilon = (epsilon : Kˣ)

/-- Large residue degree chooses the exact second-alpha unit with positive
pairing against the normalization multiplier.  The final unit is then
chosen by the strict-sum form of Lemma 8.2. -/
theorem exists_lemma92RankFourFirstTailUnitChoiceData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a)
    (N : Lemma92RankFourFirstTailNormalizationData a) :
    Nonempty (Lemma92RankFourFirstTailUnitChoiceData a N) := by
  rcases BONG.DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (1 : Fin 3)) D.secondAlpha_odd
        D.secondAlpha_nonnegative D.secondAlpha_lt_twoE with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hrefOrderLt : BONG.GoodBONG.defectOrder (K := K) reference <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect]
    exact_mod_cast D.secondAlpha_lt_twoE
  have hrefNonzero : quadraticDefect K reference ≠ 0 :=
    quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
  have hrefNotTwoE : quadraticDefect K reference ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    quadraticDefect_ne_twoE_of_defectOrder_lt_twoE reference hrefOrderLt
  have hnotPair : ¬BONG.IsZeroTwoEDefectPair
      (K := K) (N.mu : Kˣ) reference := by
    rintro (⟨_, hrefEndpoint⟩ | ⟨_, hrefZero⟩)
    · exact hrefNotTwoE hrefEndpoint
    · exact hrefNonzero hrefZero
  rcases BONG.beli2019Lemma82_ii_unit hres (N.mu : Kˣ) reference
      hrefUnit hnotPair with
    ⟨epsilonRaw, hepsilonUnit, hepsilonQuadratic, hepsilonMu⟩
  let epsilon : valuationUnitSubgroup K :=
    ⟨epsilonRaw, hepsilonUnit⟩
  have hepsilonDefect : BONG.GoodBONG.defectOrder (K := K)
      (epsilon : Kˣ) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    change BONG.GoodBONG.defectOrder (K := K) epsilonRaw = _
    exact (BONG.defectOrder_eq_of_quadraticDefect_eq
      epsilonRaw reference hepsilonQuadratic).trans hrefDefect
  have htailLastAdjacent :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
        N.transformed.tail.adjacentDefect (1 : Fin 2) := by
    have hproduct : N.transformed.tail.adjacentProduct (1 : Fin 2) =
        a.tail.adjacentProduct (1 : Fin 2) := by
      rw [N.transformed.adjacentProduct_tail]
      change N.transformed.adjacentProduct (2 : Fin 3) =
        a.tail.adjacentProduct (1 : Fin 2)
      unfold BONG.GoodBONG.adjacentProduct
      change
        -(N.transformed.valueUnit (2 : Fin 4) *
            N.transformed.valueUnit (3 : Fin 4)) =
          -(a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3))
      rw [congrFun N.values (2 : Fin 4), congrFun N.values (3 : Fin 4)]
      simp [beli2009BinaryTransformAt]
    unfold BONG.GoodBONG.adjacentDefect
    rw [hproduct]
    exact D.lastAdjacent_gt_secondAlpha
  rcases exists_lemma92TernaryUnitChoiceData_of_fixedEpsilon
      N.transformed.tail (a.alphaValue (1 : Fin 3))
        (a.alphaValue (2 : Fin 3)) epsilon hepsilonDefect
        D.thirdAlpha_odd D.thirdAlpha_nonnegative D.thirdAlpha_lt_twoE
        htailLastAdjacent D.secondThird_sum_lt_twoE with
    ⟨U, hUepsilon⟩
  exact ⟨{
    epsilon := epsilon
    epsilonMuHilbert := by
      simpa only [epsilon, Subgroup.coe_mk] using hepsilonMu
    choice := U
    choiceEpsilon := hUepsilon
  }⟩

/-- The normalized ternary tail admits the exact Lemma 9.2 scaling on its
own projected lattice, and the complete rank-three theorem turns that
realization into an adjacent-binary path.  Strict outer orders use the
property-A construction; equal outer orders use its exact scaled-last-edge
criterion. -/
theorem exists_reachable_lemma92RankFourFirstScaledTail
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a)
    (N : Lemma92RankFourFirstTailNormalizationData a)
    (C : Lemma92RankFourFirstTailUnitChoiceData a N) :
    ∃ t : BONG.GoodBONG
        (q.orthogonalSpace N.transformed.toBONG.head
          N.transformed.toBONG.head_isAnisotropic)
        (L.projectedLattice q N.transformed.toBONG.head
          N.transformed.toBONG.head_isAnisotropic) 3,
      (∀ i, t.valueUnit i = N.transformed.tail.ternaryScaledValues
        C.choice.epsilon C.choice.eta i) ∧
      Beli2009BinaryReachable (K := K)
        (fun i ↦ N.transformed.tail.valueUnit i)
        (fun i ↦ t.valueUnit i) := by
  let s := N.transformed.tail
  let U := C.choice
  have hepsilonDepth :
      (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) U.epsilon := by
    rw [show s.alphaValue (0 : Fin 2) =
        a.alphaValue (1 : Fin 3) by exact N.tailFirstAlpha_eq,
      U.epsilon_defect]
  have hetaDepth :
      (s.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) U.eta := by
    rw [show s.alphaValue (1 : Fin 2) =
        a.alphaValue (2 : Fin 3) by exact N.tailSecondAlpha_eq,
      U.eta_defect]
  have hAlphaSum : s.alphaValue (0 : Fin 2) +
      s.alphaValue (1 : Fin 2) ≤ 2 * (ramificationIndex K : ℚ) := by
    rw [show s.alphaValue (0 : Fin 2) =
        a.alphaValue (1 : Fin 3) by exact N.tailFirstAlpha_eq,
      show s.alphaValue (1 : Fin 2) =
        a.alphaValue (2 : Fin 3) by exact N.tailSecondAlpha_eq]
    exact D.secondThird_sum_lt_twoE.le
  have houterLe : s.order (0 : Fin 3) ≤ s.order (2 : Fin 3) :=
    s.good (0 : Fin 3) (by omega)
  obtain houter | houter := lt_or_eq_of_le houterLe
  · have hproperty : s.toBONG.HasPropertyA := by
      intro i hi
      have hiZero : i = (0 : Fin 3) := by
        apply Fin.ext
        omega
      subst i
      exact houter
    rcases s.exists_goodBONG_ternaryScaledValues_of_propertyA
        U.epsilon U.eta U.epsilon_isValuationUnit U.eta_isValuationUnit
        hepsilonDepth hetaDepth U.adjacent_hilbert hproperty hAlphaSum with
      ⟨t, htValues⟩
    exact ⟨t, htValues,
      reachable_rankThree_of_largeResidue hres s t⟩
  · have hcriterion : s.TernaryEqualOuterAlphaCriterion
        U.epsilon U.eta := by
      right
      left
      have hproduct :
          -(U.epsilon * s.valueUnit (1 : Fin 3) *
              s.valueUnit (2 : Fin 3)) =
            U.epsilon * s.adjacentProduct (1 : Fin 2) := by
        unfold BONG.GoodBONG.adjacentProduct
        change
          -(U.epsilon * s.valueUnit (1 : Fin 3) *
              s.valueUnit (2 : Fin 3)) =
            U.epsilon *
              -(s.valueUnit (1 : Fin 3) * s.valueUnit (2 : Fin 3))
        apply Units.ext
        simp only [Units.val_neg, Units.val_mul]
        ring
      rw [hproduct, U.scaledLastAdjacent_defect,
        N.tailFirstAlpha_eq]
    rcases s.exists_goodBONG_ternaryScaledValues_of_equalOuter
        U.epsilon U.eta U.epsilon_isValuationUnit U.eta_isValuationUnit
        hepsilonDepth hetaDepth U.adjacent_hilbert houter hcriterion with
      ⟨t, htValues⟩
    exact ⟨t, htValues,
      reachable_rankThree_of_largeResidue hres s t⟩

/-- Path-refined Lemma 9.2 in the strict first quaternary branch.  The path
is: normalize the first edge, connect the normalized ternary tail to its
exact scaling, prepend the unchanged normalized head, and remove the first
multiplier.  The specially chosen positive pairing `(mu, epsilon)=1` makes
the last inverse move legal. -/
theorem reachableLemma92_rankFourFirst_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourFirstData a) :
    Nonempty (ReachableLemma92Transform a) := by
  rcases exists_lemma92RankFourFirstTailNormalizationData hres a D with
    ⟨N⟩
  rcases exists_lemma92RankFourFirstTailUnitChoiceData hres a D N with
    ⟨C⟩
  rcases exists_reachable_lemma92RankFourFirstScaledTail hres a D N C with
    ⟨t, htValues, htailReach⟩
  let U := C.choice
  let d := N.transformed.replaceTailGood t
  have hdHead : d.valueUnit (0 : Fin 4) =
      N.transformed.valueUnit (0 : Fin 4) := by
    apply Units.ext
    change d.toBONG.value (0 : Fin 4) =
      N.transformed.toBONG.value (0 : Fin 4)
    rw [d.toBONG.value_zero_eq_quadratic_head,
      N.transformed.toBONG.value_zero_eq_quadratic_head,
      N.transformed.replaceTailGood_head t]
  have hdSucc (j : Fin 3) : d.valueUnit j.succ = t.valueUnit j := by
    apply Units.ext
    change d.toBONG.value j.succ = t.toBONG.value j
    calc
      d.toBONG.value j.succ = d.toBONG.tail.value j :=
        (d.toBONG.value_tail j).symm
      _ = t.toBONG.value j := by
        change (N.transformed.toBONG.replaceTail t.toBONG).tail.value j =
          t.toBONG.value j
        rw [BONG.replaceTail_tail]
        rfl
  have hdCons : (fun i ↦ d.valueUnit i) =
      Fin.cons (N.transformed.valueUnit (0 : Fin 4))
        (fun i ↦ t.valueUnit i) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hdHead
    · exact hdSucc j
  have htailLift : Beli2009BinaryReachable (K := K)
      (fun i ↦ N.transformed.valueUnit i) (fun i ↦ d.valueUnit i) := by
    have h := Beli2009BinaryReachable.cons
      (N.transformed.valueUnit (0 : Fin 4)) htailReach
    rw [cons_tailValues_eq N.transformed] at h
    rw [hdCons]
    exact h
  have hdValues : (fun i ↦ d.valueUnit i) =
      ![(N.mu : Kˣ) * a.valueUnit 0,
        U.epsilon * (N.mu : Kˣ) * a.valueUnit 1,
        U.epsilon * U.eta * a.valueUnit 2,
        U.eta * a.valueUnit 3] := by
    funext i
    fin_cases i
    · calc
        d.valueUnit (0 : Fin 4) =
            N.transformed.valueUnit (0 : Fin 4) := hdHead
        _ = (N.mu : Kˣ) * a.valueUnit 0 := by
              rw [congrFun N.values (0 : Fin 4)]
              rfl
    · calc
        d.valueUnit (1 : Fin 4) = t.valueUnit (0 : Fin 3) :=
          hdSucc (0 : Fin 3)
        _ = U.epsilon * N.transformed.tail.valueUnit (0 : Fin 3) := by
          rw [htValues, N.transformed.tail.ternaryScaledValues_zero]
        _ = U.epsilon * N.transformed.valueUnit (1 : Fin 4) := by
          simpa using congrArg (fun x : Kˣ ↦ U.epsilon * x)
            (N.transformed.valueUnit_goodTail (0 : Fin 3))
        _ = U.epsilon * (N.mu : Kˣ) * a.valueUnit 1 := by
          rw [congrFun N.values (1 : Fin 4)]
          simp [beli2009BinaryTransformAt, mul_assoc]
    · calc
        d.valueUnit (2 : Fin 4) = t.valueUnit (1 : Fin 3) :=
          hdSucc (1 : Fin 3)
        _ = U.epsilon * U.eta *
            N.transformed.tail.valueUnit (1 : Fin 3) := by
          rw [htValues, N.transformed.tail.ternaryScaledValues_one]
        _ = U.epsilon * U.eta *
            N.transformed.valueUnit (2 : Fin 4) := by
          simpa using congrArg (fun x : Kˣ ↦ U.epsilon * U.eta * x)
            (N.transformed.valueUnit_goodTail (1 : Fin 3))
        _ = U.epsilon * U.eta * a.valueUnit 2 := by
          rw [congrFun N.values (2 : Fin 4)]
          simp [beli2009BinaryTransformAt]
    · calc
        d.valueUnit (3 : Fin 4) = t.valueUnit (2 : Fin 3) :=
          hdSucc (2 : Fin 3)
        _ = U.eta * N.transformed.tail.valueUnit (2 : Fin 3) := by
          rw [htValues, N.transformed.tail.ternaryScaledValues_two]
        _ = U.eta * N.transformed.valueUnit (3 : Fin 4) := by
          simpa using congrArg (fun x : Kˣ ↦ U.eta * x)
            (N.transformed.valueUnit_goodTail (2 : Fin 3))
        _ = U.eta * a.valueUnit 3 := by
          rw [congrFun N.values (3 : Fin 4)]
          simp [beli2009BinaryTransformAt]
  have hdFirstAdjacent : d.adjacentProduct (0 : Fin 3) =
      (U.epsilon * a.adjacentProduct (0 : Fin 3)) *
        (N.mu : Kˣ) ^ 2 := by
    unfold BONG.GoodBONG.adjacentProduct
    change -(d.valueUnit (0 : Fin 4) * d.valueUnit (1 : Fin 4)) =
      (U.epsilon *
          -(a.valueUnit (0 : Fin 4) * a.valueUnit (1 : Fin 4))) *
        (N.mu : Kˣ) ^ 2
    rw [congrFun hdValues (0 : Fin 4), congrFun hdValues (1 : Fin 4)]
    change
      -(((N.mu : Kˣ) * a.valueUnit 0) *
          (U.epsilon * (N.mu : Kˣ) * a.valueUnit 1)) =
        (U.epsilon * -(a.valueUnit 0 * a.valueUnit 1)) *
          (N.mu : Kˣ) ^ 2
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  have hepsilonLtFirst : a.adjacentDefect (0 : Fin 3) <
      BONG.GoodBONG.defectOrder (K := K) U.epsilon := by
    rw [U.epsilon_defect]
    exact D.firstAdjacent_lt_secondAlpha
  have hepsilonFirstDefect : BONG.GoodBONG.defectOrder (K := K)
      (U.epsilon * a.adjacentProduct (0 : Fin 3)) =
        a.adjacentDefect (0 : Fin 3) :=
    BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left hepsilonLtFirst
  have hdFirstDefect : d.adjacentDefect (0 : Fin 3) =
      a.adjacentDefect (0 : Fin 3) := by
    change BONG.GoodBONG.defectOrder (K := K)
        (d.adjacentProduct (0 : Fin 3)) =
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 3))
    rw [hdFirstAdjacent, BONG.GoodBONG.defectOrder_mul_square,
      hepsilonFirstDefect]
    rfl
  have hordersD : a.SameOrders d := a.order_invariant d
  have halphasD : a.SameAlphas d := a.alpha_invariant d
  have hdFirstLeft : d.leftDefectCandidate (0 : Fin 3) (0 : Fin 3) =
      (d.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    unfold BONG.GoodBONG.leftDefectCandidate
    change
      (((d.order (1 : Fin 4) - d.order (0 : Fin 4) : Int) : ℚ) :
          WithTop ℚ) + d.adjacentDefect (0 : Fin 3) =
        (d.alphaValue (0 : Fin 3) : WithTop ℚ)
    rw [← hordersD (1 : Fin 4), ← hordersD (0 : Fin 4),
      hdFirstDefect, ← halphasD (0 : Fin 3)]
    have hcandidate := D.firstAlpha_candidate
    unfold BONG.GoodBONG.orderGap at hcandidate
    change
      (((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) :
          WithTop ℚ) + a.adjacentDefect (0 : Fin 3) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) at hcandidate
    exact hcandidate
  have hdFirstBinary : d.adjacentBinaryAlpha (0 : Fin 3) =
      (d.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    unfold BONG.GoodBONG.adjacentBinaryAlpha
    rw [hdFirstLeft]
    apply min_eq_right
    rw [← d.coe_halfGapValue]
    exact_mod_cast d.alphaValue_le_halfGapValue (0 : Fin 3)
  let nu : valuationUnitSubgroup K := N.mu⁻¹
  have hnuAlpha : d.adjacentBinaryAlpha (0 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K) (nu : Kˣ) := by
    rw [hdFirstBinary, ← halphasD (0 : Fin 3)]
    simpa only [nu, Subgroup.coe_inv,
      BONG.GoodBONG.defectOrder_inv] using N.muDepth
  have hnuHilbert : hilbertSymbol K (d.adjacentProduct (0 : Fin 3))
      (nu : Kˣ) = 1 := by
    rw [hdFirstAdjacent, hilbertSymbol_mul_square_left]
    change hilbertSymbol K
      (U.epsilon * a.adjacentProduct (0 : Fin 3)) (N.mu : Kˣ)⁻¹ = 1
    rw [hilbertSymbol_inv_right_eq_local, hilbertSymbol_mul_left,
      hilbertSymbol_comm K U.epsilon (N.mu : Kˣ),
      C.choiceEpsilon, C.epsilonMuHilbert, N.muFirstHilbert]
    norm_num
  have hnuGroup : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (d.valueUnit (1 : Fin 4) / d.valueUnit (0 : Fin 4)) := by
    exact valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (0 : Fin 3) nu hnuAlpha hnuHilbert
  rcases exists_goodBONG_binaryTransformation_exact d (0 : Fin 3)
      nu hnuGroup with ⟨g, hgValues⟩
  have hnuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ d.valueUnit i) (fun i ↦ g.valueUnit i) :=
    ⟨0, nu, hnuGroup, hgValues⟩
  have hgFinal : (fun i ↦ g.valueUnit i) =
      ![a.valueUnit 0,
        U.epsilon * a.valueUnit 1,
        U.epsilon * U.eta * a.valueUnit 2,
        U.eta * a.valueUnit 3] := by
    rw [hgValues, hdValues]
    funext i
    fin_cases i <;>
      simp [beli2009BinaryTransformAt, nu, mul_assoc, mul_left_comm,
        mul_comm] <;> group <;>
      simp [zpow_neg_one, mul_assoc, mul_left_comm, mul_comm]
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ g.valueUnit i) :=
    N.reachable.trans (htailLift.trans hnuStep.reachable)
  let S : BONG.GoodBONG.Lemma92EarlyScalingData a U.epsilon U.eta := {
    transformed := g
    firstValue_eq := by simpa using congrFun hgFinal (0 : Fin 4)
    secondValue_eq := by simpa using congrFun hgFinal (1 : Fin 4)
    thirdValue_eq := by simpa using congrFun hgFinal (2 : Fin 4)
    fourthValue_eq := by simpa using congrFun hgFinal (3 : Fin 4)
  }
  have hscaledLast : BONG.GoodBONG.defectOrder (K := K)
      (-(U.epsilon * a.valueUnit (2 : Fin 4) *
        a.valueUnit (3 : Fin 4))) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have hproduct :
        -(U.epsilon * a.valueUnit (2 : Fin 4) *
            a.valueUnit (3 : Fin 4)) =
          U.epsilon * a.tail.adjacentProduct (1 : Fin 2) := by
      unfold BONG.GoodBONG.adjacentProduct
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul]
      simp
      ring
    have hlt : BONG.GoodBONG.defectOrder (K := K) U.epsilon <
        BONG.GoodBONG.defectOrder (K := K)
          (a.tail.adjacentProduct (1 : Fin 2)) := by
      rw [U.epsilon_defect]
      simpa only [BONG.GoodBONG.adjacentDefect] using
        D.lastAdjacent_gt_secondAlpha
    rw [hproduct,
      BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right hlt,
      U.epsilon_defect]
  have hbase : g.alphaValue (2 : Fin 3) =
      g.tail.alphaValue (1 : Fin 2) := by
    apply BONG.GoodBONG.alphaValue_shift_eq_tail_of_invariant_nextAdjacentDefect
      (a := a) (c := g) (p := (1 : Fin 2))
    · exact D.thirdAlpha_recursion
    · change S.transformed.adjacentDefect (2 : Fin 3) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ)
      rw [S.adjacentDefect_two]
      exact hscaledLast
  let T : BONG.GoodBONG.Beli2019Lemma92Transform a := {
    transformed := g
    firstValue_eq := S.firstValue_eq
    laterAlpha_eq_tail := by
      intro i hi
      omega
    earlyAlpha_eq_tail := by
      intro _
      exact (a.alpha_invariant g (2 : Fin 3)).trans hbase
  }
  exact ⟨{
    transform := T
    reachable := hreach
  }⟩

/-! ## Lifting the exact ternary negative bridge to rank four -/

/-- The exact four-step bridge on the initial ternary segment lifts to a
rank-four path by appending the unchanged fourth coefficient.  All depth
and Hilbert hypotheses are the literal hypotheses of the ternary bridge. -/
theorem reachable_rankFour_initialThree_fourStep_scaling_of_dynamic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (epsilon : valuationUnitSubgroup K)
    (hepsilonFirst : hilbertSymbol K (epsilon : Kˣ)
      (a.lemma814InitialThree.adjacentProduct (0 : Fin 2)) = -1)
    (eta theta mu : valuationUnitSubgroup K)
    (hetaLast : hilbertSymbol K (eta : Kˣ)
      (a.lemma814InitialThree.adjacentProduct (1 : Fin 2)) = -1)
    (hetaEpsilon : hilbertSymbol K (eta : Kˣ)
      (epsilon : Kˣ) = 1)
    (hthetaAlpha : a.lemma814InitialThree.adjacentBinaryAlpha
        (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.lemma814InitialThree.adjacentProduct (1 : Fin 2)) = 1)
    (hmuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a.lemma814InitialThree (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hkappaAlpha : rankThreeLastBinaryAlphaAfterLeftMultiplier
        a.lemma814InitialThree (mu : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((eta / theta : valuationUnitSubgroup K) : Kˣ)))
    (hmuCombined : hilbertSymbol K
      ((eta : Kˣ) *
        a.lemma814InitialThree.adjacentProduct (0 : Fin 2))
      (mu : Kˣ) = -1)
    (hbridge : hilbertSymbol K (theta : Kˣ) (mu : Kˣ) =
      hilbertSymbol K
        (a.lemma814InitialThree.adjacentProduct (0 : Fin 2))
        (mu : Kˣ))
    (hnuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a.lemma814InitialThree (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / mu : valuationUnitSubgroup K) : Kˣ))) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i)
      ![(epsilon : Kˣ) * a.valueUnit 0,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1,
        (eta : Kˣ) * a.valueUnit 2,
        a.valueUnit 3] := by
  let s := a.lemma814InitialThree
  rcases exists_rankThree_fourStep_scaling_of_dynamic
      s epsilon hepsilonFirst eta theta mu hetaLast hetaEpsilon
        hthetaAlpha hthetaLast hmuAlpha hkappaAlpha hmuCombined hbridge
        hnuAlpha with
    ⟨c, hcValues, hlocal⟩
  let suffix : Fin 1 → Kˣ := fun _ => a.valueUnit (3 : Fin 4)
  have hlift := Beli2009BinaryReachable.appendSuffix suffix hlocal
  have hsource : appendSuffixValues (fun i => s.valueUnit i) suffix =
      (fun i => a.valueUnit i) := by
    funext i
    fin_cases i
    · change appendSuffixValues (fun i => s.valueUnit i) suffix
          (appendSuffixLeftIndex (S := 1) (0 : Fin 3)) = a.valueUnit 0
      rw [appendSuffixValues_castAdd]
      simpa [s] using a.lemma814InitialThree_valueUnit_eq (0 : Fin 3)
    · change appendSuffixValues (fun i => s.valueUnit i) suffix
          (appendSuffixLeftIndex (S := 1) (1 : Fin 3)) = a.valueUnit 1
      rw [appendSuffixValues_castAdd]
      simpa [s] using a.lemma814InitialThree_valueUnit_eq (1 : Fin 3)
    · change appendSuffixValues (fun i => s.valueUnit i) suffix
          (appendSuffixLeftIndex (S := 1) (2 : Fin 3)) = a.valueUnit 2
      rw [appendSuffixValues_castAdd]
      simpa [s] using a.lemma814InitialThree_valueUnit_eq (2 : Fin 3)
    · change appendSuffixValues (fun i => s.valueUnit i) suffix
          (appendSuffixIndex (N := 2) (0 : Fin 1)) = a.valueUnit 3
      rw [appendSuffixValues_appendSuffixIndex]
  have htarget : appendSuffixValues (fun i => c.valueUnit i) suffix =
      ![(epsilon : Kˣ) * a.valueUnit 0,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1,
        (eta : Kˣ) * a.valueUnit 2,
        a.valueUnit 3] := by
    rw [hcValues]
    funext i
    fin_cases i
    · change appendSuffixValues
          ![(epsilon : Kˣ) * s.valueUnit 0,
            (epsilon : Kˣ) * (eta : Kˣ) * s.valueUnit 1,
            (eta : Kˣ) * s.valueUnit 2] suffix
          (appendSuffixLeftIndex (S := 1) (0 : Fin 3)) =
            (epsilon : Kˣ) * a.valueUnit 0
      rw [appendSuffixValues_castAdd]
      simpa [s] using congrArg ((epsilon : Kˣ) * ·)
        (a.lemma814InitialThree_valueUnit_eq (0 : Fin 3))
    · change appendSuffixValues
          ![(epsilon : Kˣ) * s.valueUnit 0,
            (epsilon : Kˣ) * (eta : Kˣ) * s.valueUnit 1,
            (eta : Kˣ) * s.valueUnit 2] suffix
          (appendSuffixLeftIndex (S := 1) (1 : Fin 3)) =
            (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1
      rw [appendSuffixValues_castAdd]
      simpa [s, mul_assoc] using
        congrArg ((epsilon : Kˣ) * (eta : Kˣ) * ·)
          (a.lemma814InitialThree_valueUnit_eq (1 : Fin 3))
    · change appendSuffixValues
          ![(epsilon : Kˣ) * s.valueUnit 0,
            (epsilon : Kˣ) * (eta : Kˣ) * s.valueUnit 1,
            (eta : Kˣ) * s.valueUnit 2] suffix
          (appendSuffixLeftIndex (S := 1) (2 : Fin 3)) =
            (eta : Kˣ) * a.valueUnit 2
      rw [appendSuffixValues_castAdd]
      simpa [s] using congrArg ((eta : Kˣ) * ·)
        (a.lemma814InitialThree_valueUnit_eq (2 : Fin 3))
    · change appendSuffixValues
          ![(epsilon : Kˣ) * s.valueUnit 0,
            (epsilon : Kˣ) * (eta : Kˣ) * s.valueUnit 1,
            (eta : Kˣ) * s.valueUnit 2] suffix
          (appendSuffixIndex (N := 2) (0 : Fin 1)) = a.valueUnit 3
      rw [appendSuffixValues_appendSuffixIndex]
  rw [hsource, htarget] at hlift
  exact hlift

/-! ## Two simultaneous negative Hilbert characters -/

/-- At a prescribed nonzero valuation-unit defect layer, two Hilbert
characters can be made negative simultaneously whenever each character is
individually nontrivial on that layer.  Choose a negative partner for the
first character.  If it is not already negative for the second, choose a
negative partner for the second; that partner either works itself or its
product with the first one works.  The defect-product inequality keeps the
product at least as deep as the reference layer. -/
theorem exists_valuationUnit_hilbert_both_neg_one_of_sums_le
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    (chi psi reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hchi : quadraticDefect K chi + quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hpsi : quadraticDefect K psi + quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ rho : valuationUnitSubgroup K,
      BONG.GoodBONG.defectOrder (K := K) reference ≤
          BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) ∧
        hilbertSymbol K chi (rho : Kˣ) = -1 ∧
        hilbertSymbol K psi (rho : Kˣ) = -1 := by
  have hrefNonzero : quadraticDefect K reference ≠ 0 :=
    quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
  rcases (BONG.beli2019Lemma82_i chi reference).2 hchi with
    ⟨x, hxDefect, hxChi⟩
  have hxNonzero : quadraticDefect K x ≠ 0 := by
    rw [hxDefect]
    exact hrefNonzero
  rcases BONG.exists_valuationUnit_same_defect_same_hilbert
      chi x hxNonzero with
    ⟨uRaw, huUnit, huDefectX, huChiX⟩
  let u : valuationUnitSubgroup K := ⟨uRaw, huUnit⟩
  have huDefect : quadraticDefect K uRaw =
      quadraticDefect K reference := huDefectX.trans hxDefect
  have huDepth : BONG.GoodBONG.defectOrder (K := K) uRaw =
      BONG.GoodBONG.defectOrder (K := K) reference :=
    BONG.defectOrder_eq_of_quadraticDefect_eq uRaw reference huDefect
  have huChi : hilbertSymbol K chi uRaw = -1 :=
    huChiX.trans hxChi
  rcases Int.units_eq_one_or (hilbertSymbol K psi uRaw) with
      huPsi | huPsi
  · rcases (BONG.beli2019Lemma82_i psi reference).2 hpsi with
      ⟨y, hyDefect, hyPsi⟩
    have hyNonzero : quadraticDefect K y ≠ 0 := by
      rw [hyDefect]
      exact hrefNonzero
    rcases BONG.exists_valuationUnit_same_defect_same_hilbert
        psi y hyNonzero with
      ⟨vRaw, hvUnit, hvDefectY, hvPsiY⟩
    let v : valuationUnitSubgroup K := ⟨vRaw, hvUnit⟩
    have hvDefect : quadraticDefect K vRaw =
        quadraticDefect K reference := hvDefectY.trans hyDefect
    have hvDepth : BONG.GoodBONG.defectOrder (K := K) vRaw =
        BONG.GoodBONG.defectOrder (K := K) reference :=
      BONG.defectOrder_eq_of_quadraticDefect_eq vRaw reference hvDefect
    have hvPsi : hilbertSymbol K psi vRaw = -1 :=
      hvPsiY.trans hyPsi
    rcases Int.units_eq_one_or (hilbertSymbol K chi vRaw) with
        hvChi | hvChi
    · let rho : valuationUnitSubgroup K := u * v
      refine ⟨rho, ?_, ?_, ?_⟩
      · have hmin : BONG.GoodBONG.defectOrder (K := K) reference ≤
            min (BONG.GoodBONG.defectOrder (K := K) uRaw)
              (BONG.GoodBONG.defectOrder (K := K) vRaw) := by
          apply le_min
          · rw [huDepth]
          · rw [hvDepth]
        exact hmin.trans
          (BONG.GoodBONG.defectOrder_mul_ge_min (K := K) uRaw vRaw)
      · change hilbertSymbol K chi (uRaw * vRaw) = -1
        rw [hilbertSymbol_mul_right, huChi, hvChi]
        norm_num
      · change hilbertSymbol K psi (uRaw * vRaw) = -1
        rw [hilbertSymbol_mul_right, huPsi, hvPsi]
        norm_num
    · refine ⟨v, ?_, ?_, ?_⟩
      · change BONG.GoodBONG.defectOrder (K := K) reference ≤
          BONG.GoodBONG.defectOrder (K := K) vRaw
        rw [hvDepth]
      · simpa only [v, Subgroup.coe_mk] using hvChi
      · simpa only [v, Subgroup.coe_mk] using hvPsi
  · refine ⟨u, ?_, ?_, ?_⟩
    · change BONG.GoodBONG.defectOrder (K := K) reference ≤
        BONG.GoodBONG.defectOrder (K := K) uRaw
      rw [huDepth]
    · simpa only [u, Subgroup.coe_mk] using huChi
    · simpa only [u, Subgroup.coe_mk] using huPsi

/-! ## Arithmetic and the first unit in the alternating rank-four branch -/

/-- In the alternating Lemma 9.2 branch the first and third alpha values
coincide. -/
theorem lemma92RankFourAlternatingData_firstAlpha_eq_thirdAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a) :
    a.alphaValue (0 : Fin 3) = a.alphaValue (2 : Fin 3) :=
  a.alpha_zero_eq_alpha_two_of_quaternaryAlternating D.alternating

/-- The first adjacent square class lies on the second-alpha defect layer.
This is the equality obtained by cancelling the finite first order gap from
the stored first-candidate identity. -/
theorem lemma92RankFourAlternatingData_firstAdjacentDefect_eq_secondAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a) :
    a.adjacentDefect (0 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
  have hshift := a.quaternaryAlternating_alpha_one_eq D.alternating
  apply WithTop.add_left_cancel WithTop.coe_ne_top
  calc
    (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
          a.adjacentDefect (0 : Fin 3) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) :=
      D.firstAlpha_candidate
    _ = (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      rw [← WithTop.coe_add]
      congr 1
      push_cast at hshift ⊢
      linarith

/-- The strict alpha-sum in the common data makes the first alternating
alpha strictly smaller than its literal half-gap. -/
theorem lemma92RankFourAlternatingData_firstAlpha_lt_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a) :
    a.alphaValue (0 : Fin 3) < a.halfGapValue (0 : Fin 3) := by
  have hshift := a.quaternaryAlternating_alpha_one_eq D.alternating
  have halpha := lemma92RankFourAlternatingData_firstAlpha_eq_thirdAlpha a D
  have hsum := D.secondThird_sum_lt_twoE
  rw [← halpha] at hsum
  unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap
  unfold BONG.GoodBONG.orderGap at hshift
  push_cast at hshift ⊢
  linarith

/-- Consequently the literal first binary alpha is already the global first
alpha. -/
theorem lemma92RankFourAlternatingData_firstBinaryAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a) :
    a.adjacentBinaryAlpha (0 : Fin 3) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
  unfold BONG.GoodBONG.adjacentBinaryAlpha
    BONG.GoodBONG.leftDefectCandidate
  change min (a.halfGapCandidate (0 : Fin 3))
      (((((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
        a.adjacentDefect (0 : Fin 3))) =
    (a.alphaValue (0 : Fin 3) : WithTop ℚ)
  rw [D.firstAlpha_candidate]
  apply min_eq_right
  rw [← a.coe_halfGapValue]
  exact_mod_cast
    (lemma92RankFourAlternatingData_firstAlpha_lt_halfGap a D).le

/-- A first scaling unit adapted to the alternating collision.  Besides the
usual ternary unit certificate, its product with the first adjacent square
class stays on the second-alpha layer; this is what makes the final return
move of the rank-four braid legal. -/
structure Lemma92RankFourAlternatingUnitChoiceData
    (a : BONG.GoodBONG q L 4) where
  epsilon : valuationUnitSubgroup K
  epsilonDefect : BONG.GoodBONG.defectOrder (K := K)
      (epsilon : Kˣ) = (a.alphaValue (1 : Fin 3) : WithTop ℚ)
  epsilonFirstProductDefect : BONG.GoodBONG.defectOrder (K := K)
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3)) =
    (a.alphaValue (1 : Fin 3) : WithTop ℚ)
  choice : BONG.GoodBONG.Lemma92TernaryUnitChoiceData a.tail
    (a.alphaValue (1 : Fin 3)) (a.alphaValue (2 : Fin 3))
  choiceEpsilon : choice.epsilon = (epsilon : Kˣ)

/-- Lemma 8.1 chooses the first unit without cancelling the equal first
adjacent defect.  The fixed-epsilon form of Lemma 8.2 then chooses the final
unit with the Hasse sign required in Lemma 9.2. -/
theorem exists_lemma92RankFourAlternatingUnitChoiceData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a) :
    Nonempty (Lemma92RankFourAlternatingUnitChoiceData a) := by
  let A₀ := a.adjacentProduct (0 : Fin 3)
  have hA₀Defect : BONG.GoodBONG.defectOrder (K := K) A₀ =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    simpa only [A₀, BONG.GoodBONG.adjacentDefect] using
      lemma92RankFourAlternatingData_firstAdjacentDefect_eq_secondAlpha a D
  have hsecondPos : 0 < a.alphaValue (1 : Fin 3) :=
    BONG.GoodBONG.oddRationalInteger_pos_of_nonnegative
      D.secondAlpha_odd D.secondAlpha_nonnegative
  have hA₀Finite : quadraticDefect K A₀ ≠ ⊤ :=
    BONG.GoodBONG.quadraticDefect_ne_top_of_defectOrder_eq_coe
      A₀ (a.alphaValue (1 : Fin 3)) hA₀Defect
  have hA₀Nonzero : quadraticDefect K A₀ ≠ 0 := by
    intro hzero
    have hraw : BONG.GoodBONG.defectOrder (K := K) A₀ = 0 := by
      unfold BONG.GoodBONG.defectOrder
      rw [hzero]
      rfl
    rw [hA₀Defect] at hraw
    norm_cast at hraw
    linarith
  have hA₀OrderLt : BONG.GoodBONG.defectOrder (K := K) A₀ <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hA₀Defect]
    exact_mod_cast D.secondAlpha_lt_twoE
  have hA₀NotTwoE : quadraticDefect K A₀ ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    quadraticDefect_ne_twoE_of_defectOrder_lt_twoE A₀ hA₀OrderLt
  rcases BONG.beli2019Lemma81_i hres A₀ hA₀Nonzero hA₀NotTwoE with
    ⟨w, hwDefect, hA₀wDefect⟩
  have hwNonzero : quadraticDefect K w ≠ 0 := by
    rw [hwDefect]
    exact hA₀Nonzero
  have hwEven : Even (ordUnit K w) := by
    rcases Int.even_or_odd (ordUnit K w) with heven | hodd
    · exact heven
    · exact (hwNonzero
        (quadraticDefect_eq_zero_of_odd_ordUnit w hodd)).elim
  rcases BONG.GoodBONG.exists_valuationUnit_eq_mul_square_of_even_order
      w hwEven with ⟨epsilonRaw, s, hepsilonUnit, hepsilonFactor⟩
  let epsilon : valuationUnitSubgroup K :=
    ⟨epsilonRaw, hepsilonUnit⟩
  have hepsilonQuadratic : quadraticDefect K epsilonRaw =
      quadraticDefect K A₀ := by
    rw [hepsilonFactor, quadraticDefect_mul_square, hwDefect]
  have hepsilonDefect : BONG.GoodBONG.defectOrder (K := K)
      (epsilon : Kˣ) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    change BONG.GoodBONG.defectOrder (K := K) epsilonRaw = _
    exact (BONG.defectOrder_eq_of_quadraticDefect_eq
      epsilonRaw A₀ hepsilonQuadratic).trans hA₀Defect
  have hepsilonA₀Quadratic : quadraticDefect K (epsilonRaw * A₀) =
      quadraticDefect K A₀ := by
    rw [hepsilonFactor]
    have hfactor : (w * s ^ 2) * A₀ = (A₀ * w) * s ^ 2 := by ac_rfl
    rw [hfactor, quadraticDefect_mul_square, hA₀wDefect]
  have hepsilonA₀Defect : BONG.GoodBONG.defectOrder (K := K)
      ((epsilon : Kˣ) * A₀) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    change BONG.GoodBONG.defectOrder (K := K) (epsilonRaw * A₀) = _
    exact (BONG.defectOrder_eq_of_quadraticDefect_eq
      (epsilonRaw * A₀) A₀ hepsilonA₀Quadratic).trans hA₀Defect
  rcases exists_lemma92TernaryUnitChoiceData_of_fixedEpsilon
      a.tail (a.alphaValue (1 : Fin 3)) (a.alphaValue (2 : Fin 3))
        epsilon hepsilonDefect D.thirdAlpha_odd
        D.thirdAlpha_nonnegative D.thirdAlpha_lt_twoE
        D.lastAdjacent_gt_secondAlpha D.secondThird_sum_lt_twoE with
    ⟨U, hUepsilon⟩
  exact ⟨{
    epsilon := epsilon
    epsilonDefect := hepsilonDefect
    epsilonFirstProductDefect := by
      simpa only [A₀] using hepsilonA₀Defect
    choice := U
    choiceEpsilon := hUepsilon
  }⟩

/-- Normalize the middle adjacent square class to the first-alpha layer
while pairing positively with a prescribed character.  This is the
alternating analogue of the first-multiplier construction in the strict
rank-four branch. -/
theorem lemma92RankFourAlternatingData_exists_middleMultiplier
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a)
    (z : Kˣ) :
    ∃ mu : valuationUnitSubgroup K,
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) ∧
        BONG.GoodBONG.defectOrder (K := K)
            ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3)) =
          (a.alphaValue (0 : Fin 3) : WithTop ℚ) ∧
        hilbertSymbol K z (mu : Kˣ) = 1 := by
  let A₁ := a.adjacentProduct (1 : Fin 3)
  have halpha := lemma92RankFourAlternatingData_firstAlpha_eq_thirdAlpha a D
  have hfirstOdd : IsOddRationalInteger (a.alphaValue (0 : Fin 3)) := by
    rw [halpha]
    exact D.thirdAlpha_odd
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 3) := by
    rw [halpha]
    exact D.thirdAlpha_nonnegative
  have hfirstLtTwoE : a.alphaValue (0 : Fin 3) <
      2 * (ramificationIndex K : ℚ) := by
    rw [halpha]
    exact D.thirdAlpha_lt_twoE
  rcases BONG.DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (0 : Fin 3)) hfirstOdd hfirstNonnegative
        hfirstLtTwoE with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hA₁Le : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) A₁ := by
    simpa only [A₁, BONG.GoodBONG.adjacentDefect] using
      a.quaternaryAlternating_middleAdjacentDefectBound D.alternating
  by_cases hA₁Eq : BONG.GoodBONG.defectOrder (K := K) A₁ =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ)
  · have hA₁Reference : BONG.GoodBONG.defectOrder (K := K) A₁ =
        BONG.GoodBONG.defectOrder (K := K) reference := by
      rw [hA₁Eq, hrefDefect]
    have hA₁Quadratic : quadraticDefect K A₁ =
        quadraticDefect K reference :=
      BONG.GoodBONG.quadraticDefect_eq_of_defectOrder_eq
        A₁ reference hA₁Reference
    have hA₁Finite : quadraticDefect K A₁ ≠ ⊤ := by
      rw [hA₁Quadratic]
      exact BONG.GoodBONG.quadraticDefect_ne_top_of_defectOrder_eq_coe
        reference (a.alphaValue (0 : Fin 3)) hrefDefect
    have hA₁Nonzero : quadraticDefect K A₁ ≠ 0 := by
      rw [hA₁Quadratic]
      exact quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
    have hA₁OrderLt : BONG.GoodBONG.defectOrder (K := K) A₁ <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hA₁Eq]
      exact_mod_cast hfirstLtTwoE
    have hA₁NotTwoE : quadraticDefect K A₁ ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_ne_twoE_of_defectOrder_lt_twoE A₁ hA₁OrderLt
    rcases exists_valuationUnit_product_preserving_hilbert_one_of_largeResidue
        hres z A₁ hA₁Finite hA₁Nonzero hA₁NotTwoE with
      ⟨mu, hA₁Mu, hproduct, hhilbert⟩
    have hmap : Monotone
        (WithTop.map (fun n : Nat ↦ (n : ℚ))) :=
      WithTop.monotone_map_iff.mpr (by
        intro m n hmn
        change (m : ℚ) ≤ (n : ℚ)
        exact_mod_cast hmn)
    have hdepth : BONG.GoodBONG.defectOrder (K := K) A₁ ≤
        BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
      unfold BONG.GoodBONG.defectOrder
      exact hmap hA₁Mu
    refine ⟨mu, hA₁Eq ▸ hdepth, ?_, hhilbert⟩
    have hproduct' : quadraticDefect K ((mu : Kˣ) * A₁) =
        quadraticDefect K A₁ := by
      simpa only [mul_comm] using hproduct
    exact (BONG.defectOrder_eq_of_quadraticDefect_eq
      ((mu : Kˣ) * A₁) A₁ hproduct').trans hA₁Eq
  · have hfirstLtA₁ : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
        BONG.GoodBONG.defectOrder (K := K) A₁ :=
      lt_of_le_of_ne hA₁Le (Ne.symm hA₁Eq)
    have hrefOrderLt : BONG.GoodBONG.defectOrder (K := K) reference <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hrefDefect]
      exact_mod_cast hfirstLtTwoE
    have hrefNonzero : quadraticDefect K reference ≠ 0 :=
      quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
    have hrefNotTwoE : quadraticDefect K reference ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_ne_twoE_of_defectOrder_lt_twoE reference hrefOrderLt
    have hnotPair : ¬BONG.IsZeroTwoEDefectPair (K := K) z reference := by
      rintro (⟨_, hrefEndpoint⟩ | ⟨_, hrefZero⟩)
      · exact hrefNotTwoE hrefEndpoint
      · exact hrefNonzero hrefZero
    rcases BONG.beli2019Lemma82_ii_unit hres z reference hrefUnit hnotPair with
      ⟨muRaw, hmuUnit, hmuQuadratic, hmuHilbert⟩
    let mu : valuationUnitSubgroup K := ⟨muRaw, hmuUnit⟩
    have hmuOrder : BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
      change BONG.GoodBONG.defectOrder (K := K) muRaw = _
      exact (BONG.defectOrder_eq_of_quadraticDefect_eq
        muRaw reference hmuQuadratic).trans hrefDefect
    refine ⟨mu, hmuOrder.ge, ?_, ?_⟩
    · change BONG.GoodBONG.defectOrder (K := K) (muRaw * A₁) = _
      exact (BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right
        (hmuOrder ▸ hfirstLtA₁)).trans hmuOrder
    · simpa only [mu, Subgroup.coe_mk] using hmuHilbert

/-- The complementary depth `2e-x` of a positive odd interior unit-defect
depth is again a positive odd interior unit-defect depth. -/
theorem exists_valuationUnit_of_complementary_odd_defect
    [BONG.DyadicUnitDefectSpectrumLaws K]
    (x : ℚ) (hxOdd : IsOddRationalInteger x)
    (hxPos : 0 < x)
    (hxLt : x < 2 * (ramificationIndex K : ℚ)) :
    ∃ reference : Kˣ,
      IsValuationUnit K (reference : K) ∧
        BONG.GoodBONG.defectOrder (K := K) reference =
          ((2 * (ramificationIndex K : ℚ) - x : ℚ) : WithTop ℚ) := by
  have hcompOdd : IsOddRationalInteger
      (2 * (ramificationIndex K : ℚ) - x) := by
    rcases hxOdd with ⟨z, hzOdd, hz⟩
    refine ⟨2 * (ramificationIndex K : Int) - z,
      (even_two_mul (ramificationIndex K : Int)).sub_odd hzOdd, ?_⟩
    push_cast at hz ⊢
    linarith
  have hcompNonnegative :
      0 ≤ 2 * (ramificationIndex K : ℚ) - x := by linarith
  have hcompLt : 2 * (ramificationIndex K : ℚ) - x <
      2 * (ramificationIndex K : ℚ) := by linarith
  exact BONG.DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
    (2 * (ramificationIndex K : ℚ) - x) hcompOdd
      hcompNonnegative hcompLt

/-- The head multiplier used by the alternating rank-four braid.  It
normalizes the middle adjacent product to the first-alpha layer and pairs
positively with both the first adjacent product and the selected `epsilon`.
-/
structure Lemma92RankFourAlternatingFirstMultiplierData
    (a : BONG.GoodBONG q L 4)
    (C : Lemma92RankFourAlternatingUnitChoiceData a) where
  mu : valuationUnitSubgroup K
  muDepth : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
    BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ)
  muMiddleProduct : BONG.GoodBONG.defectOrder (K := K)
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3)) =
    (a.alphaValue (0 : Fin 3) : WithTop ℚ)
  muFirstHilbert : hilbertSymbol K
    (a.adjacentProduct (0 : Fin 3)) (mu : Kˣ) = 1
  muEpsilonHilbert : hilbertSymbol K (C.epsilon : Kˣ)
    (mu : Kˣ) = 1

/-- First choose a middle normalizer positive against the product of the two
required characters.  Its two signs are therefore equal.  If both signs are
negative, a simultaneous negative partner at complementary depth flips both
signs without changing either exact first-alpha defect equality. -/
theorem exists_lemma92RankFourAlternatingFirstMultiplierData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a)
    (C : Lemma92RankFourAlternatingUnitChoiceData a) :
    Nonempty (Lemma92RankFourAlternatingFirstMultiplierData a C) := by
  let A₀ := a.adjacentProduct (0 : Fin 3)
  let A₁ := a.adjacentProduct (1 : Fin 3)
  rcases lemma92RankFourAlternatingData_exists_middleMultiplier
      hres a D (A₀ * (C.epsilon : Kˣ)) with
    ⟨mu₀, hmu₀Depth, hmu₀Middle, hmu₀Character⟩
  have hcharacter : hilbertSymbol K A₀ (mu₀ : Kˣ) *
      hilbertSymbol K (C.epsilon : Kˣ) (mu₀ : Kˣ) = 1 := by
    simpa only [hilbertSymbol_mul_left] using hmu₀Character
  rcases Int.units_eq_one_or (hilbertSymbol K A₀ (mu₀ : Kˣ)) with
      hmu₀First | hmu₀First <;>
    rcases Int.units_eq_one_or
      (hilbertSymbol K (C.epsilon : Kˣ) (mu₀ : Kˣ)) with
      hmu₀Epsilon | hmu₀Epsilon
  · exact ⟨{
      mu := mu₀
      muDepth := hmu₀Depth
      muMiddleProduct := by simpa only [A₁] using hmu₀Middle
      muFirstHilbert := by simpa only [A₀] using hmu₀First
      muEpsilonHilbert := hmu₀Epsilon
    }⟩
  · rw [hmu₀First, hmu₀Epsilon] at hcharacter
    norm_num at hcharacter
  · rw [hmu₀First, hmu₀Epsilon] at hcharacter
    norm_num at hcharacter
  · have halpha :=
      lemma92RankFourAlternatingData_firstAlpha_eq_thirdAlpha a D
    have hsecondPos : 0 < a.alphaValue (1 : Fin 3) :=
      BONG.GoodBONG.oddRationalInteger_pos_of_nonnegative
        D.secondAlpha_odd D.secondAlpha_nonnegative
    rcases exists_valuationUnit_of_complementary_odd_defect
        (a.alphaValue (1 : Fin 3)) D.secondAlpha_odd hsecondPos
          D.secondAlpha_lt_twoE with
      ⟨reference, hrefUnit, hrefDefect⟩
    have hsum : a.alphaValue (1 : Fin 3) +
        a.alphaValue (0 : Fin 3) <
          2 * (ramificationIndex K : ℚ) := by
      rw [halpha]
      exact D.secondThird_sum_lt_twoE
    have hrefGtFirst :
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
          BONG.GoodBONG.defectOrder (K := K) reference := by
      rw [hrefDefect]
      exact_mod_cast (show a.alphaValue (0 : Fin 3) <
          2 * (ramificationIndex K : ℚ) -
            a.alphaValue (1 : Fin 3) by linarith)
    have hA₀Defect : BONG.GoodBONG.defectOrder (K := K) A₀ =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      simpa only [A₀, BONG.GoodBONG.adjacentDefect] using
        lemma92RankFourAlternatingData_firstAdjacentDefect_eq_secondAlpha a D
    have hA₀OrderSum : BONG.GoodBONG.defectOrder (K := K) A₀ +
          BONG.GoodBONG.defectOrder (K := K) reference ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hA₀Defect, hrefDefect]
      exact_mod_cast (show a.alphaValue (1 : Fin 3) +
          (2 * (ramificationIndex K : ℚ) -
            a.alphaValue (1 : Fin 3)) ≤
          2 * (ramificationIndex K : ℚ) by linarith)
    have hepsilonOrderSum : BONG.GoodBONG.defectOrder (K := K)
          (C.epsilon : Kˣ) +
          BONG.GoodBONG.defectOrder (K := K) reference ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [C.epsilonDefect, hrefDefect]
      exact_mod_cast (show a.alphaValue (1 : Fin 3) +
          (2 * (ramificationIndex K : ℚ) -
            a.alphaValue (1 : Fin 3)) ≤
          2 * (ramificationIndex K : ℚ) by linarith)
    have hA₀Sum : quadraticDefect K A₀ +
          quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
        A₀ reference hA₀OrderSum
    have hepsilonSum : quadraticDefect K (C.epsilon : Kˣ) +
          quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
        (C.epsilon : Kˣ) reference hepsilonOrderSum
    rcases exists_valuationUnit_hilbert_both_neg_one_of_sums_le
        A₀ (C.epsilon : Kˣ) reference hrefUnit hA₀Sum hepsilonSum with
      ⟨rho, hrhoDepth, hrhoFirst, hrhoEpsilon⟩
    let mu : valuationUnitSubgroup K := mu₀ * rho
    have hrhoGtFirst :
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
          BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) :=
      hrefGtFirst.trans_le hrhoDepth
    have hmuDepth : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
      have hmin : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
          min (BONG.GoodBONG.defectOrder (K := K) (mu₀ : Kˣ))
            (BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ)) :=
        le_min hmu₀Depth hrhoGtFirst.le
      exact hmin.trans
        (BONG.GoodBONG.defectOrder_mul_ge_min
          (K := K) (mu₀ : Kˣ) (rho : Kˣ))
    have hmuMiddle : BONG.GoodBONG.defectOrder (K := K)
        ((mu : Kˣ) * A₁) =
          (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
      have hfactor : (mu : Kˣ) * A₁ =
          (rho : Kˣ) * ((mu₀ : Kˣ) * A₁) := by
        dsimp only [mu]
        ac_rfl
      rw [hfactor,
        BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
          (hmu₀Middle ▸ hrhoGtFirst), hmu₀Middle]
    refine ⟨{
      mu := mu
      muDepth := hmuDepth
      muMiddleProduct := by simpa only [A₁] using hmuMiddle
      muFirstHilbert := ?_
      muEpsilonHilbert := ?_
    }⟩
    · change hilbertSymbol K A₀ ((mu₀ : Kˣ) * (rho : Kˣ)) = 1
      rw [hilbertSymbol_mul_right, hmu₀First, hrhoFirst]
      norm_num
    · change hilbertSymbol K (C.epsilon : Kˣ)
        ((mu₀ : Kˣ) * (rho : Kˣ)) = 1
      rw [hilbertSymbol_mul_right, hmu₀Epsilon, hrhoEpsilon]
      norm_num

/-- Complete adjacent-binary realization of the exact rank-four scaling in
the alternating branch of Lemma 9.2.  The positive middle Hilbert sign uses
`theta = epsilon`.  In the negative sign, a simultaneous negative partner
at complementary first-alpha depth is multiplied into `theta`; it is deep
enough to preserve both second-alpha defects and to make the return middle
move automatic from its half-gap term. -/
theorem reachableLemma92_rankFourAlternating_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a) :
    ∃ C : Lemma92RankFourAlternatingUnitChoiceData a,
      Beli2009BinaryReachable (K := K)
        (fun i => a.valueUnit i)
        ![a.valueUnit 0,
          C.choice.epsilon * a.valueUnit 1,
          C.choice.epsilon * C.choice.eta * a.valueUnit 2,
          C.choice.eta * a.valueUnit 3] := by
  rcases exists_lemma92RankFourAlternatingUnitChoiceData hres a D with
    ⟨C⟩
  rcases exists_lemma92RankFourAlternatingFirstMultiplierData
      hres a D C with ⟨M⟩
  let epsilon : valuationUnitSubgroup K := C.epsilon
  let eta : valuationUnitSubgroup K :=
    ⟨C.choice.eta, C.choice.eta_isValuationUnit⟩
  have halpha :=
    lemma92RankFourAlternatingData_firstAlpha_eq_thirdAlpha a D
  have hsum : a.alphaValue (1 : Fin 3) +
      a.alphaValue (0 : Fin 3) <
        2 * (ramificationIndex K : ℚ) := by
    rw [halpha]
    exact D.secondThird_sum_lt_twoE
  have hgapShift :=
    a.quaternaryAlternating_alpha_one_eq D.alternating
  have hsecondTop :
      (((a.orderGap (1 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue (0 : Fin 3) : WithTop ℚ) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun x : ℚ => (x : WithTop ℚ)) (by
      rw [a.quaternaryAlternating_orderGap_one_eq_neg_zero D.alternating]
      push_cast at hgapShift ⊢
      linarith)
  have hthirdTop :
      (((a.orderGap (2 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun x : ℚ => (x : WithTop ℚ))
      D.thirdAlpha_recursion.symm
  have hfirstTop :
      (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun x : ℚ => (x : WithTop ℚ)) (by
      push_cast at hgapShift ⊢
      linarith)
  unfold BONG.GoodBONG.orderGap at hsecondTop hthirdTop hfirstTop
  have hepsilonA₂ : BONG.GoodBONG.defectOrder (K := K)
      ((epsilon : Kˣ) * a.adjacentProduct (2 : Fin 3)) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have htailProduct : a.tail.adjacentProduct (1 : Fin 2) =
        a.adjacentProduct (2 : Fin 3) := by
      rw [a.adjacentProduct_tail]
      congr 1
    change BONG.GoodBONG.defectOrder (K := K)
        ((C.epsilon : Kˣ) * a.adjacentProduct (2 : Fin 3)) = _
    rw [← htailProduct, ← C.choiceEpsilon]
    exact C.choice.scaledLastAdjacent_defect
  have hchoice : hilbertSymbol K
        ((epsilon : Kˣ) * a.adjacentProduct (2 : Fin 3))
        (eta : Kˣ) =
      hilbertSymbol K (epsilon : Kˣ)
        (a.adjacentProduct (1 : Fin 3)) := by
    have htailZero : a.tail.adjacentProduct (0 : Fin 2) =
        a.adjacentProduct (1 : Fin 3) := by
      rw [a.adjacentProduct_tail]
      congr 1
    have htailOne : a.tail.adjacentProduct (1 : Fin 2) =
        a.adjacentProduct (2 : Fin 3) := by
      rw [a.adjacentProduct_tail]
      congr 1
    change hilbertSymbol K
        ((C.epsilon : Kˣ) * a.adjacentProduct (2 : Fin 3))
          C.choice.eta =
      hilbertSymbol K (C.epsilon : Kˣ)
        (a.adjacentProduct (1 : Fin 3))
    rw [← htailZero, ← htailOne, ← C.choiceEpsilon]
    exact C.choice.hilbert_choice
  have hmuAlpha : a.adjacentBinaryAlpha (0 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K) (M.mu : Kˣ) := by
    rw [lemma92RankFourAlternatingData_firstBinaryAlpha_eq a D]
    exact M.muDepth
  have hetaDepth : (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
    change _ ≤ BONG.GoodBONG.defectOrder (K := K) C.choice.eta
    rw [C.choice.eta_defect]
  have hnuAlpha : rankFourFirstBinaryAlphaAfterRightMultiplier
      a (epsilon : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) ((M.mu : Kˣ)⁻¹) := by
    have hmuInvDepth : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) ((M.mu : Kˣ)⁻¹) := by
      rw [BONG.GoodBONG.defectOrder_inv]
      exact M.muDepth
    unfold rankFourFirstBinaryAlphaAfterRightMultiplier
    refine (min_le_right _ _).trans ?_
    rw [show BONG.GoodBONG.defectOrder (K := K)
        ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3)) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) by
      simpa only [epsilon] using C.epsilonFirstProductDefect,
      hfirstTop]
    exact hmuInvDepth
  have hnuHilbert : hilbertSymbol K
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3))
      ((M.mu : Kˣ)⁻¹) = 1 := by
    exact hilbertSymbol_fiveStep_outer_closure
      (a.adjacentProduct (0 : Fin 3)) (M.mu : Kˣ) (epsilon : Kˣ)
      M.muFirstHilbert (by simpa only [epsilon] using M.muEpsilonHilbert)
  have finish (theta : valuationUnitSubgroup K)
      (hthetaDepth : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
      (hthetaA₂ : BONG.GoodBONG.defectOrder (K := K)
          ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ))
      (hthetaMiddle : hilbertSymbol K
          ((M.mu : Kˣ) * a.adjacentProduct (1 : Fin 3))
          (theta : Kˣ) = 1)
      (hthetaEta : hilbertSymbol K
          ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3))
          (eta : Kˣ) = 1)
      (hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
          a (M.mu : Kˣ) (eta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K)
          (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)))
      (hkappaHilbert : hilbertSymbol K
          (((M.mu : Kˣ) * (eta : Kˣ)) *
            a.adjacentProduct (1 : Fin 3))
          (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) = 1) :
      Beli2009BinaryReachable (K := K)
        (fun i => a.valueUnit i)
        ![a.valueUnit 0,
          C.choice.epsilon * a.valueUnit 1,
          C.choice.epsilon * C.choice.eta * a.valueUnit 2,
          C.choice.eta * a.valueUnit 3] := by
    have hthetaAlpha : rankFourSecondBinaryAlphaAfterFirstMultiplier
        a (M.mu : Kˣ) ≤
          BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
      refine (min_le_right _ _).trans ?_
      rw [M.muMiddleProduct, hsecondTop]
      exact hthetaDepth
    have hetaAlpha : rankFourThirdBinaryAlphaAfterSecondMultiplier
        a (theta : Kˣ) ≤
          BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
      refine (min_le_right _ _).trans ?_
      rw [hthetaA₂, hthirdTop]
      exact hetaDepth
    have hreach := reachable_rankFour_fiveStep_scaling_of_dynamic
      a M.mu theta eta epsilon hmuAlpha M.muFirstHilbert
        hthetaAlpha hthetaMiddle hetaAlpha hthetaEta
        hkappaAlpha hkappaHilbert hnuAlpha hnuHilbert
    simpa only [epsilon, eta, C.choiceEpsilon, Subgroup.coe_mk] using hreach
  rcases Int.units_eq_one_or
      (hilbertSymbol K (epsilon : Kˣ)
        (a.adjacentProduct (1 : Fin 3))) with hpositive | hnegative
  · let theta : valuationUnitSubgroup K := epsilon
    have hthetaDepth : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
      rw [show BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) by
        simpa only [theta, epsilon] using C.epsilonDefect]
    have hthetaA₂ : BONG.GoodBONG.defectOrder (K := K)
        ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      simpa only [theta] using hepsilonA₂
    have hthetaMiddle : hilbertSymbol K
        ((M.mu : Kˣ) * a.adjacentProduct (1 : Fin 3))
        (theta : Kˣ) = 1 := by
      have hmuTheta : hilbertSymbol K (theta : Kˣ) (M.mu : Kˣ) = 1 := by
        simpa only [theta, epsilon] using M.muEpsilonHilbert
      have hthetaMiddleSource : hilbertSymbol K
          (theta : Kˣ) (a.adjacentProduct (1 : Fin 3)) = 1 := by
        simpa only [theta] using hpositive
      rw [hilbertSymbol_mul_left,
        hilbertSymbol_comm K (M.mu : Kˣ) (theta : Kˣ), hmuTheta,
        hilbertSymbol_comm K (a.adjacentProduct (1 : Fin 3))
          (theta : Kˣ), hthetaMiddleSource]
      norm_num
    have hthetaEta : hilbertSymbol K
        ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3))
        (eta : Kˣ) = 1 := by
      rw [show hilbertSymbol K
          ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3))
            (eta : Kˣ) =
          hilbertSymbol K (epsilon : Kˣ)
            (a.adjacentProduct (1 : Fin 3)) by
        simpa only [theta] using hchoice,
        hpositive]
    have hkappaOne :
        ((epsilon / theta : valuationUnitSubgroup K) : Kˣ) = 1 := by
      change (((epsilon / epsilon : valuationUnitSubgroup K) : Kˣ)) = 1
      simpa using congrArg
        (fun x : valuationUnitSubgroup K => (x : Kˣ))
        (div_self epsilon)
    have hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
          a (M.mu : Kˣ) (eta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K)
          (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) := by
      rw [hkappaOne, BONG.GoodBONG.defectOrder_one]
      exact le_top
    have hkappaHilbert : hilbertSymbol K
        (((M.mu : Kˣ) * (eta : Kˣ)) *
          a.adjacentProduct (1 : Fin 3))
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) = 1 := by
      rw [hkappaOne]
      exact hilbertSymbol_one_right (K := K) _
    exact ⟨C, finish theta hthetaDepth hthetaA₂ hthetaMiddle
      hthetaEta hkappaAlpha hkappaHilbert⟩
  · have hfirstPos : 0 < a.alphaValue (0 : Fin 3) := by
      rw [halpha]
      exact BONG.GoodBONG.oddRationalInteger_pos_of_nonnegative
        D.thirdAlpha_odd D.thirdAlpha_nonnegative
    have hfirstOdd : IsOddRationalInteger
        (a.alphaValue (0 : Fin 3)) := by
      rw [halpha]
      exact D.thirdAlpha_odd
    have hfirstLt : a.alphaValue (0 : Fin 3) <
        2 * (ramificationIndex K : ℚ) := by
      rw [halpha]
      exact D.thirdAlpha_lt_twoE
    rcases exists_valuationUnit_of_complementary_odd_defect
        (a.alphaValue (0 : Fin 3)) hfirstOdd hfirstPos hfirstLt with
      ⟨reference, hrefUnit, hrefDefect⟩
    have hrefGtSecond :
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
          BONG.GoodBONG.defectOrder (K := K) reference := by
      rw [hrefDefect]
      exact_mod_cast (show a.alphaValue (1 : Fin 3) <
          2 * (ramificationIndex K : ℚ) -
            a.alphaValue (0 : Fin 3) by linarith)
    let X : Kˣ := (M.mu : Kˣ) * a.adjacentProduct (1 : Fin 3)
    have hXDefect : BONG.GoodBONG.defectOrder (K := K) X =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
      simpa only [X] using M.muMiddleProduct
    have hetaDefect : BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
      change BONG.GoodBONG.defectOrder (K := K) C.choice.eta = _
      rw [C.choice.eta_defect, ← halpha]
    have hXOrderSum : BONG.GoodBONG.defectOrder (K := K) X +
          BONG.GoodBONG.defectOrder (K := K) reference ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hXDefect, hrefDefect]
      exact_mod_cast (show a.alphaValue (0 : Fin 3) +
          (2 * (ramificationIndex K : ℚ) -
            a.alphaValue (0 : Fin 3)) ≤
          2 * (ramificationIndex K : ℚ) by linarith)
    have hetaOrderSum : BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) +
          BONG.GoodBONG.defectOrder (K := K) reference ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hetaDefect, hrefDefect]
      exact_mod_cast (show a.alphaValue (0 : Fin 3) +
          (2 * (ramificationIndex K : ℚ) -
            a.alphaValue (0 : Fin 3)) ≤
          2 * (ramificationIndex K : ℚ) by linarith)
    have hXSum : quadraticDefect K X + quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
        X reference hXOrderSum
    have hetaSum : quadraticDefect K (eta : Kˣ) +
          quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
        (eta : Kˣ) reference hetaOrderSum
    rcases exists_valuationUnit_hilbert_both_neg_one_of_sums_le
        X (eta : Kˣ) reference hrefUnit hXSum hetaSum with
      ⟨rho, hrhoDepth, hrhoX, hrhoEta⟩
    have hrhoGtSecond :
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
          BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) :=
      hrefGtSecond.trans_le hrhoDepth
    let theta : valuationUnitSubgroup K := epsilon * rho
    have hthetaDepth : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
      have hthetaEq : BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
        change BONG.GoodBONG.defectOrder (K := K)
          ((epsilon : Kˣ) * (rho : Kˣ)) = _
        rw [BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right
          (by simpa only [epsilon, C.epsilonDefect] using hrhoGtSecond),
          show BONG.GoodBONG.defectOrder (K := K) (epsilon : Kˣ) =
            (a.alphaValue (1 : Fin 3) : WithTop ℚ) by
              simpa only [epsilon] using C.epsilonDefect]
      rw [hthetaEq]
    have hthetaA₂ : BONG.GoodBONG.defectOrder (K := K)
        ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      have hfactor : (theta : Kˣ) * a.adjacentProduct (2 : Fin 3) =
          (rho : Kˣ) *
            ((epsilon : Kˣ) * a.adjacentProduct (2 : Fin 3)) := by
        change ((epsilon : Kˣ) * (rho : Kˣ)) *
            a.adjacentProduct (2 : Fin 3) = _
        ac_rfl
      rw [hfactor,
        BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
          (hepsilonA₂ ▸ hrhoGtSecond), hepsilonA₂]
    have hXepsilon : hilbertSymbol K X (epsilon : Kˣ) = -1 := by
      change hilbertSymbol K
        ((M.mu : Kˣ) * a.adjacentProduct (1 : Fin 3))
          (epsilon : Kˣ) = -1
      rw [hilbertSymbol_mul_left,
        hilbertSymbol_comm K (M.mu : Kˣ) (epsilon : Kˣ),
        show hilbertSymbol K (epsilon : Kˣ) (M.mu : Kˣ) = 1 by
          simpa only [epsilon] using M.muEpsilonHilbert,
        hilbertSymbol_comm K (a.adjacentProduct (1 : Fin 3))
          (epsilon : Kˣ), hnegative]
      norm_num
    have hthetaMiddle : hilbertSymbol K X (theta : Kˣ) = 1 := by
      change hilbertSymbol K X ((epsilon : Kˣ) * (rho : Kˣ)) = 1
      rw [hilbertSymbol_mul_right, hXepsilon, hrhoX]
      norm_num
    have hthetaEta : hilbertSymbol K
        ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3))
        (eta : Kˣ) = 1 := by
      have hbase : hilbertSymbol K
          ((epsilon : Kˣ) * a.adjacentProduct (2 : Fin 3))
          (eta : Kˣ) = -1 := hchoice.trans hnegative
      change hilbertSymbol K
        (((epsilon : Kˣ) * (rho : Kˣ)) *
          a.adjacentProduct (2 : Fin 3)) (eta : Kˣ) = 1
      rw [show ((epsilon : Kˣ) * (rho : Kˣ)) *
          a.adjacentProduct (2 : Fin 3) =
        (rho : Kˣ) *
          ((epsilon : Kˣ) * a.adjacentProduct (2 : Fin 3)) by ac_rfl,
        hilbertSymbol_mul_left, hbase,
        hilbertSymbol_comm K (rho : Kˣ) (eta : Kˣ), hrhoEta]
      norm_num
    have hkappaEq :
        ((epsilon / theta : valuationUnitSubgroup K) : Kˣ) =
          (rho : Kˣ)⁻¹ := by
      dsimp only [theta]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hhalfLeReference : a.halfGapValue (1 : Fin 3) ≤
        2 * (ramificationIndex K : ℚ) -
          a.alphaValue (0 : Fin 3) := by
      have hgap :=
        a.quaternaryAlternating_orderGap_one_eq_neg_zero D.alternating
      unfold BONG.GoodBONG.halfGapValue
      rw [hgap]
      push_cast at hgapShift ⊢
      linarith
    have hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
          a (M.mu : Kˣ) (eta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K)
          (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) := by
      refine (min_le_left _ _).trans ?_
      rw [hkappaEq, BONG.GoodBONG.defectOrder_inv, ← a.coe_halfGapValue]
      have hhalfLeRef : (a.halfGapValue (1 : Fin 3) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K) reference := by
        rw [hrefDefect]
        exact_mod_cast hhalfLeReference
      exact hhalfLeRef.trans hrhoDepth
    have hkappaHilbert : hilbertSymbol K
        (((M.mu : Kˣ) * (eta : Kˣ)) *
          a.adjacentProduct (1 : Fin 3))
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) = 1 := by
      exact hilbertSymbol_fiveStep_middle_closure
        (a.adjacentProduct (1 : Fin 3))
        (a.adjacentProduct (2 : Fin 3))
        (M.mu : Kˣ) (epsilon : Kˣ) (theta : Kˣ) (eta : Kˣ)
        (by simpa only [epsilon] using M.muEpsilonHilbert)
        hthetaMiddle hthetaEta hchoice
    exact ⟨C, finish theta hthetaDepth hthetaA₂ hthetaMiddle
      hthetaEta hkappaAlpha hkappaHilbert⟩

/-- Path-refined Lemma 9.2 in the alternating quaternary branch.  The
five-step path above and the Section 8 realization use the same two units, so
the realized good BONG is literally the endpoint of the adjacent-binary path.
-/
theorem reachableLemma92Transform_rankFourAlternating_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4)
    (D : BONG.GoodBONG.Lemma92RankFourAlternatingData a) :
    Nonempty (ReachableLemma92Transform a) := by
  rcases reachableLemma92_rankFourAlternating_of_largeResidue hres a D with
    ⟨C, hreach⟩
  let U := C.choice
  rcases a.exists_lemma92EarlyScalingData_of_lastCandidate
      U.epsilon U.eta U.epsilon_isValuationUnit U.eta_isValuationUnit
      U.epsilon_defect U.eta_defect U.adjacent_hilbert D.alternating
      (D.toLemma92RankFourCommonData.lastCandidate U) with ⟨S⟩
  have htarget :
      ![a.valueUnit 0,
        U.epsilon * a.valueUnit 1,
        U.epsilon * U.eta * a.valueUnit 2,
        U.eta * a.valueUnit 3] =
        (fun i ↦ S.transformed.valueUnit i) := by
    funext i
    fin_cases i
    · simpa using S.firstValue_eq.symm
    · simpa using S.secondValue_eq.symm
    · simpa using S.thirdValue_eq.symm
    · simpa using S.fourthValue_eq.symm
  have hreachS : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ S.transformed.valueUnit i) := by
    simpa only [U, C.choiceEpsilon] using htarget ▸ hreach
  have hbase : S.transformed.alphaValue (2 : Fin 3) =
      S.transformed.tail.alphaValue (1 : Fin 2) := by
    apply BONG.GoodBONG.alphaValue_shift_eq_tail_of_invariant_nextAdjacentDefect
      (a := a) (c := S.transformed) (p := (1 : Fin 2))
    · exact D.thirdAlpha_recursion
    · change S.transformed.adjacentDefect (2 : Fin 3) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ)
      rw [S.adjacentDefect_two]
      exact D.toLemma92RankFourCommonData.scaledLastAdjacent_defect U
  let T : BONG.GoodBONG.Beli2019Lemma92Transform a := {
    transformed := S.transformed
    firstValue_eq := S.firstValue_eq
    laterAlpha_eq_tail := by
      intro i hi
      omega
    earlyAlpha_eq_tail := by
      intro _
      exact (a.alpha_invariant S.transformed (2 : Fin 3)).trans hbase
  }
  exact ⟨{
    transform := T
    reachable := hreachS
  }⟩

/-- Complete path-refined Lemma 9.2 in rank four.  The reduction theorem
exhausts the identity, strict-first, and alternating branches; the preceding
two theorems supply concrete adjacent-binary paths in the non-identity cases.
-/
theorem reachableLemma92Transform_rankFour_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) :
    Nonempty (ReachableLemma92Transform a) := by
  by_cases hearly : a.Lemma92EarlyAlternative
  · rcases a.rankFour_reduction hearly with heq | hfirst | halternating
    · exact ⟨reachableLemma92TransformIdentity a
        (by intro i hi; omega) (by intro _; exact heq)⟩
    · exact reachableLemma92_rankFourFirst_of_largeResidue hres a hfirst
    · exact reachableLemma92Transform_rankFourAlternating_of_largeResidue
        hres a halternating
  · exact ⟨reachableLemma92TransformIdentity a
      (by intro i hi; omega) (by intro hcase; exact (hearly hcase).elim)⟩

end Beli2009FinalRemarksProof.LargeResidueConnectivity

end Bong
