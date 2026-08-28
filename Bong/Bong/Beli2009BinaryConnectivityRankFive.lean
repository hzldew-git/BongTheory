/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009BinaryConnectivityRankFour

namespace Bong

open Dyadic
open BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

/-! ## The rank-five outward-and-return braid -/

/-- The second binary alpha after the first multiplier, with the changed
adjacent product written without its irrelevant square factors. -/
noncomputable def rankFiveSecondBinaryAlphaAfterFirstMultiplier
    (a : BONG.GoodBONG q L 5) (mu : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (1 : Fin 4))
    (((((a.order (1 : Fin 4).succ -
          a.order (1 : Fin 4).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        (mu * a.adjacentProduct (1 : Fin 4)))

/-- The third binary alpha after the first two multipliers. -/
noncomputable def rankFiveThirdBinaryAlphaAfterSecondMultiplier
    (a : BONG.GoodBONG q L 5) (theta : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (2 : Fin 4))
    (((((a.order (2 : Fin 4).succ -
          a.order (2 : Fin 4).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        (theta * a.adjacentProduct (2 : Fin 4)))

/-- The fourth binary alpha after the first three multipliers. -/
noncomputable def rankFiveFourthBinaryAlphaAfterThirdMultiplier
    (a : BONG.GoodBONG q L 5) (epsilon : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (3 : Fin 4))
    (((((a.order (3 : Fin 4).succ -
          a.order (3 : Fin 4).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        (epsilon * a.adjacentProduct (3 : Fin 4)))

/-- On returning directly to the second edge, the first and third outward
multipliers remain in its adjacent product; the middle multiplier occurs as
a square and hence does not affect its defect. -/
noncomputable def rankFiveSecondBinaryAlphaAfterOuterScaling
    (a : BONG.GoodBONG q L 5) (mu epsilon : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (1 : Fin 4))
    (((((a.order (1 : Fin 4).succ -
          a.order (1 : Fin 4).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        ((mu * epsilon) * a.adjacentProduct (1 : Fin 4)))

/-- On the first return edge, the second and fourth outward multipliers remain
in the third adjacent product; the first third-edge multiplier occurs as a
square and is invisible to the defect. -/
noncomputable def rankFiveThirdBinaryAlphaAfterOuterMultipliers
    (a : BONG.GoodBONG q L 5) (theta eta : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (2 : Fin 4))
    (((((a.order (2 : Fin 4).succ -
          a.order (2 : Fin 4).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        ((theta * eta) * a.adjacentProduct (2 : Fin 4)))

/-- Dynamic realization of the seven edges
`0 -> 1 -> 2 -> 3 -> 2 -> 1 -> 0`.  The first third-edge multiplier is an
auxiliary `epsilon`; the return multiplier `omega / epsilon` replaces it by
the desired final multiplier `omega`.  The last two return multipliers are
the inverses of the first two. -/
theorem reachable_rankFive_sevenStep_scaling_of_dynamic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 5)
    (mu theta epsilon eta omega : valuationUnitSubgroup K)
    (hmuAlpha : a.adjacentBinaryAlpha (0 : Fin 4) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hmuHilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 4))
      (mu : Kˣ) = 1)
    (hthetaAlpha : rankFiveSecondBinaryAlphaAfterFirstMultiplier
        a (mu : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaHilbert : hilbertSymbol K
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 4)) (theta : Kˣ) = 1)
    (hepsilonAlpha : rankFiveThirdBinaryAlphaAfterSecondMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (epsilon : Kˣ))
    (hepsilonHilbert : hilbertSymbol K
      ((theta : Kˣ) * a.adjacentProduct (2 : Fin 4))
        (epsilon : Kˣ) = 1)
    (hetaAlpha : rankFiveFourthBinaryAlphaAfterThirdMultiplier
        a (epsilon : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hetaHilbert : hilbertSymbol K
      ((epsilon : Kˣ) * a.adjacentProduct (3 : Fin 4)) (eta : Kˣ) = 1)
    (hkappaAlpha : rankFiveThirdBinaryAlphaAfterOuterMultipliers
        a (theta : Kˣ) (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((omega / epsilon : valuationUnitSubgroup K) : Kˣ)))
    (hkappaHilbert : hilbertSymbol K
      (((theta : Kˣ) * (eta : Kˣ)) *
        a.adjacentProduct (2 : Fin 4))
      (((omega / epsilon : valuationUnitSubgroup K) : Kˣ)) = 1)
    (hlambdaAlpha : rankFiveSecondBinaryAlphaAfterOuterScaling
        a (mu : Kˣ) (omega : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) ((theta : Kˣ)⁻¹))
    (hlambdaHilbert : hilbertSymbol K
      (((mu : Kˣ) * (omega : Kˣ)) *
        a.adjacentProduct (1 : Fin 4)) ((theta : Kˣ)⁻¹) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i)
      ![a.valueUnit 0, a.valueUnit 1,
        (omega : Kˣ) * a.valueUnit 2,
        (omega : Kˣ) * (eta : Kˣ) * a.valueUnit 3,
        (eta : Kˣ) * a.valueUnit 4] := by
  have hmuGroup : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 5) / a.valueUnit (0 : Fin 5)) :=
    valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 4) mu hmuAlpha hmuHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 4)
      mu hmuGroup with ⟨b, hbValues⟩
  have hmuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) :=
    ⟨0, mu, hmuGroup, hbValues⟩
  have hbSecondAdjacent : b.adjacentProduct (1 : Fin 4) =
      (mu : Kˣ) * a.adjacentProduct (1 : Fin 4) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hbValues (1 : Fin 4).castSucc,
      congrFun hbValues (1 : Fin 4).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
    exact mul_comm _ _
  have hbSecondAlpha : b.adjacentBinaryAlpha (1 : Fin 4) =
      rankFiveSecondBinaryAlphaAfterFirstMultiplier a (mu : Kˣ) := by
    have horders := a.order_invariant b
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFiveSecondBinaryAlphaAfterFirstMultiplier
      BONG.GoodBONG.halfGapCandidate BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (1 : Fin 4).succ).symm,
      (horders (1 : Fin 4).castSucc).symm,
      hbSecondAdjacent]
  have hthetaGroup : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (b.valueUnit (2 : Fin 5) / b.valueUnit (1 : Fin 5)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      b (1 : Fin 4) theta
    · rw [hbSecondAlpha]
      exact hthetaAlpha
    · rw [hbSecondAdjacent]
      exact hthetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact b (1 : Fin 4)
      theta hthetaGroup with ⟨c, hcValues⟩
  have hthetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ b.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨1, theta, hthetaGroup, hcValues⟩
  have hcThirdAdjacent : c.adjacentProduct (2 : Fin 4) =
      (theta : Kˣ) * a.adjacentProduct (2 : Fin 4) := by
    have hcTwo : c.valueUnit (2 : Fin 5) =
        (theta : Kˣ) * b.valueUnit (2 : Fin 5) := by
      rw [congrFun hcValues (2 : Fin 5)]
      rfl
    have hcThree : c.valueUnit (3 : Fin 5) = b.valueUnit (3 : Fin 5) := by
      rw [congrFun hcValues (3 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hbTwo : b.valueUnit (2 : Fin 5) = a.valueUnit (2 : Fin 5) := by
      rw [congrFun hbValues (2 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hbThree : b.valueUnit (3 : Fin 5) = a.valueUnit (3 : Fin 5) := by
      rw [congrFun hbValues (3 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    unfold BONG.GoodBONG.adjacentProduct
    change -(c.valueUnit (2 : Fin 5) * c.valueUnit (3 : Fin 5)) = _
    rw [hcTwo, hcThree, hbTwo, hbThree]
    apply Units.ext
    simp
    ring
  have hcThirdAlpha : c.adjacentBinaryAlpha (2 : Fin 4) =
      rankFiveThirdBinaryAlphaAfterSecondMultiplier a (theta : Kˣ) := by
    have horders := a.order_invariant c
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFiveThirdBinaryAlphaAfterSecondMultiplier
      BONG.GoodBONG.halfGapCandidate BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (2 : Fin 4).succ).symm,
      (horders (2 : Fin 4).castSucc).symm,
      hcThirdAdjacent]
  have hepsilonGroup : valuationUnitClassHom K epsilon ∈
      beliNormGeneratorGroup K
        (c.valueUnit (3 : Fin 5) / c.valueUnit (2 : Fin 5)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (2 : Fin 4) epsilon
    · rw [hcThirdAlpha]
      exact hepsilonAlpha
    · rw [hcThirdAdjacent]
      exact hepsilonHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (2 : Fin 4)
      epsilon hepsilonGroup with ⟨d, hdValues⟩
  have hepsilonStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ c.valueUnit i) (fun i ↦ d.valueUnit i) :=
    ⟨2, epsilon, hepsilonGroup, hdValues⟩
  have hdFourthAdjacent : d.adjacentProduct (3 : Fin 4) =
      (epsilon : Kˣ) * a.adjacentProduct (3 : Fin 4) := by
    have hdThree : d.valueUnit (3 : Fin 5) =
        (epsilon : Kˣ) * c.valueUnit (3 : Fin 5) := by
      rw [congrFun hdValues (3 : Fin 5)]
      rfl
    have hdFour : d.valueUnit (4 : Fin 5) = c.valueUnit (4 : Fin 5) := by
      rw [congrFun hdValues (4 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hcThree : c.valueUnit (3 : Fin 5) = a.valueUnit (3 : Fin 5) := by
      rw [congrFun hcValues (3 : Fin 5)]
      simp [beli2009BinaryTransformAt]
      rw [congrFun hbValues (3 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hcFour : c.valueUnit (4 : Fin 5) = a.valueUnit (4 : Fin 5) := by
      rw [congrFun hcValues (4 : Fin 5)]
      simp [beli2009BinaryTransformAt]
      rw [congrFun hbValues (4 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    unfold BONG.GoodBONG.adjacentProduct
    change -(d.valueUnit (3 : Fin 5) * d.valueUnit (4 : Fin 5)) = _
    rw [hdThree, hdFour, hcThree, hcFour]
    apply Units.ext
    simp
    ring
  have hdFourthAlpha : d.adjacentBinaryAlpha (3 : Fin 4) =
      rankFiveFourthBinaryAlphaAfterThirdMultiplier a (epsilon : Kˣ) := by
    have horders := a.order_invariant d
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFiveFourthBinaryAlphaAfterThirdMultiplier
      BONG.GoodBONG.halfGapCandidate BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (3 : Fin 4).succ).symm,
      (horders (3 : Fin 4).castSucc).symm,
      hdFourthAdjacent]
  have hetaGroup : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (d.valueUnit (4 : Fin 5) / d.valueUnit (3 : Fin 5)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (3 : Fin 4) eta
    · rw [hdFourthAlpha]
      exact hetaAlpha
    · rw [hdFourthAdjacent]
      exact hetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact d (3 : Fin 4)
      eta hetaGroup with ⟨e, heValues⟩
  have hetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ d.valueUnit i) (fun i ↦ e.valueUnit i) :=
    ⟨3, eta, hetaGroup, heValues⟩
  have heSecondAdjacent : e.adjacentProduct (1 : Fin 4) =
      (((mu : Kˣ) * (epsilon : Kˣ)) *
        a.adjacentProduct (1 : Fin 4)) * (theta : Kˣ) ^ 2 := by
    have heOne : e.valueUnit (1 : Fin 5) = d.valueUnit (1 : Fin 5) := by
      rw [congrFun heValues (1 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have heTwo : e.valueUnit (2 : Fin 5) = d.valueUnit (2 : Fin 5) := by
      rw [congrFun heValues (2 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hdOne : d.valueUnit (1 : Fin 5) = c.valueUnit (1 : Fin 5) := by
      rw [congrFun hdValues (1 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hdTwo : d.valueUnit (2 : Fin 5) =
        (epsilon : Kˣ) * c.valueUnit (2 : Fin 5) := by
      rw [congrFun hdValues (2 : Fin 5)]
      rfl
    have hcOne : c.valueUnit (1 : Fin 5) =
        (theta : Kˣ) * b.valueUnit (1 : Fin 5) := by
      rw [congrFun hcValues (1 : Fin 5)]
      rfl
    have hcTwo : c.valueUnit (2 : Fin 5) =
        (theta : Kˣ) * b.valueUnit (2 : Fin 5) := by
      rw [congrFun hcValues (2 : Fin 5)]
      rfl
    have hbOne : b.valueUnit (1 : Fin 5) =
        (mu : Kˣ) * a.valueUnit (1 : Fin 5) := by
      rw [congrFun hbValues (1 : Fin 5)]
      rfl
    have hbTwo : b.valueUnit (2 : Fin 5) = a.valueUnit (2 : Fin 5) := by
      rw [congrFun hbValues (2 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    unfold BONG.GoodBONG.adjacentProduct
    change -(e.valueUnit (1 : Fin 5) * e.valueUnit (2 : Fin 5)) = _
    rw [heOne, heTwo, hdOne, hdTwo, hcOne, hcTwo, hbOne, hbTwo]
    apply Units.ext
    simp [pow_two]
    ring
  have heThirdAdjacent : e.adjacentProduct (2 : Fin 4) =
      ((((theta : Kˣ) * (eta : Kˣ)) *
        a.adjacentProduct (2 : Fin 4)) * (epsilon : Kˣ) ^ 2) := by
    have heTwo : e.valueUnit (2 : Fin 5) = d.valueUnit (2 : Fin 5) := by
      rw [congrFun heValues (2 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have heThree : e.valueUnit (3 : Fin 5) =
        (eta : Kˣ) * d.valueUnit (3 : Fin 5) := by
      rw [congrFun heValues (3 : Fin 5)]
      rfl
    have hdTwo : d.valueUnit (2 : Fin 5) =
        (epsilon : Kˣ) * c.valueUnit (2 : Fin 5) := by
      rw [congrFun hdValues (2 : Fin 5)]
      rfl
    have hdThree : d.valueUnit (3 : Fin 5) =
        (epsilon : Kˣ) * c.valueUnit (3 : Fin 5) := by
      rw [congrFun hdValues (3 : Fin 5)]
      rfl
    have hcTwo : c.valueUnit (2 : Fin 5) =
        (theta : Kˣ) * b.valueUnit (2 : Fin 5) := by
      rw [congrFun hcValues (2 : Fin 5)]
      rfl
    have hcThree : c.valueUnit (3 : Fin 5) = b.valueUnit (3 : Fin 5) := by
      rw [congrFun hcValues (3 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hbTwo : b.valueUnit (2 : Fin 5) = a.valueUnit (2 : Fin 5) := by
      rw [congrFun hbValues (2 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hbThree : b.valueUnit (3 : Fin 5) = a.valueUnit (3 : Fin 5) := by
      rw [congrFun hbValues (3 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    unfold BONG.GoodBONG.adjacentProduct
    change -(e.valueUnit (2 : Fin 5) * e.valueUnit (3 : Fin 5)) = _
    rw [heTwo, heThree, hdTwo, hdThree, hcTwo, hcThree, hbTwo, hbThree]
    apply Units.ext
    simp [pow_two]
    ring
  have heThirdAlpha : e.adjacentBinaryAlpha (2 : Fin 4) =
      rankFiveThirdBinaryAlphaAfterOuterMultipliers
        a (theta : Kˣ) (eta : Kˣ) := by
    have horders := a.order_invariant e
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFiveThirdBinaryAlphaAfterOuterMultipliers
      BONG.GoodBONG.halfGapCandidate BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (2 : Fin 4).succ).symm,
      (horders (2 : Fin 4).castSucc).symm,
      heThirdAdjacent, BONG.GoodBONG.defectOrder_mul_square]
  let kappa : valuationUnitSubgroup K := omega / epsilon
  have hkappaGroup : valuationUnitClassHom K kappa ∈
      beliNormGeneratorGroup K
        (e.valueUnit (3 : Fin 5) / e.valueUnit (2 : Fin 5)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      e (2 : Fin 4) kappa
    · rw [heThirdAlpha]
      simpa only [kappa] using hkappaAlpha
    · rw [heThirdAdjacent, hilbertSymbol_mul_square_left]
      simpa only [kappa] using hkappaHilbert
  rcases exists_goodBONG_binaryTransformation_exact e (2 : Fin 4)
      kappa hkappaGroup with ⟨p, hpValues⟩
  have hkappaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ e.valueUnit i) (fun i ↦ p.valueUnit i) :=
    ⟨2, kappa, hkappaGroup, hpValues⟩
  have hpSecondAdjacent : p.adjacentProduct (1 : Fin 4) =
      (((mu : Kˣ) * (omega : Kˣ)) *
        a.adjacentProduct (1 : Fin 4)) * (theta : Kˣ) ^ 2 := by
    have hlocal : p.adjacentProduct (1 : Fin 4) =
        (kappa : Kˣ) * e.adjacentProduct (1 : Fin 4) := by
      have hpOne : p.valueUnit (1 : Fin 5) = e.valueUnit (1 : Fin 5) := by
        rw [congrFun hpValues (1 : Fin 5)]
        simp [beli2009BinaryTransformAt]
      have hpTwo : p.valueUnit (2 : Fin 5) =
          (kappa : Kˣ) * e.valueUnit (2 : Fin 5) := by
        rw [congrFun hpValues (2 : Fin 5)]
        rfl
      unfold BONG.GoodBONG.adjacentProduct
      change -(p.valueUnit (1 : Fin 5) * p.valueUnit (2 : Fin 5)) = _
      rw [hpOne, hpTwo]
      apply Units.ext
      simp
      ring
    rw [hlocal, heSecondAdjacent]
    dsimp only [kappa]
    apply Units.ext
    simp [div_eq_mul_inv, pow_two]
    field_simp
  have hpSecondAlpha : p.adjacentBinaryAlpha (1 : Fin 4) =
      rankFiveSecondBinaryAlphaAfterOuterScaling
        a (mu : Kˣ) (omega : Kˣ) := by
    have horders := a.order_invariant p
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFiveSecondBinaryAlphaAfterOuterScaling
      BONG.GoodBONG.halfGapCandidate BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (1 : Fin 4).succ).symm,
      (horders (1 : Fin 4).castSucc).symm,
      hpSecondAdjacent, BONG.GoodBONG.defectOrder_mul_square]
  let lambda : valuationUnitSubgroup K := theta⁻¹
  have hlambdaGroup : valuationUnitClassHom K lambda ∈
      beliNormGeneratorGroup K
        (p.valueUnit (2 : Fin 5) / p.valueUnit (1 : Fin 5)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      p (1 : Fin 4) lambda
    · rw [hpSecondAlpha]
      simpa only [lambda, Subgroup.coe_inv] using hlambdaAlpha
    · rw [hpSecondAdjacent, hilbertSymbol_mul_square_left]
      simpa only [lambda, Subgroup.coe_inv] using hlambdaHilbert
  rcases exists_goodBONG_binaryTransformation_exact p (1 : Fin 4)
      lambda hlambdaGroup with ⟨f, hfValues⟩
  have hlambdaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ p.valueUnit i) (fun i ↦ f.valueUnit i) :=
    ⟨1, lambda, hlambdaGroup, hfValues⟩
  have hfFirstAdjacent : f.adjacentProduct (0 : Fin 4) =
      a.adjacentProduct (0 : Fin 4) * (mu : Kˣ) ^ 2 := by
    have hfZero : f.valueUnit (0 : Fin 5) = p.valueUnit (0 : Fin 5) := by
      rw [congrFun hfValues (0 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hfOne : f.valueUnit (1 : Fin 5) =
        (lambda : Kˣ) * p.valueUnit (1 : Fin 5) := by
      rw [congrFun hfValues (1 : Fin 5)]
      rfl
    have hpZero : p.valueUnit (0 : Fin 5) = e.valueUnit (0 : Fin 5) := by
      rw [congrFun hpValues (0 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hpOne : p.valueUnit (1 : Fin 5) = e.valueUnit (1 : Fin 5) := by
      rw [congrFun hpValues (1 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have heZero : e.valueUnit (0 : Fin 5) = d.valueUnit (0 : Fin 5) := by
      rw [congrFun heValues (0 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have heOne : e.valueUnit (1 : Fin 5) = d.valueUnit (1 : Fin 5) := by
      rw [congrFun heValues (1 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hdZero : d.valueUnit (0 : Fin 5) = c.valueUnit (0 : Fin 5) := by
      rw [congrFun hdValues (0 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hdOne : d.valueUnit (1 : Fin 5) = c.valueUnit (1 : Fin 5) := by
      rw [congrFun hdValues (1 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hcZero : c.valueUnit (0 : Fin 5) = b.valueUnit (0 : Fin 5) := by
      rw [congrFun hcValues (0 : Fin 5)]
      simp [beli2009BinaryTransformAt]
    have hcOne : c.valueUnit (1 : Fin 5) =
        (theta : Kˣ) * b.valueUnit (1 : Fin 5) := by
      rw [congrFun hcValues (1 : Fin 5)]
      rfl
    have hbZero : b.valueUnit (0 : Fin 5) =
        (mu : Kˣ) * a.valueUnit (0 : Fin 5) := by
      rw [congrFun hbValues (0 : Fin 5)]
      rfl
    have hbOne : b.valueUnit (1 : Fin 5) =
        (mu : Kˣ) * a.valueUnit (1 : Fin 5) := by
      rw [congrFun hbValues (1 : Fin 5)]
      rfl
    unfold BONG.GoodBONG.adjacentProduct
    change -(f.valueUnit (0 : Fin 5) * f.valueUnit (1 : Fin 5)) = _
    rw [hfZero, hfOne, hpZero, hpOne, heZero, heOne, hdZero, hdOne, hcZero, hcOne,
      hbZero, hbOne]
    dsimp only [lambda]
    apply Units.ext
    simp [beli2009BinaryTransformAt, pow_two]
    ring
  have hfFirstAlpha : f.adjacentBinaryAlpha (0 : Fin 4) =
      a.adjacentBinaryAlpha (0 : Fin 4) := by
    have horders := a.order_invariant f
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      BONG.GoodBONG.halfGapCandidate BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (0 : Fin 4).succ).symm,
      (horders (0 : Fin 4).castSucc).symm,
      hfFirstAdjacent, BONG.GoodBONG.defectOrder_mul_square]
  let nu : valuationUnitSubgroup K := mu⁻¹
  have hnuGroup : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (f.valueUnit (1 : Fin 5) / f.valueUnit (0 : Fin 5)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      f (0 : Fin 4) nu
    · rw [hfFirstAlpha]
      simpa only [nu, Subgroup.coe_inv,
        BONG.GoodBONG.defectOrder_inv] using hmuAlpha
    · rw [hfFirstAdjacent, hilbertSymbol_mul_square_left]
      simpa only [nu, Subgroup.coe_inv,
        hilbertSymbol_inv_right_eq_local] using hmuHilbert
  rcases exists_goodBONG_binaryTransformation_exact f (0 : Fin 4)
      nu hnuGroup with ⟨g, hgValues⟩
  have hnuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ f.valueUnit i) (fun i ↦ g.valueUnit i) :=
    ⟨0, nu, hnuGroup, hgValues⟩
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ g.valueUnit i) :=
    hmuStep.reachable.trans <| hthetaStep.reachable.trans <|
      hepsilonStep.reachable.trans <| hetaStep.reachable.trans <|
        hkappaStep.reachable.trans <|
          hlambdaStep.reachable.trans hnuStep.reachable
  have hnuMuSub : nu * mu = (1 : valuationUnitSubgroup K) := by
    dsimp only [nu]
    simp
  have hlambdaThetaSub : lambda * theta =
      (1 : valuationUnitSubgroup K) := by
    dsimp only [lambda]
    simp
  have hkappaEpsilonSub : kappa * epsilon = omega := by
    dsimp only [kappa]
    exact div_mul_cancel omega epsilon
  have hnuMu : (nu : Kˣ) * (mu : Kˣ) = 1 := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg (fun x : valuationUnitSubgroup K ↦ (x : Kˣ)) hnuMuSub
  have hlambdaTheta : (lambda : Kˣ) * (theta : Kˣ) = 1 := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg (fun x : valuationUnitSubgroup K ↦ (x : Kˣ)) hlambdaThetaSub
  have hkappaEpsilon : (kappa : Kˣ) * (epsilon : Kˣ) =
      (omega : Kˣ) := by
    simpa only [Subgroup.coe_mul] using
      congrArg (fun x : valuationUnitSubgroup K ↦ (x : Kˣ)) hkappaEpsilonSub
  have hgFinal : (fun i ↦ g.valueUnit i) =
      ![a.valueUnit 0, a.valueUnit 1,
        (omega : Kˣ) * a.valueUnit 2,
        (omega : Kˣ) * (eta : Kˣ) * a.valueUnit 3,
        (eta : Kˣ) * a.valueUnit 4] := by
    rw [hgValues, hfValues, hpValues, heValues, hdValues, hcValues, hbValues]
    funext i
    fin_cases i <;>
      simp [beli2009BinaryTransformAt]
    · calc
        (nu : Kˣ) * ((mu : Kˣ) * a.valueUnit 0) =
            ((nu : Kˣ) * (mu : Kˣ)) * a.valueUnit 0 := by
              rw [mul_assoc]
        _ = a.valueUnit 0 := by rw [hnuMu, one_mul]
    · calc
        (nu : Kˣ) * ((lambda : Kˣ) *
            ((theta : Kˣ) * ((mu : Kˣ) * a.valueUnit 1))) =
          (((nu : Kˣ) * (mu : Kˣ)) *
            ((lambda : Kˣ) * (theta : Kˣ))) * a.valueUnit 1 := by ac_rfl
        _ = a.valueUnit 1 := by simp [hnuMu, hlambdaTheta]
    · calc
        (lambda : Kˣ) * ((kappa : Kˣ) *
            ((epsilon : Kˣ) * ((theta : Kˣ) * a.valueUnit 2))) =
          (((lambda : Kˣ) * (theta : Kˣ)) *
            ((kappa : Kˣ) * (epsilon : Kˣ))) * a.valueUnit 2 := by ac_rfl
        _ = (omega : Kˣ) * a.valueUnit 2 := by
          rw [hlambdaTheta, hkappaEpsilon, one_mul]
    · calc
        (kappa : Kˣ) * ((eta : Kˣ) *
            ((epsilon : Kˣ) * a.valueUnit 3)) =
          ((kappa : Kˣ) * (epsilon : Kˣ)) *
            (eta : Kˣ) * a.valueUnit 3 := by ac_rfl
        _ = (omega : Kˣ) * (eta : Kˣ) * a.valueUnit 3 := by
          rw [hkappaEpsilon]
  rw [hgFinal] at hreach
  exact hreach

/-- The Hilbert condition on the first return across the third edge follows
from the two outward edge conditions, the prescribed positive pairing of the
two third-edge multipliers, and the Lemma 8.2 choice identity on the last
two adjacent products. -/
theorem hilbertSymbol_sevenStep_middle_closure
    [HilbertSymbolLaws K]
    (A₂ A₃ theta epsilon xi eta : Kˣ)
    (hthetaEpsilon : hilbertSymbol K theta epsilon = 1)
    (hxi : hilbertSymbol K (theta * A₂) xi = 1)
    (heta : hilbertSymbol K (xi * A₃) eta = 1)
    (hchoice : hilbertSymbol K (epsilon * A₃) eta =
      hilbertSymbol K epsilon A₂) :
    hilbertSymbol K ((theta * eta) * A₂) (epsilon / xi) = 1 := by
  have hxiInv : hilbertSymbol K ((theta * eta) * A₂) xi⁻¹ =
      hilbertSymbol K ((theta * eta) * A₂) xi := by
    have hmap := map_inv (hilbertCharacter K ((theta * eta) * A₂)) xi
    change hilbertSymbol K ((theta * eta) * A₂) xi⁻¹ =
      (hilbertSymbol K ((theta * eta) * A₂) xi)⁻¹ at hmap
    rw [hmap]
    rcases Int.units_eq_one_or
        (hilbertSymbol K ((theta * eta) * A₂) xi) with h | h <;>
      rw [h] <;> norm_num
  rw [div_eq_mul_inv, hilbertSymbol_mul_right, hxiInv]
  repeat' rw [hilbertSymbol_mul_left]
  rw [hilbertSymbol_mul_left] at hxi heta hchoice
  rcases Int.units_eq_one_or (hilbertSymbol K theta xi) with hthetaXi | hthetaXi <;>
    rcases Int.units_eq_one_or (hilbertSymbol K A₂ xi) with hA₂Xi | hA₂Xi <;>
    rcases Int.units_eq_one_or (hilbertSymbol K xi eta) with hxiEta | hxiEta <;>
    rcases Int.units_eq_one_or (hilbertSymbol K A₃ eta) with hA₃Eta | hA₃Eta <;>
    rcases Int.units_eq_one_or (hilbertSymbol K epsilon eta) with hepsilonEta | hepsilonEta <;>
    rcases Int.units_eq_one_or (hilbertSymbol K A₂ epsilon) with hA₂Epsilon | hA₂Epsilon <;>
    rcases Int.units_eq_one_or (hilbertSymbol K theta epsilon) with hthetaEpsilon' | hthetaEpsilon' <;>
    simp [hilbertSymbol_comm K, hthetaXi, hA₂Xi, hxiEta, hA₃Eta,
      hepsilonEta, hA₂Epsilon, hthetaEpsilon'] at hthetaEpsilon hxi heta hchoice ⊢

/-! ## Rank-free defect-layer normalization -/

/-- At any positive-residue dyadic field, an interior odd defect layer can be
realized by a valuation-unit multiplier which normalizes a prescribed element
whose defect is at least that layer, while lying in the kernel of one
prescribed Hilbert character.  This is the common local choice used for the
first two edges of the rank-five braid. -/
theorem exists_valuationUnit_normalizing_product_hilbert_one_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (t : ℚ) (htOdd : IsOddRationalInteger t) (htNonnegative : 0 ≤ t)
    (htLt : t < 2 * (ramificationIndex K : ℚ))
    (A z : Kˣ)
    (hA : (t : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) A) :
    ∃ mu : valuationUnitSubgroup K,
      (t : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) ∧
        BONG.GoodBONG.defectOrder (K := K) ((mu : Kˣ) * A) =
          (t : WithTop ℚ) ∧
        hilbertSymbol K z (mu : Kˣ) = 1 := by
  rcases BONG.DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      t htOdd htNonnegative htLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  by_cases hAEq : BONG.GoodBONG.defectOrder (K := K) A =
      (t : WithTop ℚ)
  · have hAReference : BONG.GoodBONG.defectOrder (K := K) A =
        BONG.GoodBONG.defectOrder (K := K) reference := by
      rw [hAEq, hrefDefect]
    have hAQuadratic : quadraticDefect K A = quadraticDefect K reference :=
      BONG.GoodBONG.quadraticDefect_eq_of_defectOrder_eq
        A reference hAReference
    have hAFinite : quadraticDefect K A ≠ ⊤ := by
      rw [hAQuadratic]
      exact BONG.GoodBONG.quadraticDefect_ne_top_of_defectOrder_eq_coe
        reference t hrefDefect
    have hANonzero : quadraticDefect K A ≠ 0 := by
      rw [hAQuadratic]
      exact quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
    have hAOrderLt : BONG.GoodBONG.defectOrder (K := K) A <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hAEq]
      exact_mod_cast htLt
    have hANotTwoE : quadraticDefect K A ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_ne_twoE_of_defectOrder_lt_twoE A hAOrderLt
    rcases exists_valuationUnit_product_preserving_hilbert_one_of_largeResidue
        hres z A hAFinite hANonzero hANotTwoE with
      ⟨mu, hAMu, hproduct, hhilbert⟩
    have hmap : Monotone (WithTop.map (fun n : Nat ↦ (n : ℚ))) :=
      WithTop.monotone_map_iff.mpr (by
        intro m n hmn
        change (m : ℚ) ≤ (n : ℚ)
        exact_mod_cast hmn)
    have hdepth : BONG.GoodBONG.defectOrder (K := K) A ≤
        BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
      unfold BONG.GoodBONG.defectOrder
      exact hmap hAMu
    refine ⟨mu, hAEq ▸ hdepth, ?_, hhilbert⟩
    have hproduct' : quadraticDefect K ((mu : Kˣ) * A) =
        quadraticDefect K A := by
      simpa only [mul_comm] using hproduct
    exact (BONG.defectOrder_eq_of_quadraticDefect_eq
      ((mu : Kˣ) * A) A hproduct').trans hAEq
  · have htLtA : (t : WithTop ℚ) <
        BONG.GoodBONG.defectOrder (K := K) A :=
      lt_of_le_of_ne hA (Ne.symm hAEq)
    have hrefOrderLt : BONG.GoodBONG.defectOrder (K := K) reference <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [hrefDefect]
      exact_mod_cast htLt
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
        (t : WithTop ℚ) := by
      change BONG.GoodBONG.defectOrder (K := K) muRaw = _
      exact (BONG.defectOrder_eq_of_quadraticDefect_eq
        muRaw reference hmuQuadratic).trans hrefDefect
    refine ⟨mu, hmuOrder.ge, ?_, ?_⟩
    · change BONG.GoodBONG.defectOrder (K := K) (muRaw * A) = _
      exact (BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right
        (hmuOrder ▸ htLtA)).trans hmuOrder
    · simpa only [mu, Subgroup.coe_mk] using hmuHilbert

/-! ## Numerical consequences of the strict rank-five certificate -/

theorem lemma92RankFiveData_secondAlpha_recursion
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    a.alphaValue (1 : Fin 4) =
      (a.orderGap (1 : Fin 4) : ℚ) + a.alphaValue (0 : Fin 4) := by
  have h := D.commonRightEndpoint (1 : Fin 4)
  unfold BONG.GoodBONG.alphaRightEndpoint at h
  unfold BONG.GoodBONG.orderGap
  push_cast at h ⊢
  linarith

theorem lemma92RankFiveData_thirdAlpha_recursion
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    a.alphaValue (2 : Fin 4) =
      (a.orderGap (2 : Fin 4) : ℚ) + a.alphaValue (1 : Fin 4) := by
  have hfirst := D.commonRightEndpoint (1 : Fin 4)
  have hsecond := D.commonRightEndpoint (2 : Fin 4)
  unfold BONG.GoodBONG.alphaRightEndpoint at hfirst hsecond
  unfold BONG.GoodBONG.orderGap
  push_cast at hfirst hsecond ⊢
  linarith

theorem lemma92RankFiveData_firstAlpha_lt_thirdAlpha
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    a.alphaValue (0 : Fin 4) < a.alphaValue (2 : Fin 4) := by
  have hne : a.order (1 : Fin 5) ≠ a.order (3 : Fin 5) := by
    intro heq
    exact D.notEarly (Or.inr (Or.inl heq))
  have hle : a.order (1 : Fin 5) ≤ a.order (3 : Fin 5) :=
    a.good (1 : Fin 5) (by omega)
  have hlt : a.order (1 : Fin 5) < a.order (3 : Fin 5) :=
    lt_of_le_of_ne hle hne
  have hltQ : (a.order (1 : Fin 5) : ℚ) <
      (a.order (3 : Fin 5) : ℚ) := by
    exact_mod_cast hlt
  have hright := D.commonRightEndpoint (2 : Fin 4)
  unfold BONG.GoodBONG.alphaRightEndpoint at hright
  push_cast at hright
  linarith [hltQ]

theorem lemma92RankFiveData_secondAlpha_le_fourthAlpha
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    a.alphaValue (1 : Fin 4) ≤ a.alphaValue (3 : Fin 4) := by
  have horders : a.order (2 : Fin 5) ≤ a.order (4 : Fin 5) :=
    a.good (2 : Fin 5) (by omega)
  have hordersQ : (a.order (2 : Fin 5) : ℚ) ≤
      (a.order (4 : Fin 5) : ℚ) := by
    exact_mod_cast horders
  have hrightOne := D.commonRightEndpoint (1 : Fin 4)
  have hrightThree := D.commonRightEndpoint (3 : Fin 4)
  unfold BONG.GoodBONG.alphaRightEndpoint at hrightOne hrightThree
  push_cast at hrightOne hrightThree
  linarith [hordersQ]

theorem lemma92RankFiveData_fourthAlpha_lt_halfGap
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    a.alphaValue (3 : Fin 4) < a.halfGapValue (3 : Fin 4) := by
  have hrec := D.fourthAlpha_recursion
  have hsum := D.thirdFourth_sum_lt_twoE
  unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap
  unfold BONG.GoodBONG.orderGap at hrec
  push_cast at hrec hsum ⊢
  linarith

theorem lemma92RankFiveData_alpha_lt_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a)
    (i : Fin 4) :
    a.alphaValue i < a.halfGapValue i := by
  have hfourth := lemma92RankFiveData_fourthAlpha_lt_halfGap a D
  have hfourthNe : a.alphaValue (3 : Fin 4) ≠
      a.halfGapValue (3 : Fin 4) := ne_of_lt hfourth
  by_cases hi : i = (3 : Fin 4)
  · simpa only [hi] using hfourth
  · apply lt_of_le_of_ne (a.alphaValue_le_halfGapValue i)
    intro heq
    have hle : i ≤ (3 : Fin 4) := Fin.le_last i
    have hlt : i < (3 : Fin 4) := lt_of_le_of_ne hle hi
    have hpropagate := a.beli2019Lemma84_iii
      (0 : Fin 4) (3 : Fin 4) i (Fin.zero_le _)
      (Fin.zero_le _) hle (D.commonRightEndpoint (3 : Fin 4)).symm heq
    exact hfourthNe
      (hpropagate.2 (3 : Fin 4) hle le_rfl)

theorem lemma92RankFiveData_alpha_odd
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a)
    (i : Fin 4) :
    IsOddRationalInteger (a.alphaValue i) :=
  a.beli2009Lemma27_iv i
    (ne_of_lt (lemma92RankFiveData_alpha_lt_halfGap a D i))

theorem lemma92RankFiveData_alpha_nonnegative
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 5)
    (_D : BONG.GoodBONG.Lemma92RankFiveData a)
    (i : Fin 4) :
    0 ≤ a.alphaValue i :=
  (a.beli2009Lemma27_i i).1

theorem lemma92RankFiveData_alpha_lt_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a)
    (i : Fin 4) :
    a.alphaValue i < 2 * (ramificationIndex K : ℚ) := by
  have hne : a.alphaValue i ≠ a.halfGapValue i :=
    ne_of_lt (lemma92RankFiveData_alpha_lt_halfGap a D i)
  have hgap : a.orderGap i < 2 * (ramificationIndex K : Int) := by
    by_contra hnot
    have hge : 2 * (ramificationIndex K : Int) ≤ a.orderGap i :=
      le_of_not_gt hnot
    exact hne (a.beli2009Lemma27_ii i hge)
  exact (a.beli2009Corollary28_ii i).1.mpr hgap

theorem lemma92RankFiveData_firstAlpha_le_secondAdjacentDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    (a.alphaValue (0 : Fin 4) : WithTop ℚ) ≤
      a.adjacentDefect (1 : Fin 4) := by
  have hbound := a.alpha_le_leftDefectCandidate
    (i := (1 : Fin 4)) (j := (1 : Fin 4)) le_rfl
  rw [← a.coe_alphaValue, BONG.GoodBONG.leftDefectCandidate] at hbound
  have hrecTop := congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
    (lemma92RankFiveData_secondAlpha_recursion a D)
  rw [WithTop.coe_add] at hrecTop
  rw [hrecTop] at hbound
  exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp hbound

theorem lemma92RankFiveData_secondAlpha_le_thirdAdjacentDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    (a.alphaValue (1 : Fin 4) : WithTop ℚ) ≤
      a.adjacentDefect (2 : Fin 4) := by
  have hbound := a.alpha_le_leftDefectCandidate
    (i := (2 : Fin 4)) (j := (2 : Fin 4)) le_rfl
  rw [← a.coe_alphaValue, BONG.GoodBONG.leftDefectCandidate] at hbound
  have hrecTop := congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
    (lemma92RankFiveData_thirdAlpha_recursion a D)
  rw [WithTop.coe_add] at hrecTop
  rw [hrecTop] at hbound
  exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp hbound

/-! ## The three prepared outward multipliers -/

/-- The rank-five proof first normalizes the next two adjacent products and
then chooses the target third-edge multiplier positively against the second
normalizer.  The final ternary unit certificate is constructed with that
target multiplier fixed. -/
structure Lemma92RankFivePreparedData
    (a : BONG.GoodBONG q L 5) where
  mu : valuationUnitSubgroup K
  theta : valuationUnitSubgroup K
  omega : valuationUnitSubgroup K
  unitChoice : BONG.GoodBONG.Lemma92TernaryUnitChoiceData a.tail.tail
    (a.alphaValue (2 : Fin 4)) (a.alphaValue (3 : Fin 4))
  choiceEpsilon : unitChoice.epsilon = (omega : Kˣ)
  muDepth : (a.alphaValue (0 : Fin 4) : WithTop ℚ) ≤
    BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ)
  muSecondProduct : BONG.GoodBONG.defectOrder (K := K)
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 4)) =
    (a.alphaValue (0 : Fin 4) : WithTop ℚ)
  muFirstHilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 4))
    (mu : Kˣ) = 1
  thetaDepth : (a.alphaValue (1 : Fin 4) : WithTop ℚ) ≤
    BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ)
  thetaThirdProduct : BONG.GoodBONG.defectOrder (K := K)
      ((theta : Kˣ) * a.adjacentProduct (2 : Fin 4)) =
    (a.alphaValue (1 : Fin 4) : WithTop ℚ)
  thetaSecondHilbert : hilbertSymbol K
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 4)) (theta : Kˣ) = 1
  thetaOmegaHilbert : hilbertSymbol K (theta : Kˣ) (omega : Kˣ) = 1

/-- Construction of all choices which are common to the positive and
negative Hilbert-sign branches of the rank-five braid. -/
theorem exists_lemma92RankFivePreparedData_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    Nonempty (Lemma92RankFivePreparedData a) := by
  let A₀ := a.adjacentProduct (0 : Fin 4)
  let A₁ := a.adjacentProduct (1 : Fin 4)
  let A₂ := a.adjacentProduct (2 : Fin 4)
  rcases exists_valuationUnit_normalizing_product_hilbert_one_of_largeResidue
      hres (a.alphaValue (0 : Fin 4))
      (lemma92RankFiveData_alpha_odd a D (0 : Fin 4))
      (lemma92RankFiveData_alpha_nonnegative a D (0 : Fin 4))
      (lemma92RankFiveData_alpha_lt_twoE a D (0 : Fin 4))
      A₁ A₀
      (by simpa only [A₁, BONG.GoodBONG.adjacentDefect] using
        lemma92RankFiveData_firstAlpha_le_secondAdjacentDefect a D) with
    ⟨mu, hmuDepth, hmuSecond, hmuFirst⟩
  rcases exists_valuationUnit_normalizing_product_hilbert_one_of_largeResidue
      hres (a.alphaValue (1 : Fin 4))
      (lemma92RankFiveData_alpha_odd a D (1 : Fin 4))
      (lemma92RankFiveData_alpha_nonnegative a D (1 : Fin 4))
      (lemma92RankFiveData_alpha_lt_twoE a D (1 : Fin 4))
      A₂ ((mu : Kˣ) * A₁)
      (by simpa only [A₂, BONG.GoodBONG.adjacentDefect] using
        lemma92RankFiveData_secondAlpha_le_thirdAdjacentDefect a D) with
    ⟨theta, hthetaDepth, hthetaThird, hthetaSecond⟩
  rcases BONG.DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (2 : Fin 4)) D.thirdAlpha_odd
      D.thirdAlpha_nonnegative D.thirdAlpha_lt_twoE with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hrefNonzero : quadraticDefect K reference ≠ 0 :=
    quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
  have hrefOrderLt : BONG.GoodBONG.defectOrder (K := K) reference <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect]
    exact_mod_cast D.thirdAlpha_lt_twoE
  have hrefNotTwoE : quadraticDefect K reference ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    quadraticDefect_ne_twoE_of_defectOrder_lt_twoE reference hrefOrderLt
  rcases exists_valuationUnit_same_defect_hilbert_one_of_largeResidue
      hres (theta : Kˣ) reference hrefNonzero hrefNotTwoE with
    ⟨omega, homegaQuadratic, hthetaOmega⟩
  have homegaDefect : BONG.GoodBONG.defectOrder (K := K) (omega : Kˣ) =
      (a.alphaValue (2 : Fin 4) : WithTop ℚ) :=
    (BONG.defectOrder_eq_of_quadraticDefect_eq
      (omega : Kˣ) reference homegaQuadratic).trans hrefDefect
  rcases exists_lemma92TernaryUnitChoiceData_of_fixedEpsilon
      a.tail.tail (a.alphaValue (2 : Fin 4))
      (a.alphaValue (3 : Fin 4)) omega homegaDefect
      D.fourthAlpha_odd D.fourthAlpha_nonnegative D.fourthAlpha_lt_twoE
      D.lastAdjacent_gt_thirdAlpha D.thirdFourth_sum_lt_twoE with
    ⟨U, hUepsilon⟩
  exact ⟨{
    mu := mu
    theta := theta
    omega := omega
    unitChoice := U
    choiceEpsilon := hUepsilon
    muDepth := hmuDepth
    muSecondProduct := by simpa only [A₁] using hmuSecond
    muFirstHilbert := by simpa only [A₀] using hmuFirst
    thetaDepth := hthetaDepth
    thetaThirdProduct := by simpa only [A₂] using hthetaThird
    thetaSecondHilbert := by simpa only [A₁] using hthetaSecond
    thetaOmegaHilbert := hthetaOmega
  }⟩

/-- Once the outward third-edge multiplier and the first return edge have
been certified, all remaining alpha and Hilbert conditions of the seven-step
braid follow from the rank-five numerical certificate. -/
theorem reachable_rankFive_data_scaling_of_prepared
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a)
    (P : Lemma92RankFivePreparedData a)
    (xi : valuationUnitSubgroup K)
    (hxiDepth : (a.alphaValue (2 : Fin 4) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (xi : Kˣ))
    (hxiHilbert : hilbertSymbol K
      ((P.theta : Kˣ) * a.adjacentProduct (2 : Fin 4)) (xi : Kˣ) = 1)
    (hxiLastProduct : BONG.GoodBONG.defectOrder (K := K)
      ((xi : Kˣ) * a.adjacentProduct (3 : Fin 4)) =
        (a.alphaValue (2 : Fin 4) : WithTop ℚ))
    (hxiEta : hilbertSymbol K
      ((xi : Kˣ) * a.adjacentProduct (3 : Fin 4))
        P.unitChoice.eta = 1)
    (hkappaAlpha : rankFiveThirdBinaryAlphaAfterOuterMultipliers
        a (P.theta : Kˣ) P.unitChoice.eta ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((P.omega / xi : valuationUnitSubgroup K) : Kˣ)))
    (hkappaHilbert : hilbertSymbol K
      (((P.theta : Kˣ) * P.unitChoice.eta) *
        a.adjacentProduct (2 : Fin 4))
      (((P.omega / xi : valuationUnitSubgroup K) : Kˣ)) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i)
      ![a.valueUnit 0, a.valueUnit 1,
        P.unitChoice.epsilon * a.valueUnit 2,
        P.unitChoice.epsilon * P.unitChoice.eta * a.valueUnit 3,
        P.unitChoice.eta * a.valueUnit 4] := by
  let eta : valuationUnitSubgroup K :=
    ⟨P.unitChoice.eta, P.unitChoice.eta_isValuationUnit⟩
  have hsecondTop :
      (((a.orderGap (1 : Fin 4) : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue (0 : Fin 4) : WithTop ℚ) =
        (a.alphaValue (1 : Fin 4) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
      (lemma92RankFiveData_secondAlpha_recursion a D).symm
  have hthirdTop :
      (((a.orderGap (2 : Fin 4) : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin 4) : WithTop ℚ) =
        (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
      (lemma92RankFiveData_thirdAlpha_recursion a D).symm
  have hfourthTop :
      (((a.orderGap (3 : Fin 4) : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 4) : WithTop ℚ) =
        (a.alphaValue (3 : Fin 4) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
      D.fourthAlpha_recursion.symm
  unfold BONG.GoodBONG.orderGap at hsecondTop hthirdTop hfourthTop
  have hmuAlpha : a.adjacentBinaryAlpha (0 : Fin 4) ≤
      BONG.GoodBONG.defectOrder (K := K) (P.mu : Kˣ) := by
    rw [D.firstBinary_normalized]
    exact P.muDepth
  have hthetaAlpha : rankFiveSecondBinaryAlphaAfterFirstMultiplier
      a (P.mu : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (P.theta : Kˣ) := by
    refine (min_le_right _ _).trans ?_
    rw [P.muSecondProduct, hsecondTop]
    exact P.thetaDepth
  have hxiAlpha : rankFiveThirdBinaryAlphaAfterSecondMultiplier
      a (P.theta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (xi : Kˣ) := by
    refine (min_le_right _ _).trans ?_
    rw [P.thetaThirdProduct, hthirdTop]
    exact hxiDepth
  have hetaDepth : (a.alphaValue (3 : Fin 4) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
    change _ ≤ BONG.GoodBONG.defectOrder (K := K) P.unitChoice.eta
    rw [P.unitChoice.eta_defect]
  have hetaAlpha : rankFiveFourthBinaryAlphaAfterThirdMultiplier
      a (xi : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
    refine (min_le_right _ _).trans ?_
    rw [hxiLastProduct, hfourthTop]
    exact hetaDepth
  have homegaDepth : BONG.GoodBONG.defectOrder (K := K) (P.omega : Kˣ) =
      (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    rw [← P.choiceEpsilon]
    exact P.unitChoice.epsilon_defect
  have hmuOmegaProduct : BONG.GoodBONG.defectOrder (K := K)
      (((P.mu : Kˣ) * (P.omega : Kˣ)) *
        a.adjacentProduct (1 : Fin 4)) =
      (a.alphaValue (0 : Fin 4) : WithTop ℚ) := by
    have hlt : BONG.GoodBONG.defectOrder (K := K)
        ((P.mu : Kˣ) * a.adjacentProduct (1 : Fin 4)) <
      BONG.GoodBONG.defectOrder (K := K) (P.omega : Kˣ) := by
      rw [P.muSecondProduct, homegaDepth]
      exact_mod_cast lemma92RankFiveData_firstAlpha_lt_thirdAlpha a D
    have hfactor : ((P.mu : Kˣ) * (P.omega : Kˣ)) *
          a.adjacentProduct (1 : Fin 4) =
        (P.omega : Kˣ) *
          ((P.mu : Kˣ) * a.adjacentProduct (1 : Fin 4)) := by
      ac_rfl
    rw [hfactor, BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left hlt,
      P.muSecondProduct]
  have hlambdaAlpha : rankFiveSecondBinaryAlphaAfterOuterScaling
      a (P.mu : Kˣ) (P.omega : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) ((P.theta : Kˣ)⁻¹) := by
    refine (min_le_right _ _).trans ?_
    rw [hmuOmegaProduct, hsecondTop, BONG.GoodBONG.defectOrder_inv]
    exact P.thetaDepth
  have hlambdaHilbert : hilbertSymbol K
      (((P.mu : Kˣ) * (P.omega : Kˣ)) *
        a.adjacentProduct (1 : Fin 4)) ((P.theta : Kˣ)⁻¹) = 1 := by
    rw [hilbertSymbol_inv_right_eq_local,
      show ((P.mu : Kˣ) * (P.omega : Kˣ)) *
          a.adjacentProduct (1 : Fin 4) =
        ((P.mu : Kˣ) * a.adjacentProduct (1 : Fin 4)) *
          (P.omega : Kˣ) by ac_rfl,
      hilbertSymbol_mul_left, P.thetaSecondHilbert,
      hilbertSymbol_comm K (P.omega : Kˣ) (P.theta : Kˣ),
      P.thetaOmegaHilbert]
    norm_num
  have hreach := reachable_rankFive_sevenStep_scaling_of_dynamic
    a P.mu P.theta xi eta P.omega hmuAlpha P.muFirstHilbert
      hthetaAlpha P.thetaSecondHilbert hxiAlpha hxiHilbert
      hetaAlpha (by simpa only [eta, Subgroup.coe_mk] using hxiEta)
      hkappaAlpha (by simpa only [eta, Subgroup.coe_mk] using hkappaHilbert)
      hlambdaAlpha hlambdaHilbert
  simpa only [eta, P.choiceEpsilon, Subgroup.coe_mk] using hreach

/-- The easy sign branch of the printed rank-five argument: the target
multiplier itself is legal on the outward third edge, so the first return
multiplier is the identity. -/
theorem reachable_rankFive_data_positive_of_prepared
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a)
    (P : Lemma92RankFivePreparedData a)
    (hpositive : hilbertSymbol K
      ((P.theta : Kˣ) * a.adjacentProduct (2 : Fin 4))
        (P.omega : Kˣ) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i)
      ![a.valueUnit 0, a.valueUnit 1,
        P.unitChoice.epsilon * a.valueUnit 2,
        P.unitChoice.epsilon * P.unitChoice.eta * a.valueUnit 3,
        P.unitChoice.eta * a.valueUnit 4] := by
  have homegaDepth : BONG.GoodBONG.defectOrder (K := K) (P.omega : Kˣ) =
      (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    rw [← P.choiceEpsilon]
    exact P.unitChoice.epsilon_defect
  have htailMiddle : a.tail.tail.adjacentProduct (0 : Fin 2) =
      a.adjacentProduct (2 : Fin 4) := by
    rw [a.tail.adjacentProduct_tail, a.adjacentProduct_tail]
    congr 1
  have htailLast : a.tail.tail.adjacentProduct (1 : Fin 2) =
      a.adjacentProduct (3 : Fin 4) := by
    rw [a.tail.adjacentProduct_tail, a.adjacentProduct_tail]
    congr 1
  have homegaLast : BONG.GoodBONG.defectOrder (K := K)
      ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4)) =
        (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    rw [← htailLast, ← P.choiceEpsilon]
    exact P.unitChoice.scaledLastAdjacent_defect
  have hchoice : hilbertSymbol K
      ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4))
        P.unitChoice.eta =
      hilbertSymbol K (P.omega : Kˣ)
        (a.adjacentProduct (2 : Fin 4)) := by
    rw [← htailMiddle, ← htailLast, ← P.choiceEpsilon]
    exact P.unitChoice.hilbert_choice
  have hA₂Omega : hilbertSymbol K (a.adjacentProduct (2 : Fin 4))
      (P.omega : Kˣ) = 1 := by
    rw [hilbertSymbol_mul_left, P.thetaOmegaHilbert] at hpositive
    simpa using hpositive
  have homegaEta : hilbertSymbol K
      ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4))
        P.unitChoice.eta = 1 := by
    rw [hchoice, hilbertSymbol_comm K (P.omega : Kˣ)
      (a.adjacentProduct (2 : Fin 4)), hA₂Omega]
  have hkappaOne :
      (((P.omega / P.omega : valuationUnitSubgroup K) : Kˣ)) = 1 := by
    simpa using congrArg (fun x : valuationUnitSubgroup K ↦ (x : Kˣ))
      (div_self P.omega)
  have hkappaAlpha : rankFiveThirdBinaryAlphaAfterOuterMultipliers
        a (P.theta : Kˣ) P.unitChoice.eta ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((P.omega / P.omega : valuationUnitSubgroup K) : Kˣ)) := by
    rw [hkappaOne, BONG.GoodBONG.defectOrder_one]
    exact le_top
  have hkappaHilbert : hilbertSymbol K
      (((P.theta : Kˣ) * P.unitChoice.eta) *
        a.adjacentProduct (2 : Fin 4))
      (((P.omega / P.omega : valuationUnitSubgroup K) : Kˣ)) = 1 := by
    rw [hkappaOne]
    exact hilbertSymbol_one_right (K := K) _
  exact reachable_rankFive_data_scaling_of_prepared a D P P.omega
    homegaDepth.ge hpositive homegaLast homegaEta hkappaAlpha hkappaHilbert

/-- The complementary fourth-alpha layer is deep enough for the first
return across edge two.  If the second and fourth alphas differ, the right
candidate is exactly the third alpha; if they coincide, the half-gap
candidate supplies the bound. -/
theorem rankFiveThirdAlphaAfterOuter_le_complement
    [QuadraticDefectLaws K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a)
    (P : Lemma92RankFivePreparedData a)
    (rho : valuationUnitSubgroup K)
    (hrhoDepth :
      ((2 * (ramificationIndex K : ℚ) - a.alphaValue (3 : Fin 4) : ℚ) :
          WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ)) :
    rankFiveThirdBinaryAlphaAfterOuterMultipliers
        a (P.theta : Kˣ) P.unitChoice.eta ≤
      BONG.GoodBONG.defectOrder (K := K) ((rho : Kˣ)⁻¹) := by
  have hle : a.alphaValue (1 : Fin 4) ≤
      a.alphaValue (3 : Fin 4) :=
    lemma92RankFiveData_secondAlpha_le_fourthAlpha a D
  have hthirdTop :
      (((a.orderGap (2 : Fin 4) : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin 4) : WithTop ℚ) =
        (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
      (lemma92RankFiveData_thirdAlpha_recursion a D).symm
  unfold BONG.GoodBONG.orderGap at hthirdTop
  by_cases hlt : a.alphaValue (1 : Fin 4) <
      a.alphaValue (3 : Fin 4)
  · have hetaDefect : BONG.GoodBONG.defectOrder (K := K)
        P.unitChoice.eta =
        (a.alphaValue (3 : Fin 4) : WithTop ℚ) :=
      P.unitChoice.eta_defect
    have hproduct : BONG.GoodBONG.defectOrder (K := K)
        (((P.theta : Kˣ) * P.unitChoice.eta) *
          a.adjacentProduct (2 : Fin 4)) =
        (a.alphaValue (1 : Fin 4) : WithTop ℚ) := by
      have hltTop : BONG.GoodBONG.defectOrder (K := K)
          ((P.theta : Kˣ) * a.adjacentProduct (2 : Fin 4)) <
          BONG.GoodBONG.defectOrder (K := K) P.unitChoice.eta := by
        rw [P.thetaThirdProduct, hetaDefect]
        exact_mod_cast hlt
      have hfactor : ((P.theta : Kˣ) * P.unitChoice.eta) *
            a.adjacentProduct (2 : Fin 4) =
          P.unitChoice.eta *
            ((P.theta : Kˣ) * a.adjacentProduct (2 : Fin 4)) := by
        ac_rfl
      rw [hfactor,
        BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left hltTop,
        P.thetaThirdProduct]
    have hthirdLtComp : a.alphaValue (2 : Fin 4) <
        2 * (ramificationIndex K : ℚ) -
          a.alphaValue (3 : Fin 4) := by
      linarith [D.thirdFourth_sum_lt_twoE]
    refine (min_le_right _ _).trans ?_
    rw [hproduct, hthirdTop, BONG.GoodBONG.defectOrder_inv]
    have hthirdTopLt : (a.alphaValue (2 : Fin 4) : WithTop ℚ) <
        ((2 * (ramificationIndex K : ℚ) -
          a.alphaValue (3 : Fin 4) : ℚ) : WithTop ℚ) := by
      exact_mod_cast hthirdLtComp
    exact hthirdTopLt.le.trans hrhoDepth
  · have heq : a.alphaValue (1 : Fin 4) =
        a.alphaValue (3 : Fin 4) := le_antisymm hle (le_of_not_gt hlt)
    have hhalf : a.halfGapValue (2 : Fin 4) ≤
        2 * (ramificationIndex K : ℚ) -
          a.alphaValue (3 : Fin 4) := by
      have hrec := lemma92RankFiveData_thirdAlpha_recursion a D
      have hsum := D.thirdFourth_sum_lt_twoE
      unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap
      unfold BONG.GoodBONG.orderGap at hrec
      rw [heq] at hrec
      push_cast at hrec hsum ⊢
      linarith
    refine (min_le_left _ _).trans ?_
    rw [BONG.GoodBONG.defectOrder_inv, ← a.coe_halfGapValue]
    have hhalfTop : (a.halfGapValue (2 : Fin 4) : WithTop ℚ) ≤
        ((2 * (ramificationIndex K : ℚ) -
          a.alphaValue (3 : Fin 4) : ℚ) : WithTop ℚ) := by
      exact_mod_cast hhalf
    exact hhalfTop.trans hrhoDepth

/-- The difficult sign branch of the rank-five argument.  A unit on the
complementary fourth-alpha layer is chosen negative against both relevant
Hilbert characters.  Multiplying the outward third-edge unit by this
correction flips both signs, while its greater defect leaves the two exact
third-alpha products unchanged. -/
theorem reachable_rankFive_data_negative_of_prepared
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a)
    (P : Lemma92RankFivePreparedData a)
    (hnegative : hilbertSymbol K
      ((P.theta : Kˣ) * a.adjacentProduct (2 : Fin 4))
        (P.omega : Kˣ) = -1) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i)
      ![a.valueUnit 0, a.valueUnit 1,
        P.unitChoice.epsilon * a.valueUnit 2,
        P.unitChoice.epsilon * P.unitChoice.eta * a.valueUnit 3,
        P.unitChoice.eta * a.valueUnit 4] := by
  let eta : valuationUnitSubgroup K :=
    ⟨P.unitChoice.eta, P.unitChoice.eta_isValuationUnit⟩
  have homegaDepth : BONG.GoodBONG.defectOrder (K := K) (P.omega : Kˣ) =
      (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    rw [← P.choiceEpsilon]
    exact P.unitChoice.epsilon_defect
  have htailMiddle : a.tail.tail.adjacentProduct (0 : Fin 2) =
      a.adjacentProduct (2 : Fin 4) := by
    rw [a.tail.adjacentProduct_tail, a.adjacentProduct_tail]
    congr 1
  have htailLast : a.tail.tail.adjacentProduct (1 : Fin 2) =
      a.adjacentProduct (3 : Fin 4) := by
    rw [a.tail.adjacentProduct_tail, a.adjacentProduct_tail]
    congr 1
  have homegaLast : BONG.GoodBONG.defectOrder (K := K)
      ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4)) =
        (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    rw [← htailLast, ← P.choiceEpsilon]
    exact P.unitChoice.scaledLastAdjacent_defect
  have hchoice : hilbertSymbol K
      ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4))
        P.unitChoice.eta =
      hilbertSymbol K (P.omega : Kˣ)
        (a.adjacentProduct (2 : Fin 4)) := by
    rw [← htailMiddle, ← htailLast, ← P.choiceEpsilon]
    exact P.unitChoice.hilbert_choice
  have hfourthPos : 0 < a.alphaValue (3 : Fin 4) :=
    BONG.GoodBONG.oddRationalInteger_pos_of_nonnegative
      D.fourthAlpha_odd D.fourthAlpha_nonnegative
  rcases exists_valuationUnit_of_complementary_odd_defect
      (a.alphaValue (3 : Fin 4)) D.fourthAlpha_odd hfourthPos
      D.fourthAlpha_lt_twoE with ⟨reference, hrefUnit, hrefDefect⟩
  have hrefGtThird : (a.alphaValue (2 : Fin 4) : WithTop ℚ) <
      BONG.GoodBONG.defectOrder (K := K) reference := by
    rw [hrefDefect]
    exact_mod_cast (show a.alphaValue (2 : Fin 4) <
        2 * (ramificationIndex K : ℚ) -
          a.alphaValue (3 : Fin 4) by
      linarith [D.thirdFourth_sum_lt_twoE])
  let X : Kˣ := (P.theta : Kˣ) * a.adjacentProduct (2 : Fin 4)
  have hXDefect : BONG.GoodBONG.defectOrder (K := K) X =
      (a.alphaValue (1 : Fin 4) : WithTop ℚ) := by
    simpa only [X] using P.thetaThirdProduct
  have hetaDefect : BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) =
      (a.alphaValue (3 : Fin 4) : WithTop ℚ) := by
    change BONG.GoodBONG.defectOrder (K := K) P.unitChoice.eta = _
    exact P.unitChoice.eta_defect
  have hle : a.alphaValue (1 : Fin 4) ≤
      a.alphaValue (3 : Fin 4) :=
    lemma92RankFiveData_secondAlpha_le_fourthAlpha a D
  have hXOrderSum : BONG.GoodBONG.defectOrder (K := K) X +
        BONG.GoodBONG.defectOrder (K := K) reference ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hXDefect, hrefDefect]
    exact_mod_cast (show a.alphaValue (1 : Fin 4) +
        (2 * (ramificationIndex K : ℚ) -
          a.alphaValue (3 : Fin 4)) ≤
        2 * (ramificationIndex K : ℚ) by linarith)
  have hetaOrderSum : BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) +
        BONG.GoodBONG.defectOrder (K := K) reference ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hetaDefect, hrefDefect]
    exact_mod_cast (show a.alphaValue (3 : Fin 4) +
        (2 * (ramificationIndex K : ℚ) -
          a.alphaValue (3 : Fin 4)) ≤
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
  have hrhoComplement :
      ((2 * (ramificationIndex K : ℚ) - a.alphaValue (3 : Fin 4) : ℚ) :
          WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) := by
    rw [← hrefDefect]
    exact hrhoDepth
  have hrhoGtThird : (a.alphaValue (2 : Fin 4) : WithTop ℚ) <
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) :=
    hrefGtThird.trans_le hrhoDepth
  let xi : valuationUnitSubgroup K := P.omega * rho
  have hxiDefect : BONG.GoodBONG.defectOrder (K := K) (xi : Kˣ) =
      (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    change BONG.GoodBONG.defectOrder (K := K)
      ((P.omega : Kˣ) * (rho : Kˣ)) = _
    rw [BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right
      (homegaDepth ▸ hrhoGtThird), homegaDepth]
  have hxiLast : BONG.GoodBONG.defectOrder (K := K)
      ((xi : Kˣ) * a.adjacentProduct (3 : Fin 4)) =
        (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
    have hfactor : (xi : Kˣ) * a.adjacentProduct (3 : Fin 4) =
        (rho : Kˣ) *
          ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4)) := by
      change ((P.omega : Kˣ) * (rho : Kˣ)) *
        a.adjacentProduct (3 : Fin 4) = _
      ac_rfl
    rw [hfactor, BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
      (homegaLast ▸ hrhoGtThird), homegaLast]
  have hxiHilbert : hilbertSymbol K
      ((P.theta : Kˣ) * a.adjacentProduct (2 : Fin 4)) (xi : Kˣ) = 1 := by
    change hilbertSymbol K X ((P.omega : Kˣ) * (rho : Kˣ)) = 1
    rw [hilbertSymbol_mul_right, hnegative, hrhoX]
    norm_num
  have hA₂Omega : hilbertSymbol K (a.adjacentProduct (2 : Fin 4))
      (P.omega : Kˣ) = -1 := by
    rw [hilbertSymbol_mul_left, P.thetaOmegaHilbert] at hnegative
    simpa using hnegative
  have hbaseEta : hilbertSymbol K
      ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4))
        P.unitChoice.eta = -1 := by
    rw [hchoice, hilbertSymbol_comm K (P.omega : Kˣ)
      (a.adjacentProduct (2 : Fin 4)), hA₂Omega]
  have hxiEta : hilbertSymbol K
      ((xi : Kˣ) * a.adjacentProduct (3 : Fin 4))
        P.unitChoice.eta = 1 := by
    rw [show (xi : Kˣ) * a.adjacentProduct (3 : Fin 4) =
        (rho : Kˣ) *
          ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4)) by
      change ((P.omega : Kˣ) * (rho : Kˣ)) *
        a.adjacentProduct (3 : Fin 4) = _
      ac_rfl,
      hilbertSymbol_mul_left,
      hilbertSymbol_comm K (rho : Kˣ) P.unitChoice.eta]
    change hilbertSymbol K (eta : Kˣ) (rho : Kˣ) *
      hilbertSymbol K
        ((P.omega : Kˣ) * a.adjacentProduct (3 : Fin 4))
          P.unitChoice.eta = 1
    rw [hrhoEta, hbaseEta]
    norm_num
  have hkappaEq :
      (((P.omega / xi : valuationUnitSubgroup K) : Kˣ)) =
        (rho : Kˣ)⁻¹ := by
    dsimp only [xi]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hkappaAlpha : rankFiveThirdBinaryAlphaAfterOuterMultipliers
        a (P.theta : Kˣ) P.unitChoice.eta ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((P.omega / xi : valuationUnitSubgroup K) : Kˣ)) := by
    rw [hkappaEq]
    exact rankFiveThirdAlphaAfterOuter_le_complement a D P rho hrhoComplement
  have hkappaHilbert : hilbertSymbol K
      (((P.theta : Kˣ) * P.unitChoice.eta) *
        a.adjacentProduct (2 : Fin 4))
      (((P.omega / xi : valuationUnitSubgroup K) : Kˣ)) = 1 :=
    hilbertSymbol_sevenStep_middle_closure
      (a.adjacentProduct (2 : Fin 4))
      (a.adjacentProduct (3 : Fin 4))
      (P.theta : Kˣ) (P.omega : Kˣ) (xi : Kˣ)
      P.unitChoice.eta P.thetaOmegaHilbert hxiHilbert hxiEta hchoice
  exact reachable_rankFive_data_scaling_of_prepared a D P xi
    hxiDefect.ge hxiHilbert hxiLast hxiEta hkappaAlpha hkappaHilbert

/-- Complete path-level rank-five branch of Lemma 9.2 over a dyadic field
whose residue field has more than two elements. -/
theorem reachableLemma92_rankFiveData_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    ∃ U : BONG.GoodBONG.Lemma92TernaryUnitChoiceData a.tail.tail
        (a.alphaValue (2 : Fin 4)) (a.alphaValue (3 : Fin 4)),
      Beli2009BinaryReachable (K := K)
        (fun i ↦ a.valueUnit i)
        ![a.valueUnit 0, a.valueUnit 1,
          U.epsilon * a.valueUnit 2,
          U.epsilon * U.eta * a.valueUnit 3,
          U.eta * a.valueUnit 4] := by
  rcases exists_lemma92RankFivePreparedData_of_largeResidue hres a D with ⟨P⟩
  rcases Int.units_eq_one_or (hilbertSymbol K
      ((P.theta : Kˣ) * a.adjacentProduct (2 : Fin 4))
        (P.omega : Kˣ)) with hpositive | hnegative
  · exact ⟨P.unitChoice,
      reachable_rankFive_data_positive_of_prepared a D P hpositive⟩
  · exact ⟨P.unitChoice,
      reachable_rankFive_data_negative_of_prepared a D P hnegative⟩

/-- Path-refined rank-five branch: the explicit seven-step endpoint and the
Section 8 rank-five realization use the same units, hence the good BONG in
Lemma 9.2 is literally reachable by adjacent binary transformations. -/
theorem reachableLemma92Transform_rankFiveData_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 5)
    (D : BONG.GoodBONG.Lemma92RankFiveData a) :
    Nonempty (ReachableLemma92Transform a) := by
  rcases reachableLemma92_rankFiveData_of_largeResidue hres a D with
    ⟨U, hreach⟩
  rcases a.exists_lemma92LaterScalingData
      U.epsilon U.eta U.epsilon_isValuationUnit U.eta_isValuationUnit
      U.epsilon_defect U.eta_defect U.adjacent_hilbert
      D.firstBinary_normalized D.commonRightEndpoint
      (le_of_lt D.thirdFourth_sum_lt_twoE) with ⟨S⟩
  have htarget :
      ![a.valueUnit 0, a.valueUnit 1,
        U.epsilon * a.valueUnit 2,
        U.epsilon * U.eta * a.valueUnit 3,
        U.eta * a.valueUnit 4] =
        (fun i ↦ S.transformed.valueUnit i) := by
    funext i
    fin_cases i
    · simpa using S.firstValue_eq.symm
    · simpa using S.secondValue_eq.symm
    · simpa using S.thirdValue_eq.symm
    · simpa using S.fourthValue_eq.symm
    · simpa using S.fifthValue_eq.symm
  have hreachS : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i)
      (fun i ↦ S.transformed.valueUnit i) := by
    exact htarget ▸ hreach
  have hbase : S.transformed.alphaValue (3 : Fin 4) =
      S.transformed.tail.alphaValue (2 : Fin 3) := by
    apply BONG.GoodBONG.alphaValue_shift_eq_tail_of_invariant_nextAdjacentDefect
      (a := a) (c := S.transformed) (p := (2 : Fin 3))
    · exact D.fourthAlpha_recursion
    · change S.transformed.adjacentDefect (3 : Fin 4) =
          (a.alphaValue (2 : Fin 4) : WithTop ℚ)
      rw [S.adjacentDefect_three]
      exact D.scaledLastAdjacent_defect U
  refine ⟨reachableLemma92TransformOfSelfTailAgreement
    a S.transformed hreachS S.firstValue_eq ?_ ?_⟩
  · intro i hi
    have hpi : (2 : Fin 3) ≤ i := by
      change (2 : Nat) ≤ i.1
      omega
    exact S.transformed.alphaValue_shift_eq_tail_of_base_eq
      (2 : Fin 3) i hpi hbase
  · intro hearly
    exact (D.notEarly hearly).elim

/-- Complete path-refined Lemma 9.2 for a normalized rank-five good BONG in
the complement of the early alternative. -/
theorem reachableLemma92Transform_rankFive_normalized_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 5)
    (hnotEarly : ¬a.Lemma92EarlyAlternative)
    (hbinary : a.adjacentBinaryAlpha (0 : Fin 4) =
      (a.alphaValue (0 : Fin 4) : WithTop ℚ)) :
    Nonempty (ReachableLemma92Transform a) := by
  rcases a.rankFive_reduction_of_normalized hnotEarly hbinary with heq | D
  · exact ⟨reachableLemma92TransformIdentity a
      (by
        intro i hi
        fin_cases i <;> simp_all)
      (by intro hearly; exact (hnotEarly hearly).elim)⟩
  · exact reachableLemma92Transform_rankFiveData_of_largeResidue hres a D

/-- Corollary 8.10 removes the first-binary normalization hypothesis.  The
path to that normal form is concatenated with the normalized rank-five path,
and alpha invariance rebases the Lemma 9.2 certificate to the original good
BONG. -/
theorem reachableLemma92Transform_rankFive_of_notEarly_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONG.DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 5)
    (hnotEarly : ¬a.Lemma92EarlyAlternative) :
    Nonempty (ReachableLemma92Transform a) := by
  rcases reachableCorollary810_of_largeResidue a hres with ⟨R⟩
  let b : BONG.GoodBONG q L 5 := R.data.transformed
  have hbNotEarly : ¬b.Lemma92EarlyAlternative := by
    intro hb
    exact hnotEarly
      ((a.lemma92EarlyAlternative_iff_of_sameLattice_rankFive b).mpr hb)
  have hbinary : b.adjacentBinaryAlpha (0 : Fin 4) =
      (b.alphaValue (0 : Fin 4) : WithTop ℚ) := by
    rw [b.adjacentBinaryAlpha_zero]
    exact R.data.firstBinaryAlpha_eq
  rcases reachableLemma92Transform_rankFive_normalized_of_largeResidue
      hres b hbNotEarly hbinary with ⟨T⟩
  let transform : a.Beli2019Lemma92Transform := {
    transformed := T.transform.transformed
    firstValue_eq := T.transform.firstValue_eq.trans R.data.headValue_eq
    laterAlpha_eq_tail := by
      intro i hi
      exact (a.alpha_invariant b i.succ).trans
        (T.transform.laterAlpha_eq_tail i hi)
    earlyAlpha_eq_tail := by
      intro hearly
      exact (hnotEarly hearly).elim
  }
  exact ⟨{
    transform := transform
    reachable := R.reachable.trans T.reachable
  }⟩

/-! ## Lifting the low-rank paths to arbitrary rank -/

set_option maxHeartbeats 800000 in
-- This is the path-refined counterpart of the existing local-to-global
-- proof and carries the same dependent segment-index comparisons.
/-- A reachable transform of the initial quaternary segment lifts to a
reachable full Lemma 9.2 transform in the early branch. -/
theorem reachableLemma92Transform_of_initialFourTransform
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (T : ReachableLemma92Transform a.lemma92InitialFour)
    (hlocalEarly : a.lemma92InitialFour.Lemma92EarlyAlternative) :
    Nonempty (ReachableLemma92Transform a) := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma92InitialFourSegment
      T.transform.transformed.toBONG T.transform.transformed.good with ⟨R⟩
  let d : BONG.GoodBONG q L (N + 4) := ⟨R.bong, R.good⟩
  have hvalues (i : Fin 4) : d.valueUnit ⟨i.1, by omega⟩ =
      T.transform.transformed.valueUnit i := by
    simpa only [d, zero_add] using
      (segmentReplacement_valueUnit_inside a a.lemma92InitialFourSegment
        T.transform.transformed R i)
  have hreachRaw := reachable_of_prefixSegmentReplacement
    (n := N + 4) (M := 3) (S := N) (by omega) a
      a.lemma92InitialFourSegment T.transform.transformed R T.reachable
  have hreindexed := Beli2009BinaryReachable.castLength
    (show 3 + N = N + 3 by omega) hreachRaw
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ d.valueUnit i) := by
    simpa [d] using hreindexed
  have hfirst : d.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4)) := by
    calc
      d.valueUnit (0 : Fin (N + 4)) =
          T.transform.transformed.valueUnit (0 : Fin 4) := hvalues 0
      _ = a.lemma92InitialFour.valueUnit (0 : Fin 4) :=
        T.transform.firstValue_eq
      _ = a.valueUnit (0 : Fin (N + 4)) :=
        a.lemma92InitialFour_valueUnit_eq 0
  have htailValues (i : Fin 3) :
      d.lemma92TailInitialThree.valueUnit i =
        T.transform.transformed.tail.valueUnit i := by
    calc
      d.lemma92TailInitialThree.valueUnit i =
          d.valueUnit ⟨i.1 + 1, by omega⟩ :=
        d.lemma92TailInitialThree_valueUnit_eq i
      _ = T.transform.transformed.valueUnit i.succ := by
        have hindex : (⟨i.1 + 1, by omega⟩ : Fin (N + 4)) =
            ⟨i.succ.1, by omega⟩ := Fin.ext (by simp)
        rw [hindex]
        exact hvalues i.succ
      _ = T.transform.transformed.tail.valueUnit i :=
        (T.transform.transformed.valueUnit_goodTail i).symm
  have htailAlpha : d.lemma92TailInitialThree.alpha (1 : Fin 2) =
      T.transform.transformed.tail.alpha (1 : Fin 2) :=
    d.lemma92TailInitialThree.alpha_eq_of_valueUnits_eq
      T.transform.transformed.tail htailValues (1 : Fin 2)
  have hlocalEquality : T.transform.transformed.alpha (2 : Fin 3) =
      T.transform.transformed.tail.alpha (1 : Fin 2) := by
    have hq : T.transform.transformed.alphaValue (2 : Fin 3) =
        T.transform.transformed.tail.alphaValue (1 : Fin 2) := by
      calc
        T.transform.transformed.alphaValue (2 : Fin 3) =
            a.lemma92InitialFour.alphaValue (2 : Fin 3) :=
          (a.lemma92InitialFour.alpha_invariant T.transform.transformed
            (2 : Fin 3)).symm
        _ = T.transform.transformed.tail.alphaValue (1 : Fin 2) :=
          T.transform.earlyAlpha_eq_tail hlocalEarly
    rw [← T.transform.transformed.coe_alphaValue,
      ← T.transform.transformed.tail.coe_alphaValue]
    exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hq
  have hlocalBound : T.transform.transformed.alpha (2 : Fin 3) ≤
      T.transform.transformed.leftDefectCandidate
        (2 : Fin 3) (0 : Fin 3) :=
    T.transform.transformed.alpha_le_leftDefectCandidate (Fin.zero_le _)
  have hcandidate := BONG.GoodBONG.initialFour_leftCandidate_eq
    (a := a) (d := d) T.transform.transformed hvalues
  have hfirstBound : d.tail.alpha (1 : Fin (N + 2)) ≤
      d.leftDefectCandidate (2 : Fin (N + 3)) (0 : Fin (N + 3)) := by
    calc
      d.tail.alpha (1 : Fin (N + 2)) ≤
          d.lemma92TailInitialThree.alpha (1 : Fin 2) :=
        d.tailAlpha_one_le_initialThree
      _ = T.transform.transformed.tail.alpha (1 : Fin 2) := htailAlpha
      _ = T.transform.transformed.alpha (2 : Fin 3) := hlocalEquality.symm
      _ ≤ T.transform.transformed.leftDefectCandidate
          (2 : Fin 3) (0 : Fin 3) := hlocalBound
      _ = d.leftDefectCandidate (2 : Fin (N + 3))
          (0 : Fin (N + 3)) := hcandidate.symm
  have hbase : d.alphaValue (2 : Fin (N + 3)) =
      d.tail.alphaValue (1 : Fin (N + 2)) := by
    apply WithTop.coe_injective
    rw [d.coe_alphaValue, d.tail.coe_alphaValue]
    exact le_antisymm (d.alpha_shift_le_tail (1 : Fin (N + 2)))
      (d.tailAlpha_le_shift_of_firstLeftDefectBound
        (1 : Fin (N + 2)) hfirstBound)
  refine ⟨reachableLemma92TransformOfSelfTailAgreement
    a d hreach hfirst ?_ ?_⟩
  · intro i hi
    have hpi : (1 : Fin (N + 2)) ≤ i := by
      change (1 : Nat) ≤ i.1
      omega
    exact d.alphaValue_shift_eq_tail_of_base_eq
      (1 : Fin (N + 2)) i hpi hbase
  · intro _
    exact hbase

set_option maxHeartbeats 800000 in
-- The rank-five lift has the same finite-candidate and segment-index load at
-- one additional coefficient.
/-- A reachable transform of the initial quinary segment lifts to a
reachable full Lemma 9.2 transform when the early alternative is absent. -/
theorem reachableLemma92Transform_of_initialFiveTransform
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 5))
    (T : ReachableLemma92Transform a.lemma92InitialFive)
    (hnotEarly : ¬a.Lemma92EarlyAlternative) :
    Nonempty (ReachableLemma92Transform a) := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma92InitialFiveSegment
      T.transform.transformed.toBONG T.transform.transformed.good with ⟨R⟩
  let d : BONG.GoodBONG q L (N + 5) := ⟨R.bong, R.good⟩
  have hvalues (i : Fin 5) : d.valueUnit ⟨i.1, by omega⟩ =
      T.transform.transformed.valueUnit i := by
    simpa only [d, zero_add] using
      (segmentReplacement_valueUnit_inside a a.lemma92InitialFiveSegment
        T.transform.transformed R i)
  have hreachRaw := reachable_of_prefixSegmentReplacement
    (n := N + 5) (M := 4) (S := N) (by omega) a
      a.lemma92InitialFiveSegment T.transform.transformed R T.reachable
  have hreindexed := Beli2009BinaryReachable.castLength
    (show 4 + N = N + 4 by omega) hreachRaw
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ d.valueUnit i) := by
    simpa [d] using hreindexed
  have hfirst : d.valueUnit (0 : Fin (N + 5)) =
      a.valueUnit (0 : Fin (N + 5)) := by
    calc
      d.valueUnit (0 : Fin (N + 5)) =
          T.transform.transformed.valueUnit (0 : Fin 5) := hvalues 0
      _ = a.lemma92InitialFive.valueUnit (0 : Fin 5) :=
        T.transform.firstValue_eq
      _ = a.valueUnit (0 : Fin (N + 5)) :=
        a.lemma92InitialFive_valueUnit_eq 0
  have htailValues (i : Fin 4) :
      d.lemma92TailInitialFour.valueUnit i =
        T.transform.transformed.tail.valueUnit i := by
    calc
      d.lemma92TailInitialFour.valueUnit i =
          d.valueUnit ⟨i.1 + 1, by omega⟩ :=
        d.lemma92TailInitialFour_valueUnit_eq i
      _ = T.transform.transformed.valueUnit i.succ := by
        have hindex : (⟨i.1 + 1, by omega⟩ : Fin (N + 5)) =
            ⟨i.succ.1, by omega⟩ := Fin.ext (by simp)
        rw [hindex]
        exact hvalues i.succ
      _ = T.transform.transformed.tail.valueUnit i :=
        (T.transform.transformed.valueUnit_goodTail i).symm
  have htailAlpha : d.lemma92TailInitialFour.alpha (2 : Fin 3) =
      T.transform.transformed.tail.alpha (2 : Fin 3) :=
    d.lemma92TailInitialFour.alpha_eq_of_valueUnits_eq
      T.transform.transformed.tail htailValues (2 : Fin 3)
  have hlocalEquality : T.transform.transformed.alpha (3 : Fin 4) =
      T.transform.transformed.tail.alpha (2 : Fin 3) := by
    have hq : T.transform.transformed.alphaValue (3 : Fin 4) =
        T.transform.transformed.tail.alphaValue (2 : Fin 3) := by
      calc
        T.transform.transformed.alphaValue (3 : Fin 4) =
            a.lemma92InitialFive.alphaValue (3 : Fin 4) :=
          (a.lemma92InitialFive.alpha_invariant T.transform.transformed
            (3 : Fin 4)).symm
        _ = T.transform.transformed.tail.alphaValue (2 : Fin 3) :=
          T.transform.laterAlpha_eq_tail (2 : Fin 3) (by norm_num)
    rw [← T.transform.transformed.coe_alphaValue,
      ← T.transform.transformed.tail.coe_alphaValue]
    exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hq
  have hlocalBound : T.transform.transformed.alpha (3 : Fin 4) ≤
      T.transform.transformed.leftDefectCandidate
        (3 : Fin 4) (0 : Fin 4) :=
    T.transform.transformed.alpha_le_leftDefectCandidate (Fin.zero_le _)
  have hcandidate := BONG.GoodBONG.initialFive_leftCandidate_eq
    (a := a) (d := d) T.transform.transformed hvalues
  have hfirstBound : d.tail.alpha (2 : Fin (N + 3)) ≤
      d.leftDefectCandidate (3 : Fin (N + 4)) (0 : Fin (N + 4)) := by
    calc
      d.tail.alpha (2 : Fin (N + 3)) ≤
          d.lemma92TailInitialFour.alpha (2 : Fin 3) :=
        d.tailAlpha_two_le_initialFour
      _ = T.transform.transformed.tail.alpha (2 : Fin 3) := htailAlpha
      _ = T.transform.transformed.alpha (3 : Fin 4) := hlocalEquality.symm
      _ ≤ T.transform.transformed.leftDefectCandidate
          (3 : Fin 4) (0 : Fin 4) := hlocalBound
      _ = d.leftDefectCandidate (3 : Fin (N + 4))
          (0 : Fin (N + 4)) := hcandidate.symm
  have hbase : d.alphaValue (3 : Fin (N + 4)) =
      d.tail.alphaValue (2 : Fin (N + 3)) := by
    apply WithTop.coe_injective
    rw [d.coe_alphaValue, d.tail.coe_alphaValue]
    exact le_antisymm (d.alpha_shift_le_tail (2 : Fin (N + 3)))
      (d.tailAlpha_le_shift_of_firstLeftDefectBound
        (2 : Fin (N + 3)) hfirstBound)
  refine ⟨reachableLemma92TransformOfSelfTailAgreement
    a d hreach hfirst ?_ ?_⟩
  · intro i hi
    have hpi : (2 : Fin (N + 3)) ≤ i := by
      change (2 : Nat) ≤ i.1
      omega
    exact d.alphaValue_shift_eq_tail_of_base_eq
      (2 : Fin (N + 3)) i hpi hbase
  · intro hearly
    exact (hnotEarly hearly).elim

/-- Path-refined Lemma 9.2 in every rank at least five.  The early branch is
solved on the initial four coefficients and the complementary branch on the
initial five coefficients, exactly as in the printed proof. -/
theorem reachableLemma92Transform_rankAtLeastFive_of_largeResidue
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
    {N : Nat} (a : BONG.GoodBONG q L (N + 5)) :
    Nonempty (ReachableLemma92Transform a) := by
  by_cases hearly : a.Lemma92EarlyAlternative
  · have hlocalEarly : a.lemma92InitialFour.Lemma92EarlyAlternative :=
      a.lemma92InitialFour_earlyAlternative_iff.mpr hearly
    rcases reachableLemma92Transform_rankFour_of_largeResidue
        hres a.lemma92InitialFour with ⟨T⟩
    exact reachableLemma92Transform_of_initialFourTransform
      a T hlocalEarly
  · have hlocalNotEarly :
        ¬a.lemma92InitialFive.Lemma92EarlyAlternative := by
      intro hlocal
      exact hearly (a.lemma92InitialFive_earlyAlternative_iff.mp hlocal)
    rcases reachableLemma92Transform_rankFive_of_notEarly_of_largeResidue
        hres a.lemma92InitialFive hlocalNotEarly with ⟨T⟩
    exact reachableLemma92Transform_of_initialFiveTransform a T hearly

/-- Path-refined Beli (2019), Lemma 9.2 for every rank `n ≥ 4`. -/
theorem reachableLemma92Transform_of_largeResidue
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
    {N : Nat} (a : BONG.GoodBONG q L (N + 4)) :
    Nonempty (ReachableLemma92Transform a) := by
  cases N with
  | zero =>
      exact reachableLemma92Transform_rankFour_of_largeResidue hres a
  | succ N =>
      exact reachableLemma92Transform_rankAtLeastFive_of_largeResidue hres a

end Beli2009FinalRemarksProof.LargeResidueConnectivity

end Bong
