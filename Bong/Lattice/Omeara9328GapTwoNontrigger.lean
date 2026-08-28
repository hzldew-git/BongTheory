/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328GapTwoDeterminantCorrection

/-!
# O'Meara 93:28, Step 7: the non-condition-(iii) branch

When the relative second scale has order one and the normalized norm orders
differ by two, failure of condition 93:28(iii) puts both discriminant twists
of the odd rank-four `K`-model in the second norm group.  Two explicit 93:19
exchanges replace the `K`-head by the untwisted `J`-head while preserving the
second component norm generator.  This closes the remaining branch of Step 7.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

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

/-- Convert a generator-dependent gap-two equality to the coherent generator
used in the numerical Step-7 lemmas. -/
theorem gapTwoCanonicalGap
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2) :
    ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 2 := by
  rw [← S.secondNormalizedNormGeneratorWith_order_eq A]
  exact hgap

/-- The twist attached to the corrected head norm generator is represented
by the corrected normalized tail. -/
theorem gapTwoKLeftTwist_mem
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions hgap hscale)
    ((-Lattice.scratch_omearaRhoTwistUnit N.parameters.a : Kˣ) : K) ∈
      normGroupSet (D.newTail hunit) (D.newTailLattice hunit) := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions hgap hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  apply (D.tailShift hunit).normGroup_subset
  apply S.scratch_mem_targetSecondNormalized_of_weight_order_le
  have hcanonical := S.gapTwoCanonicalGap A hgap
  have hnon := S.gapTwo_nontriggerIII_weight_order
    A hcanonical hscale hnontrigger
  have hfirstWeight := S.scratch_firstNormalized_weightIdealOrder_eq
  have hnormLe := normGeneratorOrder_le_weightIdealOrder
    D.firstGenerator D.firstGenerator_sourceFirst
  rw [hfirstWeight] at hnormLe
  rw [Lattice.scratch_neg_omearaRhoTwistUnit_order, N.parameters_a]
  have hfirstOrder : ordUnit K D.firstGenerator =
      ordUnit K S.firstNormGenerator := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact D.firstGenerator_sourceFirst.2.symm.trans
      S.firstNormGenerator_source.2
  omega

/-- The twist attached to the corrected head weight generator is represented
by the corrected normalized tail. -/
theorem gapTwoKRightTwist_mem
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions hgap hscale)
    ((-Lattice.scratch_omearaRhoTwistUnit N.parameters.b : Kˣ) : K) ∈
      normGroupSet (D.newTail hunit) (D.newTailLattice hunit) := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions hgap hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  apply (D.tailShift hunit).normGroup_subset
  apply S.gapTwo_neg_weightTwist_mem_targetSecondNormalized
    A (S.gapTwoCanonicalGap A hgap) hscale hnontrigger N.parameters.b
  rw [N.parameters_b, ordUnit_uniformizerPowerUnit,
    ← D.correctedHead_weightIdealOrder_eq_source hunit]

/-- The two coefficient exchanges which turn the odd `K`-head into the
untwisted `J`-head. -/
noncomputable def gapTwoKRhoTwistAbsorptionData
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions hgap hscale)
    Lattice.Omeara9318RankFourModelParameters.RhoTwistAbsorptionData
      N.parameters (D.newTail hunit) (D.newTailLattice hunit)
        S.relativeSecondScale := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions hgap hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  exact N.parameters.rhoTwistAbsorptionData N.alpha_zero
    (D.tailShift hunit).splitting.complement_modular
    (D.newTail_finrank hunit)
    S.relativeSecondScale_isInMaximalIdeal
    (S.gapTwoKLeftTwist_mem A conditions hgap hscale hnontrigger hodd)
    (S.gapTwoKRightTwist_mem A conditions hgap hscale hnontrigger hodd)

/-- In the odd twisted-model branch, the original normalized target pair is
isometric to the untwisted `J`-head followed by the twice-shifted tail. -/
noncomputable def gapTwoKNormalizedPairIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions hgap hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions hgap hscale)
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions hgap hscale
      hnontrigger hodd
    Isometry
      (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
      (N.parameters.jData.space.orthogonalSum B.tailSpace)
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product N.parameters.jData.lattice B.tailLattice) := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions hgap hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions hgap hscale
    hnontrigger hodd
  let identifyK := (Classical.choice hk).orthogonalProductBasic
    (Isometry.refl (D.newTail hunit) (D.newTailLattice hunit))
  exact (D.normalizedPairIsometry hunit).trans
    (identifyK.trans B.pairIsometry)

set_option maxHeartbeats 3000000 in
/-- Both 93:19 exchanges preserve the coherent second norm generator.  The
model tails are controlled by the actual represented twists; this is the
Step-7 use of `a₂ O ⊇ 4 a₁⁻¹ O`, rather than an unjustified equality of
the head-weight and second norm ideals. -/
theorem gapTwoKTail_normGenerator
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions hgap hscale
      hnontrigger hodd
    IsNormGeneratorValue B.tailSpace B.tailLattice D.secondGenerator := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions hgap hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions hgap hscale
    hnontrigger hodd
  have hfirstOrder : ordUnit K D.firstGenerator =
      ordUnit K S.firstNormGenerator := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact D.firstGenerator_sourceFirst.2.symm.trans
      S.firstNormGenerator_source.2
  have hsecondChoice : ordUnit K D.secondGenerator =
      ordUnit K (S.secondNormalizedNormGeneratorWith A) := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact D.secondGenerator_targetSecond.2.symm.trans
      (S.secondNormalizedNormGeneratorWith_target A).2
  have hsecondOrder : ordUnit K D.secondGenerator =
      ordUnit K D.firstGenerator + 2 := by
    rw [hsecondChoice, hgap, hfirstOrder]
  have hleftNeg := S.gapTwoKLeftTwist_mem A conditions hgap hscale
    hnontrigger hodd
  have hrightNeg := S.gapTwoKRightTwist_mem A conditions hgap hscale
    hnontrigger hodd
  have hleftMem : N.parameters.kData.leftTail ∈
      normGroupSet (D.newTail hunit) (D.newTailLattice hunit) := by
    have h := neg_mem_normGroupSet (D.newTail hunit)
      (D.newTailLattice hunit) hleftNeg
    simpa only [Omeara9318RankFourModelParameters.kData,
      N.alpha_zero, zero_sub, Units.val_neg, neg_neg,
      Lattice.scratch_omearaRhoTwistUnit_coe] using h
  have hrightMem : N.parameters.kData.rightTail ∈
      normGroupSet (D.newTail hunit) (D.newTailLattice hunit) := by
    have h := neg_mem_normGroupSet (D.newTail hunit)
      (D.newTailLattice hunit) hrightNeg
    simpa only [Omeara9318RankFourModelParameters.kData,
      Units.val_neg, neg_neg,
      Lattice.scratch_omearaRhoTwistUnit_coe] using h
  have hleftTail : N.parameters.kData.leftTail ∈
      principalIdeal (K := K) (D.secondGenerator : K) := by
    rw [← (D.newTail_secondGenerator hunit).2]
    exact normGroupSet_subset_normIdeal
      (D.newTail hunit) (D.newTailLattice hunit) hleftMem
  have hrightTail : N.parameters.kData.rightTail ∈
      principalIdeal (K := K) (D.secondGenerator : K) := by
    rw [← (D.newTail_secondGenerator hunit).2]
    exact normGroupSet_subset_normIdeal
      (D.newTail hunit) (D.newTailLattice hunit) hrightMem
  have hnormLeWeight : ordUnit K D.firstGenerator ≤
      weightIdealOrder (D.correctedHead hunit)
        (D.correctedHeadLattice hunit) :=
    normGeneratorOrder_le_weightIdealOrder D.firstGenerator
      (D.correctedHead_firstGenerator hunit)
  have hrightScaleSq : (N.parameters.b : K) *
      (S.relativeSecondScale : K) ^ 2 ∈
        principalIdeal (K := K) (D.secondGenerator : K) := by
    apply mem_principalIdeal_of_ord_le (Units.ne_zero D.secondGenerator)
    rw [ord_mul, ord_pow, ← coe_ordUnit, ← coe_ordUnit,
      ← coe_ordUnit]
    apply WithTop.coe_le_coe.mpr
    simp only [two_nsmul]
    rw [N.parameters_b, ordUnit_uniformizerPowerUnit, hsecondOrder, hscale]
    omega
  have hleftScaleSq : (N.parameters.a : K) *
      (S.relativeSecondScale : K) ^ 2 ∈
        principalIdeal (K := K) (D.secondGenerator : K) := by
    apply mem_principalIdeal_of_ord_le (Units.ne_zero D.secondGenerator)
    rw [ord_mul, ord_pow, ← coe_ordUnit, ← coe_ordUnit,
      ← coe_ordUnit]
    apply WithTop.coe_le_coe.mpr
    simp only [two_nsmul]
    rw [N.parameters_a, hsecondOrder, hscale]
    omega
  change IsNormGeneratorValue B.tailSpace B.tailLattice D.secondGenerator
  exact B.tailNormGenerator_of D.secondGenerator
    (D.newTail_secondGenerator hunit) hrightTail hrightScaleSq
      hleftTail hleftScaleSq

/-- The two numerical hypotheses defining the Step-7 case. -/
structure GapTwoCase
    (A : FundamentalNormGeneratorChoice S.sourceJordan) : Prop where
  hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
    ordUnit K S.firstNormGenerator + 2
  hscale : ordUnit K S.relativeSecondScale = 1

/-- Although the corrected head is the twisted `K`-model, the untwisted
`J`-model has the source norm group and the same hyperbolic underlying
space.  Unimodular classification gives the integral source-to-`J`
isometry used after twist absorption. -/
noncomputable def gapTwoKSourceToJHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    Isometry S.sourceFirstNormalized N.parameters.jData.space
      (S.sourceJordan.component 0).lattice
      N.parameters.jData.lattice := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  change Isometry S.sourceFirstNormalized N.parameters.jData.space
    (S.sourceJordan.component 0).lattice N.parameters.jData.lattice
  let kIso := Classical.choice hk
  have hgroup :
      normGroupSet S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice =
        normGroupSet N.parameters.jData.space N.parameters.jData.lattice := by
    calc
      normGroupSet S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice =
          normGroupSet (D.correctedHead hunit)
            (D.correctedHeadLattice hunit) :=
        D.correctedHead_normGroupSet_eq_source hunit
      _ = normGroupSet N.parameters.kData.space
          N.parameters.kData.lattice :=
        normGroupSet_eq_of_latticeIsometry kIso.symm
      _ = integralSquareCoset (N.parameters.a : K)
          (principalIdeal (K := K) (N.parameters.b : K)) :=
        N.parameters.k_normGroupSet_eq
      _ = normGroupSet N.parameters.jData.space
          N.parameters.jData.lattice :=
        N.parameters.j_normGroupSet_eq.symm
  let fieldIso := S.sourceFirstNormalizedHyperbolicTowerIsometry.trans
    (N.parameters.jSpaceToHyperbolicTowerIsometry N.alpha_zero).symm
  exact latticeIsometryToUnimodularModel
    S.sourceFirstNormalized_unimodular N.parameters.jData.isModular
      fieldIso hgroup

/-- The untwisted Step-7 head restored to the original first Jordan scale. -/
noncomputable abbrev gapTwoKHeadUnnormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    QuadraticSpace K ((Fin 2 → K) × (Fin 2 → K)) := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  exact N.parameters.jData.space.rescaleUnit S.firstScale

/-- The twice-shifted Step-7 tail restored to the original second Jordan
scale. -/
noncomputable abbrev gapTwoKTailUnnormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
      hnontrigger hodd
    QuadraticSpace K B.Tail := by
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
    hnontrigger hodd
  exact B.tailSpace.rescaleUnit S.firstScale

/-- Undo the common first-scale normalization after both Step-7 twists have
been absorbed. -/
noncomputable def gapTwoKOriginalPairIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
      hnontrigger hodd
    Isometry
      ((S.targetJordan.component 0).space.orthogonalSum
        (S.targetJordan.component 1).space)
      ((S.gapTwoKHeadUnnormalized A conditions C hodd).orthogonalSum
        (S.gapTwoKTailUnnormalized A conditions C hnontrigger hodd))
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product N.parameters.jData.lattice B.tailLattice) := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
    hnontrigger hodd
  let normalized := S.gapTwoKNormalizedPairIsometry A conditions
    C.hgap C.hscale hnontrigger hodd hk
  let scaled := normalized.rescaleUnitBoth S.firstScale
  let distributeSource := rescaleUnitOrthogonalProductIsometry
    S.targetFirstNormalized S.targetSecondNormalized
    (S.targetJordan.component 0).lattice
    (S.targetJordan.component 1).lattice S.firstScale
  let undoFirst : Isometry
      (S.targetFirstNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
      (S.targetJordan.component 0).lattice := by
    simpa only [targetFirstNormalized] using
      undoInverseRescaleLatticeIsometry
        (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice S.firstScale
  let undoSecond : Isometry
      (S.targetSecondNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 1).space
      (S.targetJordan.component 1).lattice
      (S.targetJordan.component 1).lattice := by
    simpa only [targetSecondNormalized] using
      undoInverseRescaleLatticeIsometry
        (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice S.firstScale
  let undoSource := distributeSource.trans
    (undoFirst.orthogonalProductBasic undoSecond)
  let distributeTarget := rescaleUnitOrthogonalProductIsometry
    N.parameters.jData.space B.tailSpace
    N.parameters.jData.lattice B.tailLattice S.firstScale
  exact undoSource.symm.trans (scaled.trans distributeTarget)

theorem gapTwoKHeadUnnormalized_modular
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    IsModular (S.gapTwoKHeadUnnormalized A conditions C hodd)
      N.parameters.jData.lattice (S.targetJordan.scaleGenerator 0) := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  have h := N.parameters.jData.isModular.rescaleQuadraticUnit S.firstScale
  simpa only [gapTwoKHeadUnnormalized, S.targetJordan_scaleGenerator,
    Omeara9328RankFourReductionSystem.firstScale, mul_one] using h

theorem gapTwoKTailUnnormalized_modular
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
      hnontrigger hodd
    IsModular
      (S.gapTwoKTailUnnormalized A conditions C hnontrigger hodd)
      B.tailLattice (S.targetJordan.scaleGenerator 1) := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
    hnontrigger hodd
  have h := B.tailModular.rescaleQuadraticUnit S.firstScale
  simpa only [gapTwoKTailUnnormalized,
    GapTwoErrorData.firstScale_mul_relativeSecondScale (S := S)] using h

theorem gapTwoKHeadUnnormalized_scaleIdeal
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    scaleIdeal (S.gapTwoKHeadUnnormalized A conditions C hodd)
        N.parameters.jData.lattice =
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 0 : K) := by
  exact (S.gapTwoKHeadUnnormalized_modular A conditions C hodd)
    |>.scaleIdeal_eq_principal (by
      simp only [Module.finrank_prod, Module.finrank_fin_fun]
      omega)

theorem gapTwoKTailUnnormalized_scaleIdeal
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
      hnontrigger hodd
    scaleIdeal
        (S.gapTwoKTailUnnormalized A conditions C hnontrigger hodd)
        B.tailLattice =
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 1 : K) := by
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
    hnontrigger hodd
  exact (S.gapTwoKTailUnnormalized_modular A conditions C
    hnontrigger hodd).scaleIdeal_eq_principal (by rw [B.tailFinrank]; omega)

theorem gapTwoKHeadUnnormalized_normGenerator
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    IsNormGeneratorValue
      (S.gapTwoKHeadUnnormalized A conditions C hodd)
      N.parameters.jData.lattice (S.firstScale * D.firstGenerator) := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  change IsNormGeneratorValue
    (N.parameters.jData.space.rescaleUnit S.firstScale)
    N.parameters.jData.lattice (S.firstScale * D.firstGenerator)
  have h := N.parameters.jData.a_isNormGeneratorValue
    |>.rescaleQuadraticUnit S.firstScale
  simpa only [Omeara9318RankFourModelParameters.jData,
    N.parameters_a] using h

theorem gapTwoKTailUnnormalized_normGenerator
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
      hnontrigger hodd
    IsNormGeneratorValue
      (S.gapTwoKTailUnnormalized A conditions C hnontrigger hodd)
      B.tailLattice (S.firstScale * D.secondGenerator) := by
  have h := S.gapTwoKTail_normGenerator A conditions C.hgap C.hscale
    hnontrigger hodd |>.rescaleQuadraticUnit S.firstScale
  simpa only [gapTwoKTailUnnormalized] using h

theorem gapTwoKHeadUnnormalized_normIdeal
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    normIdeal (S.gapTwoKHeadUnnormalized A conditions C hodd)
        N.parameters.jData.lattice =
      principalIdeal (K := K) (S.targetJordan.normGenerator 0 : K) := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  calc
    normIdeal (S.gapTwoKHeadUnnormalized A conditions C hodd)
        N.parameters.jData.lattice =
        principalIdeal (K := K)
          ((S.firstScale * D.firstGenerator : Kˣ) : K) :=
      (S.gapTwoKHeadUnnormalized_normGenerator A conditions C hodd).2
    _ = normIdeal (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice :=
      D.targetFirst_unscaledNormGenerator.2.symm
    _ = principalIdeal (K := K) (S.targetJordan.normGenerator 0 : K) :=
      S.targetJordan.normIdeal_eq 0

theorem gapTwoKTailUnnormalized_normIdeal
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
      hnontrigger hodd
    normIdeal
        (S.gapTwoKTailUnnormalized A conditions C hnontrigger hodd)
        B.tailLattice =
      principalIdeal (K := K) (S.targetJordan.normGenerator 1 : K) := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
    hnontrigger hodd
  calc
    normIdeal
        (S.gapTwoKTailUnnormalized A conditions C hnontrigger hodd)
        B.tailLattice =
        principalIdeal (K := K)
          ((S.firstScale * D.secondGenerator : Kˣ) : K) :=
      (S.gapTwoKTailUnnormalized_normGenerator A conditions C
        hnontrigger hodd).2
    _ = normIdeal (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice :=
      D.targetSecond_unscaledNormGenerator.2.symm
    _ = principalIdeal (K := K) (S.targetJordan.normGenerator 1 : K) :=
      S.targetJordan.normIdeal_eq 1

/-- The restored untwisted head contains the original first-component norm
group. -/
theorem targetFirst_normGroupSet_subset_gapTwoKHeadUnnormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice ⊆
      normGroupSet (S.gapTwoKHeadUnnormalized A conditions C hodd)
        N.parameters.jData.lattice := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  let sourceToJ := S.gapTwoKSourceToJHeadIsometry
    A conditions C hodd hk
  have hnormalized :
      normGroupSet S.targetFirstNormalized
          (S.targetJordan.component 0).lattice =
        normGroupSet N.parameters.jData.space N.parameters.jData.lattice :=
    S.firstNormalized_normGroupSet_eq.symm.trans
      (normGroupSet_eq_of_latticeIsometry sourceToJ).symm
  change normGroupSet (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice ⊆
    normGroupSet (N.parameters.jData.space.rescaleUnit S.firstScale)
      N.parameters.jData.lattice
  intro z hz
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff, ← hnormalized,
    mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using hz

/-- The restored twice-shifted tail contains the original second-component
norm group. -/
theorem targetSecond_normGroupSet_subset_gapTwoKTailUnnormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
      hnontrigger hodd
    normGroupSet (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice ⊆
      normGroupSet
        (S.gapTwoKTailUnnormalized A conditions C hnontrigger hodd)
        B.tailLattice := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
    hnontrigger hodd
  change normGroupSet (S.targetJordan.component 1).space
      (S.targetJordan.component 1).lattice ⊆
    normGroupSet (B.tailSpace.rescaleUnit S.firstScale) B.tailLattice
  intro z hz
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  apply B.normGroup_subset
  apply (D.tailShift hunit).normGroup_subset
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using hz

/-- Regard the restored untwisted head and corrected tail as a decomposition
of the original target first-pair sublattice. -/
noncomputable def gapTwoKFirstPairReplacementIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
      hnontrigger hodd
    Isometry
      ((S.gapTwoKHeadUnnormalized A conditions C hodd).orthogonalSum
        (S.gapTwoKTailUnnormalized A conditions C hnontrigger hodd))
      S.targetJordan.firstPairSublattice.space
      (product N.parameters.jData.lattice B.tailLattice)
      S.targetJordan.firstPairSublattice.lattice :=
  (S.gapTwoKOriginalPairIsometry A conditions C
    hnontrigger hodd hk).symm |>.trans
      (S.targetJordan.toOrthogonalDecomposition
        |>.orthogonalSupLatticeIsometry firstIndex_ne_secondIndex)

set_option maxHeartbeats 3000000 in
/-- Install the nontrigger twisted-model correction as a saturated Jordan
splitting of the original target lattice. -/
noncomputable def gapTwoKJordanReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    Omeara9319JordanReplacement S.targetJordan := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
    hnontrigger hodd
  let f := S.gapTwoKFirstPairReplacementIsometry A conditions C
    hnontrigger hodd hk
  let hHeadMod := S.gapTwoKHeadUnnormalized_modular A conditions C hodd
  let hTailMod := S.gapTwoKTailUnnormalized_modular A conditions C
    hnontrigger hodd
  let hHeadScale := S.gapTwoKHeadUnnormalized_scaleIdeal
    A conditions C hodd
  let hTailScale := S.gapTwoKTailUnnormalized_scaleIdeal
    A conditions C hnontrigger hodd
  let hHeadNorm := S.gapTwoKHeadUnnormalized_normIdeal
    A conditions C hodd
  let hTailNorm := S.gapTwoKTailUnnormalized_normIdeal
    A conditions C hnontrigger hodd
  let T := S.targetJordan.replaceFirstPairOfIsometry f
    hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm
  exact
    { target := T
      fundamentalType :=
        S.targetJordan.replaceFirstPairOfIsometry_sameFundamentalType f
          hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm
      saturated :=
        S.targetJordan.replaceFirstPairOfIsometry_isSaturated f
          hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm
          S.targetJordan_isSaturated
          (S.targetFirst_normGroupSet_subset_gapTwoKHeadUnnormalized
            A conditions C hodd hk)
          (S.targetSecond_normGroupSet_subset_gapTwoKTailUnnormalized
            A conditions C hnontrigger hodd)
      laterPrefixIsometry := by
        intro k hk'
        exact S.targetJordan.toOrthogonalDecomposition
          |>.replacePair_first_prefixLatticeIsometry
            (S.targetJordan.firstPairDecompositionOfIsometry f) k hk' }

/-- Restore the normalized source-to-`J` isometry to the first Jordan
scale. -/
noncomputable def gapTwoKSourceToHeadUnnormalizedIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    Isometry (S.sourceJordan.component 0).space
      (S.gapTwoKHeadUnnormalized A conditions C hodd)
      (S.sourceJordan.component 0).lattice N.parameters.jData.lattice := by
  let normalized := S.gapTwoKSourceToJHeadIsometry
    A conditions C hodd hk
  let scaled := normalized.rescaleUnitBoth S.firstScale
  let undoSource := undoInverseRescaleLatticeIsometry
    (S.sourceJordan.component 0).space
    (S.sourceJordan.component 0).lattice S.firstScale
  exact undoSource.symm.trans scaled

set_option maxHeartbeats 3000000 in
/-- The displayed untwisted head maps onto the first component of the
installed nontrigger Step-7 replacement. -/
noncomputable def gapTwoKReplacementHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let N := D.correctedHeadOddDeterminantOneData hunit hodd
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions C.hgap C.hscale)
    let R := S.gapTwoKJordanReplacement A conditions C
      hnontrigger hodd hk
    Isometry (S.gapTwoKHeadUnnormalized A conditions C hodd)
      (R.target.component 0).space N.parameters.jData.lattice
      (R.target.component 0).lattice := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  let B := S.gapTwoKRhoTwistAbsorptionData A conditions C.hgap C.hscale
    hnontrigger hodd
  let f := S.gapTwoKFirstPairReplacementIsometry A conditions C
    hnontrigger hodd hk
  let hHeadMod := S.gapTwoKHeadUnnormalized_modular A conditions C hodd
  let hTailMod := S.gapTwoKTailUnnormalized_modular A conditions C
    hnontrigger hodd
  let hHeadScale := S.gapTwoKHeadUnnormalized_scaleIdeal
    A conditions C hodd
  let hTailScale := S.gapTwoKTailUnnormalized_scaleIdeal
    A conditions C hnontrigger hodd
  let hHeadNorm := S.gapTwoKHeadUnnormalized_normIdeal
    A conditions C hodd
  let hTailNorm := S.gapTwoKTailUnnormalized_normIdeal
    A conditions C hnontrigger hodd
  let R := S.gapTwoKJordanReplacement A conditions C
    hnontrigger hodd hk
  change Isometry (S.gapTwoKHeadUnnormalized A conditions C hodd)
    (R.target.component 0).space N.parameters.jData.lattice
    (R.target.component 0).lattice
  rw [show R.target = S.targetJordan.replaceFirstPairOfIsometry f
      hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm by rfl]
  exact S.targetJordan.replaceFirstPairOfIsometry_leftIsometry f
    hHeadMod hTailMod hHeadScale hTailScale hHeadNorm hTailNorm

/-- Source head aligned with the actual first component of the installed
nontrigger replacement. -/
noncomputable def gapTwoKSourceToReplacementHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    let R := S.gapTwoKJordanReplacement A conditions C
      hnontrigger hodd hk
    Isometry (S.sourceJordan.component 0).space (R.target.component 0).space
      (S.sourceJordan.component 0).lattice (R.target.component 0).lattice :=
  (S.gapTwoKSourceToHeadUnnormalizedIsometry
    A conditions C hodd hk).trans
      (S.gapTwoKReplacementHeadIsometry A conditions C
        hnontrigger hodd hk)

/-- Complete Step-7 head alignment in the nontrigger twisted-model branch. -/
noncomputable def gapTwoHeadAlignedReplacementOfNontriggerK
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (hodd : Odd S.firstNormWeightParity)
    (hk : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.kData.space
        (D.correctedHeadLattice hunit) N.parameters.kData.lattice) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let R := S.gapTwoKJordanReplacement A conditions C
    hnontrigger hodd hk
  let head := S.gapTwoKSourceToReplacementHeadIsometry
    A conditions C hnontrigger hodd hk
  let boundary := omeara9328BoundaryZeroConditionsWith_of_headIsometry
    S.sourceJordan R.target A head
  exact R.headAlignedReplacement S.residualFundamentalType A conditions
    boundary head

/-- Nontrigger even-parity subcase of O'Meara 93:28, Step 7. -/
noncomputable def gapTwoHeadAlignedReplacementOfNontriggerEven
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (heven : Even S.firstNormWeightParity) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  exact S.gapTwoHeadAlignedReplacementOfNormalizedHead
    A conditions C.hgap C.hscale
      (D.sourceToCorrectedHeadEvenIsometry hunit heven hdet)

/-- Nontrigger odd-parity subcase in which 93:18(vi) selects the untwisted
`J`-model directly. -/
noncomputable def gapTwoHeadAlignedReplacementOfNontriggerJ
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hodd : Odd S.firstNormWeightParity)
    (hj : let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      let N := D.correctedHeadOddDeterminantOneData hunit hodd
        (S.gapTwo_correctedHead_determinantClass_eq_one
          A conditions C.hgap C.hscale)
      IsIsometric (D.correctedHead hunit) N.parameters.jData.space
        (D.correctedHeadLattice hunit) N.parameters.jData.lattice) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
    A conditions C.hgap C.hscale
  let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
  let jIso := Classical.choice hj
  have htower : (D.correctedHead hunit).IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) :=
    ⟨jIso.toQuadraticSpaceIsometry.trans
      (N.parameters.jSpaceToHyperbolicTowerIsometry N.alpha_zero)⟩
  exact S.gapTwoHeadAlignedReplacementOfNormalizedHead
    A conditions C.hgap C.hscale
      (D.sourceToCorrectedHeadIsometryOfHyperbolic hunit htower)

/-- The non-condition-(iii) half of Step 7.  Even heads are hyperbolic by
93:18(ii); odd heads are the `J`/`K` alternatives of 93:18(vi), with the
`K` alternative converted by the two explicit twist absorptions above. -/
noncomputable def gapTwoHeadAlignedReplacementOfNontrigger
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (C : S.GapTwoCase A)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  by_cases hodd : Odd S.firstNormWeightParity
  · let D := S.gapTwoCongruenceErrorData A conditions C.hgap C.hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let hdet := S.gapTwo_correctedHead_determinantClass_eq_one
      A conditions C.hgap C.hscale
    let N := D.correctedHeadOddDeterminantOneData hunit hodd hdet
    by_cases hj : IsIsometric (D.correctedHead hunit)
        N.parameters.jData.space (D.correctedHeadLattice hunit)
          N.parameters.jData.lattice
    · exact S.gapTwoHeadAlignedReplacementOfNontriggerJ
        A conditions C hodd hj
    · have hk := N.isometric_j_or_k.resolve_left hj
      exact S.gapTwoHeadAlignedReplacementOfNontriggerK
        A conditions C hnontrigger hodd hk
  · have heven : Even S.firstNormWeightParity :=
      Int.not_odd_iff_even.mp hodd
    exact S.gapTwoHeadAlignedReplacementOfNontriggerEven
      A conditions C heven

/-- Complete O'Meara 93:28 Step 7 in the gap-two, scale-one case, with no
residual local classification law. -/
noncomputable def gapTwoHeadAlignedReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let C : S.GapTwoCase A := ⟨hgap, hscale⟩
  by_cases htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A (boundaryLeftIndex 0)
  · exact S.gapTwoHeadAlignedReplacementOfConditionIII
      A conditions C.hgap C.hscale htrigger
  · exact S.gapTwoHeadAlignedReplacementOfNontrigger
      A conditions C htrigger

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
