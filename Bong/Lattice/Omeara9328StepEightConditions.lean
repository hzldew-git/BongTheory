/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightRepresentation

/-!
# O'Meara 93:28 conditions through Step 8

The two new boundaries created by Step 8 inherit all three conditions of
93:28 from the old first boundary.  Later boundaries are unchanged, up to
the common determinant factor and the common inserted hyperbolic plane.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

/-- The target has the same first scale gap as the source. -/
theorem SameFundamentalType.target_firstScaleGap_gt_one
    (F : SameFundamentalType J H)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    1 < ordUnit K (H.scaleGenerator 1) -
      ordUnit K (H.scaleGenerator 0) := by
  have hzero := F.scaleGenerator_order_eq_sameIndex (0 : Fin (n + 2))
  have hone := F.scaleGenerator_order_eq_sameIndex (1 : Fin (n + 2))
  omega

/-- Condition 93:28(i) survives the Step-8 insertion. -/
theorem SameFundamentalType.omeara9328ConditionI_stepEight
    (F : SameFundamentalType J H)
    (hJ : J.IsSaturated)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))
    (hI : J.Omeara9328ConditionI H) :
    (J.stepEightJordan hgap).Omeara9328ConditionI
      (F.targetStepEightJordan hgap) := by
  intro i
  let hgapH := F.target_firstScaleGap_gt_one hgap
  cases i using Fin.cases with
  | zero =>
      have hold := (hI (0 : Fin (n + 1))).mono
        (J.stepEight_fundamentalIdeal_first_le_first hJ hgap
          hnormGap hfirst)
      apply BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
        (H.prefixDeterminantUnit 0)
        ((F.targetStepEightJordan hgap).prefixDeterminantUnit 0)
        (J.prefixDeterminantUnit 0)
        ((J.stepEightJordan hgap).prefixDeterminantUnit 0)
        ((J.stepEightJordan hgap).fundamentalIdeal 0)
      · change determinantClass
            (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
            (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice =
          determinantClass
            ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
              |>.prefixQuadraticSublattice 1).space
            ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
              |>.prefixQuadraticSublattice 1).lattice
        exact (F.determinantClass_targetStepEight_firstPrefix
          hgap hgapH).symm
      · change determinantClass
            (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
            (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice =
          determinantClass
            ((J.stepEightJordan hgap).toOrthogonalDecomposition
              |>.prefixQuadraticSublattice 1).space
            ((J.stepEightJordan hgap).toOrthogonalDecomposition
              |>.prefixQuadraticSublattice 1).lattice
        exact (J.determinantClass_stepEight_firstPrefix hgap).symm
      · exact hold
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          let d : Kˣ := (-1 : Kˣ) * J.stepEightScale ^ 2
          have hold := (hI (0 : Fin (n + 1))).mono
            (J.stepEight_fundamentalIdeal_first_le_second hJ hgap
              hnormGap hfirst)
          have hproduct : UnitsCongruentModulo
              (d * H.prefixDeterminantUnit 0)
              (d * J.prefixDeterminantUnit 0)
              ((J.stepEightJordan hgap).fundamentalIdeal 1) :=
            (unitsCongruentModulo_mul_left_iff d
              (H.prefixDeterminantUnit 0) (J.prefixDeterminantUnit 0)
              ((J.stepEightJordan hgap).fundamentalIdeal 1)).2 hold
          apply BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
            (d * H.prefixDeterminantUnit 0)
            ((F.targetStepEightJordan hgap).prefixDeterminantUnit 1)
            (d * J.prefixDeterminantUnit 0)
            ((J.stepEightJordan hgap).prefixDeterminantUnit 1)
            ((J.stepEightJordan hgap).fundamentalIdeal 1)
          · rw [unitSquareClass_mul]
            change J.stepEightDeterminantFactor *
                determinantClass
                  (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
                  (H.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice =
              determinantClass
                ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice 2).space
                ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice 2).lattice
            exact (F.determinantClass_targetStepEight_firstTwoPrefix
              hgap hgapH).symm
          · rw [unitSquareClass_mul]
            change J.stepEightDeterminantFactor *
                determinantClass
                  (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
                  (J.toOrthogonalDecomposition.prefixQuadraticSublattice 1).lattice =
              determinantClass
                ((J.stepEightJordan hgap).toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice 2).space
                ((J.stepEightJordan hgap).toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice 2).lattice
            exact (J.determinantClass_stepEight_firstTwoPrefix hgap).symm
          · exact hproduct
      | succ i =>
          let d : Kˣ := (-1 : Kˣ) * J.stepEightScale ^ 2
          have hold := hI (i.succ : Fin (n + 1))
          rw [J.stepEightJordan_fundamentalIdeal_later hgap i]
          have hproduct : UnitsCongruentModulo
              (d * H.prefixDeterminantUnit i.succ)
              (d * J.prefixDeterminantUnit i.succ)
              (J.fundamentalIdeal i.succ) :=
            (unitsCongruentModulo_mul_left_iff d
              (H.prefixDeterminantUnit i.succ)
              (J.prefixDeterminantUnit i.succ)
              (J.fundamentalIdeal i.succ)).2 hold
          apply BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
            (d * H.prefixDeterminantUnit i.succ)
            ((F.targetStepEightJordan hgap).prefixDeterminantUnit i.succ.succ)
            (d * J.prefixDeterminantUnit i.succ)
            ((J.stepEightJordan hgap).prefixDeterminantUnit i.succ.succ)
            (J.fundamentalIdeal i.succ)
          · rw [unitSquareClass_mul]
            change J.stepEightDeterminantFactor *
                determinantClass
                  (H.toOrthogonalDecomposition.prefixQuadraticSublattice
                    (i.val + 2)).space
                  (H.toOrthogonalDecomposition.prefixQuadraticSublattice
                    (i.val + 2)).lattice =
              determinantClass
                ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice (i.val + 3)).space
                ((F.targetStepEightJordan hgap).toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice (i.val + 3)).lattice
            exact (F.determinantClass_targetStepEight_laterPrefix
              hgap hgapH i).symm
          · rw [unitSquareClass_mul]
            change J.stepEightDeterminantFactor *
                determinantClass
                  (J.toOrthogonalDecomposition.prefixQuadraticSublattice
                    (i.val + 2)).space
                  (J.toOrthogonalDecomposition.prefixQuadraticSublattice
                    (i.val + 2)).lattice =
              determinantClass
                ((J.stepEightJordan hgap).toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice (i.val + 3)).space
                ((J.stepEightJordan hgap).toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice (i.val + 3)).lattice
            exact (J.determinantClass_stepEight_laterPrefix hgap i).symm
          · exact hproduct

/-- Condition 93:28(ii) survives the Step-8 insertion.  Its first new
boundary is supplied by the old condition (iii), while its second new
boundary is supplied by the old condition (ii). -/
theorem SameFundamentalType.omeara9328ConditionIIWith_stepEight
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))
    (hII : J.Omeara9328ConditionIIWith H A)
    (hIII : J.Omeara9328ConditionIIIWith H A) :
    (J.stepEightJordan hgap).Omeara9328ConditionIIWith
      (F.targetStepEightJordan hgap)
      (J.stepEightFundamentalNormGeneratorChoice A hJ hgap
        hnormGap hfirst) := by
  intro i htrigger
  let hgapH := F.target_firstScaleGap_gt_one hgap
  let A₈ := J.stepEightFundamentalNormGeneratorChoice A hJ hgap
    hnormGap hfirst
  cases i using Fin.cases with
  | zero =>
      have hnew :
          (J.stepEightJordan hgap).fundamentalIdeal 0 <
            (J.stepEightJordan hgap).fourNormOverWeightIdealWith A₈ 1 := by
        simpa [A₈, boundaryRightIndex] using htrigger
      have hold : J.fundamentalIdeal 0 <
          J.fourNormOverWeightIdealWith A 0 :=
        (J.stepEight_fundamentalIdeal_first_le_first hJ hgap
          hnormGap hfirst).trans_lt <|
          hnew.trans_le <|
            J.stepEight_fourNormOverWeightIdealWith_inserted_le_first
              A hJ hgap hnormGap hfirst
      have hrep := hIII (0 : Fin (n + 1)) (by
        simpa [boundaryLeftIndex] using hold)
      have htransfer := F.stepEightFirstPrefix_embedsInto hgap hgapH
        (J.stepEightRaisedLineIsometry A).symm hrep
      simpa [boundaryRightIndex, A₈,
        J.stepEightFundamentalNormGeneratorChoice_inserted] using htransfer
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          have hnew :
              (J.stepEightJordan hgap).fundamentalIdeal 1 <
                (J.stepEightJordan hgap).fourNormOverWeightIdealWith A₈ 2 := by
            simpa [A₈, boundaryRightIndex] using htrigger
          have hthreshold :
              (J.stepEightJordan hgap).fourNormOverWeightIdealWith A₈ 2 =
                J.fourNormOverWeightIdealWith A 1 := by
            have h := J.stepEight_fourNormOverWeightIdealWith_old
              A hJ hgap hnormGap hfirst (1 : Fin (n + 2))
            simpa [A₈] using h
          have hold : J.fundamentalIdeal 0 <
              J.fourNormOverWeightIdealWith A 1 :=
            (J.stepEight_fundamentalIdeal_first_le_second hJ hgap
              hnormGap hfirst).trans_lt <| hnew.trans_eq hthreshold
          have hrep := hII (0 : Fin (n + 1)) (by
            simpa [boundaryRightIndex] using hold)
          have htransfer := F.stepEightFirstTwoPrefix_embedsInto hgap hgapH
            (QuadraticSpace.Isometry.refl
              (QuadraticSpace.scaledLine (A.value 1))) hrep
          have hvalue : A₈.value (2 : Fin (n + 3)) = A.value 1 := by
            have h := J.stepEightFundamentalNormGeneratorChoice_old
              A hJ hgap hnormGap hfirst (1 : Fin (n + 2))
            simpa [A₈] using h
          have hvalueGoal :
              A₈.value
                  (boundaryRightIndex ((0 : Fin (n + 1)).succ)) =
                A.value 1 := by
            simpa [boundaryRightIndex] using hvalue
          rw [hvalueGoal]
          simpa using htransfer
      | succ i =>
          have hright :
              boundaryRightIndex (i.succ.succ : Fin (n + 2)) =
                (1 : Fin (n + 3)).succAbove
                  (boundaryRightIndex (i.succ : Fin (n + 1))) := by
            apply Fin.ext
            simp [boundaryRightIndex]
          rw [J.stepEightJordan_fundamentalIdeal_later hgap i,
            hright,
            J.stepEight_fourNormOverWeightIdealWith_old A hJ hgap
              hnormGap hfirst] at htrigger
          have hrep := hII (i.succ : Fin (n + 1)) htrigger
          have htransfer := F.stepEightLaterPrefix_embedsInto hgap hgapH i
            (QuadraticSpace.Isometry.refl
              (QuadraticSpace.scaledLine
                (A.value (boundaryRightIndex (i.succ : Fin (n + 1))))))
            hrep
          rw [hright,
            J.stepEightFundamentalNormGeneratorChoice_old A hJ hgap
              hnormGap hfirst]
          exact htransfer

/-- Condition 93:28(iii) survives the Step-8 insertion.  Both new
boundaries reduce to the old first condition-(iii) representation. -/
theorem SameFundamentalType.omeara9328ConditionIIIWith_stepEight
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))
    (hIII : J.Omeara9328ConditionIIIWith H A) :
    (J.stepEightJordan hgap).Omeara9328ConditionIIIWith
      (F.targetStepEightJordan hgap)
      (J.stepEightFundamentalNormGeneratorChoice A hJ hgap
        hnormGap hfirst) := by
  intro i htrigger
  let hgapH := F.target_firstScaleGap_gt_one hgap
  let A₈ := J.stepEightFundamentalNormGeneratorChoice A hJ hgap
    hnormGap hfirst
  cases i using Fin.cases with
  | zero =>
      have hnew :
          (J.stepEightJordan hgap).fundamentalIdeal 0 <
            (J.stepEightJordan hgap).fourNormOverWeightIdealWith A₈ 0 := by
        simpa [A₈, boundaryLeftIndex] using htrigger
      have hthreshold :
          (J.stepEightJordan hgap).fourNormOverWeightIdealWith A₈ 0 =
            J.fourNormOverWeightIdealWith A 0 := by
        have h := J.stepEight_fourNormOverWeightIdealWith_old
          A hJ hgap hnormGap hfirst (0 : Fin (n + 2))
        simpa [A₈] using h
      have hold : J.fundamentalIdeal 0 <
          J.fourNormOverWeightIdealWith A 0 :=
        (J.stepEight_fundamentalIdeal_first_le_first hJ hgap
          hnormGap hfirst).trans_lt <| hnew.trans_eq hthreshold
      have hrep := hIII (0 : Fin (n + 1)) (by
        simpa [boundaryLeftIndex] using hold)
      have htransfer := F.stepEightFirstPrefix_embedsInto hgap hgapH
        (QuadraticSpace.Isometry.refl
          (QuadraticSpace.scaledLine (A.value 0))) hrep
      have hvalue : A₈.value (0 : Fin (n + 3)) = A.value 0 := by
        have h := J.stepEightFundamentalNormGeneratorChoice_old
          A hJ hgap hnormGap hfirst (0 : Fin (n + 2))
        simpa [A₈] using h
      have hvalueGoal :
          A₈.value (boundaryLeftIndex (0 : Fin (n + 2))) =
            A.value 0 := by
        simpa [boundaryLeftIndex] using hvalue
      rw [hvalueGoal]
      simpa using htransfer
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          have hnew :
              (J.stepEightJordan hgap).fundamentalIdeal 1 <
                (J.stepEightJordan hgap).fourNormOverWeightIdealWith A₈ 1 := by
            simpa [A₈, boundaryLeftIndex] using htrigger
          have hold : J.fundamentalIdeal 0 <
              J.fourNormOverWeightIdealWith A 0 :=
            (J.stepEight_fundamentalIdeal_first_le_second hJ hgap
              hnormGap hfirst).trans_lt <|
              hnew.trans_le <|
                J.stepEight_fourNormOverWeightIdealWith_inserted_le_first
                  A hJ hgap hnormGap hfirst
          have hrep := hIII (0 : Fin (n + 1)) (by
            simpa [boundaryLeftIndex] using hold)
          have htransfer := F.stepEightFirstTwoPrefix_embedsInto hgap hgapH
            (J.stepEightRaisedLineIsometry A).symm hrep
          simpa [boundaryLeftIndex, A₈,
            J.stepEightFundamentalNormGeneratorChoice_inserted] using htransfer
      | succ i =>
          have hleft :
              boundaryLeftIndex (i.succ.succ : Fin (n + 2)) =
                (1 : Fin (n + 3)).succAbove
                  (boundaryLeftIndex (i.succ : Fin (n + 1))) := by
            apply Fin.ext
            simp [boundaryLeftIndex]
          rw [J.stepEightJordan_fundamentalIdeal_later hgap i,
            hleft,
            J.stepEight_fourNormOverWeightIdealWith_old A hJ hgap
              hnormGap hfirst] at htrigger
          have hrep := hIII (i.succ : Fin (n + 1)) htrigger
          have htransfer := F.stepEightLaterPrefix_embedsInto hgap hgapH i
            (QuadraticSpace.Isometry.refl
              (QuadraticSpace.scaledLine
                (A.value (boundaryLeftIndex (i.succ : Fin (n + 1))))))
            hrep
          rw [hleft,
            J.stepEightFundamentalNormGeneratorChoice_old A hJ hgap
              hnormGap hfirst]
          exact htransfer

/-- All three semantic conditions of 93:28 pass to the raw Step-8 pair. -/
theorem SameFundamentalType.omeara9328ConditionsWith_stepEight
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))
    (h : J.Omeara9328ConditionsWith H A) :
    (J.stepEightJordan hgap).Omeara9328ConditionsWith
      (F.targetStepEightJordan hgap)
      (J.stepEightFundamentalNormGeneratorChoice A hJ hgap
        hnormGap hfirst) :=
  ⟨F.omeara9328ConditionI_stepEight hJ hgap hnormGap hfirst h.1,
    F.omeara9328ConditionIIWith_stepEight A hJ hgap hnormGap hfirst
      h.2.1 h.2.2,
    F.omeara9328ConditionIIIWith_stepEight A hJ hgap hnormGap hfirst
      h.2.2⟩

end Lattice.JordanDecomposition

end Bong
