/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96RankThreeGeometry
import Bong.Bong.Beli2019Lemma96SquareBranch
import Bong.Bong.Beli2019RepresentationProblem

/-!
# Beli (2019), Lemma 9.6 in rank three

At rank three the ordinary signed-determinant square branch is impossible:
the represented source line would make the whole anisotropic ternary target
isotropic.  Thus the discriminant-twisted branch supplies the bad BONG, whose
binary projected tail is the complete lower-rank problem.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The literal ternary endpoint at which Lemma 9.6 replaces the target
head by the exceptional norm generator. -/
def Beli2019Lemma96BoundaryRankThree
    (a : GoodBONG q L 3) (b : GoodBONG r M 3) : Prop :=
  a.order (0 : Fin 3) = a.order (2 : Fin 3) ∧
    a.order (0 : Fin 3) = b.order (0 : Fin 3) ∧
    a.orderGap (0 : Fin 2) = 2 * (ramificationIndex K : Int) - 2 ∧
    a.Beli2019Lemma96DefectBound b ∧
    a.Lemma814FirstThreeAnisotropic

/-- In ternary rank the ordinary square-class alternative in Lemma 9.6
contradicts anisotropy of the complete target space. -/
theorem not_beli2019Lemma96_rawSquare_rankThree
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (ambient : q.Represents r)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    ¬ IsSquare ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
  intro hrawSquare
  have hfull : DiagonalRepresents b.toBONG.value a.toBONG.value :=
    a.toBONG.diagonalRepresents_of_ambient b.toBONG ambient
  have hunaryPrefix :
      DiagonalRepresents
        (fun i : Fin 1 ↦ b.toBONG.value
          ⟨i.val, i.isLt.trans_le (by omega)⟩)
        b.toBONG.value :=
    DiagonalRepresents.prefixOfLE b.toBONG.value (by omega)
  have hunary : DiagonalRepresents
      (fun i : Fin 1 ↦ b.toBONG.value
        ⟨i.val, i.isLt.trans_le (by omega)⟩)
      a.toBONG.value := hunaryPrefix.trans hfull
  let head : Fin 3 → Kˣ := a.prefixValueUnits 3 (by omega)
  let source : Kˣ := b.valueUnit (0 : Fin 3)
  have hbValues : b.prefixValues 1 (by omega) =
      (fun _ : Fin 1 ↦ (source : K)) := by
    funext i
    rw [Fin.eq_zero i]
    rfl
  have haValues : a.prefixValues 3 (by omega) =
      diagonalUnitCoefficients head := by
    exact (a.diagonalUnitCoefficients_prefixValueUnits 3 (by omega)).symm
  have hrep : DiagonalRepresents
      (b.prefixValues 1 (by omega))
      (a.prefixValues 3 (by omega)) := by
    convert hunary using 1 <;> funext i <;> rfl
  have hrep' : DiagonalRepresents
      (fun _ : Fin 1 ↦ (source : K))
      (diagonalUnitCoefficients head) := by
    simpa only [← hbValues, ← haValues] using hrep
  have hheadDeterminant : diagonalUnitDeterminant head =
      a.prefixProduct 3 :=
    a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega)
  have hbProduct : b.prefixProduct 1 = source := by
    change b.toBONG.prefixProduct 1 = b.toBONG.valueUnit 0
    rw [b.toBONG.prefixProduct_succ 0 (by omega),
      b.toBONG.prefixProduct_zero, one_mul]
    congr 1
  have hsquare : IsSquare
      ((-1 : Kˣ) * diagonalUnitDeterminant head * source) := by
    rw [hheadDeterminant, ← hbProduct]
    exact hrawSquare
  have hisotropic : DiagonalIsotropic
      (diagonalUnitCoefficients head) :=
    DyadicTernaryRepresentationObstructionLaws.isotropic_of_represents_and_signedDeterminantSquare
      (K := K) head source hrep' hsquare
  have hisotropic' : DiagonalIsotropic
      (a.prefixValues 3 (by omega)) := by
    rwa [haValues]
  rcases hisotropic' with ⟨x, hx, hzero⟩
  exact hx (hanisotropic x hzero)

/-- The ternary Lemma 9.6 boundary necessarily lies in the
discriminant-twisted normal-form branch. -/
theorem exists_beli2019Lemma96MatchedNormalFormData_rankThree
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [modelAlpha : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (boundary : Beli2019Lemma96BoundaryRankThree a b)
    (ambient : q.Represents r) :
    Nonempty (Beli2019Lemma96MatchedNormalFormData a b) := by
  have hfirstGap :
      a.order (1 : Fin 3) - a.order (0 : Fin 3) =
        2 * (ramificationIndex K : Int) - 2 := by
    change a.orderGap (0 : Fin 2) = _
    exact boundary.2.2.1
  rcases a.beli2019Lemma96_squareRaw_or_matchedNormalForm (T := 0) b
      (targetAlpha := targetAlpha) (modelAlpha := modelAlpha)
      boundary.1 hfirstGap
      boundary.2.2.2.2 boundary.2.1.symm boundary.2.2.2.1 with
    hraw | hmatched
  · exact (a.not_beli2019Lemma96_rawSquare_rankThree b ambient
      boundary.2.2.2.2 hraw).elim
  · exact hmatched

namespace Beli2019Lemma96MatchedNormalFormData

variable [laws : DyadicDiscriminantClassLaws K]
  {a : GoodBONG q L 3} {b : GoodBONG r M 3}

/-- The unique binary-tail comparison invariant is strictly negative.
This is the rank-three specialization of `A'_2 < 0` in Lemma 9.6. -/
theorem projectedTail_representationAlpha_lt_zero_rankThree
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hsourceOrder : b.order (0 : Fin 3) = a.order (0 : Fin 3))
    (hsourceGap : 2 * (ramificationIndex K : Int) ≤
      b.order (1 : Fin 3) - b.order (0 : Fin 3))
    (i : RepresentationIndex 2 2) :
    D.projectedTailGoodBONGrankThree.representationAlpha b.tail i < 0 := by
  have hi : i.val = 1 := by
    have := i.pos
    have := i.lt_large
    omega
  have hcOrder :
      D.projectedTailGoodBONGrankThree.order (1 : Fin 2) =
        a.order (0 : Fin 3) - 1 :=
    D.projectedTailGoodBONGrankThree_order_one
  have hbTailOrder : b.tail.order (0 : Fin 2) =
      b.order (1 : Fin 3) := by
    rw [b.order_goodTail]
    congr 1
  have horder :
      D.projectedTailGoodBONGrankThree.order (1 : Fin 2) -
          b.tail.order (0 : Fin 2) ≤
        -(2 * (ramificationIndex K : Int)) - 1 := by
    rw [hcOrder, hbTailOrder, ← hsourceOrder]
    omega
  have horderQ :
      ((D.projectedTailGoodBONGrankThree.order (1 : Fin 2) -
          b.tail.order (0 : Fin 2) : Int) : ℚ) ≤
        ((-(2 * (ramificationIndex K : Int)) - 1 : Int) : ℚ) := by
    exact_mod_cast horder
  have hhalf :
      (((D.projectedTailGoodBONGrankThree.order (1 : Fin 2) -
            b.tail.order (0 : Fin 2) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) < 0 := by
    push_cast at horderQ ⊢
    linarith
  have hcandidate :
      D.projectedTailGoodBONGrankThree.representationHalfGap b.tail i < 0 := by
    unfold representationHalfGap
    have hiTarget : (⟨i.val, i.lt_large⟩ : Fin 2) = (1 : Fin 2) := by
      apply Fin.ext
      norm_num [hi]
    have hiSource :
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin 2) =
          (0 : Fin 2) := by
      apply Fin.ext
      norm_num [hi]
    rw [hiTarget, hiSource]
    exact_mod_cast hhalf
  exact (D.projectedTailGoodBONGrankThree.representationAlpha_le_halfGap
    b.tail i).trans_lt hcandidate

/-- Condition (i) for the binary projected pair.  The first inequality is
the source gap forced by the Lemma 9.6 defect bound; the second is the last
rank-three instance of the original order condition. -/
theorem projectedTail_orderCondition_rankThree
    [sourceAlpha : Beli2006AlphaLaws.{u, w} K]
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (boundary : Beli2019Lemma96BoundaryRankThree a b)
    (conditions : RepresentationConditions a b (Nat.le_refl 2)) :
    D.projectedTailGoodBONGrankThree.RepresentationOrderCondition
      b.tail (Nat.le_refl 1) := by
  have hsourceGap : 2 * (ramificationIndex K : Int) ≤
      b.order (1 : Fin 3) - b.order (0 : Fin 3) := by
    simpa using a.lemma96_sourceFirstGap_ge_twoE b (by omega)
      boundary.2.2.2.1
  intro i
  by_cases hiZero : i.val = 0
  · left
    have hiFin : i = 0 := Fin.ext hiZero
    subst i
    change D.projectedTailGoodBONGrankThree.order (0 : Fin 2) ≤
      b.toBONG.tail.order (0 : Fin 2)
    rw [D.projectedTailGoodBONGrankThree_order_zero,
      b.toBONG.order_tail]
    have hindex : Fin.succ (0 : Fin 2) = (1 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hindex]
    change a.order (0 : Fin 3) +
        (2 * (ramificationIndex K : Int) - 1) ≤
      b.order (1 : Fin 3)
    have hsourceOrder := boundary.2.1
    omega
  · have hiOne : i.val = 1 := by
      have := i.isLt
      omega
    have horiginal := conditions.orderCondition i.succ
    rcases horiginal with hdirect | ⟨_, hlarge, _⟩
    · left
      change D.projectedTailGoodBONGrankThree.order i ≤
        b.toBONG.tail.order i
      rw [b.toBONG.order_tail]
      have hiFin : i = (1 : Fin 2) := Fin.ext hiOne
      subst i
      rw [D.projectedTailGoodBONGrankThree_order_one]
      have hindex : Fin.succ (1 : Fin 2) = (2 : Fin 3) := by
        apply Fin.ext
        rfl
      rw [hindex]
      change a.order (0 : Fin 3) - 1 ≤ b.order (2 : Fin 3)
      have hdirect' : a.order (2 : Fin 3) ≤ b.order (2 : Fin 3) := by
        simpa using hdirect
      have houter := boundary.1
      omega
    · simp only [Fin.val_succ] at hlarge
      omega

/-- Condition (ii) for the binary projected pair.  There is only one
representation index, and its invariant is negative whereas every capped
prefix defect is nonnegative. -/
theorem projectedTail_defectCondition_rankThree
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceAlpha : Beli2006AlphaLaws.{u, w} K]
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (boundary : Beli2019Lemma96BoundaryRankThree a b) :
    D.projectedTailGoodBONGrankThree.RepresentationDefectCondition
      b.tail := by
  have hsourceGap : 2 * (ramificationIndex K : Int) ≤
      b.order (1 : Fin 3) - b.order (0 : Fin 3) := by
    simpa using a.lemma96_sourceFirstGap_ge_twoE b (by omega)
      boundary.2.2.2.1
  rw [D.projectedTailGoodBONGrankThree.representationDefectCondition_iff_forall_at
    b.tail]
  intro i
  unfold RepresentationDefectAt
  exact (D.projectedTail_representationAlpha_lt_zero_rankThree
      boundary.1 boundary.2.1.symm hsourceGap i).le.trans
    (D.projectedTailGoodBONGrankThree.truncatedPrefixDefect_nonneg
      (alphaV := targetAlpha) (alphaW := sourceAlpha)
      b.tail 1 i.val i.val)

/-- All four conditions of Theorem 2.1 for the binary projected pair. -/
theorem projectedTail_representationConditions_rankThree
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceAlpha : Beli2006AlphaLaws.{u, w} K]
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (boundary : Beli2019Lemma96BoundaryRankThree a b)
    (conditions : RepresentationConditions a b (Nat.le_refl 2)) :
    RepresentationConditions D.projectedTailGoodBONGrankThree b.tail
      (Nat.le_refl 1) where
  orderCondition := D.projectedTail_orderCondition_rankThree
    (sourceAlpha := sourceAlpha)
    boundary conditions
  defectCondition := D.projectedTail_defectCondition_rankThree
    (targetAlpha := targetAlpha) (sourceAlpha := sourceAlpha) boundary
  centralRepresentations := by
    intro i
    have := i.one_lt
    have := i.lt_large
    omega
  longRepresentations := by
    intro i
    have := i.one_lt
    have := i.succ_lt_large
    omega

/-- The exceptional ternary BONG and its binary tail form the literal
solved-head reduction consumed by the final induction. -/
noncomputable def headReductionRankThree
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceAlpha : Beli2006AlphaLaws.{u, w} K]
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (boundary : Beli2019Lemma96BoundaryRankThree a b)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl 2)) :
    Beli2019RepresentationProblem.HeadReduction
      (Beli2019RepresentationProblem.ofData
        a b (Nat.le_refl 2) ambient conditions) where
  targetHead := D.targetHeadRankThree
  sourceHead := b.toBONG.head
  targetHeadGenerator := D.targetHeadRankThree_isNormGenerator
  sourceHeadGenerator := b.toBONG.head_isNormGenerator
  targetHeadAnisotropic := D.targetHeadRankThree_anisotropic
  sourceHeadAnisotropic := b.toBONG.head_isAnisotropic
  headValue_eq := by
    change q.quadratic D.exceptionalBONGrankThree.head =
      r.quadratic b.toBONG.head
    rw [← D.exceptionalBONGrankThree.value_zero_eq_quadratic_head,
      ← b.toBONG.value_zero_eq_quadratic_head]
    exact D.exceptionalBONGrankThree_value_zero
  tailIndex := 1
  targetIndex_eq := rfl
  sourceIndex_eq := rfl
  targetTail := D.projectedTailGoodBONGrankThree
  sourceTail := b.tail
  tailConditions := D.projectedTail_representationConditions_rankThree
    (targetAlpha := targetAlpha) (sourceAlpha := sourceAlpha)
    boundary conditions

end Beli2019Lemma96MatchedNormalFormData

/-- The complete rank-three endpoint of Lemma 9.6: the boundary produces a
genuine solved-head reduction, with no residual square-class alternative. -/
theorem exists_beli2019Lemma96_headReduction_rankThree
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceAlpha : Beli2006AlphaLaws.{u, w} K]
    [modelAlpha : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [GoodBONGClassificationLaws.{u, v, u} K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (boundary : Beli2019Lemma96BoundaryRankThree a b)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl 2)) :
    Nonempty (Beli2019RepresentationProblem.HeadReduction
      (Beli2019RepresentationProblem.ofData
        a b (Nat.le_refl 2) ambient conditions)) := by
  rcases a.exists_beli2019Lemma96MatchedNormalFormData_rankThree
      (targetAlpha := targetAlpha) (modelAlpha := modelAlpha)
      b boundary ambient with ⟨D⟩
  exact ⟨D.headReductionRankThree
    (targetAlpha := targetAlpha) (sourceAlpha := sourceAlpha)
    boundary ambient conditions⟩

end BONG.GoodBONG

end Bong
