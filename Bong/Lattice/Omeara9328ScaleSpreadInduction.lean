/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328HeadReductionDispatcher

/-!
# Scale-spread induction for the sufficiency half of O'Meara 93:28

Step 8 may insert an additional Jordan component, so induction on the number
of components is not valid.  We package a saturated classification problem
and apply strong recursion to its scale spread.  The head-reduction theorem
supplies exactly the strict inequality needed for the recursive tail.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]

/-- A nonempty saturated 93:28 classification problem with the rank lower
bound needed for simultaneous rank-four reduction. -/
structure Omeara9328SaturatedProblem where
  sourceCarrier : Type u
  [sourceAddCommGroup : AddCommGroup sourceCarrier]
  [sourceModule : Module K sourceCarrier]
  targetCarrier : Type u
  [targetAddCommGroup : AddCommGroup targetCarrier]
  [targetModule : Module K targetCarrier]
  sourceForm : QuadraticSpace K sourceCarrier
  targetForm : QuadraticSpace K targetCarrier
  sourceLattice : Lattice K sourceCarrier
  targetLattice : Lattice K targetCarrier
  componentPred : Nat
  sourceJordan : JordanDecomposition sourceForm sourceLattice (componentPred + 1)
  targetJordan : JordanDecomposition targetForm targetLattice (componentPred + 1)
  ambient : sourceForm.IsIsometric targetForm
  sourceSaturated : sourceJordan.IsSaturated
  targetSaturated : targetJordan.IsSaturated
  fundamentalType : SameFundamentalType sourceJordan targetJordan
  choice : FundamentalNormGeneratorChoice sourceJordan
  conditions : sourceJordan.Omeara9328ConditionsWith targetJordan choice
  componentRank_atLeastTwo : ∀ i, 2 ≤ sourceJordan.componentRank i

namespace Omeara9328SaturatedProblem

/-- Named additive structure on a problem's source carrier. -/
noncomputable instance problemSourceAddCommGroup
    (P : Omeara9328SaturatedProblem (K := K)) :
    AddCommGroup P.sourceCarrier := P.sourceAddCommGroup

/-- Named module structure on a problem's source carrier. -/
noncomputable instance problemSourceModule
    (P : Omeara9328SaturatedProblem (K := K)) :
    Module K P.sourceCarrier := P.sourceModule

/-- Named additive structure on a problem's target carrier. -/
noncomputable instance problemTargetAddCommGroup
    (P : Omeara9328SaturatedProblem (K := K)) :
    AddCommGroup P.targetCarrier := P.targetAddCommGroup

/-- Named module structure on a problem's target carrier. -/
noncomputable instance problemTargetModule
    (P : Omeara9328SaturatedProblem (K := K)) :
    Module K P.targetCarrier := P.targetModule

/-- The exact integral classification result attached to a problem. -/
abbrev Solution (P : Omeara9328SaturatedProblem (K := K)) :=
  Isometry P.sourceForm P.targetForm P.sourceLattice P.targetLattice

/-- The exact tail problem supplied by one head-aligned reduction. -/
noncomputable def tailProblem
    {V : Type u} [AddCommGroup V] [Module K V]
    {W : Type u} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (D : Omeara9328HeadAlignedReduction J H) :
    Omeara9328SaturatedProblem (K := K) := by
  let T := D.toData
  letI : AddCommGroup T.sourceCarrier := T.sourceAddCommGroup
  letI : Module K T.sourceCarrier := T.sourceModule
  letI : AddCommGroup T.targetCarrier := T.targetAddCommGroup
  letI : Module K T.targetCarrier := T.targetModule
  exact {
    sourceCarrier :=
      (T.sourceJordan.toOrthogonalDecomposition.suffixQuadraticSublattice 1).carrier
    sourceAddCommGroup := inferInstance
    sourceModule := inferInstance
    targetCarrier :=
      (T.targetJordan.toOrthogonalDecomposition.suffixQuadraticSublattice 1).carrier
    targetAddCommGroup := inferInstance
    targetModule := inferInstance
    sourceForm :=
      (T.sourceJordan.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
    targetForm :=
      (T.targetJordan.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
    sourceLattice :=
      (T.sourceJordan.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice
    targetLattice :=
      (T.targetJordan.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice
    componentPred := T.nextN
    sourceJordan := T.sourceJordan.tail
    targetJordan := T.targetJordan.tail
    ambient := ⟨T.sourceJordan.tailSpaceIsometry T.targetJordan
      (Classical.choice T.ambient) T.head.toQuadraticSpaceIsometry⟩
    sourceSaturated := T.sourceSaturated.tail
    targetSaturated := T.targetSaturated.tail
    fundamentalType := T.fundamentalType.tail
      T.sourceSaturated T.targetSaturated
    choice := T.choice.tail T.sourceSaturated
    conditions := omeara9328ConditionsWith_tail
      T.sourceSaturated T.head T.choice T.conditions
    componentRank_atLeastTwo := by
      intro i
      rw [T.sourceJordan.tail_componentRank]
      exact T.componentRank_atLeastTwo i.succ }

set_option maxHeartbeats 1000000 in
/-- Strong recursion on scale spread.  Component count is inspected only to
select the one-component base case; it is not the recursive measure. -/
noncomputable def solve (P : Omeara9328SaturatedProblem (K := K)) : P.Solution := by
  let motive : Nat → Sort (u + 2) := fun d =>
    (Q : Omeara9328SaturatedProblem (K := K)) →
      Q.sourceJordan.scaleSpread = d → Q.Solution
  let step : ∀ d, (∀ e, e < d → motive e) → motive d := by
    intro d recurse Q hspread
    rcases Q with ⟨sourceCarrier, targetCarrier,
      sourceForm, targetForm, sourceLattice, targetLattice,
      componentPred, sourceJordan, targetJordan, ambient,
      sourceSaturated, targetSaturated, fundamentalType,
      choice, conditions, componentRank_atLeastTwo⟩
    cases componentPred with
    | zero =>
        exact omeara9328_singleComponent sourceJordan targetJordan
          ambient fundamentalType
    | succ n =>
        let S : Omeara9328RankFourReductionSystem sourceJordan targetJordan :=
          ⟨sourceSaturated, targetSaturated, fundamentalType,
            componentRank_atLeastTwo⟩
        let A₂ := S.sourceFundamentalNormGeneratorChoice choice
        let C₂ := S.omeara9328ConditionsWith_rankFour choice conditions
        let D := S.firstHeadAlignedReduction ambient A₂ C₂
        let T := D.toData
        letI : AddCommGroup T.sourceCarrier := T.sourceAddCommGroup
        letI : Module K T.sourceCarrier := T.sourceModule
        letI : AddCommGroup T.targetCarrier := T.targetAddCommGroup
        letI : Module K T.targetCarrier := T.targetModule
        let R := tailProblem D
        let tailIsometry : R.Solution := recurse R.sourceJordan.scaleSpread
          (by
            calc
              R.sourceJordan.scaleSpread = T.sourceJordan.tail.scaleSpread := rfl
              _ < sourceJordan.scaleSpread := T.tailScaleSpread_lt
              _ = d := hspread)
          R rfl
        let alignedIsometry := T.sourceJordan.headTailIsometry
          T.targetJordan T.head tailIsometry
        exact D.unwind alignedIsometry
  exact Nat.strongRecOn (motive := motive)
    P.sourceJordan.scaleSpread step P rfl

end Omeara9328SaturatedProblem

/-- Rank-aware saturated sufficiency for any nonempty Jordan decomposition. -/
noncomputable def omeara9328SaturatedIsometryOfRankAtLeastTwo
    {V : Type u} [AddCommGroup V] [Module K V]
    {W : Type u} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m : Nat}
    (J : JordanDecomposition q L (m + 1))
    (H : JordanDecomposition r M (m + 1))
    (ambient : q.IsIsometric r)
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A)
    (hrank : ∀ i, 2 ≤ J.componentRank i) :
    Isometry q r L M :=
  Omeara9328SaturatedProblem.solve {
    sourceCarrier := V
    sourceAddCommGroup := inferInstance
    sourceModule := inferInstance
    targetCarrier := W
    targetAddCommGroup := inferInstance
    targetModule := inferInstance
    sourceForm := q
    targetForm := r
    sourceLattice := L
    targetLattice := M
    componentPred := m
    sourceJordan := J
    targetJordan := H
    ambient := ambient
    sourceSaturated := hJ
    targetSaturated := hH
    fundamentalType := F
    choice := A
    conditions := conditions
    componentRank_atLeastTwo := hrank }

end Lattice.JordanDecomposition

end Bong
