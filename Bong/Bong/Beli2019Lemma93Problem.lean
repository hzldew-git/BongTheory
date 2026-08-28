/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93Reduction
import Bong.Bong.Beli2019RepresentationProblemReindex

/-!
# Beli (2019), Lemma 9.3 for a bundled recursive problem

`lemma93HeadReduction` proves the paper's rank reduction for two explicitly
indexed BONGs.  The final well-founded induction, however, works with a
bundled `Beli2019RepresentationProblem`.  This file supplies the exact
bridge: an inspectable ordinary-head input contains only the head equality,
the second-order inequality, and the essential-endpoint `A=A*` equalities.
The resulting `HeadReduction` is then constructed, not assumed.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

section AlignedBONGs

variable (p : Beli2019RepresentationProblem.{u, v, w} K)

local instance : AddCommGroup p.Target := p.targetAddCommGroup
local instance : Module K p.Target := p.targetModule
local instance : AddCommGroup p.Source := p.sourceAddCommGroup
local instance : Module K p.Source := p.sourceModule

/-- The target BONG, with an exposed positive predecessor of its index. -/
noncomputable def lemma93TargetBONG (tailIndex : Nat)
    (hindex : p.targetIndex = tailIndex + 1) :
    BONG.GoodBONG p.targetQ p.targetLattice (tailIndex + 2) :=
  p.targetBONG.castLength (show p.targetIndex + 1 = tailIndex + 2 by omega)

/-- The source BONG, reindexed to the same exposed rank. -/
noncomputable def lemma93SourceBONG (tailIndex : Nat)
    (hindex : p.sourceIndex = tailIndex + 1) :
    BONG.GoodBONG p.sourceQ p.sourceLattice (tailIndex + 2) :=
  p.sourceBONG.castLength (show p.sourceIndex + 1 = tailIndex + 2 by omega)

/-- The original four conditions transported to the common exposed rank. -/
theorem lemma93AlignedConditions (tailIndex : Nat)
    (htarget : p.targetIndex = tailIndex + 1)
    (hsource : p.sourceIndex = tailIndex + 1) :
    RepresentationConditions
      (p.lemma93TargetBONG tailIndex htarget)
      (p.lemma93SourceBONG tailIndex hsource)
      (Nat.le_refl (tailIndex + 1)) :=
  representationConditions_castIndices p.targetBONG p.sourceBONG
    p.rankBound p.conditions htarget hsource

/-- The concrete arithmetic input of the ordinary Lemma 9.3 branch.

The paper is allowed to replace the BONGs of the original problem before
deleting their first vectors.  Consequently the selected BONGs and the four
representation conditions transported to them are explicit fields here;
they are not forced to be the particular BONGs stored in `p`.  No
representation conclusion is stored.  The last field is precisely the
selected-BONG equality used at essential endpoints in the paper; all
nonessential and central-trigger cases are proved in the tail-condition
modules. -/
structure Lemma93Input where
  tailIndex : Nat
  targetIndex_eq : p.targetIndex = tailIndex + 1
  sourceIndex_eq : p.sourceIndex = tailIndex + 1
  targetBONG :
    BONG.GoodBONG p.targetQ p.targetLattice (tailIndex + 2)
  sourceBONG :
    BONG.GoodBONG p.sourceQ p.sourceLattice (tailIndex + 2)
  selectedConditions :
    RepresentationConditions targetBONG sourceBONG
      (Nat.le_refl (tailIndex + 1))
  headValue_eq :
    targetBONG.value 0 = sourceBONG.value 0
  secondOrder_le :
    targetBONG.order ⟨1, by omega⟩ ≤
      sourceBONG.order ⟨1, by omega⟩
  essentialAlpha_eq :
    ∀ i : RepresentationIndex (tailIndex + 1) (tailIndex + 1),
      (targetBONG.tail.IsCurrentEssential sourceBONG.tail i ∨
        targetBONG.tail.IsNextEssential sourceBONG.tail i) →
      targetBONG.tail.representationAlpha sourceBONG.tail i =
        targetBONG.representationAlpha sourceBONG i.tailShift

end AlignedBONGs

namespace Lemma93Input

variable {p : Beli2019RepresentationProblem.{u, v, w} K}

local instance : AddCommGroup p.Target := p.targetAddCommGroup
local instance : Module K p.Target := p.targetModule
local instance : AddCommGroup p.Source := p.sourceAddCommGroup
local instance : Module K p.Source := p.sourceModule

/-- The ordinary-head arithmetic input constructs the literal lower-rank
problem consumed by the well-founded induction. -/
noncomputable def headReduction
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (D : Lemma93Input p) : HeadReduction p := by
  refine
    { targetHead := D.targetBONG.toBONG.head
      sourceHead := D.sourceBONG.toBONG.head
      targetHeadGenerator := D.targetBONG.toBONG.head_isNormGenerator
      sourceHeadGenerator := D.sourceBONG.toBONG.head_isNormGenerator
      targetHeadAnisotropic := D.targetBONG.toBONG.head_isAnisotropic
      sourceHeadAnisotropic := D.sourceBONG.toBONG.head_isAnisotropic
      headValue_eq := ?_
      tailIndex := D.tailIndex
      targetIndex_eq := D.targetIndex_eq
      sourceIndex_eq := D.sourceIndex_eq
      targetTail := D.targetBONG.tail
      sourceTail := D.sourceBONG.tail
      tailConditions := D.targetBONG.representationConditions_tail
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        D.sourceBONG D.selectedConditions D.headValue_eq D.secondOrder_le
          D.essentialAlpha_eq }
  rw [← D.targetBONG.toBONG.value_zero_eq_quadratic_head,
    ← D.sourceBONG.toBONG.value_zero_eq_quadratic_head]
  exact D.headValue_eq

end Lemma93Input

end Beli2019RepresentationProblem

end Bong
