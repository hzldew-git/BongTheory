/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96TailConditions
import Bong.Bong.Beli2019RepresentationProblem

/-!
# Beli (2019), Lemma 9.6 for a bundled recursive problem

This is the exceptional-head analogue of `Beli2019Lemma93Problem`.  It turns
the concrete bad-BONG data constructed in Lemma 9.6 into the literal
lower-rank `HeadReduction` consumed by the well-founded induction.

The input does not contain a representation of either the projected or the
original lattices.  Its only nonstructural fields are the three transparent
profiles proved in the tail modules: orders, prefix transport, and comparison
invariants.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

section Input

variable (p : Beli2019RepresentationProblem.{u, v, w} K)

local instance lemma96InputTargetAddCommGroup : AddCommGroup p.Target :=
  p.targetAddCommGroup
local instance lemma96InputTargetModule : Module K p.Target := p.targetModule
local instance lemma96InputSourceAddCommGroup : AddCommGroup p.Source :=
  p.sourceAddCommGroup
local instance lemma96InputSourceModule : Module K p.Source := p.sourceModule

/-- The complete inspectable input produced by the rank-at-least-four branch
of Beli's Lemma 9.6. -/
structure Lemma96Input where
  extraRank : Nat
  targetIndex_eq : p.targetIndex = extraRank + 3
  sourceIndex_eq : p.sourceIndex = extraRank + 3
  targetBONG : BONG.GoodBONG p.targetQ p.targetLattice (extraRank + 4)
  sourceBONG : BONG.GoodBONG p.sourceQ p.sourceLattice (extraRank + 4)
  selectedConditions : RepresentationConditions targetBONG sourceBONG
    (Nat.le_refl (extraRank + 3))
  targetHead : p.Target
  targetHeadGenerator : Lattice.IsNormGenerator p.targetQ
    p.targetLattice targetHead
  targetHeadValue : p.targetQ.quadratic targetHead = sourceBONG.value 0
  targetHeadAnisotropic : p.targetQ.IsAnisotropic targetHead
  targetTail : BONG.GoodBONG
    (p.targetQ.orthogonalSpace targetHead targetHeadAnisotropic)
    (Lattice.projectedLattice p.targetQ p.targetLattice targetHead
      targetHeadAnisotropic) (extraRank + 3)
  orderProfile :
    BONG.GoodBONG.Beli2019Lemma96TailOrderProfile targetBONG targetTail
  prefixTransport :
    BONG.GoodBONG.Beli2019Lemma96PrefixTransport
      targetBONG sourceBONG targetTail
  comparisonProfile :
    BONG.GoodBONG.Beli2019Lemma96TailComparisonProfile
      targetBONG sourceBONG targetTail
  firstGap :
    targetBONG.order (1 : Fin (extraRank + 4)) -
        targetBONG.order (0 : Fin (extraRank + 4)) =
      2 * (ramificationIndex K : Int) - 2
  sourceFirstOrder :
    sourceBONG.order (0 : Fin (extraRank + 4)) =
      targetBONG.order (0 : Fin (extraRank + 4))
  sourceFirstGap :
    2 * (ramificationIndex K : Int) ≤
      sourceBONG.order (1 : Fin (extraRank + 4)) -
        sourceBONG.order (0 : Fin (extraRank + 4))

end Input

namespace Lemma96Input

variable {p : Beli2019RepresentationProblem.{u, v, w} K}

local instance lemma96MethodsTargetAddCommGroup : AddCommGroup p.Target :=
  p.targetAddCommGroup
local instance lemma96MethodsTargetModule : Module K p.Target := p.targetModule
local instance lemma96MethodsSourceAddCommGroup : AddCommGroup p.Source :=
  p.sourceAddCommGroup
local instance lemma96MethodsSourceModule : Module K p.Source := p.sourceModule

/-- The source head selected by the exceptional branch. -/
noncomputable def sourceHead (D : Lemma96Input p) : p.Source :=
  D.sourceBONG.toBONG.head

/-- The source head is a norm generator. -/
theorem sourceHeadGenerator (D : Lemma96Input p) :
    Lattice.IsNormGenerator p.sourceQ p.sourceLattice D.sourceHead :=
  D.sourceBONG.toBONG.head_isNormGenerator

/-- The source head is anisotropic. -/
theorem sourceHeadAnisotropic (D : Lemma96Input p) :
    p.sourceQ.IsAnisotropic D.sourceHead :=
  D.sourceBONG.toBONG.head_isAnisotropic

/-- The displayed matched-head identity in quadratic-space form. -/
theorem headValue_eq (D : Lemma96Input p) :
    p.targetQ.quadratic D.targetHead =
      p.sourceQ.quadratic D.sourceHead := by
  change p.targetQ.quadratic D.targetHead =
    p.sourceQ.quadratic D.sourceBONG.toBONG.head
  rw [← D.sourceBONG.toBONG.value_zero_eq_quadratic_head]
  exact D.targetHeadValue

/-- The exceptional input constructs the concrete lower-rank projected
problem used by the final induction. -/
noncomputable def headReduction
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (D : Lemma96Input p) : HeadReduction p := by
  refine
    { targetHead := D.targetHead
      sourceHead := D.sourceHead
      targetHeadGenerator := D.targetHeadGenerator
      sourceHeadGenerator := D.sourceHeadGenerator
      targetHeadAnisotropic := D.targetHeadAnisotropic
      sourceHeadAnisotropic := D.sourceHeadAnisotropic
      headValue_eq := D.headValue_eq
      tailIndex := D.extraRank + 2
      targetIndex_eq := D.targetIndex_eq.trans (by omega)
      sourceIndex_eq := D.sourceIndex_eq.trans (by omega)
      targetTail := D.targetTail
      sourceTail := D.sourceBONG.tail
      tailConditions := D.targetBONG.beli2019Lemma96_tailConditions
        (cLaws := targetLaws) (bLaws := sourceLaws)
        D.sourceBONG D.targetTail D.orderProfile D.prefixTransport
          D.comparisonProfile D.selectedConditions D.firstGap
            D.sourceFirstOrder D.sourceFirstGap }

end Lemma96Input

end Beli2019RepresentationProblem

end Bong
