/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96Problem
import Bong.Bong.Beli2019Lemma96TailComparison

/-!
# Beli (2019), Lemma 9.6: assembling the projected-tail input

This file connects the matched ternary normal form and the concrete
orthogonal projection constructed in the proof of Lemma 9.6 to the bundled
lower-rank input consumed by the final induction.  In particular, the order,
prefix, and comparison profiles below are the proved profiles of the actual
projected lattice; no abstract tail certificate is supplied by the caller.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019RepresentationProblem.Lemma96Input

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {p : Beli2019RepresentationProblem.{u, v, w} K}

local instance lemma96AssemblyTargetAddCommGroup : AddCommGroup p.Target :=
  p.targetAddCommGroup
local instance lemma96AssemblyTargetModule : Module K p.Target := p.targetModule
local instance lemma96AssemblySourceAddCommGroup : AddCommGroup p.Source :=
  p.sourceAddCommGroup
local instance lemma96AssemblySourceModule : Module K p.Source := p.sourceModule

/-- Assemble the literal Lemma 9.6 input from the matched normal form.

The three profiles in `Lemma96Input` are not additional hypotheses: they are
the order computation, prefix representation, and comparison arithmetic of
the projected lattice proved in the preceding Lemma 9.6 files. -/
noncomputable def ofMatchedNormalForm
    [laws : DyadicDiscriminantClassLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (N : Nat)
    (htarget : p.targetIndex = N + 3)
    (hsource : p.sourceIndex = N + 3)
    (a : BONG.GoodBONG p.targetQ p.targetLattice (N + 4))
    (b : BONG.GoodBONG p.sourceQ p.sourceLattice (N + 4))
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (D : BONG.GoodBONG.Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstOrder :
      b.order (0 : Fin (N + 4)) = a.order (0 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    Lemma96Input p where
  extraRank := N
  targetIndex_eq := htarget
  sourceIndex_eq := hsource
  targetBONG := a
  sourceBONG := b
  selectedConditions := conditions
  targetHead := D.matchedHead.vector
  targetHeadGenerator := D.matchedHead.isNormGenerator
  targetHeadValue := by
    simpa only [BONG.GoodBONG.coe_valueUnit] using
      D.matchedHead.quadratic_eq
  targetHeadAnisotropic := D.matchedHead.anisotropic
  targetTail := D.projectedTailGoodBONG S houter hfourth
  orderProfile := D.projectedTail_orderProfile S houter hfirstGap hfourth
  prefixTransport := D.projectedTail_prefixTransport S houter hfourth
  comparisonProfile := D.projectedTail_comparisonProfile
    (targetLaws := targetLaws) sourceLaws S houter hfirstGap hfourth
      hsourceFirstOrder hsourceFirstGap hdefect
  firstGap := hfirstGap
  sourceFirstOrder := hsourceFirstOrder
  sourceFirstGap := hsourceFirstGap

/-- The matched normal form therefore produces the concrete head reduction
used in the rank-at-least-four exceptional branch of Lemma 9.6. -/
noncomputable def headReductionOfMatchedNormalForm
    [laws : DyadicDiscriminantClassLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (N : Nat)
    (htarget : p.targetIndex = N + 3)
    (hsource : p.sourceIndex = N + 3)
    (a : BONG.GoodBONG p.targetQ p.targetLattice (N + 4))
    (b : BONG.GoodBONG p.sourceQ p.sourceLattice (N + 4))
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (D : BONG.GoodBONG.Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (hsourceFirstOrder :
      b.order (0 : Fin (N + 4)) = a.order (0 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    Beli2019RepresentationProblem.HeadReduction p :=
  Lemma96Input.headReduction
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (ofMatchedNormalForm (p := p) (targetLaws := targetLaws)
      (sourceLaws := sourceLaws) N htarget hsource a b conditions D S houter
      hfirstGap hfourth hsourceFirstOrder hsourceFirstGap hdefect)

end Beli2019RepresentationProblem.Lemma96Input

end Bong
