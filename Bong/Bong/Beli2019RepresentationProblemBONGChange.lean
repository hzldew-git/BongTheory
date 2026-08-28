/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93Problem
import Bong.Bong.Beli2019Lemma96Problem
import Bong.Bong.Beli2019IntermediateReduction

/-!
# Changing the root good BONG of a representation problem

The recursive certificates used in Sections 9.3, 9.6, and 9.12 may select a
different good BONG of the same target lattice.  Their geometric content only
depends on the ambient spaces and lattices; the selected BONG and its
transported conditions are already explicit fields of each certificate.

The constructors below make this independence definitional at the bundled
`Beli2019RepresentationProblem` boundary.  They do not transport a proof or
add a law: they rebuild the same inspectable certificate for a root problem
whose stored target BONG is different.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

namespace Lemma93Input

/-- Repackage a Lemma 9.3 input after changing only the good BONG stored at
the root target problem. -/
def transport_ofData_targetBONG
    (a a' : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank)
    (conditions' : RepresentationConditions a' b hRank)
    (D : Lemma93Input (ofData a' b hRank ambient conditions')) :
    Lemma93Input (ofData a b hRank ambient conditions) where
  tailIndex := D.tailIndex
  targetIndex_eq := D.targetIndex_eq
  sourceIndex_eq := D.sourceIndex_eq
  targetBONG := D.targetBONG
  sourceBONG := D.sourceBONG
  selectedConditions := D.selectedConditions
  headValue_eq := D.headValue_eq
  secondOrder_le := D.secondOrder_le
  essentialAlpha_eq := D.essentialAlpha_eq

end Lemma93Input

namespace Lemma96Input

/-- Repackage a Lemma 9.6 input after changing only the good BONG stored at
the root target problem. -/
def transport_ofData_targetBONG
    (a a' : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank)
    (conditions' : RepresentationConditions a' b hRank)
    (D : Lemma96Input (ofData a' b hRank ambient conditions')) :
    Lemma96Input (ofData a b hRank ambient conditions) where
  extraRank := D.extraRank
  targetIndex_eq := D.targetIndex_eq
  sourceIndex_eq := D.sourceIndex_eq
  targetBONG := D.targetBONG
  sourceBONG := D.sourceBONG
  selectedConditions := D.selectedConditions
  targetHead := D.targetHead
  targetHeadGenerator := D.targetHeadGenerator
  targetHeadValue := D.targetHeadValue
  targetHeadAnisotropic := D.targetHeadAnisotropic
  targetTail := D.targetTail
  orderProfile := D.orderProfile
  prefixTransport := D.prefixTransport
  comparisonProfile := D.comparisonProfile
  firstGap := D.firstGap
  sourceFirstOrder := D.sourceFirstOrder
  sourceFirstGap := D.sourceFirstGap

end Lemma96Input

namespace IndexPReduction

/-- Repackage an index-`p` reduction after changing only the good BONG stored
at the root target problem. -/
def transport_ofData_targetBONG
    (a a' : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank)
    (conditions' : RepresentationConditions a' b hRank)
    (D : IndexPReduction (ofData a' b hRank ambient conditions')) :
    IndexPReduction (ofData a b hRank ambient conditions) where
  index_eq := D.index_eq
  lattice := D.lattice
  inclusion := D.inclusion
  targetBONG := D.targetBONG
  conditions := D.conditions

end IndexPReduction

end Beli2019RepresentationProblem

end Bong
