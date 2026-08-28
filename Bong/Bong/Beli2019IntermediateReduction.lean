/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationProblem
import Bong.Bong.Beli2019SectionFive
import Bong.Bong.Beli2019OrderSums
import Bong.Bong.Beli2019VolumeOrders

/-!
# Same-rank index-p reductions for Beli (2019), Sections 7 and 9

Sections 7 and 9 use the same well-founded step.  Starting from a same-rank
representation problem, one constructs an index-`p` sublattice of the target
which still satisfies the four conditions relative to the source.  The new
problem has the same rank and its volume gap is strictly smaller.

This file proves that general reduction principle.  It separates the formal
well-founded argument from the case-specific constructions in Lemma 9.12.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The full prefix sum of a nonempty BONG order sequence is the lattice
volume order. -/
theorem orderPrefixSum_full_eq_volumeOrder (b : GoodBONG q L (n + 1)) :
    b.orderPrefixSum (n + 1) = Lattice.volumeOrder q L := by
  unfold orderPrefixSum
  rw [← b.orderSequence_suffixSum_zero_eq_volumeOrder,
    b.orderSequence.suffixSum_eq_total_sub_prefix 0 (Nat.zero_le (n + 1)),
    b.orderSequence.prefixSum_zero, sub_zero]

/-- At equal rank, condition 2.1(i) implies the expected inequality between
the two lattice volume orders. -/
theorem volumeOrder_le_of_representationOrderCondition
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b (Nat.le_refl n)) :
    Lattice.volumeOrder q L ≤ Lattice.volumeOrder r M := by
  rw [← a.orderPrefixSum_full_eq_volumeOrder,
    ← b.orderPrefixSum_full_eq_volumeOrder]
  exact a.orderPrefixSum_le_of_representationOrderCondition b
    (Nat.le_refl n) horder (n + 1) le_rfl

end BONG.GoodBONG

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

section SublatticeReduction

variable (p : Beli2019RepresentationProblem.{u, v, w} K)

local instance sublatticeReductionTargetAddCommGroup : AddCommGroup p.Target :=
  p.targetAddCommGroup
local instance sublatticeReductionTargetModule : Module K p.Target :=
  p.targetModule
local instance sublatticeReductionSourceAddCommGroup : AddCommGroup p.Source :=
  p.sourceAddCommGroup
local instance sublatticeReductionSourceModule : Module K p.Source :=
  p.sourceModule

/-- A concrete same-rank replacement of the target by a strict sublattice
which still satisfies all four conditions of Theorem 2.1.  Unlike
`IndexPReduction`, this certificate permits any positive finite volume jump;
this is the reduction used in Section 7 when an entire binary block is
multiplied by the uniformizer. -/
structure SublatticeReduction where
  index_eq : p.targetIndex = p.sourceIndex
  lattice : Lattice K p.Target
  lattice_le : lattice ≤ p.targetLattice
  volumeOrder_lt :
    Lattice.volumeOrder p.targetQ p.targetLattice <
      Lattice.volumeOrder p.targetQ lattice
  targetBONG : BONG.GoodBONG p.targetQ lattice (p.sourceIndex + 1)
  conditions : RepresentationConditions targetBONG p.sourceBONG
    (Nat.le_refl p.sourceIndex)

namespace SublatticeReduction

/-- The same-rank problem obtained from a strict target sublattice. -/
noncomputable def next (D : SublatticeReduction p) :
    Beli2019RepresentationProblem.{u, v, w} K where
  Target := p.Target
  Source := p.Source
  targetAddCommGroup := p.targetAddCommGroup
  targetModule := p.targetModule
  sourceAddCommGroup := p.sourceAddCommGroup
  sourceModule := p.sourceModule
  targetQ := p.targetQ
  sourceQ := p.sourceQ
  targetLattice := D.lattice
  sourceLattice := p.sourceLattice
  targetIndex := p.sourceIndex
  sourceIndex := p.sourceIndex
  targetBONG := D.targetBONG
  sourceBONG := p.sourceBONG
  rankBound := Nat.le_refl p.sourceIndex
  ambient := p.ambient
  conditions := D.conditions

@[simp]
theorem next_measure_rank (D : SublatticeReduction p) :
    D.next.measure.rank = p.measure.rank :=
  rfl

/-- Strict growth of target volume order strictly decreases the nonnegative
source-minus-target volume gap. -/
theorem next_measure_volumeGap_lt (D : SublatticeReduction p) :
    D.next.measure.volumeGap < p.measure.volumeGap := by
  have hnextLeSource :
      Lattice.volumeOrder p.targetQ D.lattice ≤
        Lattice.volumeOrder p.sourceQ p.sourceLattice :=
    D.targetBONG.volumeOrder_le_of_representationOrderCondition
      p.sourceBONG D.conditions.orderCondition
  have hstrict := D.volumeOrder_lt
  change Int.toNat
      (Lattice.volumeOrder p.sourceQ p.sourceLattice -
        Lattice.volumeOrder p.targetQ D.lattice) <
    Int.toNat
      (Lattice.volumeOrder p.sourceQ p.sourceLattice -
        Lattice.volumeOrder p.targetQ p.targetLattice)
  omega

/-- A strict same-rank sublattice reduction decreases the rank-volume
measure used by the final well-founded induction. -/
theorem smaller (D : SublatticeReduction p) :
    Beli2019ProblemSmaller Beli2019RepresentationProblem.measure
      D.next p := by
  apply beli2019ProblemSmaller_of_volumeGap_lt
  · exact D.next_measure_rank
  · exact D.next_measure_volumeGap_lt

/-- A representation by the reduced target composes with its literal
inclusion into the original target. -/
theorem parentRepresents_of_nextRepresents (D : SublatticeReduction p)
    (hnext : D.next.Represents) : p.Represents := by
  have htarget : Lattice.Represents p.targetQ p.targetQ
      p.targetLattice D.lattice :=
    Lattice.represents_of_le p.targetQ D.lattice_le
  have hsource : Lattice.Represents p.targetQ p.sourceQ
      D.lattice p.sourceLattice := by
    change D.next.Represents at hnext
    exact hnext
  exact htarget.trans hsource

/-- A counterexample therefore descends to the strict target sublattice. -/
theorem nextCounterexample (D : SublatticeReduction p)
    (hp : p.Counterexample) : D.next.Counterexample := by
  intro hnext
  exact hp (parentRepresents_of_nextRepresents p D hnext)

/-- Existential descent package consumed by the paper's final induction. -/
theorem counterexampleDescent (D : SublatticeReduction p)
    (hp : p.Counterexample) :
    ∃ next, next.Counterexample ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next p :=
  ⟨D.next, nextCounterexample p D hp, D.smaller⟩

end SublatticeReduction

end SublatticeReduction

section IndexPReduction

variable (p : Beli2019RepresentationProblem.{u, v, w} K)

local instance indexPReductionTargetAddCommGroup : AddCommGroup p.Target :=
  p.targetAddCommGroup
local instance indexPReductionTargetModule : Module K p.Target :=
  p.targetModule
local instance indexPReductionSourceAddCommGroup : AddCommGroup p.Source :=
  p.sourceAddCommGroup
local instance indexPReductionSourceModule : Module K p.Source :=
  p.sourceModule

/-- Concrete output required from the construction part of Lemma 9.12: an
index-`p` target sublattice which still satisfies Theorem 2.1 relative to the
unchanged source. -/
structure IndexPReduction where
  index_eq : p.targetIndex = p.sourceIndex
  lattice : Lattice K p.Target
  inclusion : Beli2019IndexPInclusion p.targetQ p.targetLattice lattice
  targetBONG : BONG.GoodBONG p.targetQ lattice (p.sourceIndex + 1)
  conditions : RepresentationConditions targetBONG p.sourceBONG
    (Nat.le_refl p.sourceIndex)

/-- Every literal index-`p` reduction is, in particular, a strict
same-rank sublattice reduction. -/
def IndexPReduction.toSublatticeReduction (D : IndexPReduction p) :
    SublatticeReduction p where
  index_eq := D.index_eq
  lattice := D.lattice
  lattice_le := D.inclusion.lattice_le
  volumeOrder_lt := by
    rw [D.inclusion.volumeOrder_eq]
    omega
  targetBONG := D.targetBONG
  conditions := D.conditions

namespace IndexPReduction

/-- The same-rank problem obtained by replacing the target lattice by the
constructed index-`p` sublattice. -/
noncomputable def next (D : IndexPReduction p) :
    Beli2019RepresentationProblem.{u, v, w} K where
  Target := p.Target
  Source := p.Source
  targetAddCommGroup := p.targetAddCommGroup
  targetModule := p.targetModule
  sourceAddCommGroup := p.sourceAddCommGroup
  sourceModule := p.sourceModule
  targetQ := p.targetQ
  sourceQ := p.sourceQ
  targetLattice := D.lattice
  sourceLattice := p.sourceLattice
  targetIndex := p.sourceIndex
  sourceIndex := p.sourceIndex
  targetBONG := D.targetBONG
  sourceBONG := p.sourceBONG
  rankBound := Nat.le_refl p.sourceIndex
  ambient := p.ambient
  conditions := D.conditions

@[simp]
theorem next_measure_rank (D : IndexPReduction p) :
    D.next.measure.rank = p.measure.rank :=
  rfl

/-- The new target problem has a strictly smaller volume gap. -/
theorem next_measure_volumeGap_lt (D : IndexPReduction p) :
    D.next.measure.volumeGap < p.measure.volumeGap := by
  have hnextLeSource :
      Lattice.volumeOrder p.targetQ D.lattice ≤
        Lattice.volumeOrder p.sourceQ p.sourceLattice :=
    D.targetBONG.volumeOrder_le_of_representationOrderCondition
      p.sourceBONG D.conditions.orderCondition
  change Int.toNat
      (Lattice.volumeOrder p.sourceQ p.sourceLattice -
        Lattice.volumeOrder p.targetQ D.lattice) <
    Int.toNat
      (Lattice.volumeOrder p.sourceQ p.sourceLattice -
        Lattice.volumeOrder p.targetQ p.targetLattice)
  rw [D.inclusion.volumeOrder_eq] at hnextLeSource ⊢
  omega

/-- An index-`p` reduction strictly decreases the concrete rank-volume
measure used by the final induction. -/
theorem smaller (D : IndexPReduction p) :
    Beli2019ProblemSmaller Beli2019RepresentationProblem.measure
      D.next p := by
  apply beli2019ProblemSmaller_of_volumeGap_lt
  · exact D.next_measure_rank
  · exact D.next_measure_volumeGap_lt

/-- A solution of the reduced problem composes with the literal target
lattice inclusion to solve the parent problem. -/
theorem parentRepresents_of_nextRepresents (D : IndexPReduction p)
    (hnext : D.next.Represents) : p.Represents := by
  have htarget : Lattice.Represents p.targetQ p.targetQ
      p.targetLattice D.lattice :=
    Lattice.represents_of_le p.targetQ D.inclusion.lattice_le
  have hsource : Lattice.Represents p.targetQ p.sourceQ
      D.lattice p.sourceLattice := by
    change D.next.Represents at hnext
    exact hnext
  exact htarget.trans hsource

/-- Consequently a counterexample descends to the new index-`p` target
problem. -/
theorem nextCounterexample (D : IndexPReduction p)
    (hp : p.Counterexample) : D.next.Counterexample := by
  intro hnext
  exact hp (parentRepresents_of_nextRepresents p D hnext)

/-- The reduction packaged in exactly the existential form consumed by the
well-founded final step. -/
theorem counterexampleDescent (D : IndexPReduction p)
    (hp : p.Counterexample) :
    ∃ next, next.Counterexample ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next p :=
  ⟨D.next, nextCounterexample p D hp, D.smaller⟩

end IndexPReduction

end IndexPReduction

end Beli2019RepresentationProblem

end Bong
