/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SolvedHead
import Bong.Bong.Beli2019VolumeOrders
import Bong.Bong.Beli2019RankVolumeDescent
import Bong.QuadraticSpace.Reflection

/-!
# Concrete recursive problems for Beli (2019), Sections 7--9

The final induction changes both ambient vector spaces when it passes to
orthogonal complements.  This file packages one source/target pair together
with all data of Theorem 2.1, while allowing successive problems to use
different carrier types in the same universes.

Unlike the former abstract problem code, representation and counterexample
are now fixed predicates, and the rank-volume measure is computed from the
actual BONG rank and lattice volume orders.
-/

namespace Bong

open Dyadic

universe u v w

set_option linter.checkUnivs false in
/-- A fully concrete recursive instance of Beli (2019), Theorem 2.1. -/
structure Beli2019RepresentationProblem
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] where
  Target : Type v
  Source : Type w
  [targetAddCommGroup : AddCommGroup Target]
  [targetModule : Module K Target]
  [sourceAddCommGroup : AddCommGroup Source]
  [sourceModule : Module K Source]
  targetQ : QuadraticSpace K Target
  sourceQ : QuadraticSpace K Source
  targetLattice : Lattice K Target
  sourceLattice : Lattice K Source
  targetIndex : Nat
  sourceIndex : Nat
  targetBONG : BONG.GoodBONG targetQ targetLattice (targetIndex + 1)
  sourceBONG : BONG.GoodBONG sourceQ sourceLattice (sourceIndex + 1)
  rankBound : sourceIndex ≤ targetIndex
  ambient : targetQ.Represents sourceQ
  conditions : RepresentationConditions targetBONG sourceBONG rankBound

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The desired conclusion at a recursive problem. -/
def Represents (p : Beli2019RepresentationProblem.{u, v, w} K) : Prop :=
  letI := p.targetAddCommGroup
  letI := p.targetModule
  letI := p.sourceAddCommGroup
  letI := p.sourceModule
  Lattice.Represents p.targetQ p.sourceQ p.targetLattice p.sourceLattice

/-- A counterexample is definitionally the failure of the concrete lattice
representation carried by the problem. -/
def Counterexample (p : Beli2019RepresentationProblem.{u, v, w} K) : Prop :=
  ¬p.Represents

/-- The equal-norm stopping condition of Section 7.  This is the literal
equality `n(M) = n(N)` from the paper, not an abstract branch label. -/
def EqualNorm (p : Beli2019RepresentationProblem.{u, v, w} K) : Prop :=
  letI := p.targetAddCommGroup
  letI := p.targetModule
  letI := p.sourceAddCommGroup
  letI := p.sourceModule
  Lattice.normIdeal p.targetQ p.targetLattice =
    Lattice.normIdeal p.sourceQ p.sourceLattice

section EqualNorm

variable (p : Beli2019RepresentationProblem.{u, v, w} K)

local instance equalNormTargetAddCommGroup : AddCommGroup p.Target :=
  p.targetAddCommGroup
local instance equalNormTargetModule : Module K p.Target := p.targetModule
local instance equalNormSourceAddCommGroup : AddCommGroup p.Source :=
  p.sourceAddCommGroup
local instance equalNormSourceModule : Module K p.Source := p.sourceModule

/-- For the selected good BONGs, Section 7's equal-norm condition is
equivalent to equality of the first displayed orders. -/
theorem equalNorm_iff_firstOrder_eq
    : p.EqualNorm ↔ p.targetBONG.order 0 = p.sourceBONG.order 0 := by
  unfold EqualNorm
  change
    Lattice.normIdeal p.targetQ p.targetLattice =
        Lattice.normIdeal p.sourceQ p.sourceLattice ↔
      p.targetBONG.toBONG.order 0 = p.sourceBONG.toBONG.order 0
  rw [p.targetBONG.toBONG.head_isNormGenerator.normIdeal_eq,
    p.sourceBONG.toBONG.head_isNormGenerator.normIdeal_eq,
    ← p.targetBONG.toBONG.value_zero_eq_quadratic_head,
    ← p.sourceBONG.toBONG.value_zero_eq_quadratic_head]
  constructor
  · intro hideal
    have htargetSource :
        Lattice.principalIdeal (K := K) (p.targetBONG.toBONG.value 0) ≤
          Lattice.principalIdeal (K := K) (p.sourceBONG.toBONG.value 0) := by
      rw [hideal]
    have hsourceTarget :
        Lattice.principalIdeal (K := K) (p.sourceBONG.toBONG.value 0) ≤
          Lattice.principalIdeal (K := K) (p.targetBONG.toBONG.value 0) := by
      rw [hideal]
    have hge := (Lattice.principalIdeal_le_iff_ord_ge
      (p.targetBONG.toBONG.value_ne_zero 0)
        (p.sourceBONG.toBONG.value_ne_zero 0)).1
        htargetSource
    have hle := (Lattice.principalIdeal_le_iff_ord_ge
      (p.sourceBONG.toBONG.value_ne_zero 0)
        (p.targetBONG.toBONG.value_ne_zero 0)).1
        hsourceTarget
    apply WithTop.coe_injective
    rw [p.targetBONG.toBONG.coe_order, p.sourceBONG.toBONG.coe_order]
    exact le_antisymm hle hge
  · intro horder
    apply le_antisymm
    · apply (Lattice.principalIdeal_le_iff_ord_ge
        (p.targetBONG.toBONG.value_ne_zero 0)
          (p.sourceBONG.toBONG.value_ne_zero 0)).2
      rw [← p.targetBONG.toBONG.coe_order,
        ← p.sourceBONG.toBONG.coe_order, horder]
    · apply (Lattice.principalIdeal_le_iff_ord_ge
        (p.sourceBONG.toBONG.value_ne_zero 0)
          (p.targetBONG.toBONG.value_ne_zero 0)).2
      rw [← p.targetBONG.toBONG.coe_order,
        ← p.sourceBONG.toBONG.coe_order, horder]

end EqualNorm

/-- The lexicographic induction measure computed from the actual source rank
and the source-minus-target lattice volume order. -/
noncomputable def measure
    (p : Beli2019RepresentationProblem.{u, v, w} K) :
    Beli2019RankVolumeMeasure := by
  letI := p.targetAddCommGroup
  letI := p.targetModule
  letI := p.sourceAddCommGroup
  letI := p.sourceModule
  exact
    { rank := p.sourceIndex + 1
      volumeGap := Int.toNat
        (Lattice.volumeOrder p.sourceQ p.sourceLattice -
          Lattice.volumeOrder p.targetQ p.targetLattice) }

/-- A solved-head witness for a concrete recursive problem. -/
def SolvedHead (p : Beli2019RepresentationProblem.{u, v, w} K) : Prop :=
  letI := p.targetAddCommGroup
  letI := p.targetModule
  letI := p.sourceAddCommGroup
  letI := p.sourceModule
  Nonempty (Beli2019SolvedHeadData p.targetQ p.sourceQ
    p.targetLattice p.sourceLattice)

/-- A solved-head witness proves the concrete conclusion of its problem. -/
theorem SolvedHead.represents
    {p : Beli2019RepresentationProblem.{u, v, w} K}
    (h : p.SolvedHead) : p.Represents := by
  letI := p.targetAddCommGroup
  letI := p.targetModule
  letI := p.sourceAddCommGroup
  letI := p.sourceModule
  change Nonempty (Beli2019SolvedHeadData p.targetQ p.sourceQ
    p.targetLattice p.sourceLattice) at h
  change Lattice.Represents p.targetQ p.sourceQ
    p.targetLattice p.sourceLattice
  rcases h with ⟨D⟩
  exact D.represents

section SolvedHeadConstructor

variable (p : Beli2019RepresentationProblem.{u, v, w} K)

local instance : AddCommGroup p.Target := p.targetAddCommGroup
local instance : Module K p.Target := p.targetModule
local instance : AddCommGroup p.Source := p.sourceAddCommGroup
local instance : Module K p.Source := p.sourceModule

/-- Paper-facing constructor for the solved branches of Section 9.  At equal
rank, Lemma 9.3 or 9.6 only has to provide equal-valued norm-generating heads
and the induction-hypothesis representation of the two projected lattices. -/
theorem solvedHead_of_projected
    (hindex : p.sourceIndex = p.targetIndex)
    (targetHead : p.Target) (sourceHead : p.Source)
    (targetHeadGenerator : Lattice.IsNormGenerator p.targetQ
      p.targetLattice targetHead)
    (sourceHeadGenerator : Lattice.IsNormGenerator p.sourceQ
      p.sourceLattice sourceHead)
    (targetHeadAnisotropic : p.targetQ.IsAnisotropic targetHead)
    (sourceHeadAnisotropic : p.sourceQ.IsAnisotropic sourceHead)
    (hvalue : p.targetQ.quadratic targetHead =
      p.sourceQ.quadratic sourceHead)
    (tail : Lattice.Represents
      (p.targetQ.orthogonalSpace targetHead targetHeadAnisotropic)
      (p.sourceQ.orthogonalSpace sourceHead sourceHeadAnisotropic)
      (Lattice.projectedLattice p.targetQ p.targetLattice targetHead
        targetHeadAnisotropic)
      (Lattice.projectedLattice p.sourceQ p.sourceLattice sourceHead
        sourceHeadAnisotropic)) :
    p.SolvedHead := by
  have hsource : p.sourceIndex + 1 = Module.finrank K p.Source :=
    p.sourceBONG.toBONG.length_eq_finrank
  have htarget : p.targetIndex + 1 = Module.finrank K p.Target :=
    p.targetBONG.toBONG.length_eq_finrank
  have hfinrank : Module.finrank K p.Source = Module.finrank K p.Target := by
    omega
  rcases tail with ⟨tailRepresentation⟩
  change Nonempty (Beli2019SolvedHeadData p.targetQ p.sourceQ
    p.targetLattice p.sourceLattice)
  exact ⟨Beli2019SolvedHeadData.ofProjectedRepresentation
    targetHead sourceHead targetHeadGenerator sourceHeadGenerator
    targetHeadAnisotropic sourceHeadAnisotropic hvalue hfinrank
    tailRepresentation⟩

/-- At equal BONG rank, the ambient representation stored in a recursive
problem is automatically an ambient isometry. -/
theorem exists_ambientIsometry_of_index_eq
    (hindex : p.sourceIndex = p.targetIndex) :
    Nonempty (QuadraticSpace.Isometry p.sourceQ p.targetQ) := by
  letI : FiniteDimensional K p.Source :=
    p.sourceLattice.ambientBasis.finiteDimensional_of_finite
  letI : FiniteDimensional K p.Target :=
    p.targetLattice.ambientBasis.finiteDimensional_of_finite
  have hsource : p.sourceIndex + 1 = Module.finrank K p.Source :=
    p.sourceBONG.toBONG.length_eq_finrank
  have htarget : p.targetIndex + 1 = Module.finrank K p.Target :=
    p.targetBONG.toBONG.length_eq_finrank
  have hfinrank : Module.finrank K p.Source = Module.finrank K p.Target := by
    omega
  rcases p.ambient with ⟨f⟩
  exact ⟨f.toIsometryOfFinrankEq hfinrank⟩

/-- Equal-valued anisotropic heads in an equal-rank problem can be matched by
an ambient isometry. -/
theorem exists_ambientIsometry_map_heads
    (hindex : p.sourceIndex = p.targetIndex)
    (targetHead : p.Target) (sourceHead : p.Source)
    (targetHeadAnisotropic : p.targetQ.IsAnisotropic targetHead)
    (sourceHeadAnisotropic : p.sourceQ.IsAnisotropic sourceHead)
    (hvalue : p.targetQ.quadratic targetHead =
      p.sourceQ.quadratic sourceHead) :
    ∃ g : QuadraticSpace.Isometry p.sourceQ p.targetQ,
      g.toLinearEquiv sourceHead = targetHead := by
  rcases p.exists_ambientIsometry_of_index_eq hindex with ⟨base⟩
  have hmapped : p.targetQ.IsAnisotropic
      (base.toLinearEquiv sourceHead) :=
    base.map_isAnisotropic sourceHeadAnisotropic
  have heq : p.targetQ.quadratic (base.toLinearEquiv sourceHead) =
      p.targetQ.quadratic targetHead :=
    (base.map_quadratic sourceHead).trans hvalue.symm
  let correction := p.targetQ.equalValueTransportIsometry
    (base.toLinearEquiv sourceHead) targetHead hmapped
      targetHeadAnisotropic heq
  refine ⟨base.trans correction, ?_⟩
  change correction.toLinearEquiv (base.toLinearEquiv sourceHead) =
    targetHead
  exact p.targetQ.equalValueTransportIsometry_apply_left
    (base.toLinearEquiv sourceHead) targetHead hmapped
      targetHeadAnisotropic heq

/-- Equal heads identify the two orthogonal-complement ambient spaces.  This
is the ambient hypothesis needed for the lower-rank invocation of Theorem
2.1 in Lemmas 9.3 and 9.6. -/
theorem orthogonalAmbient_of_heads
    (hindex : p.sourceIndex = p.targetIndex)
    (targetHead : p.Target) (sourceHead : p.Source)
    (targetHeadAnisotropic : p.targetQ.IsAnisotropic targetHead)
    (sourceHeadAnisotropic : p.sourceQ.IsAnisotropic sourceHead)
    (hvalue : p.targetQ.quadratic targetHead =
      p.sourceQ.quadratic sourceHead) :
    (p.targetQ.orthogonalSpace targetHead targetHeadAnisotropic).Represents
      (p.sourceQ.orthogonalSpace sourceHead sourceHeadAnisotropic) := by
  rcases p.exists_ambientIsometry_map_heads hindex targetHead sourceHead
    targetHeadAnisotropic sourceHeadAnisotropic hvalue with ⟨g, hmap⟩
  subst targetHead
  exact ⟨(g.orthogonalIsometry sourceHead sourceHeadAnisotropic).toRepresentation⟩

/-- A rank-dropping solved-head branch.  The tail BONGs live on the literal
orthogonal projections selected by the two heads and satisfy Theorem 2.1 in
one smaller common rank. -/
structure HeadReduction where
  targetHead : p.Target
  sourceHead : p.Source
  targetHeadGenerator : Lattice.IsNormGenerator p.targetQ
    p.targetLattice targetHead
  sourceHeadGenerator : Lattice.IsNormGenerator p.sourceQ
    p.sourceLattice sourceHead
  targetHeadAnisotropic : p.targetQ.IsAnisotropic targetHead
  sourceHeadAnisotropic : p.sourceQ.IsAnisotropic sourceHead
  headValue_eq : p.targetQ.quadratic targetHead =
    p.sourceQ.quadratic sourceHead
  tailIndex : Nat
  targetIndex_eq : p.targetIndex = tailIndex + 1
  sourceIndex_eq : p.sourceIndex = tailIndex + 1
  targetTail : BONG.GoodBONG
    (p.targetQ.orthogonalSpace targetHead targetHeadAnisotropic)
    (Lattice.projectedLattice p.targetQ p.targetLattice targetHead
      targetHeadAnisotropic) (tailIndex + 1)
  sourceTail : BONG.GoodBONG
    (p.sourceQ.orthogonalSpace sourceHead sourceHeadAnisotropic)
    (Lattice.projectedLattice p.sourceQ p.sourceLattice sourceHead
      sourceHeadAnisotropic) (tailIndex + 1)
  tailConditions : RepresentationConditions targetTail sourceTail
    (Nat.le_refl tailIndex)

namespace HeadReduction

/-- The literal lower-rank projected-lattice problem. -/
noncomputable def next (D : HeadReduction p) :
    Beli2019RepresentationProblem.{u, v, w} K where
  Target := p.targetQ.vectorOrthogonal D.targetHead
  Source := p.sourceQ.vectorOrthogonal D.sourceHead
  targetAddCommGroup := inferInstance
  targetModule := inferInstance
  sourceAddCommGroup := inferInstance
  sourceModule := inferInstance
  targetQ := p.targetQ.orthogonalSpace D.targetHead
    D.targetHeadAnisotropic
  sourceQ := p.sourceQ.orthogonalSpace D.sourceHead
    D.sourceHeadAnisotropic
  targetLattice := Lattice.projectedLattice p.targetQ p.targetLattice
    D.targetHead D.targetHeadAnisotropic
  sourceLattice := Lattice.projectedLattice p.sourceQ p.sourceLattice
    D.sourceHead D.sourceHeadAnisotropic
  targetIndex := D.tailIndex
  sourceIndex := D.tailIndex
  targetBONG := D.targetTail
  sourceBONG := D.sourceTail
  rankBound := Nat.le_refl D.tailIndex
  ambient := p.orthogonalAmbient_of_heads
    (D.sourceIndex_eq.trans D.targetIndex_eq.symm)
    D.targetHead D.sourceHead D.targetHeadAnisotropic
      D.sourceHeadAnisotropic D.headValue_eq
  conditions := D.tailConditions

@[simp]
theorem next_measure_rank (D : HeadReduction p) :
    D.next.measure.rank = D.tailIndex + 1 :=
  rfl

/-- The projected problem has strictly smaller rank than its parent. -/
theorem smaller (D : HeadReduction p) :
    Beli2019ProblemSmaller Beli2019RepresentationProblem.measure
      D.next p := by
  apply beli2019ProblemSmaller_of_rank_lt
  rw [D.next_measure_rank]
  change D.tailIndex + 1 < p.sourceIndex + 1
  rw [D.sourceIndex_eq]
  omega

/-- A representation of the lower-rank problem produces the solved-head
certificate for the parent problem. -/
theorem solvedHead_of_next_represents (D : HeadReduction p)
    (hnext : D.next.Represents) : p.SolvedHead := by
  have hindex : p.sourceIndex = p.targetIndex := by
    rw [D.sourceIndex_eq, D.targetIndex_eq]
  have htail : Lattice.Represents
      (p.targetQ.orthogonalSpace D.targetHead D.targetHeadAnisotropic)
      (p.sourceQ.orthogonalSpace D.sourceHead D.sourceHeadAnisotropic)
      (Lattice.projectedLattice p.targetQ p.targetLattice D.targetHead
        D.targetHeadAnisotropic)
      (Lattice.projectedLattice p.sourceQ p.sourceLattice D.sourceHead
        D.sourceHeadAnisotropic) := by
    dsimp only [next, Represents] at hnext
    exact hnext
  exact solvedHead_of_projected p hindex D.targetHead D.sourceHead
    D.targetHeadGenerator D.sourceHeadGenerator
    D.targetHeadAnisotropic D.sourceHeadAnisotropic D.headValue_eq htail

/-- If the parent is a counterexample, then its lower-rank projected problem
is a counterexample as well. -/
theorem nextCounterexample (D : HeadReduction p)
    (hp : p.Counterexample) : D.next.Counterexample := by
  intro hnext
  exact hp
    (HeadReduction.solvedHead_of_next_represents p D hnext).represents

end HeadReduction

end SolvedHeadConstructor

/-- Package the root data of one invocation of Theorem 2.1 as a recursive
problem. -/
def ofData
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank) :
    Beli2019RepresentationProblem.{u, v, w} K where
  Target := V
  Source := W
  targetAddCommGroup := inferInstance
  targetModule := inferInstance
  sourceAddCommGroup := inferInstance
  sourceModule := inferInstance
  targetQ := q
  sourceQ := r
  targetLattice := L
  sourceLattice := M
  targetIndex := m
  sourceIndex := n
  targetBONG := a
  sourceBONG := b
  rankBound := hRank
  ambient := ambient
  conditions := conditions

@[simp]
theorem ofData_represents
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank) :
    (ofData a b hRank ambient conditions).Represents ↔
      Lattice.Represents q r L M :=
  Iff.rfl

@[simp]
theorem measure_ofData_rank
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank) :
    (measure (ofData a b hRank ambient conditions)).rank = n + 1 :=
  rfl

end Beli2019RepresentationProblem

end Bong
