/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328GeneratorChoice

/-!
# The strict containment clauses in O'Meara 93:28

The printed theorem uses proper containment in clauses (ii) and (iii).
This distinction is mathematically visible at the equality boundary and is
also the source of the strict inequality `2e < alpha_{i-1} + alpha_i` in
Beli's translation.  The earlier non-strict predicates are retained as
strong auxiliary hypotheses for the existing sufficiency construction; the
definitions in this file are the paper-faithful statements used by the final
classification theorem.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Paper-faithful O'Meara 93:28(ii): the representation is required only
under proper containment of the fundamental ideal in the right threshold. -/
noncomputable def Omeara9328StrictConditionII
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1)) : Prop :=
  ∀ i : Fin n,
    J.fundamentalIdeal i <
        J.fourNormOverWeightIdeal (boundaryRightIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine
          (J.fundamentalNormGenerator (boundaryRightIndex i)))

/-- Paper-faithful O'Meara 93:28(iii), with proper containment in the left
threshold. -/
noncomputable def Omeara9328StrictConditionIII
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1)) : Prop :=
  ∀ i : Fin n,
    J.fundamentalIdeal i <
        J.fourNormOverWeightIdeal (boundaryLeftIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine
          (J.fundamentalNormGenerator (boundaryLeftIndex i)))

/-- The three paper-faithful semantic conditions in O'Meara 93:28. -/
noncomputable def Omeara9328StrictConditions
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1)) : Prop :=
  J.Omeara9328ConditionI H ∧ J.Omeara9328StrictConditionII H ∧
    J.Omeara9328StrictConditionIII H

/-- A transported splitting satisfies the strict right-hand clause. -/
theorem omeara9328StrictConditionII_mapIsometry
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (f : Lattice.Isometry q r L M) :
    J.Omeara9328StrictConditionII (J.mapIsometry f) := by
  intro i _
  let g := J.toOrthogonalDecomposition.prefixLatticeIsometry f
    (i.val + 1)
  exact g.toQuadraticSpaceIsometry.embedsInto_orthogonalSum_target
    (QuadraticSpace.scaledLine
      (J.fundamentalNormGenerator (boundaryRightIndex i)))

/-- A transported splitting satisfies the strict left-hand clause. -/
theorem omeara9328StrictConditionIII_mapIsometry
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (f : Lattice.Isometry q r L M) :
    J.Omeara9328StrictConditionIII (J.mapIsometry f) := by
  intro i _
  let g := J.toOrthogonalDecomposition.prefixLatticeIsometry f
    (i.val + 1)
  exact g.toQuadraticSpaceIsometry.embedsInto_orthogonalSum_target
    (QuadraticSpace.scaledLine
      (J.fundamentalNormGenerator (boundaryLeftIndex i)))

/-- All paper-faithful conditions hold for the transported splitting. -/
theorem omeara9328StrictConditions_mapIsometry
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (f : Lattice.Isometry q r L M) :
    J.Omeara9328StrictConditions (J.mapIsometry f) :=
  ⟨J.omeara9328ConditionI_mapIsometry f,
    J.omeara9328StrictConditionII_mapIsometry f,
    J.omeara9328StrictConditionIII_mapIsometry f⟩

/-- Strict condition (ii) with a coherent generator family. -/
noncomputable def Omeara9328StrictConditionIIWith
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (A : FundamentalNormGeneratorChoice J) : Prop :=
  ∀ i : Fin n,
    J.fundamentalIdeal i <
        J.fourNormOverWeightIdealWith A (boundaryRightIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))

/-- Strict condition (iii) with a coherent generator family. -/
noncomputable def Omeara9328StrictConditionIIIWith
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (A : FundamentalNormGeneratorChoice J) : Prop :=
  ∀ i : Fin n,
    J.fundamentalIdeal i <
        J.fourNormOverWeightIdealWith A (boundaryLeftIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))

/-- The paper-faithful conditions with a coherent generator family. -/
noncomputable def Omeara9328StrictConditionsWith
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (A : FundamentalNormGeneratorChoice J) : Prop :=
  J.Omeara9328ConditionI H ∧ J.Omeara9328StrictConditionIIWith H A ∧
    J.Omeara9328StrictConditionIIIWith H A

/-- Canonical generators identify the two strict formulations
definitionally. -/
theorem omeara9328StrictConditionsWith_canonical_iff
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1)) :
    J.Omeara9328StrictConditionsWith H
        (canonicalFundamentalNormGeneratorChoice J) ↔
      J.Omeara9328StrictConditions H :=
  Iff.rfl

end Lattice.JordanDecomposition

end Bong
