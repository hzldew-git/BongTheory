/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328SaturatedInduction
import Bong.Lattice.OmearaFundamentalTypeAlgebra

/-!
# Head-aligned replacements obtained from an integral isometry

Once an integral isometry of the complete lattices has been constructed,
transporting the source Jordan decomposition along it gives a saturated
target decomposition whose head is literally the transported source head.
This small bridge lets the scale-spread induction in O'Meara 93:28 feed a
complete isometry back into the head-and-tail recursion.
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
  {L : Lattice K V} {M : Lattice K W} {t : Nat}

/-- Saturatedness is preserved when a Jordan splitting is transported by
an integral isometry. -/
theorem IsSaturated.mapIsometry
    {J : JordanDecomposition q L t} (hJ : J.IsSaturated)
    (f : Isometry q r L M) :
    (J.mapIsometry f).IsSaturated := by
  intro i
  let componentMap := (J.component i).mapLatticeIsometry f
  calc
    normGroupSet ((J.mapIsometry f).component i).space
        ((J.mapIsometry f).component i).lattice =
        normGroupSet (J.component i).space (J.component i).lattice :=
      normGroupSet_eq_of_latticeIsometry componentMap
    _ = J.fundamentalNormGroup i := hJ i
    _ = (J.mapIsometry f).fundamentalNormGroup i := by
      symm
      unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
      exact normGroupSet_scaleTruncation_eq_of_isometry f _

/-- A transported splitting has the same complete fundamental type as the
source splitting. -/
noncomputable def SameFundamentalType.mapIsometry
    (J : JordanDecomposition q L t) (f : Isometry q r L M) :
    SameFundamentalType J (J.mapIsometry f) :=
  sameFundamentalTypeOfIsometry J (J.mapIsometry f) f

/-- The 93:28 conditions with any coherent source generator choice hold
against the transported source splitting. -/
theorem omeara9328ConditionsWith_mapIsometry
    {n : Nat} (J : JordanDecomposition q L (n + 1))
    (A : FundamentalNormGeneratorChoice J)
    (f : Isometry q r L M) :
    J.Omeara9328ConditionsWith (J.mapIsometry f) A := by
  refine ⟨J.omeara9328ConditionI_mapIsometry f, ?_, ?_⟩
  · intro i _
    let g := J.toOrthogonalDecomposition.prefixLatticeIsometry f
      (i.val + 1)
    exact g.toQuadraticSpaceIsometry.embedsInto_orthogonalSum_target
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))
  · intro i _
    let g := J.toOrthogonalDecomposition.prefixLatticeIsometry f
      (i.val + 1)
    exact g.toQuadraticSpaceIsometry.embedsInto_orthogonalSum_target
      (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))

/-- Turn a complete integral isometry into the target-splitting replacement
required by the saturated head-and-tail induction. -/
noncomputable def headAlignedReplacementOfIsometry
    {n : Nat} (J : JordanDecomposition q L (n + 2))
    (_H : JordanDecomposition r M (n + 2))
    (hJ : J.IsSaturated)
    (A : FundamentalNormGeneratorChoice J)
    (f : Isometry q r L M) :
    Omeara9328HeadAlignedReplacement J _H A where
  target := J.mapIsometry f
  saturated := hJ.mapIsometry f
  fundamentalType := SameFundamentalType.mapIsometry J f
  conditions := J.omeara9328ConditionsWith_mapIsometry A f
  head := (J.component 0).mapLatticeIsometry f

end Lattice.JordanDecomposition

end Bong
