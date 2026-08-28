/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328CoefficientShiftReplacement
import Bong.Lattice.Omeara9328FirstPairConditionTransfer
import Bong.Lattice.Omeara9328HeadAlignment
import Bong.Lattice.OmearaFundamentalTypeAlgebra

/-!
# The 93:28 conditions after a 93:19 coefficient shift

A concrete 93:19 replacement changes only the first two components.  Once
the three clauses at boundary zero and the new head isometry are supplied by
the local case calculation, the replacement is exactly the head-alignment
object consumed by the saturated 93:28 induction.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition.Omeara9319JordanReplacement

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}
  {J : JordanDecomposition q L (m + 2)}
  {H : JordanDecomposition r M (m + 2)}

/-- Only the first boundary must be recomputed after the coefficient shift;
later clauses are transported through the canonical prefix isometries. -/
theorem conditionsWith
    (R : Omeara9319JordanReplacement H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A)
    (boundary : Omeara9328BoundaryZeroConditionsWith J R.target A) :
    J.Omeara9328ConditionsWith R.target A := by
  apply omeara9328ConditionsWith_of_boundaryZero_and_laterPrefixIsometry
    J H R.target A conditions boundary
  intro i hi
  have hiVal : i.val ≠ 0 := by
    intro hzero
    apply hi
    apply Fin.ext
    simpa using hzero
  exact R.laterPrefixIsometry (i.val + 1) (by omega)

/-- Package a coefficient shift, its first-boundary calculation, and its
aligned new head as the exact replacement required by the 93:28 recursion. -/
noncomputable def headAlignedReplacement
    (R : Omeara9319JordanReplacement H)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A)
    (boundary : Omeara9328BoundaryZeroConditionsWith J R.target A)
    (head : Isometry (J.component 0).space (R.target.component 0).space
      (J.component 0).lattice (R.target.component 0).lattice) :
    Omeara9328HeadAlignedReplacement J H A where
  target := R.target
  saturated := R.saturated
  fundamentalType := F.trans R.fundamentalType
  conditions := R.conditionsWith A conditions boundary
  head := head

end Lattice.JordanDecomposition.Omeara9319JordanReplacement

end Bong
