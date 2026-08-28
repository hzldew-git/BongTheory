/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReverseDualBoundary
import Bong.Lattice.Omeara9328Conditions

/-!
# Threshold ideals under reverse duality

The norm-generator and weight orders of a fundamental layer acquire the
same `-2S` correction under reverse duality.  Their difference, and hence
O'Meara's threshold ideal `4 a_i w_i⁻¹`, is therefore unchanged at the
reversed index.  Together with the boundary-ideal identity this is the
ideal-theoretic content needed to exchange conditions 93:28(ii) and (iii).
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- O'Meara's ideal `4 a_i w_i⁻¹` is invariant under reverse duality,
up to reversing the component index. -/
@[simp]
theorem reverseDual_fourNormOverWeightIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin (t + 1)) :
    J.reverseDual.fourNormOverWeightIdeal i =
      J.fourNormOverWeightIdeal (Fin.rev i) := by
  unfold fourNormOverWeightIdeal
  rw [J.reverseDual_fundamentalNormGenerator_order,
    J.reverseDual_fundamentalWeightOrder]
  congr 1
  ring

/-- At a reversed boundary, the trigger for 93:28(ii) is exactly the old
trigger for 93:28(iii). -/
theorem reverseDual_conditionII_trigger_iff
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.reverseDual.fundamentalIdeal i ≤
        J.reverseDual.fourNormOverWeightIdeal (boundaryRightIndex i) ↔
      J.fundamentalIdeal (Fin.rev i) ≤
        J.fourNormOverWeightIdeal
          (boundaryLeftIndex (Fin.rev i)) := by
  rw [J.reverseDual_fundamentalIdeal,
    J.reverseDual_fourNormOverWeightIdeal,
    rev_boundaryRightIndex]

/-- At a reversed boundary, the trigger for 93:28(iii) is exactly the old
trigger for 93:28(ii). -/
theorem reverseDual_conditionIII_trigger_iff
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.reverseDual.fundamentalIdeal i ≤
        J.reverseDual.fourNormOverWeightIdeal (boundaryLeftIndex i) ↔
      J.fundamentalIdeal (Fin.rev i) ≤
        J.fourNormOverWeightIdeal
          (boundaryRightIndex (Fin.rev i)) := by
  rw [J.reverseDual_fundamentalIdeal,
    J.reverseDual_fourNormOverWeightIdeal,
    rev_boundaryLeftIndex]

end Lattice.JordanDecomposition

end Bong
