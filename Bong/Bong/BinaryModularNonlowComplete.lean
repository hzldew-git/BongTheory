/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BinaryModularPrincipalUpper
import Bong.Bong.BinaryModularNonlowSpinor

/-!
# Complete non-low binary spinor formula in the negative modular branch

The forward Hsia--Xu estimate and the reverse shifted-generator construction
are combined here.  This closes Beli (2003), Definition 4, cases III(v) and
III(vi), including the lower endpoint, for every negative even BONG gap.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Exact-model equality in the negative, even, non-low branch. -/
theorem spinorNormImage_binaryModel_eq_beliSpinorGroupRepresentative_negative_even_nonlow
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (hRneg : ordUnit K a < 0)
    (hEven : Even (ordUnit K a))
    (hdLower : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      (beliSpinorGroupRepresentative K a : Set (SquareClass K)) := by
  apply Set.Subset.antisymm
  · exact
      spinorNormImage_binaryModel_le_beliSpinorGroupRepresentative_negative_even_nonlow
        (K := K) a c ha hRneg hEven hdLower htwo hdiag
  · have hRupper : ordUnit K a ≤
        2 * (ramificationIndex K : Int) := by
      have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
      omega
    exact
      beliSpinorGroupRepresentative_le_spinorNormImage_binaryModel_of_even_nonlow
        (K := K) a c ha hRupper hEven hdLower htwo hdiag

/-- Intrinsic equality for an arbitrary binary BONG with negative even gap
in the non-low branch. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_negative_even_nonlow
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2)
    (hRneg : b.binaryOrderGap < 0)
    (hEven : Even b.binaryOrderGap)
    (hdLower : ¬2 * beliParameterDefect K b.binaryParameter ≤
      (beliSpinorCaseIIILowerCutoff K b.binaryParameter : ℕ∞)) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K)) := by
  rw [b.spinorNormImage_eq_binaryModel]
  apply
    spinorNormImage_binaryModel_eq_beliSpinorGroupRepresentative_negative_even_nonlow
  · exact b.binaryParameter_isBinaryParameterAdmissible
  · change b.binaryParameterOrder < 0
    rwa [b.binaryParameterOrder_eq_orderGap]
  · change Even b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]
  · exact hdLower
  · exact b.binaryModelCoefficient_isAdmissibleWitness.1
  · exact b.binaryModelCoefficient_isAdmissibleWitness.2

end BONG

end Bong
