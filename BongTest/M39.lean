/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.OrthogonalBasis

/-!
# M39 binary orthogonal invariants smoke tests
-/

namespace BongTest.M39

open Bong Bong.Dyadic Module

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

example (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) :
    (BONG.ofOrthogonalBasisFinTwoOfOrdLe
      q basis horth hne0 hne1 horder).binaryOrderGap =
        ordUnit K (Units.mk0 (q.quadratic (basis 1)) hne1) -
          ordUnit K (Units.mk0 (q.quadratic (basis 0)) hne0) :=
  BONG.binaryOrderGap_ofOrthogonalBasisFinTwoOfOrdLe
    q basis horth hne0 hne1 horder

example (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) :
    (BONG.ofOrthogonalBasisFinTwoOfOrdLe
      q basis horth hne0 hne1 horder).binaryDeterminantInvariant =
        unitSquareClass K
          (Units.mk0 (q.quadratic (basis 1)) hne1 /
            Units.mk0 (q.quadratic (basis 0)) hne0) :=
  BONG.binaryDeterminantInvariant_ofOrthogonalBasisFinTwoOfOrdLe
    q basis horth hne0 hne1 horder

#print axioms Bong.BONG.binaryParameter_ofOrthogonalBasisFinTwoOfOrdLe
#print axioms Bong.BONG.binaryOrderGap_ofOrthogonalBasisFinTwoOfOrdLe
#print axioms Bong.BONG.binaryDeterminantInvariant_ofOrthogonalBasisFinTwoOfOrdLe

end

end BongTest.M39
