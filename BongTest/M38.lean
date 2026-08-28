/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M38 ordered orthogonal binary basis smoke tests
-/

namespace BongTest.M38

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
    BONG V q (Lattice.basisLattice basis) 2 :=
  BONG.ofOrthogonalBasisFinTwoOfOrdLe
    q basis horth hne0 hne1 horder

example (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) (i : Fin 2) :
    (BONG.ofOrthogonalBasisFinTwoOfOrdLe
      q basis horth hne0 hne1 horder).ambientVector i = basis i :=
  BONG.ambientVector_ofOrthogonalBasisFinTwoOfOrdLe
    q basis horth hne0 hne1 horder i

example (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) (i : Fin 2) :
    (BONG.ofOrthogonalBasisFinTwoOfOrdLe
      q basis horth hne0 hne1 horder).value i =
        q.quadratic (basis i) :=
  BONG.value_ofOrthogonalBasisFinTwoOfOrdLe
    q basis horth hne0 hne1 horder i

#print axioms Bong.BONG.ofOrthogonalBasisFinTwoOfOrdLe
#print axioms Bong.BONG.ambientVector_ofOrthogonalBasisFinTwoOfOrdLe
#print axioms Bong.BONG.value_ofOrthogonalBasisFinTwoOfOrdLe

end

end BongTest.M38
