/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma319

/-!
# M85 Beli 2003, Lemma 3.19 smoke tests
-/

namespace BongTest.M85

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  [QuadraticDefectLaws K]

example (a : Kˣ)
    (hlarge : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    ∃ s : Kˣ,
      (s : K) ^ 2 = 1 - (a : K) ∧
      ord K (1 + (s : K)) = ord K (2 : K) ∧
      ordUnit K s = 0 :=
  exists_squareRoot_one_sub_with_order_one_add_eq_ord_two a hlarge

example (x y : V) (R : Int)
    (hx : (R : WithTop Int) < ord K (q.quadratic x))
    (hy : (R : WithTop Int) < ord K (q.quadratic y))
    (hsum : ord K (q.quadratic (x + y)) = (R : WithTop Int)) :
    ∃ hne : q.bilin x y ≠ 0,
      ordUnit K (Units.mk0 (q.bilin x y) hne) =
        R - ramificationIndex K :=
  BONG.mixedPairing_order_eq_sub_ramificationIndex
    x y R hx hy hsum

example (x y : V) (R : Int)
    (hx : (R : WithTop Int) < ord K (q.quadratic x))
    (hy : (R : WithTop Int) < ord K (q.quadratic y))
    (hsum : ord K (q.quadratic (x + y)) = (R : WithTop Int)) :
    BONG.IsScaledHyperbolicPair q x y
      (R - ramificationIndex K) :=
  BONG.beliLemma319 x y R hx hy hsum

#print axioms Bong.Dyadic.exists_squareRoot_one_sub_with_order_one_add_eq_ord_two
#print axioms Bong.Lattice.basisLattice_isIsometric_hyperbolicPlane
#print axioms Bong.BONG.mixedPairing_order_eq_sub_ramificationIndex
#print axioms Bong.BONG.beliLemma319

end

end BongTest.M85
