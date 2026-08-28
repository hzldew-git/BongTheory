/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryModularInvariant

/-!
# M42 modular dual norm smoke tests
-/

namespace BongTest.M42

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    2 * ordUnit K a = b.order 0 + b.order 1 :=
  b.two_mul_modularOrder_eq_order_add a hmodular

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    Lattice.IsNormGenerator q (Lattice.dualLattice q L)
      ((a⁻¹ : Kˣ) • b.head) :=
  b.inverseModularParameter_smul_head_isNormGenerator_dual a hmodular

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    ord K (q.quadratic (((a⁻¹ : Kˣ) : K) • b.head)) =
      ((-b.order 1 : Int) : WithTop Int) :=
  b.ord_quadratic_inverseModularParameter_smul_head a hmodular

#print axioms Bong.Lattice.IsNormGenerator.rescale
#print axioms Bong.Lattice.IsModular.normGenerator_dual
#print axioms Bong.BONG.two_mul_modularOrder_eq_order_add
#print axioms Bong.BONG.ord_quadratic_inverseModularParameter_smul_head

end

end BongTest.M42
