/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormalForm

/-!
# M47 modular binary normal-form smoke tests
-/

namespace BongTest.M47

open Bong Bong.Dyadic
open Module

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (a : Kˣ) (hmodular : Lattice.IsModular q L a)
    (hfin : 0 < finrank K V) :
    Lattice.scaleIdeal q L =
      Lattice.principalIdeal (K := K) (a : K) :=
  hmodular.scaleIdeal_eq_principal hfin

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    Lattice.scaleIdeal q L =
        Lattice.principalIdeal (K := K) (a : K) ∧
      Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (b.value 0) ∧
      Lattice.normIdeal q (Lattice.dualLattice q L) =
        Lattice.principalIdeal (K := K)
          (q.quadratic (((a⁻¹ : Kˣ) : K) • b.head)) ∧
      2 * ordUnit K a = b.order 0 + b.order 1 ∧
      ord K (q.quadratic (((a⁻¹ : Kˣ) : K) • b.head)) =
        ((-b.order 1 : Int) : WithTop Int) ∧
      b.order 0 ≡ b.order 1 [ZMOD 2] :=
  b.modular_binary_ideal_formulas a hmodular

#print axioms Bong.Lattice.IsModular.scaleIdeal_eq_principal
#print axioms Bong.BONG.exists_of_normGenerator_with_modular_normal_form
#print axioms Bong.BONG.modular_binary_ideal_formulas
#print axioms Bong.BONG.exists_modular_parameter_with_binary_ideal_formulas

end

end BongTest.M47
