/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryModularInvariant

/-!
# M41 modular volume and binary invariants smoke tests
-/

namespace BongTest.M41

open Bong Bong.Dyadic Module

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (a : Kˣ) (hmodular : Lattice.IsModular q L a) :
    Lattice.volumeOrder q L =
      (finrank K V : Int) * ordUnit K a :=
  hmodular.volumeOrder_eq

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    b.binaryOrderGap = 2 * ordUnit K a - 2 * b.order 0 :=
  b.binaryOrderGap_eq_of_isModular a hmodular

example (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    Even b.binaryOrderGap :=
  b.even_binaryOrderGap_of_isModular a hmodular

#print axioms Bong.Lattice.volumeOrder_rescale
#print axioms Bong.Lattice.volumeOrder_dualLattice
#print axioms Bong.Lattice.IsModular.volumeOrder_eq
#print axioms Bong.BONG.binaryOrderGap_eq_of_isModular
#print axioms Bong.BONG.even_binaryOrderGap_of_isModular

end

end BongTest.M41
