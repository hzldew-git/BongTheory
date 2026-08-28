/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41

/-!
# M86 Beli 2003, Definitions 7--9, Lemma 4.1, and Corollary 4.2
-/

namespace BongTest.M86

open Bong Bong.Dyadic
open Bong.Lattice.OrthogonalDecomposition

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

example (J : Lattice.JordanDecomposition q L t) (hJ : J.HasPropertyA) :
    Lattice.MaximalNormSplitting q L t :=
  Lattice.MaximalNormSplitting.ofJordanPropertyA J hJ

example (b : BONG V q L n) :
    b.IsGood ↔
      ∀ (i : Fin n) (hi : i.1 + 2 < n),
        b.order i ≤ b.order ⟨i.1 + 2, hi⟩ :=
  b.beliDefinition9

variable [BeliSectionFourLaws.{u, v} K]

example (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily) :
    ∃ b : BONG V q L (Module.finrank K V),
      b.IsPutTogether M.toOrthogonalDecomposition c :=
  BONG.beliLemma41_i M c

example (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (hb : b.IsPutTogether M.toOrthogonalDecomposition c) : b.IsGood :=
  BONG.beliCorollary42_ii M c b hb

variable [BONGStructuralLaws.{u, v} K]

example (b : BONG V q L n) (hL : Lattice.HasJordanPropertyA q L) :
    b.HasPropertyA :=
  b.beliCorollary42_i hL

#print axioms Bong.Lattice.MaximalNormSplitting.componentRank_eq_one_or_two
#print axioms Bong.Lattice.MaximalNormSplitting.ofJordanPropertyA_component
#print axioms Bong.BONG.PutTogetherWitness.value_eq
#print axioms Bong.BONG.beliDefinition9
#print axioms Bong.BONG.beliLemma41_i
#print axioms Bong.BONG.beliCorollary42_i
#print axioms Bong.BONG.beliCorollary42_ii

end

end BongTest.M86
