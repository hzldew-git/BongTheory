/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44

/-!
# M88 Beli 2003, Corollary 4.4 smoke tests
-/

namespace BongTest.M88

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

variable [BeliCorollary44Laws.{u, v} K]

example (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n)
    (horder : b.order i ≤ b.order ⟨i.1 + 1, hi⟩) :
    b.HasTwoBlockSplit (i.1 + 1) (by omega) :=
  b.beliCorollary44_i hgood i hi horder

example (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n)
    (horder : b.order ⟨i.1 + 1, hi⟩ < b.order i) :
    b.HasThreeBlockSplit i hi :=
  b.beliCorollary44_ii hgood i hi horder

example (b : BONG V q L n)
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (hconcat : b.IsPutTogether M.toOrthogonalDecomposition c)
    (i : Fin n) (hi : i.1 + 1 < n)
    (horder : b.order ⟨i.1 + 1, hi⟩ < b.order i) :
    b.AdjacentPairIsOneComponent M c i hi :=
  b.beliCorollary44_iii M c hconcat i hi horder

example (b : BONG V q L (n + 2)) (hgood : b.IsGood) :
    Lattice.HasDoubledScaleOrder q L
      (min (2 * b.order 0) (b.order 0 + b.order 1)) :=
  b.beliCorollary44_iv hgood

#print axioms Bong.BONG.SegmentWitness.toQuadraticSublattice_carrier
#print axioms Bong.BONG.beliCorollary44_i
#print axioms Bong.BONG.beliCorollary44_ii
#print axioms Bong.BONG.beliCorollary44_iii
#print axioms Bong.BONG.beliCorollary44_iv
#print axioms Bong.BONG.beliCorollary44_v

end

end BongTest.M88
