/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemmas48To410

/-!
# M90 Beli 2003, Lemmas 4.8--4.9 and Corollary 4.10 smoke tests
-/

namespace BongTest.M90

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

variable [BONGStructuralLaws.{u, v} K]

example (b : BONG.GoodBONG q L n) :
    ∃ c : BONG.GoodBONG q (Lattice.dualLattice q L) n,
      (∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i) ∧
      (∀ i, c.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)) ∧
      ∀ i, c.order i = -b.order (Fin.rev i) :=
  b.exists_reverseDual_with_values

variable [BeliLemma49Laws.{u, v} K]

example (b : BONG V q L n) (hgood : b.IsGood) (i : Fin n) :
    squareClass K (b.valueUnit i) ∈
      Lattice.improperSpinorNormImage (q := q) (L := L) :=
  b.beliCorollary410_i hgood i

variable [BinarySpinorLocalLaws.{u, v} K]

example (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n) :
    (beliSpinorGroup K (b.adjacentUnitSquareClass i hi) :
        Set (SquareClass K)) ⊆
      Lattice.spinorNormImage (q := q) (L := L) :=
  b.beliCorollary410_ii hgood i hi

#print axioms Bong.BONG.GoodBONG.exists_reverseDual_with_values
#print axioms Bong.BONG.beliLemma49_i_good
#print axioms Bong.BONG.beliLemma49_i_propertyA
#print axioms Bong.BONG.beliLemma49_ii
#print axioms Bong.BONG.beliCorollary410_i
#print axioms Bong.BONG.beliCorollary410_ii
#print axioms Bong.BONG.beliCorollary410_iii

end

end BongTest.M90
