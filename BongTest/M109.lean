/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaCompression

/-!
# M109 Beli 2009/2010, Lemma 2.4--Remark 2.6 smoke tests
-/

namespace BongTest.M109

open Bong Bong.Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

variable [localization : Bong.Beli2009AlphaLocalizationLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 2))
    (s : AlphaLocalizationIndex (n + 1)) (i : Fin (n + 1))
    (hi : s.pivotFin ≤ i)
    (witness : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha i =
      (b.leftCompressedCandidates s i witness).min'
        (b.leftCompressedCandidates_nonempty s i witness) :=
  b.beli2009Lemma24_left s i hi witness

example (b : BONG.GoodBONG q L (n + 2))
    (s : AlphaLocalizationIndex (n + 1)) (i : Fin (n + 1))
    (hi : i ≤ s.pivotFin)
    (witness : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha i =
      (b.rightCompressedCandidates s i witness).min'
        (b.rightCompressedCandidates_nonempty s i witness) :=
  b.beli2009Lemma24_right s i hi witness

example (b : BONG.GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    b.alpha i =
      (b.recursiveAlphaCandidates i).min'
        (b.recursiveAlphaCandidates_nonempty i) :=
  b.beli2009Corollary25_i i

example (b : BONG.GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    b.alpha i =
      (b.segmentRecursiveAlphaCandidates i).min'
        (b.segmentRecursiveAlphaCandidates_nonempty i) :=
  b.beli2009Corollary25_ii i

example (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) (s : Kˣ)
    (h : a.IsCoefficientScale b s) (i : Fin n) :
    b.alphaValue i = a.alphaValue i :=
  BONG.GoodBONG.beli2009Remark26_scaling a b s h i

variable [structural : Bong.BONGStructuralLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 1)) :
    ∃ c : BONG.GoodBONG q (Lattice.dualLattice q L) (n + 1),
      (∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i) ∧
      (∀ i, c.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)) ∧
      (∀ i, c.order i = -b.order (Fin.rev i)) ∧
      ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i) :=
  b.beli2009Remark26_duality

#print axioms Bong.BONG.GoodBONG.beli2009Lemma24_left
#print axioms Bong.BONG.GoodBONG.beli2009Lemma24_right
#print axioms Bong.BONG.GoodBONG.beli2009Corollary25_i
#print axioms Bong.BONG.GoodBONG.beli2009Corollary25_ii
#print axioms Bong.BONG.GoodBONG.beli2009Remark26_scaling
#print axioms Bong.BONG.GoodBONG.beli2009Remark26_duality

end BongTest.M109
