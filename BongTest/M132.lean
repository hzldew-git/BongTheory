/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019KeyLemma

/-!
# M132 Beli 2019, Section 4 key-lemma assembly smoke tests
-/

namespace BongTest.M132

open Bong Bong.Dyadic

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {n : Nat}

example (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (c : BONG.GoodBONG s N (n + 1)) (i : Fin (n + 1))
    (hi : i.val = 0) :
    a.KeyLemmaRightDirectTrigger b c i :=
  a.keyLemmaRightDirectTrigger_of_zero b c i hi

example (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (c : BONG.GoodBONG s N (n + 1))
    (hab : a.RepresentationDefectCondition b)
    (hbc : b.RepresentationDefectCondition c)
    (hkey : BONG.GoodBONG.SectionFourKeyLemmaBounds a b c)
    (hreduce : BONG.GoodBONG.SectionFourDefectReduction a b c) :
    a.RepresentationDefectCondition c :=
  a.representationDefectCondition_trans_of_keyLemma b c hab hbc hkey hreduce

#print axioms Bong.BONG.GoodBONG.keyLemmaLeftDirectTrigger_of_eq_one
#print axioms Bong.BONG.GoodBONG.keyLemmaLeftDirectTrigger_of_last
#print axioms Bong.BONG.GoodBONG.keyLemmaRightDirectTrigger_of_zero
#print axioms Bong.BONG.GoodBONG.keyLemmaRightDirectTrigger_of_penultimate
#print axioms Bong.BONG.GoodBONG.representationAlpha_le_leftAlpha
#print axioms Bong.BONG.GoodBONG.representationAlpha_le_rightAlpha
#print axioms Bong.BONG.GoodBONG.representationDefectCondition_trans_of_keyLemma

end BongTest.M132
