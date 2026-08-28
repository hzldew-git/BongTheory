/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Transitivity

/-!
# M130 Beli 2019, Section 4 transitivity smoke tests
-/

namespace BongTest.M130

open Bong

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {m n k : Nat}

example (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (c : BONG.GoodBONG s N (k + 1))
    (hnm : n ≤ m) (hkn : k ≤ n)
    (hab : a.RepresentationOrderCondition b hnm)
    (hbc : b.RepresentationOrderCondition c hkn) :
    a.RepresentationOrderCondition c (hkn.trans hnm) :=
  a.representationOrderCondition_trans b c hnm hkn hab hbc

example (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (c : BONG.GoodBONG s N (n + 1))
    (hab : a.RepresentationDefectCondition b)
    (hbc : b.RepresentationDefectCondition c)
    (hkey : ∀ i : RepresentationIndex (n + 1) (n + 1),
      a.representationAlpha c i ≤ a.representationAlpha b i ∧
        a.representationAlpha c i ≤ b.representationAlpha c i) :
    a.RepresentationDefectCondition c :=
  a.representationDefectCondition_trans_of_bounds b c hab hbc hkey

#print axioms Bong.BONG.GoodBONG.representationOrderCondition_trans
#print axioms Bong.BONG.GoodBONG.representationDefectAt_trans_of_bounds
#print axioms Bong.BONG.GoodBONG.representationDefectCondition_trans_of_bounds

end BongTest.M130
