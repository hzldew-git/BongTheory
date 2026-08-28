/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionFourInvariants

/-!
# M119 Beli 2006, Lemma 4.2 and Definition 4.3 smoke tests
-/

namespace BongTest.M119

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q r : QuadraticSpace K V} {L M : Lattice K V} {m n : Nat}

example (x y : Kˣ) :
    min (BONG.GoodBONG.defectOrder (K := K) x)
        (BONG.GoodBONG.defectOrder (K := K) y) ≤
      BONG.GoodBONG.defectOrder (K := K) (x * y) :=
  BONG.GoodBONG.defectOrder_mul_ge_min x y

example (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    {U : Type*} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {N : Lattice K U} {k : Nat}
    (c : BONG.GoodBONG s N (k + 1)) (ε η : Kˣ) (i j l : Nat) :
    min (a.truncatedPrefixDefect b ε i j)
        (b.truncatedPrefixDefect c η j l) ≤
      a.truncatedPrefixDefect c (ε * η) i l :=
  BONG.GoodBONG.truncatedPrefixDefect_domination a b c ε η i j l

variable [classification : GoodBONGClassificationLaws.{u, v, v} K]
  [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]

example (a a' : BONG.GoodBONG q L (m + 1)) (i : Nat) :
    a.prefixAlphaCap i = a'.prefixAlphaCap i :=
  BONG.GoodBONG.prefixAlphaCap_invariant
    (classification := classification) a a' i

example (a a' : BONG.GoodBONG q L (m + 1))
    (b b' : BONG.GoodBONG r M (n + 1)) (ε : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b ε i j =
      a'.truncatedPrefixDefect b' ε i j :=
  BONG.GoodBONG.truncatedPrefixDefect_invariant
    (classificationV := classification) (classificationW := classification)
    (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
    a a' b b' ε i j

example (a a' : BONG.GoodBONG q L (m + 1))
    (b b' : BONG.GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha b i = a'.representationAlpha b' i :=
  BONG.GoodBONG.representationAlpha_invariant
    (classificationV := classification) (classificationW := classification)
    (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
    a a' b b' i

example (a a' : BONG.GoodBONG q L (m + 1))
    (b b' : BONG.GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) :
    a.terminalAdjustedAlpha b hgap = a'.terminalAdjustedAlpha b' hgap :=
  BONG.GoodBONG.terminalAdjustedAlpha_invariant
    (classificationV := classification) (classificationW := classification)
    (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
    a a' b b' hgap

#print axioms Bong.BONG.GoodBONG.defectOrder_mul_ge_min
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_domination
#print axioms Bong.BONG.GoodBONG.prefixAlphaCap_invariant
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_invariant
#print axioms Bong.BONG.GoodBONG.representationAlpha_invariant
#print axioms Bong.BONG.GoodBONG.terminalAdjustedAlpha_invariant

end BongTest.M119
