/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaArithmetic

/-!
# M110 Beli 2009/2010, Lemma 2.7 and Corollaries 2.8--2.9 smoke tests
-/

namespace BongTest.M110

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    0 ≤ b.alphaValue i ∧
      (b.alphaValue i = 0 ↔
        b.orderGap i = -(2 * (ramificationIndex K : Int))) :=
  b.beli2009Lemma27_i i

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap i) :
    b.alphaValue i = b.halfGapValue i :=
  b.beli2009Lemma27_ii i hgap

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : b.orderGap i ≤ 2 * (ramificationIndex K : Int)) :
    (b.orderGap i : ℚ) ≤ b.alphaValue i ∧
      (b.alphaValue i = (b.orderGap i : ℚ) ↔
        b.orderGap i = 2 * (ramificationIndex K : Int) ∨
          Odd (b.orderGap i)) :=
  b.beli2009Lemma27_iii i hgap

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n)
    (hne : b.alphaValue i ≠ b.halfGapValue i) :
    IsOddRationalInteger (b.alphaValue i) :=
  b.beli2009Lemma27_iv i hne

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n)
    (hnot : ¬(Odd (b.orderGap i) ∧
      2 * (ramificationIndex K : Int) < b.orderGap i)) :
    IsRationalInteger (b.alphaValue i) :=
  b.beli2009Corollary28_i i hnot

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    (b.alphaValue i < 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i < 2 * (ramificationIndex K : Int)) ∧
    (b.alphaValue i = 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i = 2 * (ramificationIndex K : Int)) ∧
    (2 * (ramificationIndex K : ℚ) < b.alphaValue i ↔
      2 * (ramificationIndex K : Int) < b.orderGap i) :=
  b.beli2009Corollary28_ii i

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    (0 ≤ b.alphaValue i ∧
        b.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) ∧
        IsRationalInteger (b.alphaValue i)) ∨
      (2 * (ramificationIndex K : ℚ) < b.alphaValue i ∧
        IsRationalHalfInteger (b.alphaValue i)) :=
  b.beli2009Corollary28_iii i

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n)
    (hcase :
      2 * (ramificationIndex K : Int) ≤ b.orderGap i ∨
      b.orderGap i = -(2 * (ramificationIndex K : Int)) ∨
      b.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
      b.orderGap i = 2 * (ramificationIndex K : Int) - 2) :
    b.alphaValue i = b.halfGapValue i :=
  b.beli2009Corollary29_i i hcase

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n)
    (hodd : Odd (b.orderGap i)) :
    b.alphaValue i = min (b.halfGapValue i) (b.orderGap i : ℚ) :=
  b.beli2009Corollary29_ii i hodd

#print axioms Bong.BONG.GoodBONG.beli2009Lemma27_i
#print axioms Bong.BONG.GoodBONG.beli2009Lemma27_ii
#print axioms Bong.BONG.GoodBONG.beli2009Lemma27_iii
#print axioms Bong.BONG.GoodBONG.beli2009Lemma27_iv
#print axioms Bong.BONG.GoodBONG.beli2009Corollary28_i
#print axioms Bong.BONG.GoodBONG.beli2009Corollary28_ii
#print axioms Bong.BONG.GoodBONG.beli2009Corollary28_iii
#print axioms Bong.BONG.GoodBONG.beli2009Corollary29_i
#print axioms Bong.BONG.GoodBONG.beli2009Corollary29_ii

end BongTest.M110
