/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanCoordinates

/-!
# M112 Beli 2009/2010, Lemmas 2.13--2.16 and Corollary 2.17 smoke tests
-/

namespace BongTest.M112

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n N : Nat}

example (b : BONG.GoodBONG q L N)
    (C : b.JordanBlockCoordinates) (j : Nat)
    (hstart : C.start <= j) (hstop : j < C.stop) : True := by
  have _ := C.beli2009Lemma213_i j hstart hstop
  have _ := C.beli2009Lemma213_ii j hstart hstop
  trivial

example (b : BONG.GoodBONG q L N)
    (C : b.JordanBlockCoordinates) (j : Nat)
    (hstart : C.start <= j) (hnext : j + 1 < C.stop) : True := by
  have _ := C.adjacent_order_sum j hstart hnext
  trivial

section JordanBlock

variable [Beli2009JordanBlockLaws.{u, v} K]

example (b : BONG.GoodBONG q L N)
    (C : b.JordanBlockLatticeData) : True := by
  have _ := C.beli2009Lemma213_iii
  trivial

end JordanBlock

section Weight

variable [Beli2009WeightIdealData.{u, v} K]
  [Beli2009JordanWeightOrderLaws.{u, v} K]

example (b : BONG.GoodBONG q L 1) : True := by
  have _ := b.beli2009Lemma214_unary
  trivial

example (b : BONG.GoodBONG q L (n + 2))
    (hdescending : b.order 1 <= b.order 0) : True := by
  have _ := b.beli2009Lemma214
  have _ := b.beli2009Lemma214_of_firstBlock_not_unary hdescending
  trivial

end Weight

section Unary

variable [Beli2009UnaryJordanIdealLaws.{u} K]

example (U : Lattice.UnaryJordanIdealData K) : True := by
  have _ := U.beli2009Lemma215
  have _ := U.beli2009Lemma215_order
  trivial

example (U : Lattice.UnaryJordanIdealData K)
    (previousAlpha nextAlpha : Option Rat)
    (hprevious : previousAlpha.map
        (fun x => min x (ramificationIndex K : Rat)) =
      U.previousFundamental.map
        (fun I => min (I.order : Rat) (ramificationIndex K : Rat)))
    (hnext : nextAlpha.map
        (fun x => min x (ramificationIndex K : Rat)) =
      U.nextFundamental.map
        (fun I => min (I.order : Rat) (ramificationIndex K : Rat))) : True := by
  have _ := Lattice.beli2009Corollary217_ii
    U previousAlpha nextAlpha hprevious hnext
  trivial

end Unary

section InternalAlpha

variable [Beli2009JordanAlphaLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 1))
    (D : b.InternalJordanAlphaData) (ak : Units K)
    (hak : ordUnit K ak = b.order D.leftIndex) : True := by
  have _ := D.beli2009Lemma216_i
  have _ := D.beli2009Corollary217_i ak hak
  trivial

end InternalAlpha

section BoundaryAlpha

variable [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]
  [Beli2009JordanAlphaLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 1))
    (D : b.BoundaryJordanAlphaData) : True := by
  have _ := D.beli2009Lemma216_ii
  have _ := D.fundamentalOrder_min_e_eq_alpha_min_e
  trivial

end BoundaryAlpha

#print axioms Bong.BONG.GoodBONG.JordanBlockCoordinates.beli2009Lemma213_i
#print axioms Bong.BONG.GoodBONG.JordanBlockCoordinates.beli2009Lemma213_ii
#print axioms Bong.BONG.GoodBONG.JordanBlockCoordinates.adjacent_order_sum
#print axioms Bong.BONG.GoodBONG.JordanBlockLatticeData.beli2009Lemma213_iii
#print axioms Bong.BONG.GoodBONG.beli2009Lemma214_unary
#print axioms Bong.BONG.GoodBONG.beli2009Lemma214
#print axioms Bong.BONG.GoodBONG.beli2009Lemma214_of_firstBlock_not_unary
#print axioms Bong.Lattice.UnaryJordanIdealData.beli2009Lemma215
#print axioms Bong.Lattice.UnaryJordanIdealData.beli2009Lemma215_order
#print axioms Bong.BONG.GoodBONG.InternalJordanAlphaData.beli2009Lemma216_i
#print axioms Bong.BONG.GoodBONG.BoundaryJordanAlphaData.beli2009Lemma216_ii
#print axioms Bong.BONG.GoodBONG.InternalJordanAlphaData.beli2009Corollary217_i
#print axioms Bong.Lattice.neighboringMinimum_congr
#print axioms Bong.Lattice.beli2009Corollary217_ii

end BongTest.M112
