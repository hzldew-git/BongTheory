/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009QuadraticRepresentation

/-!
# M114 Beli 2009/2010, Lemmas 3.5--3.7 smoke tests
-/

namespace BongTest.M114

open Bong Bong.Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

section Lemma35

variable [FiniteDimensional K V] [FiniteDimensional K W]
  [Beli2009QuadraticRepresentationLaws.{u, v, w} K]

example (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (hdim : Module.finrank K W + 1 = Module.finrank K V) : True := by
  have _ := QuadraticSpace.beli2009Lemma35_i q r hdim
  trivial

example (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W) : True := by
  have _ := QuadraticSpace.beli2009Lemma35_ii
    q r detQ detR a detQ_spec detR_spec hdim
  trivial

example (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a b : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W)
    (hhilbert : hilbertSymbol K (a * b) (detQ * detR) = 1) : True := by
  have _ := QuadraticSpace.beli2009Lemma35_iii
    q r detQ detR a b detQ_spec detR_spec hdim hhilbert
  trivial

variable [HilbertSymbolLaws K]

example (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a b : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W)
    (hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K (a * b) + quadraticDefect K (detQ * detR)) : True := by
  have _ := QuadraticSpace.beli2009Lemma35_iii_of_defect
    q r detQ detR a b detQ_spec detR_spec hdim hdefect
  trivial

end Lemma35

section Lemma36And37

variable [FiniteDimensional K V] [FiniteDimensional K W]
  [repVW : Beli2009QuadraticRepresentationLaws.{u, v, w} K]
  [repWV : Beli2009QuadraticRepresentationLaws.{u, w, v} K]
  [HilbertSymbolLaws K]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}

example (D : Beli2009RepresentationSwitchData q r) : True := by
  have _ := Beli2009RepresentationSwitchData.beli2009Lemma36_i
    (repVW := repVW) (repWV := repWV) D
  have _ := Beli2009RepresentationSwitchData.beli2009Lemma36_ii
    (repVW := repVW) (repWV := repWV) D
  trivial

example (D : Beli2009RepresentationSwitchData q r)
    (J : Beli2009PrefixRepresentationBridge D)
    [Beli2009PrefixRepresentationBridgeLaws J] : True := by
  have _ := Beli2009PrefixRepresentationBridge.beli2009Lemma37_i
    (repVW := repVW) (repWV := repWV) J
  have _ := Beli2009PrefixRepresentationBridge.beli2009Lemma37_ii
    (repVW := repVW) (repWV := repWV) J
  trivial

end Lemma36And37

#print axioms Bong.QuadraticSpace.beli2009Lemma35_i
#print axioms Bong.QuadraticSpace.beli2009Lemma35_ii
#print axioms Bong.QuadraticSpace.beli2009Lemma35_iii
#print axioms Bong.QuadraticSpace.beli2009Lemma35_iii_of_defect
#print axioms Bong.Beli2009RepresentationSwitchData.beli2009Lemma36_i
#print axioms Bong.Beli2009RepresentationSwitchData.beli2009Lemma36_ii
#print axioms Bong.Beli2009PrefixRepresentationBridge.beli2009Lemma37_i
#print axioms Bong.Beli2009PrefixRepresentationBridge.beli2009Lemma37_ii

end BongTest.M114
