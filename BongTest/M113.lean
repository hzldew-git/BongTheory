/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ClassificationPropagation

/-!
# M113 Beli 2009/2010, Lemmas 3.2--3.4 smoke tests
-/

namespace BongTest.M113

open Bong Bong.Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {s : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n N t : Nat}

example (a : BONG V q L N) (i : Nat) (hi : i < N) : True := by
  have _ := a.prefixProduct_succ i hi
  trivial

example (a : BONG.GoodBONG q L (N + 1))
    (b : BONG.GoodBONG s M (N + 1))
    (i : Nat) (hi : i + 1 < N + 1) : True := by
  have _ := a.comparisonPrefixDefect_add_two b i hi
  have _ := a.comparisonPrefixDefect_reverse_add_two b i hi
  trivial

section Lemma32

variable [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AmbientDeterminantLaws.{u, v, w} K]

example {l r : Nat} (ambient : q.IsIsometric s)
    (a : BONG.GoodBONG q L ((l + r + 1) + 2))
    (b : BONG.GoodBONG s M ((l + r + 1) + 2))
    (horders : a.SameOrders b) (halphas : a.SameAlphas b)
    (houter : a.order ⟨l, by omega⟩ = a.order ⟨l + 2, by omega⟩)
    (hleft : l = 0 ∨ ∃ hl : 0 < l,
      (a.alphaValue ⟨l - 1, by omega⟩ : WithTop ℚ) <=
        a.comparisonPrefixDefect b l)
    (hright : r = 0 ∨ ∃ hr : 0 < r,
      (a.alphaValue ⟨l + 2, by omega⟩ : WithTop ℚ) <=
        a.comparisonPrefixDefect b (l + 3)) : True := by
  have _ := BONG.GoodBONG.beli2009Lemma32
    ambient a b horders halphas houter hleft hright
  trivial

end Lemma32

section Lemma33

variable {a : BONG.GoodBONG q L (N + 1)}
  {b : BONG.GoodBONG s M (N + 1)}
  (J : BONG.GoodBONG.JordanClassificationReduction a b t)
  [BONG.GoodBONG.Beli2009JordanReductionLaws J]

example :
    a.PrefixDefectBounds b ↔
      (∀ k, J.componentCongruence k) ∧
        (∀ k, J.boundaryCongruence k) :=
  J.beli2009Lemma33

end Lemma33

section Lemma34

variable [Beli2006AlphaLaws.{u, v} K]

example {l r : Nat} (a : BONG.GoodBONG q L ((l + r + 1) + 2))
    (houter : a.order ⟨l, by omega⟩ = a.order ⟨l + 2, by omega⟩) :
    True := by
  have _ := a.beli2009Lemma34 houter
  trivial

end Lemma34

#print axioms Bong.BONG.prefixProduct_succ
#print axioms Bong.BONG.GoodBONG.comparisonPrefixDefect_add_two
#print axioms Bong.BONG.GoodBONG.comparisonPrefixDefect_reverse_add_two
#print axioms Bong.BONG.GoodBONG.beli2009Lemma32
#print axioms Bong.BONG.GoodBONG.JordanClassificationReduction.beli2009Lemma33
#print axioms Bong.BONG.GoodBONG.beli2009Lemma34

end BongTest.M113
