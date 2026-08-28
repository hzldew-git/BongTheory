/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainConditions
import Bong.Bong.TruthParity

/-!
# Beli (2019), the parity mechanism in Lemma 1.5

Lemma 1.5 uses the fact that quadratic spaces of fixed dimension and
determinant have at most two isometry classes.  This file formalizes the
entire two-class cycle argument independently of the later diagonal-space
identifications used in its three applications.
-/

namespace Bong

universe u

/-- A presentation of an equivalence relation with at most two classes. -/
structure TwoClassPresentation (X : Type u) (relation : X → X → Prop) where
  color : X → Bool
  relation_iff_color (x y : X) : relation x y ↔ color x = color y

namespace TwoClassPresentation

variable {X : Type u} {relation : X → X → Prop}

/-- Four edges around a cycle in a two-class space have even truth parity. -/
theorem cycle_even (P : TwoClassPresentation X relation)
    (x₁ x₂ x₃ x₄ : X) :
    EvenTruthParity
      (relation x₁ x₂) (relation x₂ x₃)
      (relation x₁ x₄) (relation x₃ x₄) := by
  rw [P.relation_iff_color, P.relation_iff_color,
    P.relation_iff_color, P.relation_iff_color]
  unfold EvenTruthParity
  generalize P.color x₁ = c₁
  generalize P.color x₂ = c₂
  generalize P.color x₃ = c₃
  generalize P.color x₄ = c₄
  cases c₁ <;> cases c₂ <;> cases c₃ <;> cases c₄ <;> decide

end TwoClassPresentation

/-- The abstract four-space diagram used in each of the three cases of
Lemma 1.5.  Later modules instantiate the four propositions with prefix
representations and the indicated Hilbert-symbol equality. -/
structure Beli2019RepresentationParityDiagram where
  Space : Type u
  relation : Space → Space → Prop
  twoClass : TwoClassPresentation Space relation
  V₁ : Space
  V₂ : Space
  V₃ : Space
  V₄ : Space
  first : Prop
  second : Prop
  third : Prop
  fourth : Prop
  first_iff : first ↔ relation V₁ V₂
  second_iff : second ↔ relation V₂ V₃
  third_iff : third ↔ relation V₁ V₄
  fourth_iff : fourth ↔ relation V₃ V₄

namespace Beli2019RepresentationParityDiagram

/-- Beli (2019), Lemma 1.5, once one of its displayed four-space diagrams
has been constructed. -/
theorem evenTruthParity (D : Beli2019RepresentationParityDiagram) :
    EvenTruthParity D.first D.second D.third D.fourth := by
  rw [D.first_iff, D.second_iff, D.third_iff, D.fourth_iff]
  exact D.twoClass.cycle_even D.V₁ D.V₂ D.V₃ D.V₄

/-- The paper's first stated consequence of Lemma 1.5. -/
theorem remaining_iff_of_first_second
    (D : Beli2019RepresentationParityDiagram)
    (hfirst : D.first) (hsecond : D.second) : D.third ↔ D.fourth :=
  D.evenTruthParity.remaining_iff_of_first_second hfirst hsecond

/-- The paper's second stated consequence of Lemma 1.5. -/
theorem fourth_of_first_three
    (D : Beli2019RepresentationParityDiagram)
    (hfirst : D.first) (hsecond : D.second) (hthird : D.third) :
    D.fourth :=
  D.evenTruthParity.all_triple_consequences.1 hfirst hsecond hthird

end Beli2019RepresentationParityDiagram

end Bong
