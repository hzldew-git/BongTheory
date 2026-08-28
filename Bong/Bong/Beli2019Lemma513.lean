/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019DefectConditionBranches

/-!
# Beli (2019), Lemma 5.13 and condition 2.1(ii)

Lemma 5.13 is a *reduced-range* statement: Section 5.2 first cuts the proof
at the distinguished Jordan block, and the complementary boundaries are
handled after swapping reverse duals.  Keeping that range hypothesis is
essential.  For example, in the proper unary shift the right endpoint has
`S_i = R_i + 1`, but the preceding cumulative sums differ by one; hence the
unrestricted version of Lemma 5.13(ii) would be false.

We therefore separate the literal reduced-range lemma from its global
duality-completed consequence.  The latter is exactly the common-prefix or
odd-prefix dichotomy consumed by condition 2.1(ii).  No representation
theorem is assumed.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The literal two conclusions of Lemma 5.13 on the range selected in
Section 5.2.  The predicate is kept abstract here because its concrete form
is expressed by the position of the distinguished almost-Jordan block. -/
structure Beli2019Lemma513LocalData
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop) : Prop where
  commonApproximation
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i) :
    b.orderSequence.entryOrZero (i.val - 1) ≠
        a.orderSequence.entryOrZero (i.val - 1) + 1 →
      ∃ X : Kˣ,
        a.IsPrefixApproximation i.val X ∧
          b.IsPrefixApproximation i.val X
  previousPrefixSum_eq
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i) :
    b.orderSequence.entryOrZero (i.val - 1) =
        a.orderSequence.entryOrZero (i.val - 1) + 1 →
      a.orderSequence.prefixSum (i.val - 1) =
        b.orderSequence.prefixSum (i.val - 1)

/-- The alpha estimates from the case analysis following Lemma 5.13, on
the same reduced range as the literal lemma. -/
structure Beli2019Lemma513LocalBounds
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop) : Prop where
  commonBound
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i) (X : Kˣ) :
    a.IsPrefixApproximation i.val X →
      b.IsPrefixApproximation i.val X →
        a.representationAlpha b i ≤
          min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val)
  oddBound
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i) :
    b.orderSequence.entryOrZero (i.val - 1) =
        a.orderSequence.entryOrZero (i.val - 1) + 1 →
      a.representationAlpha b i ≤ 0

namespace Beli2019Lemma513LocalData

/-- Lemma 5.13(ii), converted from equality of the preceding sums to the
odd cumulative-order equality used by the defect calculation. -/
theorem prefixSum_succ_of_current_succ
    {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (n + 1)}
    {InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop}
    (D : Beli2019Lemma513LocalData a b InReducedRange)
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    b.orderSequence.prefixSum i.val =
      a.orderSequence.prefixSum i.val + 1 := by
  have hprevious := D.previousPrefixSum_eq i hi hcurrent
  have hipos := i.pos
  rw [show i.val = (i.val - 1) + 1 by omega,
    b.orderSequence.prefixSum_succ, a.orderSequence.prefixSum_succ,
    ← hprevious, hcurrent]
  abel

end Beli2019Lemma513LocalData

/-- The reduced-range form of Lemma 5.13 and its local alpha estimates prove
condition 2.1(ii) at one covered boundary. -/
theorem representationDefect_at_of_lemma513Local
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (InReducedRange : RepresentationIndex (m + 1) (n + 1) → Prop)
    (D : Beli2019Lemma513LocalData a b InReducedRange)
    (bounds : Beli2019Lemma513LocalBounds a b InReducedRange)
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : InReducedRange i) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
  by_cases hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1
  · exact representationDefect_at_of_prefixSum_succ
      (alphaV := alphaV) (alphaW := alphaW) a b i
      (D.prefixSum_succ_of_current_succ i hi hcurrent)
      (bounds.oddBound i hi hcurrent)
  · obtain ⟨X, hX, hY⟩ := D.commonApproximation i hi hcurrent
    exact a.representationDefect_at_of_common_approximation b i X hX hY
      (bounds.commonBound i hi X hX hY)

/-- The global consequence of Lemma 5.13 after the Section 5.2 reverse-dual
reduction.  At a boundary on the far side of the distinguished block, the
common-approximation branch can occur even when `S_i = R_i + 1`; this is why
the global interface records the dichotomy itself rather than the invalid
unrestricted implication of Lemma 5.13(ii). -/
structure Beli2019Lemma513Data
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) : Prop where
  common_or_prefixSum_succ
    (i : RepresentationIndex (m + 1) (n + 1)) :
    (∃ X : Kˣ,
        a.IsPrefixApproximation i.val X ∧
          b.IsPrefixApproximation i.val X) ∨
      b.orderSequence.prefixSum i.val =
        a.orderSequence.prefixSum i.val + 1

/-- The alpha estimates supplied by the case analysis following Lemma 5.13.
They are separated from Lemma 5.13 itself because the paper proves them using
Lemmas 5.14--5.17 and the final Jordan-component cases. -/
structure Beli2019Lemma513Bounds
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) : Prop where
  commonBound
    (i : RepresentationIndex (m + 1) (n + 1)) (X : Kˣ) :
    a.IsPrefixApproximation i.val X →
      b.IsPrefixApproximation i.val X →
        a.representationAlpha b i ≤
          min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val)
  oddBound
    (i : RepresentationIndex (m + 1) (n + 1)) :
    b.orderSequence.prefixSum i.val =
        a.orderSequence.prefixSum i.val + 1 →
      a.representationAlpha b i ≤ 0

/-- Lemma 5.13 together with the bounds proved in the following Jordan case
analysis gives all of condition 2.1(ii). -/
theorem representationDefectCondition_of_lemma513
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (D : Beli2019Lemma513Data a b)
    (bounds : Beli2019Lemma513Bounds a b) :
    a.RepresentationDefectCondition b := by
  apply a.representationDefectCondition_of_common_or_odd_branches
    (alphaV := alphaV) (alphaW := alphaW) b
  intro i
  rcases D.common_or_prefixSum_succ i with ⟨X, hX, hY⟩ | hsum
  · exact Or.inl ⟨X, hX, hY, bounds.commonBound i X hX hY⟩
  · exact Or.inr ⟨hsum, bounds.oddBound i hsum⟩

end BONG.GoodBONG

end Bong
