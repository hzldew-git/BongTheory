/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96TailRepresentation
import Bong.Bong.Beli2019Lemma213Nonessential
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 9.6: projected-tail defect condition

Lines 9629--9683 of the revised-v2 proof compare the representation
invariants of the original pair with those of the projected pair.  The first
tail boundary has `A'_2 < 0`; at every later essential boundary one has
`A'_i = A_i`, while the new capped comparison defect dominates the old one.
If neither adjacent endpoint is essential, Lemma 2.13 proves condition (ii)
directly.

This file turns exactly those pointwise arithmetic conclusions into the full
condition 2.1(ii).  It contains no representation conclusion and introduces
no typeclass or theorem-level law.
-/

namespace Bong

open Dyadic

universe u v w x

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type x} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {P : Lattice K U}
  {N : Nat}

/-- The remaining pointwise comparison statements in lines 9668--9677.
The central-trigger field is the same calculation in the form consumed by
condition (iii); it will be derived from the exact `A_i` identities in the
next arithmetic module. -/
structure Beli2019Lemma96TailComparisonProfile
    (a : GoodBONG q L (N + 4))
    (b : GoodBONG r M (N + 4))
    (c : GoodBONG s P (N + 3)) : Prop where
  firstAlpha_lt_zero : ∀ i : RepresentationIndex (N + 3) (N + 3),
    i.val = 1 → c.representationAlpha b.tail i < 0
  essentialAlpha_eq : ∀ i : RepresentationIndex (N + 3) (N + 3),
    2 ≤ i.val →
    (c.IsCurrentEssential b.tail i ∨ c.IsNextEssential b.tail i) →
    c.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift
  comparisonDefect_le : ∀ i : RepresentationIndex (N + 3) (N + 3),
    2 ≤ i.val →
    a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) ≤
      c.truncatedPrefixDefect b.tail 1 i.val i.val
  centralTrigger : ∀ i : CentralRepresentationIndex (N + 3) (N + 3),
    c.centralAlphaTrigger b.tail i →
      a.centralAlphaTrigger b i.tailShift

namespace Beli2019Lemma96TailComparisonProfile

variable {a : GoodBONG q L (N + 4)}
  {b : GoodBONG r M (N + 4)}
  {c : GoodBONG s P (N + 3)}

/-- The comparison profile and the original condition (ii) imply condition
(ii) for the exceptional projected pair. -/
theorem representationDefectCondition
    [cLaws : Beli2006AlphaLaws.{u, x} K]
    [bLaws : Beli2006AlphaLaws.{u, w} K]
    (D : Beli2019Lemma96TailComparisonProfile a b c)
    (hdefect : a.RepresentationDefectCondition b) :
    c.RepresentationDefectCondition b.tail := by
  rw [c.representationDefectCondition_iff_forall_at b.tail]
  intro i
  by_cases hiOne : i.val = 1
  · unfold RepresentationDefectAt
    exact (D.firstAlpha_lt_zero i hiOne).le.trans
      (c.truncatedPrefixDefect_nonneg
        (alphaV := cLaws) (alphaW := bLaws)
        b.tail 1 i.val i.val)
  · have hiTwo : 2 ≤ i.val := by
      have := i.pos
      omega
    by_cases hcurrent : c.IsCurrentEssential b.tail i
    · have horiginal := hdefect i.tailShift
      have horiginal' :
          a.representationAlpha b i.tailShift ≤
            a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) := by
        simpa only [a.coe_representationAlphaValue b i.tailShift,
          RepresentationIndex.tailShift_val] using horiginal
      unfold RepresentationDefectAt
      calc
        c.representationAlpha b.tail i =
            a.representationAlpha b i.tailShift :=
          D.essentialAlpha_eq i hiTwo (Or.inl hcurrent)
        _ ≤ a.truncatedPrefixDefect b 1
              (i.val + 1) (i.val + 1) := horiginal'
        _ ≤ c.truncatedPrefixDefect b.tail 1 i.val i.val :=
          D.comparisonDefect_le i hiTwo
    · by_cases hnext : c.IsNextEssential b.tail i
      · have horiginal := hdefect i.tailShift
        have horiginal' :
            a.representationAlpha b i.tailShift ≤
              a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) := by
          simpa only [a.coe_representationAlphaValue b i.tailShift,
            RepresentationIndex.tailShift_val] using horiginal
        unfold RepresentationDefectAt
        calc
          c.representationAlpha b.tail i =
              a.representationAlpha b i.tailShift :=
            D.essentialAlpha_eq i hiTwo (Or.inr hnext)
          _ ≤ a.truncatedPrefixDefect b 1
                (i.val + 1) (i.val + 1) := horiginal'
          _ ≤ c.truncatedPrefixDefect b.tail 1 i.val i.val :=
            D.comparisonDefect_le i hiTwo
      · exact c.representationDefectAt_of_not_essential
          (sourceLaws := cLaws) (targetLaws := bLaws)
          b.tail i hcurrent hnext

end Beli2019Lemma96TailComparisonProfile

end BONG.GoodBONG

end Bong
