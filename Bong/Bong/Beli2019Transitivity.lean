/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ApproximationInvariants
import Bong.Bong.Beli2019OrderSequence

/-!
# Beli (2019), Section 4: transitivity skeleton

This file proves the parts of transitivity that are independent of the long
essential-index analysis.  Condition (i) is inherited from the order on
`BeliOrderSequence`; condition (ii) follows from the three-lattice defect
domination theorem once the local bounds supplied by Section 4's key lemma
are available.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {m n k : Nat}

/-- Condition 2.1(i) is transitive, including the rank inequalities. -/
theorem representationOrderCondition_trans
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (k + 1))
    (hnm : n ≤ m) (hkn : k ≤ n)
    (hab : a.RepresentationOrderCondition b hnm)
    (hbc : b.RepresentationOrderCondition c hkn) :
    a.RepresentationOrderCondition c (hkn.trans hnm) := by
  rw [a.representationOrderCondition_iff b hnm] at hab
  rw [b.representationOrderCondition_iff c hkn] at hbc
  rw [a.representationOrderCondition_iff c (hkn.trans hnm)]
  exact BeliOrderLE.trans hab hbc

/-- At one same-rank boundary, the two local bounds from the key lemma turn
the two source defect conditions into the target defect condition. -/
theorem representationDefectAt_trans_of_bounds
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hab : a.RepresentationDefectCondition b)
    (hbc : b.RepresentationDefectCondition c)
    (hca : a.representationAlpha c i ≤ a.representationAlpha b i)
    (hcb : a.representationAlpha c i ≤ b.representationAlpha c i) :
    (a.representationAlphaValue c i : WithTop ℚ) ≤
      a.truncatedPrefixDefect c 1 i.val i.val := by
  have habAt : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    simpa only [← a.coe_representationAlphaValue b i] using hab i
  have hbcAt : b.representationAlpha c i ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
    simpa only [← b.coe_representationAlphaValue c i] using hbc i
  rw [a.coe_representationAlphaValue c i]
  calc
    a.representationAlpha c i ≤
        min (a.representationAlpha b i)
          (b.representationAlpha c i) := le_min hca hcb
    _ ≤ min (a.truncatedPrefixDefect b 1 i.val i.val)
        (b.truncatedPrefixDefect c 1 i.val i.val) :=
      min_le_min habAt hbcAt
    _ ≤ a.truncatedPrefixDefect c (1 * 1) i.val i.val :=
      a.truncatedPrefixDefect_domination b c 1 1
        i.val i.val i.val
    _ = a.truncatedPrefixDefect c 1 i.val i.val := by
      rw [one_mul]

/-- Section 4's direct branch of condition 2.1(ii), simultaneously at all
same-rank boundaries. -/
theorem representationDefectCondition_trans_of_bounds
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationDefectCondition b)
    (hbc : b.RepresentationDefectCondition c)
    (hkey : ∀ i : RepresentationIndex (n + 1) (n + 1),
      a.representationAlpha c i ≤ a.representationAlpha b i ∧
        a.representationAlpha c i ≤ b.representationAlpha c i) :
    a.RepresentationDefectCondition c := by
  intro i
  exact a.representationDefectAt_trans_of_bounds b c i hab hbc
    (hkey i).1 (hkey i).2

end BONG.GoodBONG

end Bong
