/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIIRightNonoverlap

/-!
# Beli (2019), Lemma 7.9(iii): complete type-III right region

The center alpha is one in both the overlapping and nonoverlapping branches.
This excludes the first Lemma 2.18 alternative everywhere and the second
alternative before the terminal coordinate.  At the terminal coordinate the
overlapping branch has zero mixed defect, while the nonoverlapping branch is
excluded by the domination and parity argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The type-III target center alpha is one, independently of whether the
central source gap is the overlapping gap `1`. -/
theorem lemma79Central_typeIIIRight_centerAlpha_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
    b.alphaValue ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1 := by
  by_cases hoverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1
  · exact a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
      b D horder hdefect htotal hoverlap
  · exact (a.beli2019Lemma78_alphas_and_gap_local
      b D hfirst horder hdefect htotal hoverlap hinitial).2.1

set_option maxHeartbeats 10000000 in
-- The terminal nonoverlap proof contains the paper's capped-domination argument.
/-- Case 9: the second Lemma 2.18 alternative is impossible throughout the
type-III right difference region. -/
theorem lemma79Central_typeIIIRight_secondAlternative_impossible
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  have hcenterOne := lemma79Central_typeIIIRight_centerAlpha_eq_one
    a b D hfirst hab.orderCondition hab.defectCondition htotal hinitial
  by_cases hiLast : i.val = D.outer.last
  · by_cases hoverlap : a.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1
    · have hzero :=
        lemma79Central_typeIIIOverlapRight_terminal_currentDefect_eq_zero
          a b c D hfirst hoverlap hnorm i hright hiLast htrigger
      have hbeta :=
        a.lemma79Central_typeIIIRight_terminal_currentAlpha_eq_one_of_center
          b D hab.orderCondition hab.defectCondition htotal hcenterOne
            i hright hiLast
      rw [b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) i.lt_large, hzero, add_zero, hbeta] at hcurrent
      have hstrict : 2 * (ramificationIndex K : ℚ) < 1 := by
        exact_mod_cast hcurrent
      have heOne : (1 : ℚ) ≤ ramificationIndex K := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (ramificationIndex_pos (K := K)))
      linarith
    · exact a.lemma79Central_typeIIIRight_nonoverlap_terminal_second_not
        b c D hfirst hab.orderCondition hab.defectCondition htotal
          hoverlap hinitial hnorm i hright hiLast htrigger hcurrent
  · have hiBeforeLast : i.val < D.outer.last := by omega
    have hiNext : i.val + 1 < n + 2 := by
      have hbound := D.outer.lastDifference.bound
      omega
    have hsum := b.lemma79Central_secondAlternative_targetAlphaSum
      c i hiNext hcurrent
    let j : CentralRepresentationIndex (n + 2) (n + 2) :=
      ⟨i.val + 1, by
        have := i.one_lt
        omega, hiNext, by omega⟩
    have hnot := a.lemma79Central_typeIIIRight_not_leftAlphaSum
      b D hab.orderCondition hab.defectCondition htotal hcenterOne j (by
        simp only [j]
        omega) (by simp only [j]; omega)
    apply hnot
    simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega,
      show i.val + 1 - 1 = i.val by omega] using hsum

/-- Complete central witness family on the type-III right interval. -/
theorem lemma79CentralWitness_typeIIIRight
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (htrigger : b.centralAlphaTrigger c i) :
    Lemma79CentralWitness a b c i := by
  have hcenterOne := lemma79Central_typeIIIRight_centerAlpha_eq_one
    a b D hfirst hab.orderCondition hab.defectCondition htotal hinitial
  rcases b.beli2019Lemma218_target c hdefectBC i htrigger with
    hprevious | hcurrent
  · exfalso
    apply a.lemma79Central_typeIIIRight_not_leftAlphaSum
      b D hab.orderCondition hab.defectCondition htotal hcenterOne i
        hright hthroughLast
    have hcomparison : b.representationAlpha c i.previous ≤
        b.prefixAlphaCap (i.val - 1) := by
      calc
        b.representationAlpha c i.previous =
            b.representationAlphaValue c i.previous := by
          rw [b.coe_representationAlphaValue c i.previous]
        _ ≤ b.truncatedPrefixDefect c 1 (i.val - 1)
            (i.val - 1) := by
          simpa only [CentralRepresentationIndex.previous] using
            hdefectBC i.previous
        _ ≤ b.prefixAlphaCap (i.val - 1) :=
          b.truncatedPrefixDefect_le_leftCap c 1
            (i.val - 1) (i.val - 1)
    have hcap := hprevious.trans_le (add_le_add le_rfl hcomparison)
    rw [b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) i.lt_large,
      b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) (by
          have := i.lt_large
          omega)] at hcap
    have hsum : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ := by
      exact_mod_cast hcap
    rw [add_comm]
    exact hsum
  · exact False.elim
      (lemma79Central_typeIIIRight_secondAlternative_impossible
        a b c D hfirst hab htotal hinitial hnorm i hright hthroughLast
          htrigger hcurrent)

end BONG.GoodBONG

end Bong
