/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIAlphaBound

/-!
# Beli (2019), Lemma 7.9(ii): the type-II core

This file assembles case 5 of the proof.  If the current comparison order
lies above the type-II plateau, the primary candidate is nonpositive.  In
the remaining branch the two prefix sums have equal parity, both alpha caps
are at least one, and the comparison alpha is at most one.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 5: every coordinate in the constant type-II core
satisfies the representation-defect inequality. -/
theorem beli2019Lemma79_ii_typeII_core
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : D.outer.transition.lastZero < i.val)
    (hright : i.val + 1 < D.outer.transition.firstTwo) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hiPrevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have htargetMiddle (j : Nat)
      (hleftJ : D.outer.transition.lastZero < j)
      (hrightJ : j + 1 < D.outer.transition.firstTwo) :
      b.orderSequence.entryOrZero j = T := by
    have hcommon := D.outer.transition.middle j hleftJ hrightJ
    have hsource := D.middle j hleftJ hrightJ
    exact hcommon.symm.trans (by simpa only [T] using hsource)
  have hbPrevious : b.orderSequence.entryOrZero (i.val - 1) = T := by
    by_cases heq : i.val - 1 = D.outer.transition.lastZero
    · rw [heq]
    · apply htargetMiddle (i.val - 1)
      · have := i.pos
        omega
      · omega
  have hbCurrent : b.orderSequence.entryOrZero i.val = T :=
    htargetMiddle i.val hleft hright
  have hbc := a.beli2019Lemma79_i_typeII_orderCondition
    b c D hfirst hac hdefectAC hnorm
  have hnextAlpha := a.beli2019Lemma69_i_typeII_targetCore_eq_one
    b D hfirst i.val hleft.le (by omega)
  by_cases hcLe : c.orderSequence.entryOrZero (i.val - 1) ≤ T
  · have heven := a.beli2019Lemma79_typeII_core_prefix_even
      b c D hfirst hnorm i (by omega) (by simpa only [T] using hcLe)
    have hAlpha := a.beli2019Lemma79_typeII_core_alpha_le_one
      b c D hfirst hbc i hleft hright (by simpa only [T] using hcLe)
        heven
    have hpreviousAlpha :=
      a.beli2019Lemma69_i_typeII_targetMiddle_eq_one
        b D hfirst (i.val - 1) (by omega) (by
          have hindex : i.val - 1 + 2 = i.val + 1 := by omega
          rw [hindex]
          exact hright)
    have hbAlpha : (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩ := by
      have hpreviousAlpha' : b.alphaValue ⟨i.val - 1, by
          have := i.pos
          have := i.lt_large
          omega⟩ = 1 := by
        simpa using hpreviousAlpha
      rw [hpreviousAlpha']
    have hcAlpha := b.one_le_previousAlpha_of_constant_pair
      c hbc i T hbPrevious hbCurrent (by simpa only [T] using hcLe)
    exact b.lemma79_ii_of_alpha_le_one_and_even c i hAlpha
      hbAlpha hcAlpha heven
  · have hcStrict : T < c.orderSequence.entryOrZero (i.val - 1) :=
      lt_of_not_ge hcLe
    have hprimary := b.representationAlphaValue_le_primary_nextAlpha
      c i (by
        have hbound := D.outer.transition.firstTwo_le_rank
        omega)
    have hprimary' : b.representationAlphaValue c i ≤
        ((b.orderSequence.entryOrZero i.val -
          c.orderSequence.entryOrZero (i.val - 1) : Int) : ℚ) +
          b.alphaValue ⟨i.val, by
            have hbound := D.outer.transition.firstTwo_le_rank
            omega⟩ := by
      simpa only [
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.lt_large,
        BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
        orderSequence_at] using hprimary
    rw [hbCurrent, hnextAlpha] at hprimary'
    have hnonpositive : b.representationAlphaValue c i ≤ 0 := by
      have hshiftInt : T -
          c.orderSequence.entryOrZero (i.val - 1) + 1 ≤ 0 := by omega
      have hshiftQ :
          ((T - c.orderSequence.entryOrZero (i.val - 1) : Int) : ℚ) +
            1 ≤ 0 := by
        exact_mod_cast hshiftInt
      exact hprimary'.trans hshiftQ
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤ 0 := by
        exact_mod_cast hnonpositive
      _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
        b.truncatedPrefixDefect_nonneg c 1 i.val i.val

end BONG.GoodBONG

end Bong
