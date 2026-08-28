/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIBeforeLast
import Bong.Bong.Beli2019Lemma79OrderTypeIFullRankTerminal
import Bong.Bong.Beli2019Lemma79OrderTypeITerminal
import Bong.Bong.Beli2019Lemma79OrderTypeITerminalSwitch

/-!
# Beli (2019), Lemma 7.9(i): complete type-I branch

The nonterminal coordinate theorem, the two proper-suffix terminal branches,
and the full-rank endpoint together cover every coordinate through the last
difference.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) at every altered coordinate in the type-I branch of
Lemma 7.9. -/
theorem beli2019Lemma79_i_typeI
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have _ := D.anchor_bound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hlast : k ≤ D.profile.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hstrict : k < D.profile.last
  · exact beli2019Lemma79_i_typeI_beforeLast
      a b c D C hfirst horderAB horderAC hdefectAB hdefectAC hinitial
        hnorm k hk hstrict
  · have hkLast : k = D.profile.last := by omega
    subst k
    by_cases hnext : D.profile.last + 1 < n + 2
    · by_cases hright : C.rightSwitch < D.profile.last
      · exact beli2019Lemma79_i_typeI_terminal
          a b c D C hfirst hright hdefectAB hdefectAC hinitial hnorm hnext
      · have hrightEq : C.rightSwitch = D.profile.last :=
          Nat.le_antisymm C.right_le_last (Nat.le_of_not_gt hright)
        simpa only [hrightEq] using
          beli2019Lemma79_i_typeI_terminalSwitch
            a b c D C hfirst hrightEq hdefectAB hdefectAC hinitial hnorm
              (by simpa only [hrightEq] using hnext)
    · left
      apply beli2019Lemma79_i_typeI_fullRankTerminal
        a b c D C hfirst hnorm
      omega

end BONG.GoodBONG

end Bong
