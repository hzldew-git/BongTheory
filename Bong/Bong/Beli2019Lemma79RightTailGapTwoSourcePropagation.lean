/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoFirstSourceComplete
import Bong.Bong.Beli2019Lemma79RightTailSourceDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 8: source-prefix propagation

Every adjacent source factor after the gap-two endpoint has defect strictly
larger than the central coefficient.  Sharp multiplication therefore keeps
the defect of each longer even source prefix equal to that coefficient.
This formalizes lines 5894--5897.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- One or more alternating source pairs can be appended to the first
gap-two source prefix without changing its defect. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect_succ
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (pairs : Nat)
    (hend : D.profile.last + 2 + 2 * pairs ≤ tailLast.val) :
    a.truncatedPrefixDefect a
        ((-1) ^ ((D.profile.last + 2 + 2 * (pairs + 1)) / 2)) 0
        (D.profile.last + 2 + 2 * (pairs + 1)) =
      ((((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
          b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) : Rat) +
        b.alphaValue ⟨D.profile.last, hlast⟩ : Rat) : WithTop Rat) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let first : Fin (n + 1) := ⟨D.profile.last, hlast⟩
  let start : Fin (n + 1) := ⟨D.profile.last + 2, by omega⟩
  let central : WithTop Rat :=
    ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
      b.alphaValue first : Rat) : WithTop Rat)
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.profile.lastDifference.after k
    · simp only [first] at hk
      omega
    · exact hkn
  have hfirstStart : first < start := by
    change first.val < start.val
    simp only [first, start]
    omega
  have hstartTail : start ≤ tailLast := by
    change start.val ≤ tailLast.val
    simp only [start]
    omega
  have hsegmentRaw := H.source_alternating_defect_gt
    hsuffix hstrictTail start hfirstStart hstartTail pairs (by
      simpa only [start] using hend)
  have horderTwo : b.order first.castSucc ≤ b.order start.castSucc := by
    change b.order (⟨D.profile.last, by omega⟩ : Fin (n + 2)) ≤
      b.order (⟨D.profile.last + 2, by omega⟩ : Fin (n + 2))
    simpa only [orderSequence] using
      b.orderSequence.twoStep D.profile.last (by omega)
  have hcentralLe : central ≤
      ((((b.order start.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat) := by
    apply WithTop.coe_le_coe.mpr
    have horderTwoQ : (b.order first.castSucc : Rat) ≤
        (b.order start.castSucc : Rat) := by
      exact_mod_cast horderTwo
    push_cast
    linarith
  have hsegment : central <
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 1))
        start.val (start.val + 2 * (pairs + 1)) :=
    hcentralLe.trans_lt (by simpa only [central] using hsegmentRaw)
  have hinitial :=
    beli2019Lemma79_typeI_caseEight_gapTwo_firstSourcePrefixDefect_complete
      a b D hfirst hgapTwo hlast horder hdefect H hfirstTail hstrictTail
  have hseparation :
      a.truncatedPrefixDefect a
          ((-1) ^ ((D.profile.last + 2) / 2)) 0 start.val <
        a.truncatedPrefixDefect a ((-1) ^ (pairs + 1))
          start.val (start.val + 2 * (pairs + 1)) := by
    rw [show a.truncatedPrefixDefect a
        ((-1) ^ ((D.profile.last + 2) / 2)) 0 start.val = central by
      simpa only [start, central, first] using hinitial]
    exact hsegment
  have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
    a a ((-1) ^ ((D.profile.last + 2) / 2))
      ((-1) ^ (pairs + 1)) 0 start.val
      (start.val + 2 * (pairs + 1)) hseparation
  have hsign :
      ((-1 : Kˣ) ^ ((D.profile.last + 2) / 2)) *
          ((-1) ^ (pairs + 1)) =
        (-1) ^ ((D.profile.last + 2 + 2 * (pairs + 1)) / 2) := by
    rcases I.last_even with ⟨d, hd⟩
    have hhalfStart : (D.profile.last + 2) / 2 = d + 1 := by omega
    have hhalfEnd :
        (D.profile.last + 2 + 2 * (pairs + 1)) / 2 =
          d + pairs + 2 := by omega
    rw [hhalfStart, hhalfEnd, ← pow_add]
    congr 1
    omega
  calc
    a.truncatedPrefixDefect a
        ((-1) ^ ((D.profile.last + 2 + 2 * (pairs + 1)) / 2)) 0
        (D.profile.last + 2 + 2 * (pairs + 1)) =
      a.truncatedPrefixDefect a
        (((-1) ^ ((D.profile.last + 2) / 2)) *
          ((-1) ^ (pairs + 1))) 0
        (start.val + 2 * (pairs + 1)) := by
          rw [hsign]
    _ = a.truncatedPrefixDefect a
        ((-1) ^ ((D.profile.last + 2) / 2)) 0 start.val := hsharp
    _ = _ := by simpa only [start, central, first] using hinitial

end BONG.GoodBONG

end Bong
