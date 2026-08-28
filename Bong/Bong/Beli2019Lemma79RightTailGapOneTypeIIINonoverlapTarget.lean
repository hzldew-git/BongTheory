/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapSource
import Bong.Bong.Beli2019Remark616

/-!
# Beli (2019), Lemma 7.9(ii), case 8: type-III target prefixes

For every even prefix whose final alpha lies in the strict type-III tail,
the first tail beta and two-step order monotonicity put the target alpha cap
above the central defect.  Remark 6.16 therefore transfers the exact source
prefix defect to the target prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Every even target prefix from the end of a nonoverlapping type-III
profile through the strict beta tail has the central Lemma 7.8 defect. -/
theorem beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hlast : D.outer.last < n + 1)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (length : Nat) (hstart : D.outer.last + 1 ≤ length)
    (hend : length ≤ tailLast.val + 1) (heven : Even length) :
    b.truncatedPrefixDefect b ((-1) ^ (length / 2)) 0 length =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  let first : Fin (n + 1) := ⟨D.outer.last, hlast⟩
  have hbound : length < n + 2 := by
    have htailBound := tailLast.isLt
    omega
  let current : Fin (n + 1) := ⟨length - 1, by omega⟩
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨length, by omega, hbound, by omega⟩
  let central : WithTop Rat :=
    (((b.order ⟨D.outer.transition.lastZero, by
          have htransition := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at htransition
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have htransition := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at htransition
          omega⟩ : Int) : Rat) : WithTop Rat)
  have hsource :
      a.truncatedPrefixDefect a ((-1) ^ (length / 2)) 0 length =
        central := by
    simpa only [central] using
      beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect
        a b D hfirst hdefect hnotOverlap hinitial hlast H hstrictTail
          length hstart hend heven
  have hfirstCurrent : first ≤ current := by
    change first.val ≤ current.val
    simp only [first, current]
    omega
  have hcurrentTail : current ≤ tailLast := by
    change current.val ≤ tailLast.val
    simp only [current]
    omega
  have hfirstTail : first ≤ tailLast := hfirstCurrent.trans hcurrentTail
  have hcentralLeQ :=
    beli2019Lemma79_typeIII_nonoverlap_central_le_firstBeta
      a b D hfirst hdefect hnotOverlap hlast H hfirstTail hstrictTail
  have hcentralLeFirst :
      (b.order ⟨D.outer.transition.lastZero, by
            have htransition := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at htransition
            omega⟩ : Rat) -
          (a.order ⟨D.outer.transition.lastZero + 1, by
            have htransition := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at htransition
            omega⟩ : Rat) ≤
        b.alphaValue first := by
    push_cast at hcentralLeQ
    simpa only [first] using hcentralLeQ
  have hvalue := H.value_eq current hfirstCurrent hcurrentTail
  have hfirstSuccEven :=
    beli2019Lemma79_typeIII_last_succ_even a b D hfirst
  have hevenGap : Even (length - (D.outer.last + 1)) := by
    rcases hfirstSuccEven with ⟨d, hd⟩
    rcases heven with ⟨e, he⟩
    refine ⟨e - d, ?_⟩
    omega
  have horderEntry := b.orderSequence.entryOrZero_le_of_evenGap
    (D.outer.last + 1) length hstart hbound hevenGap
  have horderMonotone : b.order first.succ ≤ b.order current.succ := by
    rw [b.orderSequence_entryOrZero_eq_order
        (⟨D.outer.last + 1, by omega⟩ : Fin (n + 2)),
      b.orderSequence_entryOrZero_eq_order
        (⟨length, hbound⟩ : Fin (n + 2))] at horderEntry
    have hfirstIndex :
        (⟨D.outer.last + 1, by omega⟩ : Fin (n + 2)) =
          first.succ := by
      apply Fin.ext
      rfl
    have hcurrentIndex :
        (⟨length, hbound⟩ : Fin (n + 2)) = current.succ := by
      apply Fin.ext
      simp only [current, Fin.val_succ]
      omega
    simpa only [hfirstIndex, hcurrentIndex] using horderEntry
  have hbetaQ :
      ((b.order ⟨D.outer.transition.lastZero, by
            have htransition := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at htransition
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have htransition := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at htransition
            omega⟩ : Int) : Rat) ≤
        b.alphaValue current := by
    have horderQ : (b.order first.succ : Rat) ≤
        (b.order current.succ : Rat) := by
      exact_mod_cast horderMonotone
    push_cast at hvalue ⊢
    exact hcentralLeFirst.trans (by linarith)
  have hbeta : central ≤ (b.alphaValue current : WithTop Rat) := by
    exact WithTop.coe_le_coe.mpr (by simpa only [central] using hbetaQ)
  have hsuffix : ∀ k, idx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · simp only [idx] at hk
      omega
    · exact hkn
  have hAlphaRaw := a.beli2019Lemma63_sameRank_right_value
    b hdefect idx hsuffix
  have hAlpha : a.representationAlphaValue b idx =
      b.alphaValue current := by
    simpa only [idx, current] using hAlphaRaw
  have hformula := beli2019Remark616_rightPrefix
    a b hdefect idx hAlpha ((-1) ^ (length / 2))
  calc
    b.truncatedPrefixDefect b ((-1) ^ (length / 2)) 0 length =
      min (a.truncatedPrefixDefect a ((-1) ^ (length / 2)) 0 length)
        (b.alphaValue current : WithTop Rat) := by
          simpa only [idx, current] using hformula
    _ = a.truncatedPrefixDefect a ((-1) ^ (length / 2)) 0 length := by
      rw [min_eq_left]
      rw [hsource]
      exact hbeta
    _ = _ := by simpa only [hsource, central]

/-- If the strict tail ends an odd distance from the type-III boundary,
the next even target prefix still has the central defect.  This is the
prefix used in the odd-index branch of lines 5840--5849. -/
theorem beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect_endpoint
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hlast : D.outer.last < n + 1)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.outer.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (hnext : tailLast.val + 1 < n + 1)
    (hparity : Odd (tailLast.val - D.outer.last)) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((tailLast.val + 2) / 2)) 0 (tailLast.val + 2) =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  let first : Fin (n + 1) := ⟨D.outer.last, hlast⟩
  let current : Fin (n + 1) := ⟨tailLast.val + 1, hnext⟩
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨tailLast.val + 2, by omega, by omega, by omega⟩
  let central : WithTop Rat :=
    (((b.order ⟨D.outer.transition.lastZero, by
          have htransition := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at htransition
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have htransition := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at htransition
          omega⟩ : Int) : Rat) : WithTop Rat)
  rcases hparity with ⟨pairs, hpairs⟩
  have htailEq :
      tailLast.val = D.outer.last + 2 * pairs + 1 := by
    have hle : D.outer.last ≤ tailLast.val := by
      change first.val ≤ tailLast.val at hfirstTail
      simpa only [first] using hfirstTail
    omega
  have hsourceRaw :=
    beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect_succ
      a b D hfirst hdefect hnotOverlap hinitial hlast H hstrictTail
        pairs (by omega)
  have hsource :
      a.truncatedPrefixDefect a
          ((-1) ^ ((tailLast.val + 2) / 2)) 0
          (tailLast.val + 2) = central := by
    have hlength : tailLast.val + 2 =
        D.outer.last + 1 + 2 * (pairs + 1) := by omega
    rw [hlength]
    simpa only [central] using hsourceRaw
  have hcentralLeQ :=
    beli2019Lemma79_typeIII_nonoverlap_central_le_firstBeta
      a b D hfirst hdefect hnotOverlap hlast H hfirstTail hstrictTail
  have hcentralLeFirst : central ≤ (b.alphaValue first : WithTop Rat) := by
    exact WithTop.coe_le_coe.mpr (by
      simpa only [central, first] using hcentralLeQ)
  have hlastValue := H.value_eq tailLast hfirstTail le_rfl
  have htailCurrent : tailLast ≤ current := by
    change tailLast.val ≤ current.val
    simp only [current]
    omega
  have hleftEndpoint := b.alphaLeftEndpoint_monotone htailCurrent
  have hsameIndex : current.castSucc = tailLast.succ := by
    apply Fin.ext
    rfl
  unfold alphaLeftEndpoint at hleftEndpoint
  rw [hsameIndex] at hleftEndpoint
  have hevenGap : Even (tailLast.val - (D.outer.last + 1)) := by
    refine ⟨pairs, ?_⟩
    omega
  have horderEntry := b.orderSequence.entryOrZero_le_of_evenGap
    (D.outer.last + 1) tailLast.val (by omega) (by omega) hevenGap
  have horderMonotone : b.order first.succ ≤
      b.order tailLast.castSucc := by
    rw [b.orderSequence_entryOrZero_eq_order
        (⟨D.outer.last + 1, by omega⟩ : Fin (n + 2)),
      b.orderSequence_entryOrZero_eq_order
        (⟨tailLast.val, by omega⟩ : Fin (n + 2))] at horderEntry
    have hfirstIndex :
        (⟨D.outer.last + 1, by omega⟩ : Fin (n + 2)) =
          first.succ := by
      apply Fin.ext
      rfl
    have htailIndex :
        (⟨tailLast.val, by omega⟩ : Fin (n + 2)) =
          tailLast.castSucc := by
      apply Fin.ext
      rfl
    simpa only [hfirstIndex, htailIndex] using horderEntry
  have hfirstBetaLeCurrent : b.alphaValue first ≤
      b.alphaValue current := by
    have horderQ : (b.order first.succ : Rat) ≤
        (b.order tailLast.castSucc : Rat) := by
      exact_mod_cast horderMonotone
    push_cast at hlastValue hleftEndpoint
    linarith
  have hbeta : central ≤ (b.alphaValue current : WithTop Rat) :=
    hcentralLeFirst.trans (WithTop.coe_le_coe.mpr hfirstBetaLeCurrent)
  have hsuffix : ∀ k, idx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · simp only [idx] at hk
      omega
    · exact hkn
  have hAlphaRaw := a.beli2019Lemma63_sameRank_right_value
    b hdefect idx hsuffix
  have hcurrentIndex :
      (⟨idx.val - 1, by
        have hi := idx.lt_large
        have hp := idx.pos
        omega⟩ : Fin (n + 1)) = current := by
    apply Fin.ext
    simp only [idx, current]
    omega
  have hAlpha : a.representationAlphaValue b idx =
      b.alphaValue current := by
    simpa only [hcurrentIndex] using hAlphaRaw
  have hformula := beli2019Remark616_rightPrefix
    a b hdefect idx hAlpha ((-1) ^ ((tailLast.val + 2) / 2))
  rw [hcurrentIndex] at hformula
  calc
    b.truncatedPrefixDefect b
        ((-1) ^ ((tailLast.val + 2) / 2)) 0 (tailLast.val + 2) =
      min (a.truncatedPrefixDefect a
          ((-1) ^ ((tailLast.val + 2) / 2)) 0 (tailLast.val + 2))
        (b.alphaValue current : WithTop Rat) := by
          simpa only [idx] using hformula
    _ = a.truncatedPrefixDefect a
        ((-1) ^ ((tailLast.val + 2) / 2)) 0 (tailLast.val + 2) := by
      rw [min_eq_left]
      rw [hsource]
      exact hbeta
    _ = _ := by simpa only [hsource, central]

end BONG.GoodBONG

end Bong
