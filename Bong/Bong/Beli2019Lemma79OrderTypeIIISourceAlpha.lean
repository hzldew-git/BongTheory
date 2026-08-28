/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29SourceReduction
import Bong.Bong.Beli2019Lemma67Classification
import Bong.Bong.Beli2019Lemma74
import Bong.Bong.Beli2019Lemma79OrderRightAlternating
import Bong.Bong.Beli2019Lemma79OrderTypeIIIHalfGap

/-!
# Beli (2019), Lemma 7.9(i): the type-III source-alpha candidate

The source-alpha candidate proves the adjacent-pair alternative unless its
alpha term vanishes and the next source order is exactly the left target
boundary.  In that exceptional case P2 gives a gap of `-2e`; parity and
good-BONG monotonicity propagate it back to the normalized initial gap and
give a contradiction.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A nonzero alpha invariant is at least one.  Corollary 2.8(iii) is
needed here because an alpha above `2e` can be half-integral. -/
theorem one_le_alphaValue_of_ne_zero
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (i : Fin n)
    (hne : a.alphaValue i ≠ 0) : (1 : ℚ) ≤ a.alphaValue i := by
  rcases a.beli2009Corollary28_iii i with hsmall | hlarge
  · rcases hsmall.2.2 with ⟨z, hz⟩
    have hzNonnegative : (0 : Int) ≤ z := by
      exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
        simpa only [← hz] using hsmall.1)
    have hzNe : z ≠ 0 := by
      intro hzZero
      apply hne
      rw [hz, hzZero]
      norm_num
    have hzOne : (1 : Int) ≤ z := by omega
    rw [hz]
    exact_mod_cast hzOne
  · have hePos := ramificationIndex_pos (K := K)
    have honeTwoE : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast (show (1 : Int) ≤
        2 * (ramificationIndex K : Int) by omega)
    exact honeTwoE.trans hlarge.1.le

/-- The source-alpha branch of the hard type-III calculation proves the
adjacent-pair alternative in condition (i). -/
theorem lemma79_typeIII_pair_of_sourceAlpha_le_mixedShift
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (k : Nat) (_hk : k < n + 2) (hkPos : 0 < k)
    (hkNext : k + 1 < n + 2) (hkNextNext : k + 2 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1)))
    (hsourceAlpha : a.representationSecondarySourceAlpha c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } (by
        change 1 < k + 1 ∧ k + 1 + 1 < n + 2
        omega) ≤
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
              WithTop ℚ)) :
    b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) ≤
      c.orderSequence.entryOrZero (k - 1) +
        c.orderSequence.entryOrZero k := by
  let left := D.outer.transition.lastZero
  let idx : RepresentationIndex (n + 2) (n + 2) := {
    val := k + 1
    pos := by omega
    lt_large := hkNext
    le_small := hkNext.le }
  let p : Fin (n + 1) := ⟨k + 1, by omega⟩
  let C : Int := b.orderSequence.entryOrZero left -
    a.orderSequence.entryOrZero (left + 1)
  change a.representationSecondarySourceAlpha c idx (by
      change 1 < k + 1 ∧ k + 1 + 1 < n + 2
      omega) ≤
    (((C : ℚ)) : WithTop ℚ) at hsourceAlpha
  have hsourceAlphaQ :
      (2 * (a.order ⟨idx.val, idx.lt_large⟩ : ℚ) -
          (c.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ : ℚ) -
          (c.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : ℚ)) +
        a.alphaValue p ≤ (C : ℚ) := by
    change (((2 * a.order ⟨idx.val, idx.lt_large⟩ -
        c.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
        c.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + (a.alphaValue p : WithTop ℚ) ≤
      (((C : ℚ)) : WithTop ℚ) at hsourceAlpha
    norm_cast at hsourceAlpha
    push_cast at hsourceAlpha
    exact hsourceAlpha
  have haIdx : a.order ⟨idx.val, idx.lt_large⟩ =
      a.orderSequence.entryOrZero (k + 1) := by
    simpa only [idx] using
      (a.orderSequence_entryOrZero_eq_order
        ⟨idx.val, idx.lt_large⟩).symm
  have hcPrev : c.order ⟨idx.val - 2, by
        have := idx.le_small
        omega⟩ = c.orderSequence.entryOrZero (k - 1) := by
    have hval : idx.val - 2 = k - 1 := by
      simp only [idx]
      omega
    rw [← hval]
    exact (c.orderSequence_entryOrZero_eq_order
      ⟨idx.val - 2, by have := idx.le_small; omega⟩).symm
  have hcCurrent : c.order ⟨idx.val - 1, by
        have := idx.le_small
        omega⟩ = c.orderSequence.entryOrZero k := by
    simpa only [idx, Nat.add_sub_cancel] using
      (c.orderSequence_entryOrZero_eq_order
        ⟨idx.val - 1, by have := idx.le_small; omega⟩).symm
  rw [haIdx, hcPrev, hcCurrent] at hsourceAlphaQ
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    simp only [left]
    rw [D.adjacent]
    omega
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    k hright hlast heven
  have hrightBoundary := D.outer.transition.rightBoundary
  have hcurrentTarget : b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero (left + 1) + 1 := by
    rw [hcurrentBoundary, hrightBoundary, hrightIndex]
  have htargetNext := a.lemma79_typeIII_targetNext_le_sourceNext
    b D k hkNext hright hlast heven
  have hsourceNext := a.lemma79_typeIII_leftTarget_le_sourceNext
    b D k hkNext hright hlast heven
  have hsourceNext' : b.orderSequence.entryOrZero left ≤
      a.orderSequence.entryOrZero (k + 1) := by
    simpa only [left] using hsourceNext
  by_cases halphaZero : a.alphaValue p = 0
  · by_cases hsourceStrict : b.orderSequence.entryOrZero left <
        a.orderSequence.entryOrZero (k + 1)
    · have hdesiredQ :
          (b.orderSequence.entryOrZero k : ℚ) +
              (b.orderSequence.entryOrZero (k + 1) : ℚ) ≤
            (c.orderSequence.entryOrZero (k - 1) : ℚ) +
              (c.orderSequence.entryOrZero k : ℚ) := by
        have hstrictQ :
            (b.orderSequence.entryOrZero left : ℚ) + 1 ≤
              (a.orderSequence.entryOrZero (k + 1) : ℚ) := by
          exact_mod_cast (show b.orderSequence.entryOrZero left + 1 ≤
            a.orderSequence.entryOrZero (k + 1) by omega)
        have htargetNextQ :
            (b.orderSequence.entryOrZero (k + 1) : ℚ) ≤
              (a.orderSequence.entryOrZero (k + 1) : ℚ) := by
          exact_mod_cast htargetNext
        have hcurrentTargetQ :
            (b.orderSequence.entryOrZero k : ℚ) =
              (a.orderSequence.entryOrZero (left + 1) : ℚ) + 1 := by
          exact_mod_cast hcurrentTarget
        have hC : (C : ℚ) =
            (b.orderSequence.entryOrZero left : ℚ) -
              (a.orderSequence.entryOrZero (left + 1) : ℚ) := by
          dsimp only [C]
          push_cast
          rfl
        rw [halphaZero] at hsourceAlphaQ
        norm_num at hsourceAlphaQ
        linarith
      exact_mod_cast hdesiredQ
    · have hsourceEq : a.orderSequence.entryOrZero (k + 1) =
          b.orderSequence.entryOrZero left := by omega
      have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
      have hsourceLeft := D.outer.source_leftEven_eq_first
        hfirst left le_rfl hleftEven
      rcases heven with ⟨d, hd⟩
      have hrightOdd : Odd (D.outer.transition.firstTwo - 1) := by
        rcases hleftEven with ⟨e, he⟩
        rw [hrightIndex]
        exact ⟨e, by omega⟩
      have hkOdd : Odd k := by
        rcases hrightOdd with ⟨e, he⟩
        exact ⟨e + d, by omega⟩
      have hnextNextOdd : Odd (k + 2) := by
        rcases hkOdd with ⟨e, he⟩
        exact ⟨e + 1, by omega⟩
      have hsourceOddLe := a.orderSequence.entryOrZero_le_of_evenGap
        1 (k + 2) (by omega) hkNextNext (by
          rcases hnextNextOdd with ⟨e, he⟩
          exact ⟨e, by omega⟩)
      have hgapAtP := (a.alpha_p2 p).2.mp halphaZero
      have hpGap : a.orderGap p =
          a.orderSequence.entryOrZero (k + 2) -
            a.orderSequence.entryOrZero (k + 1) := by
        unfold orderGap
        rw [← a.orderSequence_entryOrZero_eq_order p.succ,
          ← a.orderSequence_entryOrZero_eq_order p.castSucc]
        simp only [p, Fin.val_succ, Fin.val_castSucc]
      have hinitialFormula : a.orderGap ⟨0, by omega⟩ =
          a.orderSequence.entryOrZero 1 -
            a.orderSequence.entryOrZero 0 := by
        unfold orderGap
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega),
          BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
        rfl
      have hinitialUpper : a.orderGap ⟨0, by omega⟩ ≤
          1 - 2 * (ramificationIndex K : Int) := by
        have hgapEntries :
            a.orderSequence.entryOrZero (k + 2) -
                a.orderSequence.entryOrZero (k + 1) =
              -(2 * (ramificationIndex K : Int)) := by
          rw [← hpGap, hgapAtP]
        have hleftBoundary := D.outer.transition.leftBoundary
        rw [hsourceEq, hleftBoundary, hsourceLeft] at hgapEntries
        rw [hinitialFormula]
        omega
      have hinitialEq : a.orderGap ⟨0, by omega⟩ =
          1 - 2 * (ramificationIndex K : Int) := by
        have hinitial' : -(2 * (ramificationIndex K : Int)) <
            a.orderGap ⟨0, by omega⟩ := by simpa using hinitial
        omega
      have hePos := ramificationIndex_pos (K := K)
      have hinitialNegative : a.orderGap ⟨0, by omega⟩ < 0 := by
        rw [hinitialEq]
        omega
      have hinitialEven := a.orderGap_even_of_negative
        ⟨0, by omega⟩ hinitialNegative
      have hinitialOdd : Odd (a.orderGap ⟨0, by omega⟩) := by
        rw [hinitialEq]
        exact ⟨-(ramificationIndex K : Int), by omega⟩
      exact False.elim
        ((Int.not_even_iff_odd.mpr hinitialOdd) hinitialEven)
  · have halphaOne := a.one_le_alphaValue_of_ne_zero p halphaZero
    have hdesiredQ :
        (b.orderSequence.entryOrZero k : ℚ) +
            (b.orderSequence.entryOrZero (k + 1) : ℚ) ≤
          (c.orderSequence.entryOrZero (k - 1) : ℚ) +
            (c.orderSequence.entryOrZero k : ℚ) := by
      have hsourceNextQ :
          (b.orderSequence.entryOrZero left : ℚ) ≤
            (a.orderSequence.entryOrZero (k + 1) : ℚ) := by
        exact_mod_cast hsourceNext'
      have htargetNextQ :
          (b.orderSequence.entryOrZero (k + 1) : ℚ) ≤
            (a.orderSequence.entryOrZero (k + 1) : ℚ) := by
        exact_mod_cast htargetNext
      have hcurrentTargetQ :
          (b.orderSequence.entryOrZero k : ℚ) =
            (a.orderSequence.entryOrZero (left + 1) : ℚ) + 1 := by
        exact_mod_cast hcurrentTarget
      have hC : (C : ℚ) =
          (b.orderSequence.entryOrZero left : ℚ) -
            (a.orderSequence.entryOrZero (left + 1) : ℚ) := by
        dsimp only [C]
        push_cast
        rfl
      linarith
    exact_mod_cast hdesiredQ

end BONG.GoodBONG

end Bong
