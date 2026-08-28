/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOne

/-!
# Beli (2019), Lemma 7.9(ii), case 8: gap-one type data

This file converts the entrywise last-difference data of Lemma 6.7 into
the order identities needed by the gap-one calculation.  The conversion
works uniformly for a singleton tail and a nontrivial tail.  Types II and
III always lie in this branch; type I supplies the selected disjunct.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

namespace CaseEightStrictBetaTailConsequences

/-- Entrywise gap-one and suffix equality imply the odd-gap and explicit
beta conclusions for a strict case-8 tail. -/
theorem gapOne_formula_of_entryOrZero
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hfirstLast : first ≤ last)
    (hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k)
    (hentry : b.orderSequence.entryOrZero first.val =
      a.orderSequence.entryOrZero first.val + 1)
    (hstrictLast : b.alphaValue last < a.alphaValue last) :
    Odd (b.orderGap first) ∧
      ∀ j : Fin (n + 1), first ≤ j → j ≤ last →
        b.alphaValue j =
          ((b.order j.succ - b.order first.castSucc : Int) : Rat) := by
  have hcurrent :
      b.order first.castSucc = a.order first.castSucc + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order first.castSucc,
      ← a.orderSequence_entryOrZero_eq_order first.castSucc]
    simpa using hentry
  have horders (j : Fin (n + 1)) (hfirst : first ≤ j)
      (hlast : j ≤ last) :
      a.order j.succ = b.order j.succ := by
    have hentryNext := hsuffix (j.val + 1) (by omega) (by omega)
    rw [a.orderSequence_entryOrZero_eq_order
        (Fin.mk (j.val + 1) (by omega)),
      b.orderSequence_entryOrZero_eq_order
        (Fin.mk (j.val + 1) (by omega))] at hentryNext
    have hindex :
        (Fin.mk (j.val + 1) (by omega) : Fin (n + 2)) = j.succ := by
      apply Fin.ext
      rfl
    simpa only [hindex] using hentryNext
  have hnext : b.order first.succ = a.order first.succ :=
    (horders first le_rfl hfirstLast).symm
  have hstrictFirst : b.alphaValue first < a.alphaValue first :=
    H.targetAlpha_lt_sourceAlpha horders hstrictLast
      first le_rfl hfirstLast
  have hodd := H.firstGap_odd_of_target_eq_source_add_one
    hfirstLast hcurrent hnext hstrictFirst
  refine ⟨hodd, ?_⟩
  intro j hfirst hlast
  exact H.alphaValue_eq_order_sub_first_of_target_eq_source_add_one
    hfirstLast hcurrent hnext hstrictFirst j hfirst hlast

end CaseEightStrictBetaTailConsequences

/-- Type-I gap-one tail data. -/
theorem beli2019Lemma79_typeI_caseEight_gapOne_formula
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (last : Fin (n + 1))
    (hfirstLast : D.profile.last ≤ last.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last (by omega)) last)
    (hstrictLast : b.alphaValue last < a.alphaValue last)
    (hgapOne : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 1) :
    Odd (b.orderGap (Fin.mk D.profile.last (by omega))) ∧
      ∀ j : Fin (n + 1), Fin.mk D.profile.last (by omega) ≤ j →
        j ≤ last →
        b.alphaValue j =
          ((b.order j.succ -
            b.order (Fin.mk D.profile.last (by omega)).castSucc : Int) :
              Rat) := by
  let first : Fin (n + 1) := Fin.mk D.profile.last (by omega)
  have hle : first ≤ last := by
    change D.profile.last ≤ last.val
    exact hfirstLast
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.profile.lastDifference.after k
    · simp only [first] at hk
      omega
    · exact hkn
  have hresult := H.gapOne_formula_of_entryOrZero
    hle hsuffix (by simpa only [first] using hgapOne) hstrictLast
  simpa only [first] using hresult

/-- Type-II gap-one tail data. -/
theorem beli2019Lemma79_typeII_caseEight_gapOne_formula
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (last : Fin (n + 1))
    (hfirstLast : D.outer.last ≤ last.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last (by omega)) last)
    (hstrictLast : b.alphaValue last < a.alphaValue last) :
    Odd (b.orderGap (Fin.mk D.outer.last (by omega))) ∧
      ∀ j : Fin (n + 1), Fin.mk D.outer.last (by omega) ≤ j →
        j ≤ last →
        b.alphaValue j =
          ((b.order j.succ -
            b.order (Fin.mk D.outer.last (by omega)).castSucc : Int) :
              Rat) := by
  let first : Fin (n + 1) := Fin.mk D.outer.last (by omega)
  have hle : first ≤ last := by
    change D.outer.last ≤ last.val
    exact hfirstLast
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · simp only [first] at hk
      omega
    · exact hkn
  have hgapOne := beli2019Lemma79_typeII_caseEight_lastGap a b D
  have hresult := H.gapOne_formula_of_entryOrZero
    hle hsuffix (by simpa only [first] using hgapOne) hstrictLast
  simpa only [first] using hresult

/-- Type-III gap-one tail data. -/
theorem beli2019Lemma79_typeIII_caseEight_gapOne_formula
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (last : Fin (n + 1))
    (hfirstLast : D.outer.last ≤ last.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last (by omega)) last)
    (hstrictLast : b.alphaValue last < a.alphaValue last) :
    Odd (b.orderGap (Fin.mk D.outer.last (by omega))) ∧
      ∀ j : Fin (n + 1), Fin.mk D.outer.last (by omega) ≤ j →
        j ≤ last →
        b.alphaValue j =
          ((b.order j.succ -
            b.order (Fin.mk D.outer.last (by omega)).castSucc : Int) :
              Rat) := by
  let first : Fin (n + 1) := Fin.mk D.outer.last (by omega)
  have hle : first ≤ last := by
    change D.outer.last ≤ last.val
    exact hfirstLast
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · simp only [first] at hk
      omega
    · exact hkn
  have hgapOne := beli2019Lemma79_typeIII_caseEight_lastGap a b D
  have hresult := H.gapOne_formula_of_entryOrZero
    hle hsuffix (by simpa only [first] using hgapOne) hstrictLast
  simpa only [first] using hresult

end BONG.GoodBONG

end Bong
