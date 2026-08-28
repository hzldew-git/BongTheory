/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 8: strict source domination

Past the first boundary of the strict beta tail, every source alpha is
strictly larger than the corresponding target beta.  The unchanged order
suffix turns this into a strict lower bound for every adjacent source
defect.  Strict repeated domination then joins any alternating source block.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Strict lower bounds on all adjacent factors propagate to their complete
alternating product. -/
theorem truncatedPrefixDefect_alternating_gt
    (b : GoodBONG q L (n + 1)) (start pairs : Nat)
    (hbound : start + 2 * (pairs + 1) <= n + 1)
    (c : WithTop Rat)
    (hlocal : forall t, t <= pairs ->
      c < b.truncatedPrefixDefect b (-1)
        (start + 2 * t) (start + 2 * t + 2)) :
    c < b.truncatedPrefixDefect b ((-1) ^ (pairs + 1))
      start (start + 2 * (pairs + 1)) := by
  induction pairs with
  | zero =>
      simpa using hlocal 0 le_rfl
  | succ pairs ih =>
      have hprevious := ih (by omega) (fun t ht =>
        hlocal t (by omega))
      have hlast := hlocal (pairs + 1) (by omega)
      have hend : start + 2 * (pairs + 1) + 2 =
          start + 2 * (pairs + 2) := by
        omega
      rw [hend] at hlast
      have hdom := b.truncatedPrefixDefect_domination b b
        ((-1) ^ (pairs + 1)) (-1) start
        (start + 2 * (pairs + 1)) (start + 2 * (pairs + 2))
      have hjoined := (lt_min hprevious hlast).trans_le hdom
      simpa only [pow_succ] using hjoined

/-- On a strict case-8 beta tail, every alternating source block beginning
strictly after the first boundary has defect strictly above the target
coefficient at its left endpoint. -/
theorem CaseEightStrictBetaTailConsequences.source_alternating_defect_gt
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k)
    (hstrict : b.alphaValue last < a.alphaValue last)
    (j : Fin (n + 1)) (hfirst : first < j) (hlast : j <= last)
    (pairs : Nat) (hend : j.val + 2 * pairs <= last.val) :
    ((((b.order j.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat) <
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 1))
        j.val (j.val + 2 * (pairs + 1)) := by
  let critical : WithTop Rat :=
    ((((b.order j.castSucc - b.order first.succ : Int) : Rat) +
      b.alphaValue first : Rat) : WithTop Rat)
  have hbound : j.val + 2 * (pairs + 1) <= n + 2 := by
    have hlastBound := last.isLt
    omega
  have hordersSucc (l : Fin (n + 1)) (hlFirst : first <= l)
      (hlLast : l <= last) :
      a.order l.succ = b.order l.succ := by
    have hentry := hsuffix (l.val + 1) (by omega) (by omega)
    have haEntry := a.orderSequence_entryOrZero_eq_order
      (Fin.mk (l.val + 1) (by omega))
    have hbEntry := b.orderSequence_entryOrZero_eq_order
      (Fin.mk (l.val + 1) (by omega))
    rw [haEntry, hbEntry] at hentry
    have hindex :
        (Fin.mk (l.val + 1) (by omega) : Fin (n + 2)) = l.succ := by
      apply Fin.ext
      rfl
    simpa only [hindex] using hentry
  have hlocal (t : Nat) (ht : t <= pairs) :
      critical < a.truncatedPrefixDefect a (-1)
        (j.val + 2 * t) (j.val + 2 * t + 2) := by
    let l : Fin (n + 1) := Fin.mk (j.val + 2 * t) (by omega)
    have hjl : j <= l := by
      change j.val <= l.val
      simp only [l]
      omega
    have hllast : l <= last := by
      change l.val <= last.val
      simp only [l]
      omega
    have hfirstL : first <= l := hfirst.le.trans hjl
    have htargetSource : b.alphaValue l < a.alphaValue l :=
      H.targetAlpha_lt_sourceAlpha hordersSucc hstrict l
        hfirstL hllast
    have hcurrentEntry := hsuffix l.val (by
      change first.val + 1 <= l.val
      have hjValue : j.val <= l.val := hjl
      have hfirstValue : first.val < j.val := hfirst
      omega) (by omega)
    have haCurrent := a.orderSequence_entryOrZero_eq_order
      (Fin.mk l.val (by omega))
    have hbCurrent := b.orderSequence_entryOrZero_eq_order
      (Fin.mk l.val (by omega))
    rw [haCurrent, hbCurrent] at hcurrentEntry
    have hcurrentIndex :
        (Fin.mk l.val (by omega) : Fin (n + 2)) = l.castSucc := by
      apply Fin.ext
      rfl
    have hcurrentOrder :
        a.order l.castSucc = b.order l.castSucc := by
      simpa only [hcurrentIndex] using hcurrentEntry
    have hnextOrder := hordersSucc l hfirstL hllast
    have hvalue := H.value_eq l hfirstL hllast
    have hcoefficientLt :
        ((b.order l.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first <
          ((a.order l.castSucc - a.order l.succ : Int) : Rat) +
            a.alphaValue l := by
      rw [hcurrentOrder, hnextOrder]
      push_cast at hvalue ⊢
      linarith
    have horderEntry := b.orderSequence.entryOrZero_le_of_evenGap
      j.val l.val (by omega) (by omega) (by
        refine ⟨t, ?_⟩
        simp only [l]
        omega)
    have hjEntry := b.orderSequence_entryOrZero_eq_order
      (Fin.mk j.val (by omega))
    have hlEntry := b.orderSequence_entryOrZero_eq_order
      (Fin.mk l.val (by omega))
    rw [hjEntry, hlEntry] at horderEntry
    have hjIndex :
        (Fin.mk j.val (by omega) : Fin (n + 2)) = j.castSucc := by
      apply Fin.ext
      rfl
    have hlIndex :
        (Fin.mk l.val (by omega) : Fin (n + 2)) = l.castSucc := by
      apply Fin.ext
      rfl
    rw [hjIndex, hlIndex] at horderEntry
    have horderQ :
        (b.order j.castSucc : Rat) <= (b.order l.castSucc : Rat) := by
      exact_mod_cast horderEntry
    have hcriticalLt :
        ((b.order j.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first <
          ((a.order l.castSucc - a.order l.succ : Int) : Rat) +
            a.alphaValue l := by
      push_cast at hcoefficientLt ⊢
      linarith
    have hsource := a.order_sub_add_alpha_le_cappedAdjacent l
    exact (WithTop.coe_lt_coe.mpr hcriticalLt).trans_le hsource
  exact a.truncatedPrefixDefect_alternating_gt
    j.val pairs hbound critical hlocal

end BONG.GoodBONG

end Bong
