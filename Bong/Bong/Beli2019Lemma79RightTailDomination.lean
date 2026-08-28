/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74
import Bong.Bong.Beli2019Lemma79RightTailFromConditions

/-!
# Beli (2019), Lemma 7.9(ii), case 8: alternating tail domination

On the strict beta tail, Remark 1.1 identifies every adjacent capped defect
with `S_j - S_(u+1) + beta_u`.  Same-parity order monotonicity then bounds
each local defect by its value at the first boundary of an alternating
block.  Repeated defect domination joins the block, exactly as in case 8.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V} {n : Nat}

/-- The adjacent capped defect at every boundary of the strict beta tail is
the shifted left-order coefficient displayed in case 8. -/
theorem CaseEightStrictBetaTailConsequences.local_defect_eq
    [Beli2006AlphaLaws.{u, v} K]
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (j : Fin (n + 1)) (hfirst : first <= j) (hlast : j <= last) :
    b.truncatedPrefixDefect b (-1) j.val (j.val + 2) =
      (((b.order j.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : WithTop Rat) := by
  have hlocal := H.local_formula j hfirst hlast
  have hvalue := H.value_eq j hfirst hlast
  by_cases htop :
      b.truncatedPrefixDefect b (-1) j.val (j.val + 2) =
        (⊤ : WithTop Rat)
  · rw [htop] at hlocal
    have hne : (b.alphaValue j : WithTop Rat) ≠ ⊤ := by
      rw [b.coe_alphaValue]
      exact b.alpha_ne_top j
    apply (hne ?_).elim
    simpa only [add_top] using hlocal
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hd] at hlocal ⊢
    norm_cast at hlocal ⊢
    push_cast at hlocal hvalue ⊢
    linarith

/-- Repeated domination on any alternating block contained in the strict
case-8 beta tail. -/
theorem CaseEightStrictBetaTailConsequences.alternating_defect_ge
    [Beli2006AlphaLaws.{u, v} K]
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (j : Fin (n + 1)) (hfirst : first <= j) (hlast : j <= last)
    (pairs : Nat) (hend : j.val + 2 * pairs <= last.val) :
    ((((b.order j.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat) <=
      b.truncatedPrefixDefect b ((-1) ^ (pairs + 1))
        j.val (j.val + 2 * (pairs + 1)) := by
  let critical : WithTop Rat :=
    ((((b.order j.castSucc - b.order first.succ : Int) : Rat) +
      b.alphaValue first : Rat) : WithTop Rat)
  have hbound : j.val + 2 * (pairs + 1) <= n + 2 := by
    have hlastBound := last.isLt
    omega
  have hlocal (t : Nat) (ht : t <= pairs) :
      critical <= b.truncatedPrefixDefect b (-1)
        (j.val + 2 * t) (j.val + 2 * t + 2) := by
    let l : Fin (n + 1) := ⟨j.val + 2 * t, by omega⟩
    have hjl : j <= l := by
      change j.val <= l.val
      simp only [l]
      omega
    have hllast : l <= last := by
      change l.val <= last.val
      simp only [l]
      omega
    have horderEntry := b.orderSequence.entryOrZero_le_of_evenGap
      j.val l.val (by omega) (by omega) (by
        refine ⟨t, ?_⟩
        simp only [l]
        omega)
    have hjEntry := b.orderSequence_entryOrZero_eq_order
      ⟨j.val, by omega⟩
    have hlEntry := b.orderSequence_entryOrZero_eq_order
      ⟨l.val, by omega⟩
    rw [hjEntry, hlEntry] at horderEntry
    have hjIndex :
        (⟨j.val, by omega⟩ : Fin (n + 2)) = j.castSucc := by
      apply Fin.ext
      rfl
    have hlIndex :
        (⟨l.val, by omega⟩ : Fin (n + 2)) = l.castSucc := by
      apply Fin.ext
      rfl
    rw [hjIndex, hlIndex] at horderEntry
    have horderQ :
        (b.order j.castSucc : Rat) <= (b.order l.castSucc : Rat) := by
      exact_mod_cast horderEntry
    have hcoefficient :
        ((b.order j.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first <=
          ((b.order l.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first := by
      push_cast
      linarith
    rw [H.local_defect_eq l (hfirst.trans hjl) hllast]
    exact WithTop.coe_le_coe.mpr hcoefficient
  exact b.truncatedPrefixDefect_alternating_ge
    j.val pairs hbound critical hlocal

end BONG.GoodBONG

end Bong
