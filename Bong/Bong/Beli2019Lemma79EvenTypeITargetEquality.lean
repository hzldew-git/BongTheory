/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeIEqualityParity
import Bong.Bong.Beli2019Lemma79EvenTargetParity
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the final equality branch

The right-endpoint equality supplies the missing parity of the third prefix,
so the mixed primary defect vanishes.  If the witness gap is `-2e`, its
adjacent coefficient is `2e`; otherwise its alpha is at least one and the
same adjacent coefficient dominates the mixed primary order coefficient.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- The proof follows the two final witness-gap alternatives in the paper.
/-- The equality exception left by the integral reduction still satisfies the
central even target-prefix bound. -/
theorem beli2019Lemma79_typeI_central_even_target_of_domination_equality
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int))
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjBefore : j.val + 1 < i.val)
    (hjOrder : c.order j.castSucc =
      b.order ⟨i.val, i.lt_large⟩ - 1)
    (hjDefect : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val)
    (heq : c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
      ((show ℚ from
          ((b.order ⟨i.val, i.lt_large⟩ -
            c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
        WithTop ℚ)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  let T : Int := a.orderSequence.entryOrZero D.anchor + 1
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpSucc : p.succ = evenTargetPreviousIndex i := by
    apply Fin.ext
    simp only [p, evenTargetPreviousAlphaIndex, evenTargetPreviousIndex,
      Fin.succ_mk]
    omega
  have hpreviousIndex :
      (⟨i.val - 1, by
        have hi := i.le_small
        omega⟩ : Fin (n + 2)) = evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  have haZero := C.source_to_anchor 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hbLeft := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have hbPlateau := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft hiRight hiEven
  have hbCurrentRaw : b.orderSequence.entryOrZero i.val = T + 1 := by
    dsimp only [T]
    omega
  have hbCurrent : b.order ⟨i.val, i.lt_large⟩ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    exact hbCurrentRaw
  have hjOrderT : c.order j.castSucc = T := by
    rw [hjOrder, hbCurrent]
    omega
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at hnormOrder
  have hnormRaw : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence_entryOrZero_eq_order
          (⟨0, by omega⟩ : Fin (n + 2))]
        simp only [Fin.zero_eta]
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence_entryOrZero_eq_order
          (⟨0, by omega⟩ : Fin (n + 2))]
        simp only [Fin.zero_eta]
  have hfirstLower : T ≤ c.orderSequence.entryOrZero 0 := by
    dsimp only [T]
    omega
  have hendpoint :=
    lemma79_even_rightEndpoint_eq_of_domination_equality
      c i hiTwo j hjBefore (b.order ⟨i.val, i.lt_large⟩)
        hjOrder hjDefect heq
  have hcPrefix :=
    lemma79_typeI_even_thirdPrefix_modEq_of_rightEndpoint_eq
      c i hiTwo hiEven j hjEven hjBefore T hfirstLower hjOrderT hendpoint
  have hbModRaw := lemma72_typeI_target_after_of_canonical
    a b D C hfirst (i.val + 1) (by omega) (by
      have hrightLast := C.right_le_last
      omega)
  have hreference :
      a.orderSequence.entryOrZero D.anchor + 2 = T + 1 := by
    dsimp only [T]
    ring
  have hbMod : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (((i.val + 1 : Nat) : Int) * (T + 1)) := by
    simpa only [hreference] using hbModRaw
  have hcountPreviousOne : Int.ModEq 2
      (((i.val - 1 : Nat) : Int)) 1 := by
    rcases hiEven with ⟨d, hd⟩
    have hdPos : 0 < d := by omega
    rw [Int.modEq_iff_dvd]
    refine ⟨-((d - 1 : Nat) : Int), ?_⟩
    omega
  have hcMod : Int.ModEq 2
      (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) * T) :=
    hcPrefix.trans (by
      simpa only [one_mul] using (hcountPreviousOne.mul_right T).symm)
  have hiPrefixBound : i.val + 1 ≤ n + 2 := by
    have hiLarge := i.lt_large
    omega
  have hodd := lemma79_typeI_even_primaryProduct_odd_of_modEq
    b c i.val hiEven hiTwo hiPrefixBound T hbMod hcMod
  have hzero := b.truncatedPrefixDefect_eq_zero_of_odd_order_general
    c (-1) (i.val + 1) (i.val - 1) hodd
  have hBcross : (b.representationAlphaValue c i : WithTop ℚ) ≤
      (((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) :
          WithTop ℚ) := by
    rw [b.coe_representationAlphaValue c i]
    calc
      b.representationAlpha c i ≤ b.representationAlphaPrime c i :=
        b.representationAlpha_le_prime c i
      _ ≤ b.representationPrimaryDefect c i :=
        b.representationAlphaPrime_le_primaryDefect c i
      _ = (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) :
            WithTop ℚ) := by
        unfold representationPrimaryDefect
        rw [hpreviousIndex, hzero, add_zero]
  have hadjacentToSelf :=
    (c.order_sub_add_alpha_le_cappedAdjacent j).trans hjDefect
  by_cases hgapMinimal :
      c.orderGap j = -(2 * (ramificationIndex K : Int))
  · have halphaZero := (c.beli2009Lemma27_i j).2.mpr hgapMinimal
    have hdiff : c.order j.castSucc - c.order j.succ =
        2 * (ramificationIndex K : Int) := by
      unfold orderGap at hgapMinimal
      omega
    have htwoEAdjacent :
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) =
          (((((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
            c.alphaValue j : ℚ)) : WithTop ℚ) := by
      apply congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
      rw [halphaZero, add_zero]
      exact_mod_cast hdiff.symm
    exact (representationAlphaValue_le_twoE_of_crossGap_le
      b c i hcross).trans (by
        rw [htwoEAdjacent]
        exact hadjacentToSelf)
  · have halphaNe : c.alphaValue j ≠ 0 := by
      intro halphaZero
      exact hgapMinimal ((c.beli2009Lemma27_i j).2.mp halphaZero)
    have halphaOne := c.one_le_alphaValue_of_ne_zero j halphaNe
    have hgapEven : Even ((i.val - 1) - (j.val + 1)) := by
      rcases hiEven with ⟨d, hd⟩
      rcases hjEven with ⟨s, hs⟩
      refine ⟨d - s - 1, ?_⟩
      omega
    have hnextRaw := c.orderSequence.entryOrZero_le_of_evenGap
      (j.val + 1) (i.val - 1) (by omega) (by
        have hiLarge := i.lt_large
        omega) hgapEven
    have hnextLePrevious : c.order j.succ ≤
        c.order (evenTargetPreviousIndex i) := by
      rw [← c.orderSequence_entryOrZero_eq_order,
        ← c.orderSequence_entryOrZero_eq_order]
      exact hnextRaw
    have hcrossToAdjacentQ :
        ((b.order ⟨i.val, i.lt_large⟩ -
            c.order (evenTargetPreviousIndex i) : Int) : ℚ) ≤
          ((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
            c.alphaValue j := by
      have hnextQ : (c.order j.succ : ℚ) ≤
          (c.order (evenTargetPreviousIndex i) : ℚ) := by
        exact_mod_cast hnextLePrevious
      rw [hjOrder]
      push_cast
      linarith
    have hcrossToAdjacent :
        (((b.order ⟨i.val, i.lt_large⟩ -
            c.order (evenTargetPreviousIndex i) : Int) : ℚ) :
          WithTop ℚ) ≤
          (((((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
            c.alphaValue j : ℚ)) : WithTop ℚ) := by
      exact_mod_cast hcrossToAdjacentQ
    exact hBcross.trans (hcrossToAdjacent.trans hadjacentToSelf)

end BONG.GoodBONG

end Bong
