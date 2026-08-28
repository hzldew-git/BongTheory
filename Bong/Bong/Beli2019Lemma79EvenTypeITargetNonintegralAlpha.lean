/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTargetParity
import Bong.Bong.Beli2019Lemma79EvenTypeITargetReduction

/-!
# Beli (2019), Lemma 7.9(ii), case 3: nonintegral preceding alpha

When the target alpha immediately preceding an even central coordinate is
nonintegral, its adjacent order gap is strictly larger than `2e`.  If the
earlier target order lies above the source norm floor, the scalar primary
coefficient is negative.  At equality, the canonical prefix congruences make
the mixed primary defect vanish.  Both alternatives bound the representation
alpha by the target self-prefix defect.
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
-- The two order-floor alternatives follow the two subcases in the paper.
/-- A nonintegral preceding target alpha closes the central even target-prefix
branch of Lemma 7.9(ii). -/
theorem beli2019Lemma79_typeI_central_even_target_of_previousAlpha_not_integral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hnotAlpha : ¬ IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  let T : Int := a.orderSequence.entryOrZero D.anchor + 1
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpVal : p.val = i.val - 2 := by
    simp only [p, evenTargetPreviousAlphaIndex]
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
  have hpEven : Even p.val := by
    rw [hpVal]
    rcases hiEven with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    omega
  have hpBound : p.val < n + 2 := p.castSucc.isLt
  have hcMonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 p.val (Nat.zero_le _) hpBound hpEven
  have hpLowerRaw : T ≤ c.orderSequence.entryOrZero p.val :=
    hfirstLower.trans hcMonotone
  have hpLower : T ≤ c.order p.castSucc := by
    rw [← c.orderSequence_entryOrZero_eq_order]
    exact hpLowerRaw
  have halphaLarge : 2 * (ramificationIndex K : ℚ) < c.alphaValue p := by
    rcases c.beli2009Corollary28_iii p with hsmall | hlarge
    · exact False.elim (hnotAlpha (by simpa only [p] using hsmall.2.2))
    · exact hlarge.1
  have hgapLarge : 2 * (ramificationIndex K : Int) < c.orderGap p :=
    ((c.beli2009Corollary28_ii p).2.2).mp halphaLarge
  have halphaHalf := c.beli2009Lemma27_ii p hgapLarge.le
  have hselfNonneg := c.truncatedPrefixDefect_nonneg c
    ((-1) ^ (i.val / 2)) 0 i.val
  rcases lt_or_eq_of_le hpLower with hpHigh | hpEq
  · have hpHighStep : T + 1 ≤ c.order p.castSucc := by omega
    have hpHighStepQ : (T : ℚ) + 1 ≤ (c.order p.castSucc : ℚ) := by
      exact_mod_cast hpHighStep
    have hgapLargeQ :
        2 * (ramificationIndex K : ℚ) <
          (c.order p.succ : ℚ) - (c.order p.castSucc : ℚ) := by
      change 2 * (ramificationIndex K : Int) <
        c.order p.succ - c.order p.castSucc at hgapLarge
      exact_mod_cast hgapLarge
    have hprimaryNonpos :
        ((b.order ⟨i.val, i.lt_large⟩ -
            c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
            c.alphaValue p ≤ 0 := by
      rw [hbCurrent, ← hpSucc, halphaHalf]
      unfold halfGapValue orderGap
      push_cast
      linarith
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤
          (((b.order ⟨i.val, i.lt_large⟩ -
              c.order (evenTargetPreviousIndex i) : Int) : ℚ) :
            WithTop ℚ) + (c.alphaValue p : WithTop ℚ) := by
        simpa only [p] using
          lemma79_even_representationAlphaValue_le_primaryCoefficient
            b c i hiTwo
      _ ≤ 0 := by
        rw [← WithTop.coe_add]
        exact_mod_cast hprimaryNonpos
      _ ≤ c.truncatedPrefixDefect c
          ((-1) ^ (i.val / 2)) 0 i.val := hselfNonneg
  · have hbModRaw := lemma72_typeI_target_after_of_canonical
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
    have hpCurrentRaw : c.orderSequence.entryOrZero p.val ≤ T := by
      calc
        c.orderSequence.entryOrZero p.val = c.order p.castSucc := by
          simpa using c.orderSequence_entryOrZero_eq_order p.castSucc
        _ ≤ T := hpEq.ge
    have hcModRaw :=
      c.prefixSum_modEq_mul_of_current_le_reference_le_first
        T p.val hpBound hfirstLower hpCurrentRaw
    have hcLength : p.val + 1 = i.val - 1 := by omega
    have hcMod : Int.ModEq 2
        (c.orderSequence.prefixSum (i.val - 1))
        (((i.val - 1 : Nat) : Int) * T) := by
      simpa only [hcLength] using hcModRaw
    have hiPrefixBound : i.val + 1 ≤ n + 2 := by
      have hiLarge := i.lt_large
      omega
    have hodd := lemma79_typeI_even_primaryProduct_odd_of_modEq
      b c i.val hiEven hiTwo hiPrefixBound T hbMod hcMod
    have hzero := b.truncatedPrefixDefect_eq_zero_of_odd_order_general
      c (-1) (i.val + 1) (i.val - 1) hodd
    have hePos := ramificationIndex_pos (K := K)
    have hcrossNonpos : b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) ≤ 0 := by
      rw [hbCurrent, ← hpSucc]
      change 2 * (ramificationIndex K : Int) <
        c.order p.succ - c.order p.castSucc at hgapLarge
      omega
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
      _ ≤ 0 := by exact_mod_cast hcrossNonpos
      _ ≤ c.truncatedPrefixDefect c
          ((-1) ^ (i.val / 2)) 0 i.val := hselfNonneg

end BONG.GoodBONG

end Bong
