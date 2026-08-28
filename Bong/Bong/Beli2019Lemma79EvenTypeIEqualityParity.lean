/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma73
import Bong.Bong.Beli2019Lemma79EvenTypeITargetReduction
import Bong.Bong.Beli2019Lemma79ThirdPrefixParity

/-!
# Beli (2019), Lemma 7.9(ii), case 3: parity in the equality branch

Equality in the target domination chain identifies two right alpha endpoints.
Lemma 7.3(ii) then fixes the parity of all intervening orders.  Since both the
coordinate and the domination witness are even, the intervening tail has even
length, leaving the third prefix sum congruent to the common floor order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {N : Lattice K V} {n : Nat}

/-- Equality of the whole capped prefix with the transported witness
coefficient forces equality in the antitone right-endpoint estimate. -/
theorem lemma79_even_rightEndpoint_eq_of_domination_equality
    [Beli2006AlphaLaws.{u, v} K]
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (j : Fin (n + 1))
    (hjBefore : j.val + 1 < i.val) (current : Int)
    (hjOrder : c.order j.castSucc = current - 1)
    (hjDefect : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val)
    (heq : c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
      ((show ℚ from
          ((current - c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
        WithTop ℚ)) :
    c.alphaRightEndpoint j =
      c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i) := by
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpVal : p.val = i.val - 2 := by
    simp only [p, evenTargetPreviousAlphaIndex]
  have hpSucc : p.succ = evenTargetPreviousIndex i := by
    apply Fin.ext
    simp only [p, evenTargetPreviousAlphaIndex, evenTargetPreviousIndex,
      Fin.succ_mk]
    omega
  have hjp : j ≤ p := by
    change j.val ≤ p.val
    rw [hpVal]
    omega
  have hselfWitness :
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
        (((((c.order j.castSucc - c.order p.succ : Int) : ℚ) +
          c.alphaValue p : ℚ)) : WithTop ℚ) := by
    calc
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
          ((show ℚ from
              ((current - c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
              c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
            WithTop ℚ) := heq
      _ = (((((c.order j.castSucc - c.order p.succ : Int) : ℚ) +
          c.alphaValue p : ℚ)) : WithTop ℚ) := by
        rw [← hpSucc]
        apply congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
        rw [hjOrder]
        push_cast
        ring
  have hadjacentToSelf :=
    (c.order_sub_add_alpha_le_cappedAdjacent j).trans hjDefect
  have hadjacentToWitness :
      (((((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j : ℚ)) : WithTop ℚ) ≤
        (((((c.order j.castSucc - c.order p.succ : Int) : ℚ) +
          c.alphaValue p : ℚ)) : WithTop ℚ) := by
    rw [← hselfWitness]
    exact hadjacentToSelf
  have hadjacentToWitnessQ :
      ((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j ≤
        ((c.order j.castSucc - c.order p.succ : Int) : ℚ) +
          c.alphaValue p := by
    exact_mod_cast hadjacentToWitness
  have hreverse : c.alphaRightEndpoint j ≤ c.alphaRightEndpoint p := by
    unfold alphaRightEndpoint
    push_cast at hadjacentToWitnessQ ⊢
    linarith
  have hforward := c.alphaRightEndpoint_antitone hjp
  exact le_antisymm hreverse (by simpa only [p] using hforward)

/-- The parity conclusion used after Lemma 7.3(ii) in the final equality
subcase of Lemma 7.9(ii), case 3. -/
theorem lemma79_typeI_even_thirdPrefix_modEq_of_rightEndpoint_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjBefore : j.val + 1 < i.val) (T : Int)
    (hfirstLower : T ≤ c.orderSequence.entryOrZero 0)
    (hjOrder : c.order j.castSucc = T)
    (hendpoint : c.alphaRightEndpoint j =
      c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i)) :
    Int.ModEq 2 (c.orderSequence.prefixSum (i.val - 1)) T := by
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpVal : p.val = i.val - 2 := by
    simp only [p, evenTargetPreviousAlphaIndex]
  have hjBound : j.val < n + 2 := j.castSucc.isLt
  have hjCurrent : c.orderSequence.entryOrZero j.val ≤ T := by
    calc
      c.orderSequence.entryOrZero j.val = c.order j.castSucc := by
        simpa using c.orderSequence_entryOrZero_eq_order j.castSucc
      _ ≤ T := hjOrder.le
  have hbaseRaw :=
    c.prefixSum_modEq_mul_of_current_le_reference_le_first
      T j.val hjBound hfirstLower hjCurrent
  have hcountOne : Int.ModEq 2 (((j.val + 1 : Nat) : Int)) 1 := by
    rcases hjEven with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    push_cast
    omega
  have hbase : Int.ModEq 2
      (c.orderSequence.prefixSum (j.val + 1)) T :=
    hbaseRaw.trans (by
      simpa only [one_mul] using hcountOne.mul_right T)
  have hjp : j ≤ p := by
    change j.val ≤ p.val
    rw [hpVal]
    omega
  by_cases hjpEq : j = p
  · have hlength : j.val + 1 = i.val - 1 := by
      rw [hjpEq, hpVal]
      omega
    simpa only [hlength] using hbase
  · have hjpStrict : j < p := lt_of_le_of_ne hjp hjpEq
    have hconsequences := c.beli2019Lemma73_ii j p hjpStrict (by
      simpa only [p] using hendpoint)
    have hstartEnd : j.val + 1 ≤ i.val - 1 := by omega
    have htail := c.orderSequence.prefixSum_modEq_add_mul_of_tail
      T (c.order j.succ) hstartEnd hbase (by
        intro k hkStart hkEnd
        let r : Fin (n + 1) := ⟨k - 1, by omega⟩
        have hjr : j ≤ r := by
          change j.val ≤ r.val
          simp only [r]
          omega
        have hrp : r ≤ p := by
          change r.val ≤ p.val
          simp only [r]
          rw [hpVal]
          omega
        have hmod := hconsequences.order_modEq r hjr hrp
        let kFin : Fin (n + 2) := ⟨k, by omega⟩
        have hrSucc : r.succ = kFin := by
          apply Fin.ext
          simp only [r, kFin, Fin.val_succ]
          omega
        calc
          c.orderSequence.entryOrZero k = c.order kFin := by
            simpa only [kFin] using
              c.orderSequence_entryOrZero_eq_order kFin
          _ = c.order r.succ := by rw [hrSucc]
          _ ≡ c.order j.succ [ZMOD 2] := hmod)
    have htailCountEven : Even ((i.val - 1) - (j.val + 1)) := by
      rcases hiEven with ⟨d, hd⟩
      rcases hjEven with ⟨s, hs⟩
      refine ⟨d - s - 1, ?_⟩
      omega
    have htailCountZero : Int.ModEq 2
        ((((i.val - 1) - (j.val + 1) : Nat) : Int)) 0 := by
      rcases htailCountEven with ⟨d, hd⟩
      rw [Int.modEq_iff_dvd]
      refine ⟨-(d : Int), ?_⟩
      omega
    have hreference : Int.ModEq 2
        (T + ((((i.val - 1) - (j.val + 1) : Nat) : Int) *
          c.order j.succ)) T := by
      have hzero := htailCountZero.mul_right (c.order j.succ)
      simpa only [zero_mul, add_zero] using (Int.ModEq.rfl.add hzero)
    exact htail.trans hreference

end BONG.GoodBONG

end Bong
