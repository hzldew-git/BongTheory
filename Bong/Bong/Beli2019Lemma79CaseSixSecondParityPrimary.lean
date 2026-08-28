/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixFirstParity

/-!
# Beli (2019), Lemma 7.9(ii), case 6: second-parity primary bound

In the second parity branch, congruent current orders preserve the odd
valuation of the comparison prefix when the two prefix lengths are shifted
by one.  The primary defect then vanishes, and a nonpositive current shift
proves condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Odd comparison-prefix order is preserved by replacing the equal-length
prefixes with lengths `i + 1` and `i - 1`, provided the exchanged entries
have the same parity. -/
theorem caseSix_primaryProduct_odd_of_prefix_odd_and_orders_modEq
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hprefix : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1))) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  have hcPrefix : c.orderSequence.prefixSum i.val =
      c.orderSequence.prefixSum (i.val - 1) +
        c.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [Nat.sub_add_cancel i.pos] using
      c.orderSequence.prefixSum_succ (i.val - 1)
  have hbaseOrder :
      ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val) =
        b.orderSequence.prefixSum i.val +
          c.orderSequence.prefixSum (i.val - 1) +
            c.orderSequence.entryOrZero (i.val - 1) := by
    rw [ordUnit_mul,
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        i.val i.lt_large.le,
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        i.val i.lt_large.le,
      hcPrefix]
    ring
  have hiNextLE : i.val + 1 ≤ n + 2 :=
    Nat.succ_le_of_lt i.lt_large
  have hiPreviousLE : i.val - 1 ≤ n + 2 :=
    (Nat.sub_le i.val 1).trans i.lt_large.le
  have hshiftedOrder :
      ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
          c.prefixProduct (i.val - 1)) =
        b.orderSequence.prefixSum i.val +
          c.orderSequence.prefixSum (i.val - 1) +
            b.orderSequence.entryOrZero i.val := by
    rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i.val + 1) hiNextLE,
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i.val - 1) hiPreviousLE,
      b.orderSequence.prefixSum_succ]
    ring
  rw [hbaseOrder] at hprefix
  rw [hshiftedOrder]
  rcases hprefix with ⟨z, hz⟩
  rw [Int.modEq_iff_dvd] at horders
  rcases horders with ⟨d, hd⟩
  exact ⟨z - d, by omega⟩

/-- Once the shifted primary product has odd order and its order coefficient
is nonpositive, the primary candidate proves condition 2.1(ii). -/
theorem lemma79_caseSix_secondParity_of_primaryProduct_odd_and_current_le
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hprimaryOdd : Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1))))
    (hcurrent : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hzero := b.truncatedPrefixDefect_eq_zero_of_odd_order_general
    c (-1) (i.val + 1) (i.val - 1) hprimaryOdd
  have hiPrevious : i.val - 1 < n + 2 :=
    lt_of_le_of_lt (Nat.sub_le i.val 1) i.lt_large
  have hcurrentOrder : b.order ⟨i.val, i.lt_large⟩ ≤
      c.order ⟨i.val - 1, hiPrevious⟩ := by
    simpa only [
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.lt_large,
      BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
      orderSequence_at] using hcurrent
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
      b.representationAlpha_le_primary c i
    _ = ((((b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) : WithTop ℚ)) := by
      unfold representationPrimaryDefect
      rw [hzero, add_zero]
    _ ≤ 0 := by
      norm_cast
      exact_mod_cast sub_nonpos.mpr hcurrentOrder
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
      b.truncatedPrefixDefect_nonneg c 1 i.val i.val

/-- The previous two facts packaged in the form used by the first subcase
of the paper's second parity branch. -/
theorem lemma79_caseSix_secondParity_of_prefix_odd_orders_modEq_current_le
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hprefix : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)))
    (hcurrent : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  apply lemma79_caseSix_secondParity_of_primaryProduct_odd_and_current_le
    b c i
  · exact caseSix_primaryProduct_odd_of_prefix_odd_and_orders_modEq
      b c i hprefix horders
  · exact hcurrent

end BONG.GoodBONG

end Bong
