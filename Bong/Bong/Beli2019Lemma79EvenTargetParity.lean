/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72TypeICanonical
import Bong.Bong.Beli2019Lemma79ThirdPrefixParity
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 7.9(ii), case 3: target-prefix parity

The exceptional nonintegral-alpha branch uses prefixes of lengths `i + 1`
and `i - 1`.  Their canonical congruences have odd total valuation.  This
file also records the unequal-length, signed form of the resulting zero
capped defect.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Odd valuation of a signed product of two arbitrary prefixes forces its
capped defect to be zero. -/
theorem truncatedPrefixDefect_eq_zero_of_odd_order_general
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (epsilon : Kˣ) (i j : Nat)
    (hodd : Odd (ordUnit K
      (epsilon * a.prefixProduct i * b.prefixProduct j))) :
    a.truncatedPrefixDefect b epsilon i j = 0 := by
  apply le_antisymm
  · calc
      a.truncatedPrefixDefect b epsilon i j ≤
          defectOrder (K := K)
            (epsilon * a.prefixProduct i * b.prefixProduct j) :=
        a.truncatedPrefixDefect_le_defect b epsilon i j
      _ = 0 := by
        unfold defectOrder
        rw [quadraticDefect_eq_zero_of_odd_ordUnit _ hodd]
        rfl
  · exact a.truncatedPrefixDefect_nonneg b epsilon i j

/-- The type-I target prefix of length `i + 1` and third prefix of length
`i - 1` have a signed product of odd valuation. -/
theorem lemma79_typeI_even_primaryProduct_odd_of_modEq
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : Nat) (hiEven : Even i) (hiTwo : 2 ≤ i)
    (hiBound : i + 1 ≤ n + 2) (T : Int)
    (hb : Int.ModEq 2 (b.orderSequence.prefixSum (i + 1))
      (((i + 1 : Nat) : Int) * (T + 1)))
    (hc : Int.ModEq 2 (c.orderSequence.prefixSum (i - 1))
      (((i - 1 : Nat) : Int) * T)) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i + 1) *
      c.prefixProduct (i - 1))) := by
  have ordUnit_neg_eq (z : Kˣ) : ordUnit K (-z) = ordUnit K z := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    simpa using ord_neg K (z : K)
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hneg : ordUnit K (-1 : Kˣ) = 0 := by
    rw [ordUnit_neg_eq, hone]
  have horder : ordUnit K
        ((-1 : Kˣ) * b.prefixProduct (i + 1) *
          c.prefixProduct (i - 1)) =
      b.orderSequence.prefixSum (i + 1) +
        c.orderSequence.prefixSum (i - 1) := by
    rw [ordUnit_mul, ordUnit_mul, hneg, zero_add,
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i + 1) hiBound,
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i - 1) (Nat.le_trans (Nat.sub_le i 1) (by omega))]
  have hsum := hb.add hc
  have hreferenceOdd : Odd
      ((((i + 1 : Nat) : Int) * (T + 1)) +
        (((i - 1 : Nat) : Int) * T)) := by
    rcases hiEven with ⟨d, hd⟩
    have hdPos : 0 < d := by omega
    have hiAdd : i + 1 = 2 * d + 1 := by omega
    have hiSub : i - 1 = 2 * (d - 1) + 1 := by omega
    have hdCast : ((d - 1 : Nat) : Int) = (d : Int) - 1 := by
      omega
    refine ⟨2 * (d : Int) * T + d, ?_⟩
    rw [hiAdd, hiSub]
    push_cast
    rw [hdCast]
    ring
  have hreferenceOne : Int.ModEq 2
      ((((i + 1 : Nat) : Int) * (T + 1)) +
        (((i - 1 : Nat) : Int) * T)) 1 := by
    rcases hreferenceOdd with ⟨z, hz⟩
    rw [Int.modEq_iff_dvd]
    exact ⟨-z, by omega⟩
  have htotalOne := hsum.trans hreferenceOne
  rw [horder]
  rw [Int.modEq_iff_dvd] at htotalOne
  rcases htotalOne with ⟨z, hz⟩
  exact ⟨-z, by omega⟩

end BONG.GoodBONG

end Bong
