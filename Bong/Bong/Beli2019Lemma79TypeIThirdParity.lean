/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79ThirdPrefixParity
import Bong.Bong.Beli2019Lemma79TypeIProfileAlpha

/-!
# Beli (2019), Lemma 7.9(ii): the type-I third-prefix parity

This file performs the parity calculation in case 4.  It combines the
target-prefix congruence from Lemma 7.2(i) with the comparison-prefix
congruence from Lemma 6.6(i).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The two prefix-sum congruences in case 4 force the product occurring in
the secondary candidate to have odd valuation. -/
theorem lemma79_typeI_thirdPrefix_odd_of_modEq
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : Nat) (hiOdd : Odd i) (hiTwo : 2 ≤ i)
    (hiBound : i + 2 ≤ n + 2)
    (T : Int)
    (hb : Int.ModEq 2 (b.orderSequence.prefixSum (i + 2))
      (((i + 2 : Nat) : Int) * (T + 1)))
    (hc : Int.ModEq 2 (c.orderSequence.prefixSum (i - 2))
      (((i - 2 : Nat) : Int) * T)) :
    Odd (ordUnit K ((1 : Kˣ) * b.prefixProduct (i + 2) *
      c.prefixProduct (i - 2))) := by
  have horder : ordUnit K
        ((1 : Kˣ) * b.prefixProduct (i + 2) *
          c.prefixProduct (i - 2)) =
      b.orderSequence.prefixSum (i + 2) +
        c.orderSequence.prefixSum (i - 2) := by
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    rw [ordUnit_mul, ordUnit_mul, hone, zero_add,
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i + 2) hiBound,
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i - 2) (by omega)]
  have hsum := hb.add hc
  have hreferenceOdd : Odd
      ((((i + 2 : Nat) : Int) * (T + 1)) +
        (((i - 2 : Nat) : Int) * T)) := by
    rcases hiOdd with ⟨d, hd⟩
    have hdPos : 0 < d := by omega
    have hiAdd : i + 2 = 2 * d + 3 := by omega
    have hiSub : i - 2 = 2 * (d - 1) + 1 := by omega
    have hdCast : ((d - 1 : Nat) : Int) = (d : Int) - 1 := by
      omega
    refine ⟨((2 * (d : Int) + 1) * T + d + 1), ?_⟩
    rw [hiAdd, hiSub]
    push_cast
    rw [hdCast]
    ring
  have hreferenceOne : Int.ModEq 2
      ((((i + 2 : Nat) : Int) * (T + 1)) +
        (((i - 2 : Nat) : Int) * T)) 1 := by
    rcases hreferenceOdd with ⟨z, hz⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-z, ?_⟩
    omega
  have htotalOne := hsum.trans hreferenceOne
  rw [horder]
  rw [Int.modEq_iff_dvd] at htotalOne
  rcases htotalOne with ⟨z, hz⟩
  exact ⟨-z, by omega⟩

end BONG.GoodBONG

end Bong
