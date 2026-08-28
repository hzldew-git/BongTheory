/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIGamma
import Bong.Bong.Beli2019Lemma79DefectOneCap

/-!
# Beli (2019), Lemma 7.9(ii), case 5: prefix parity

Inside the type-II core the target prefix has order congruent to `iT` by
Lemma 7.2(ii).  If the comparison order at the current boundary is at most
`T`, Lemma 6.6 gives the same congruence for the comparison prefix.  Their
product therefore has even order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The type-II core comparison product has even valuation. -/
theorem beli2019Lemma79_typeII_core_prefix_even
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : i.val < D.outer.transition.firstTwo)
    (hcPrevious : c.orderSequence.entryOrZero (i.val - 1) ≤
      b.orderSequence.entryOrZero D.outer.transition.lastZero) :
    Even (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)) := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  let k := i.val - 1
  have hkBound : k < n + 2 := by
    have := i.lt_large
    simp only [k]
    omega
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hleftValue := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
  have hreferenceFirst : T ≤ c.orderSequence.entryOrZero 0 := by
    simpa only [T, hleftValue] using hfirstOrder
  have hcParity :=
    c.prefixSum_modEq_mul_of_current_le_reference_le_first
      T k hkBound hreferenceFirst (by
        simpa only [T, k] using hcPrevious)
  let P := a.beli2019Lemma72_ii b D hfirst
  have hbParity := P.target_before i.val hright
  have hcombined : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val) := by
    have hcParity' : Int.ModEq 2 (c.orderSequence.prefixSum i.val)
        ((i.val : Int) * T) := by
      simpa only [k, Nat.sub_add_cancel i.pos] using hcParity
    exact hbParity.trans hcParity'.symm
  exact b.comparisonPrefixProduct_order_even_of_prefixSum_modEq
    c i.val i.lt_large.le i.lt_large.le hcombined

end BONG.GoodBONG

end Bong
