/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIRight
import Bong.Bong.Beli2019PrefixChange

/-!
# Beli (2019), Lemma 7.9(i): the type-II terminal coordinate

Lemma 6.5 cannot be applied at the last coordinate because there is no next
source entry.  The paper's ambient-space convention supplies the replacement:
the complete value products of two BONG bases differ by a square, so their
total order sums have the same parity.  This rules out the only possible
failure of the direct terminal comparison.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Full order sums of BONGs in the same quadratic space are congruent
modulo two. -/
theorem fullPrefixSum_modEq
    (a : GoodBONG q L n) (b : GoodBONG q M n) :
    Int.ModEq 2 (a.orderSequence.prefixSum n)
      (b.orderSequence.prefixSum n) := by
  rcases BONG.exists_valueProduct_eq_mul_square
    a.toBONG b.toBONG with ⟨p, hp⟩
  have hvaluation := congrArg (ordUnit K) hp
  rw [ordUnit_mul, ordUnit_pow] at hvaluation
  have ha := a.ordUnit_prefixProduct_eq_orderSequence_prefixSum n le_rfl
  have hb := b.ordUnit_prefixProduct_eq_orderSequence_prefixSum n le_rfl
  rw [a.prefixProduct_eq_valueProduct_of_rank_le n le_rfl] at ha
  rw [b.prefixProduct_eq_valueProduct_of_rank_le n le_rfl] at hb
  rw [Int.modEq_iff_dvd]
  refine ⟨ordUnit K p, ?_⟩
  rw [← ha, ← hb]
  omega

/-- The hard type-II parity class at the final coordinate.  Here the
determinant-square parity replaces the unavailable next-coordinate instance
of Lemma 6.5. -/
theorem beli2019Lemma79_i_typeII_terminal
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hkTerminal : k + 1 = n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entry k (by omega) ≤
      c.orderSequence.entry k (by omega) := by
  have hk : k < n + 2 := by omega
  by_contra hnot
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    k hright hlast heven
  have hbCurrent : b.orderSequence.entryOrZero k = T + 1 := by
    rw [hcurrentBoundary, D.right_target]
  have hcCurrent : c.orderSequence.entryOrZero k ≤ T := by
    rw [b.orderSequence.entryOrZero_of_lt hk] at hbCurrent
    rw [c.orderSequence.entryOrZero_of_lt hk]
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
      T k hk hreferenceFirst hcCurrent
  let P := a.beli2019Lemma72_ii b D hfirst
  have haParity := P.source_after (k + 1) (by
    have hseparated := D.outer.transition.separated
    omega) (by omega)
  have hfullParity := a.fullPrefixSum_modEq c
  have hacParity : Int.ModEq 2
      (a.orderSequence.prefixSum (k + 1))
      (c.orderSequence.prefixSum (k + 1)) := by
    simpa only [hkTerminal] using hfullParity
  let X : Int := (((k + 1 : Nat) : Int) * T)
  have hcontradiction : Int.ModEq 2 (X - 1) X := by
    have ha : Int.ModEq 2
        (a.orderSequence.prefixSum (k + 1)) (X - 1) := by
      simpa only [P, X] using haParity
    have hc : Int.ModEq 2
        (c.orderSequence.prefixSum (k + 1)) X := by
      simpa only [X] using hcParity
    exact ha.symm.trans (hacParity.trans hc)
  rw [Int.modEq_iff_dvd] at hcontradiction
  rcases hcontradiction with ⟨d, hd⟩
  omega

end BONG.GoodBONG

end Bong
