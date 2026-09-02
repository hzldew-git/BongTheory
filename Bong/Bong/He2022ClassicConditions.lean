/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Invariants
import Bong.Lattice.ClassicIntegrality

/-!
# He's criterion for classic n-universality: statement layer

This file transcribes Theorem 1.1 of Zilong He, *On classic n-universal
quadratic forms over dyadic local fields*, manuscripta math. 174 (2024),
559--595. The publisher version of record is the semantic authority.

Paper indices are one based; bounded Lean indices are zero based. No proof of
the main equivalence is asserted in this file.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The alternative `x in {0,1}` used throughout He, Theorem 1.1. -/
def HeClassicZeroOrOne (x : Int) : Prop := x = 0 ∨ x = 1

/-- `d(-a_j a_{j+1})` at a zero-based adjacent index. -/
noncomputable def heClassicAdjacentDefectAt {m : Nat}
    (a : GoodBONG q L m) (j : Fin (m - 1)) : WithTop ℚ :=
  defectOrder (K := K)
    (-(a.valueUnit ⟨j.1, by omega⟩ *
      a.valueUnit ⟨j.1 + 1, by omega⟩))

/-- The order after a zero-based adjacent index: Lean index `j` represents
paper index `j+1`, and this returns the paper's `R_{j+2}`. -/
noncomputable def heClassicOrderAfterAdjacent {m : Nat}
    (a : GoodBONG q L m) (j : Fin (m - 1)) : Int :=
  a.order ⟨j.1 + 1, by omega⟩

/-- The signed prefix defect `d((-1)^s a_1 ... a_r)`. -/
noncomputable def heClassicSignedPrefixDefect {m : Nat}
    (a : GoodBONG q L m) (s r : Nat) : WithTop ℚ :=
  defectOrder (K := K) ((-1 : Kˣ) ^ s * a.prefixProduct r)

/-- Theorem 1.1(ii), for even `n`. -/
structure HeClassicEvenConditions {m : Nat} (a : GoodBONG q L m)
    (n : Nat) (hm : n + 3 ≤ m) : Prop where
  parity : Even n
  order_n1 : a.order ⟨n, by omega⟩ = 0
  order_n2 : HeClassicZeroOrOne (a.order ⟨n + 1, by omega⟩)
  zero_branch :
    a.order ⟨n + 1, by omega⟩ = 0 →
      ((a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) =
          (1 : ℚ) ∨
        HeClassicZeroOrOne (a.order ⟨n + 2, by omega⟩)) ∧
      ((1 : Nat) < ramificationIndex K ∧
          a.order ⟨n + 1, by omega⟩ = 0 ∧
          a.order ⟨n + 2, by omega⟩ = 0 ∧
          (1 : ℚ) <
            a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) →
        ∃ j : Fin (m - 1),
          a.heClassicAdjacentDefectAt j =
            ((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ)))
  last_gap :
    a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)

/-- Theorem 1.1(iii), for odd `n`. -/
structure HeClassicOddConditions {m : Nat} (a : GoodBONG q L m)
    (n : Nat) (hm : n + 3 ≤ m) : Prop where
  parity : Odd n
  order_n1 : HeClassicZeroOrOne (a.order ⟨n, by omega⟩)
  zero_branch :
    a.order ⟨n, by omega⟩ = 0 →
      ((a.heClassicSignedPrefixDefect ((n + 1) / 2) (n + 1) =
          (1 : ℚ) ∨
        HeClassicZeroOrOne (a.order ⟨n + 1, by omega⟩)) ∧
      ((1 : Nat) < ramificationIndex K ∧
          a.order ⟨n, by omega⟩ = 0 ∧
          a.order ⟨n + 1, by omega⟩ = 0 ∧
          (1 : ℚ) <
            a.heClassicSignedPrefixDefect ((n + 1) / 2) (n + 1) →
        ∃ j : Fin (m - 1),
          a.heClassicAdjacentDefectAt j =
            ((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ)))
  upper_branch :
    (a.order ⟨n, by omega⟩ = 1 ∨
        1 < a.order ⟨n + 1, by omega⟩) →
      ((Even (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) →
        (a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ ≤
            2 * (ramificationIndex K : Int) - 2 ∨
          ∃ j : Fin (m - 1), n + 1 ≤ j.1 ∧
            a.heClassicAdjacentDefectAt j ≤
              ((2 * (ramificationIndex K : Int) +
                a.order ⟨n, by omega⟩ -
                a.heClassicOrderAfterAdjacent j - 1 : Int) : ℚ))) ∧
      (Odd (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) →
        (a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ ≤
            2 * (ramificationIndex K : Int) ∨
          ∃ j : Fin (m - 1), n + 1 ≤ j.1 ∧
            a.heClassicAdjacentDefectAt j ≤
              ((2 * (ramificationIndex K : Int) +
                a.order ⟨n, by omega⟩ -
                a.heClassicOrderAfterAdjacent j : Int) : ℚ))))
  last_gap :
    a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)

/-- The complete right-hand side of He, Theorem 1.1. -/
structure HeClassicTheorem11Conditions {m : Nat} (a : GoodBONG q L m)
    (n : Nat) : Prop where
  rank_bound : n + 3 ≤ m
  initial_orders : ∀ i : Fin n, a.order ⟨i.1, by omega⟩ = 0
  parity_branch :
    HeClassicEvenConditions a n rank_bound ∨
      HeClassicOddConditions a n rank_bound

/-- The exact publisher theorem proposition. This is a definition, not a
proved theorem. -/
def HeClassicTheorem11Statement {m : Nat} (a : GoodBONG q L m)
    (n : Nat) (_hn : 2 ≤ n) (_hL : Lattice.IsClassicIntegral q L) : Prop :=
  Lattice.IsClassicNUniversal.{u, v, w} q L n ↔
    HeClassicTheorem11Conditions a n

end BONG.GoodBONG

end Bong
