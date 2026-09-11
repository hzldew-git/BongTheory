/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Invariants
import Bong.Lattice.Universality
import Bong.QuadraticSpace.HyperbolicPlane
import Bong.QuadraticSpace.OrthogonalSum

/-!
# He--Hu's criterion for n-universality: statement layer

This file encodes the right-hand side of Theorem 1.1 in Zilong He and
Yong Hu, *On n-universal quadratic forms over dyadic local fields*,
Sci. China Math. 67 (2024), 1481--1506.

The source uses one-based indices.  The declarations below use Lean's
zero-based `Fin` indices, with named helpers that expose the translation.
No equivalence with `IsNUniversal` is asserted in this statement-layer file.
That equivalence is the proof obligation for the theorem layer.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Membership in the paper's even interval `[lo, hi]_E`. -/
def HeHuInEvenInterval (x lo hi : Int) : Prop :=
  lo ≤ x ∧ x ≤ hi ∧ Even x

/-- The paper's alternative `x ∈ {0,1}`. -/
def HeHuZeroOrOne (x : Int) : Prop := x = 0 ∨ x = 1

/-- `R_i`, with the paper's one-based index `i` made explicit. -/
noncomputable def heHuOrder {m : Nat} (a : GoodBONG q L m)
    (i : Nat) (hi : 1 ≤ i) (him : i ≤ m) : Int :=
  a.order ⟨i - 1, by omega⟩

/-- `d(-a_j a_{j+1})` at a zero-based adjacent index. -/
noncomputable def heHuAdjacentDefectAt {m : Nat} (a : GoodBONG q L m)
    (j : Fin (m - 1)) : WithTop ℚ :=
  defectOrder (K := K)
    (-(a.valueUnit ⟨j.1, by omega⟩ *
      a.valueUnit ⟨j.1 + 1, by omega⟩))

/-- The order immediately after a zero-based adjacent index. -/
noncomputable def heHuOrderAfterAdjacent {m : Nat} (a : GoodBONG q L m)
    (j : Fin (m - 1)) : Int :=
  a.order ⟨j.1 + 1, by omega⟩

/-- `d(-a_j a_{j+1})`, with the paper's one-based adjacent index `j`. -/
noncomputable def heHuAdjacentDefect {m : Nat} (a : GoodBONG q L m)
    (j : Nat) (hj : 1 ≤ j) (hjm : j < m) : WithTop ℚ :=
  a.heHuAdjacentDefectAt ⟨j - 1, by omega⟩

/-- The defect of the product `a_1 ... a_i`. -/
noncomputable def heHuPrefixDefect {m : Nat} (a : GoodBONG q L m)
    (i : Nat) : WithTop ℚ :=
  defectOrder (K := K) (a.prefixProduct i)

/-- The common alternating order profile in Theorem 1.1(i). -/
def HeHuAlternatingInitialOrders {m : Nat} (a : GoodBONG q L m)
    (n : Nat) (hm : n + 3 ≤ m) : Prop :=
  (∀ i : Fin n, Odd (i.1 + 1) →
      a.order ⟨i.1, by omega⟩ = 0) ∧
    (∀ i : Fin n, Even (i.1 + 1) →
      a.order ⟨i.1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)))

/-- Theorem 1.1(ii), the even-`n` branch of the stable-rank criterion. -/
structure HeHuEvenConditions {m : Nat} (a : GoodBONG q L m)
    (n : Nat) (hm : n + 3 ≤ m) : Prop where
  parity : Even n
  order_n1 : a.order ⟨n, by omega⟩ = 0
  order_n2_range :
    HeHuInEvenInterval (a.order ⟨n + 1, by omega⟩)
        (-(2 * (ramificationIndex K : Int))) 0 ∨
      a.order ⟨n + 1, by omega⟩ = 1
  middle_even_branch :
    HeHuInEvenInterval (a.order ⟨n + 1, by omega⟩)
        (2 - 2 * (ramificationIndex K : Int)) 0 →
      ((a.order ⟨n + 1, by omega⟩ =
          2 - 2 * (ramificationIndex K : Int) →
        (a.heHuAdjacentDefectAt ⟨n, by omega⟩ =
            ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) ∨
          HeHuZeroOrOne (a.order ⟨n + 2, by omega⟩))) ∧
      (a.order ⟨n + 1, by omega⟩ ≠
          2 - 2 * (ramificationIndex K : Int) →
        ∃ j : Fin (m - 1), n ≤ j.1 ∧
          a.heHuAdjacentDefectAt j =
            ((1 - a.heHuOrderAfterAdjacent j : Int) : ℚ)))
  large_last_gap :
    2 * (ramificationIndex K : Int) <
        a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ →
      a.order ⟨n + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) ∧
        ((4 ≤ n ∨
            (n = 2 ∧ a.heHuPrefixDefect 4 =
              ((2 * (ramificationIndex K : Int) : Int) : ℚ))) →
          a.order ⟨n + 2, by omega⟩ = 1)

/-- Theorem 1.1(iii), the odd-`n` branch of the stable-rank criterion. -/
structure HeHuOddConditions {m : Nat} (a : GoodBONG q L m)
    (n : Nat) (hm : n + 3 ≤ m) : Prop where
  parity : Odd n
  order_n1_range :
    HeHuInEvenInterval (a.order ⟨n, by omega⟩)
        (-(2 * (ramificationIndex K : Int))) 0 ∨
      a.order ⟨n, by omega⟩ = 1
  middle_even_branch :
    HeHuInEvenInterval (a.order ⟨n, by omega⟩)
        (4 - 2 * (ramificationIndex K : Int)) 0 →
      ∃ j : Fin (m - 1), n - 1 ≤ j.1 ∧
        a.heHuAdjacentDefectAt j =
          ((1 - a.heHuOrderAfterAdjacent j : Int) : ℚ)
  upper_branch :
    (a.order ⟨n, by omega⟩ = 1 ∨
        (a.order ⟨n, by omega⟩ ≠
            -(2 * (ramificationIndex K : Int)) ∧
          1 < a.order ⟨n + 1, by omega⟩)) →
      ((Even (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) →
        (a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ ≤
            2 * (ramificationIndex K : Int) - 2 ∨
          ∃ j : Fin (m - 1), n + 1 ≤ j.1 ∧
            a.heHuAdjacentDefectAt j ≤
              ((2 * (ramificationIndex K : Int) +
                a.order ⟨n, by omega⟩ - a.heHuOrderAfterAdjacent j - 1 : Int) : ℚ))) ∧
      (Odd (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) →
        (a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ ≤
            2 * (ramificationIndex K : Int) ∨
          ∃ j : Fin (m - 1), n + 1 ≤ j.1 ∧
            a.heHuAdjacentDefectAt j ≤
              ((2 * (ramificationIndex K : Int) +
                a.order ⟨n, by omega⟩ - a.heHuOrderAfterAdjacent j : Int) : ℚ))))
  bottom_branch :
    a.order ⟨n, by omega⟩ = -(2 * (ramificationIndex K : Int)) →
      HeHuZeroOrOne (a.order ⟨n + 1, by omega⟩)
  last_gap :
    a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)

/-- The `m ≥ n+3` alternative of Theorem 1.1. -/
structure HeHuStableConditions {m : Nat} (a : GoodBONG q L m)
    (n : Nat) (hm : n + 3 ≤ m) : Prop where
  initialOrders : a.HeHuAlternatingInitialOrders n hm
  parityBranch : HeHuEvenConditions a n hm ∨ HeHuOddConditions a n hm

/-- The exceptional `m=n+2=4` alternative in Theorem 1.1. -/
def HeHuExceptionalQuaternaryConditions {m : Nat}
    (a : GoodBONG q L m) (n : Nat) : Prop :=
  m = 4 ∧ n = 2 ∧
    q.IsIsometric
      ((QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
        (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ))) ∧
    ∀ hm : m = 4,
      a.order ⟨0, by omega⟩ = 0 ∧
      a.order ⟨2, by omega⟩ = 0 ∧
      a.order ⟨1, by omega⟩ + 2 * (ramificationIndex K : Int) = 0 ∧
      a.order ⟨3, by omega⟩ + 2 * (ramificationIndex K : Int) = 0

/-- The complete published right-hand side of He--Hu, Theorem 1.1. -/
def HeHuTheorem11Conditions {m : Nat} (a : GoodBONG q L m)
    (n : Nat) : Prop :=
  a.HeHuExceptionalQuaternaryConditions n ∨
    ∃ hm : n + 3 ≤ m, a.HeHuStableConditions n hm

/-- The exact theorem proposition whose proof is the He--Hu Theorem 1.1
formalization target.  This is a definition, not a proved theorem. -/
def HeHuTheorem11Statement {m : Nat} (a : GoodBONG q L m)
    (n : Nat) (_hn : 2 ≤ n) (_hL : Lattice.IsIntegral q L) : Prop :=
  Lattice.IsNUniversal.{u, v, w} q L n ↔ a.HeHuTheorem11Conditions n

end BONG.GoodBONG

end Bong
