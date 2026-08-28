/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectSharp

/-!
# Strict triangles for capped prefix defects

Beli repeatedly uses the square-class rule that, in a triangle of three
defects, if one side is strictly larger than a second side, then the second
and third sides agree.  The same rule holds for capped prefix defects.  The
proof below needs only the already proved three-lattice domination theorem.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {m n k : Nat}

/-- Strict triangle rule for capped prefix defects.  The hypotheses say that
the two multipliers have square one; the applications use only `1` and `-1`.

Writing
`X = d[epsilon a_i b_j]`, `Y = d[eta b_j c_l]`, and
`Z = d[epsilon eta a_i c_l]`, the three domination inequalities give
`min X Z <= Y` and `min Y Z <= X`.  Hence `X < Z` forces `X = Y`. -/
theorem truncatedPrefixDefect_eq_middle_of_lt_composite
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (k + 1)) (epsilon eta : Kˣ)
    (hepsilon : epsilon * epsilon = 1) (heta : eta * eta = 1)
    (i j l : Nat)
    (hstrict : a.truncatedPrefixDefect b epsilon i j <
      a.truncatedPrefixDefect c (epsilon * eta) i l) :
    a.truncatedPrefixDefect b epsilon i j =
      b.truncatedPrefixDefect c eta j l := by
  have hepsilonProduct : epsilon * (epsilon * eta) = eta := by
    rw [← mul_assoc, hepsilon, one_mul]
  have hetaProduct : eta * (epsilon * eta) = epsilon := by
    calc
      eta * (epsilon * eta) = epsilon * (eta * eta) := by ac_rfl
      _ = epsilon := by rw [heta, mul_one]
  have hxz :
      min (a.truncatedPrefixDefect b epsilon i j)
          (a.truncatedPrefixDefect c (epsilon * eta) i l) ≤
        b.truncatedPrefixDefect c eta j l := by
    have hdom := b.truncatedPrefixDefect_domination a c
      epsilon (epsilon * eta) j i l
    rw [← a.truncatedPrefixDefect_comm b epsilon i j,
      hepsilonProduct] at hdom
    exact hdom
  have hyz :
      min (b.truncatedPrefixDefect c eta j l)
          (a.truncatedPrefixDefect c (epsilon * eta) i l) ≤
        a.truncatedPrefixDefect b epsilon i j := by
    have hdom := b.truncatedPrefixDefect_domination c a
      eta (epsilon * eta) j l i
    rw [← a.truncatedPrefixDefect_comm c (epsilon * eta) i l,
      hetaProduct, ← a.truncatedPrefixDefect_comm b epsilon i j] at hdom
    exact hdom
  apply le_antisymm
  · simpa only [min_eq_left hstrict.le] using hxz
  · by_contra hnot
    have hxy : a.truncatedPrefixDefect b epsilon i j <
        b.truncatedPrefixDefect c eta j l := lt_of_not_ge hnot
    have hlt : a.truncatedPrefixDefect b epsilon i j <
        min (b.truncatedPrefixDefect c eta j l)
          (a.truncatedPrefixDefect c (epsilon * eta) i l) :=
      lt_min hxy hstrict
    exact (not_lt_of_ge hyz) hlt

/-- The sign pattern most often used in Section 4:
`d[-a_i b_j] < d[-a_i c_l]` implies
`d[-a_i b_j] = d[b_j c_l]`. -/
theorem truncatedPrefixDefect_neg_eq_pos_of_lt_neg
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (k + 1)) (i j l : Nat)
    (hstrict : a.truncatedPrefixDefect b (-1) i j <
      a.truncatedPrefixDefect c (-1) i l) :
    a.truncatedPrefixDefect b (-1) i j =
      b.truncatedPrefixDefect c 1 j l := by
  have hstrict' : a.truncatedPrefixDefect b (-1) i j <
      a.truncatedPrefixDefect c ((-1) * 1) i l := by
    simpa only [mul_one] using hstrict
  have h := a.truncatedPrefixDefect_eq_middle_of_lt_composite
    b c (-1) 1 (by simp) (by simp) i j l hstrict'
  exact h

/-- The all-negative triangle:
`d[-a_i b_j] < d[a_i c_l]` implies
`d[-a_i b_j] = d[-b_j c_l]`. -/
theorem truncatedPrefixDefect_neg_eq_neg_of_lt_pos
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (k + 1)) (i j l : Nat)
    (hstrict : a.truncatedPrefixDefect b (-1) i j <
      a.truncatedPrefixDefect c 1 i l) :
    a.truncatedPrefixDefect b (-1) i j =
      b.truncatedPrefixDefect c (-1) j l := by
  have hstrict' : a.truncatedPrefixDefect b (-1) i j <
      a.truncatedPrefixDefect c ((-1) * (-1)) i l := by
    simpa only [neg_mul_neg, one_mul] using hstrict
  have h := a.truncatedPrefixDefect_eq_middle_of_lt_composite
    b c (-1) (-1) (by simp) (by simp) i j l hstrict'
  exact h

end BONG.GoodBONG

end Bong
