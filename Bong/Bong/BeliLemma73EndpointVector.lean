/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma73EndpointApproximation
import Bong.Bong.BinaryAdmissibility

/-!
# The endpoint vector in Beli (2003), Lemma 7.3

For a ternary BONG, the product of its two adjacent parameters is the ratio
of the last and first values.  Scaling the first endpoint by a valuation unit
therefore turns the quadratic value of `s x₀ + x₂` into precisely the
quadratic-approximation error controlled by the parameter product defect.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The endpoint vector `s x₀ + x₂` in the local ternary block. -/
noncomputable def lemma73EndpointVector
    (b : BONG V q L 3) (s : Kˣ) : V :=
  (s : K) • b.ambientVector 0 + b.ambientVector 2

/-- The negative product of adjacent parameters is `-a₂/a₀`. -/
theorem coe_neg_adjacentParameterProduct
    (b : BONG V q L 3) :
    (((-(b.adjacentParameter 0 (by omega) *
          b.adjacentParameter 1 (by omega))) : Kˣ) : K) =
      -(b.value 2 / b.value 0) := by
  simp [adjacentParameter]

/-- Exact quadratic value of the endpoint vector. -/
@[simp]
theorem quadratic_lemma73EndpointVector
    (b : BONG V q L 3) (s : Kˣ) :
    q.quadratic (b.lemma73EndpointVector s) =
      b.value 2 *
        (1 - (s : K) ^ 2 /
          (((-(b.adjacentParameter 0 (by omega) *
            b.adjacentParameter 1 (by omega))) : Kˣ) : K)) := by
  rw [lemma73EndpointVector, q.quadratic_add, q.quadratic_smul]
  have horth : q.bilin (b.ambientVector 0) (b.ambientVector 2) = 0 := by
    exact (LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho)
      0 2 (by decide)
  rw [LinearMap.BilinForm.smul_left, horth]
  simp only [mul_zero, add_zero]
  rw [b.quadratic_ambientVector,
    b.quadratic_ambientVector, b.coe_neg_adjacentParameterProduct]
  field_simp [b.value_ne_zero]
  ring

/-- A weak approximation-depth bound gives the corresponding norm-order
bound for the endpoint vector. -/
theorem ord_quadratic_lemma73EndpointVector_ge
    (b : BONG V q L 3) (s : Kˣ) (R k : Int)
    (hR : b.order 2 = R)
    (herror : (k : WithTop Int) ≤
      ord K (1 - (s : K) ^ 2 /
        (((-(b.adjacentParameter 0 (by omega) *
          b.adjacentParameter 1 (by omega))) : Kˣ) : K))) :
    ((R + k : Int) : WithTop Int) ≤
      ord K (q.quadratic (b.lemma73EndpointVector s)) := by
  rw [b.quadratic_lemma73EndpointVector, ord_mul, ← b.coe_order, hR]
  simpa only [WithTop.coe_add, add_comm] using
    (add_le_add_left herror (R : WithTop Int))

/-- A strict approximation-depth bound gives the corresponding strict
norm-order bound for the endpoint vector. -/
theorem ord_quadratic_lemma73EndpointVector_gt
    (b : BONG V q L 3) (s : Kˣ) (R k : Int)
    (hR : b.order 2 = R)
    (herror : (k : WithTop Int) <
      ord K (1 - (s : K) ^ 2 /
        (((-(b.adjacentParameter 0 (by omega) *
          b.adjacentParameter 1 (by omega))) : Kˣ) : K))) :
    ((R + k : Int) : WithTop Int) <
      ord K (q.quadratic (b.lemma73EndpointVector s)) := by
  rw [b.quadratic_lemma73EndpointVector, ord_mul, ← b.coe_order, hR]
  simpa only [WithTop.coe_add] using
    (WithTop.add_lt_add_left
      (show (R : WithTop Int) ≠ ⊤ from WithTop.coe_ne_top) herror)

end BONG

end Bong
