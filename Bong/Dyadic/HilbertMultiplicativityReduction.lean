/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.HilbertSymbol
import Mathlib.GroupTheory.Index

/-!
# Reducing Hilbert-symbol multiplicativity to the norm-index theorem

For a fixed quadratic parameter `a`, the values represented by
`x^2 - a * y^2` already form a subgroup of `Kˣ`.  Consequently every case
of Hilbert-symbol multiplicativity is elementary except the product of two
non-norms.  This file records the exact remaining local-field statement:
the complement of the quadratic norm subgroup is a single coset.

This reduction is purely algebraic.  It introduces no law interface and is
intended as the endpoint for the O'Meara 63:11--63:13 norm-index proof.
-/

namespace Bong.Dyadic

variable {K : Type*} [Field K]

/-- Multiplication by a norm preserves and reflects membership in the
quadratic norm group. -/
theorem isQuadraticNorm_mul_iff_of_left
    {a b c : Kˣ} (hb : IsQuadraticNorm K a b) :
    IsQuadraticNorm K a (b * c) ↔ IsQuadraticNorm K a c := by
  constructor
  · intro hbc
    have h := IsQuadraticNorm.mul K hbc (IsQuadraticNorm.inv K hb)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  · intro hc
    exact IsQuadraticNorm.mul K hb hc

/-- Right-handed form of `isQuadraticNorm_mul_iff_of_left`. -/
theorem isQuadraticNorm_mul_iff_of_right
    {a b c : Kˣ} (hc : IsQuadraticNorm K a c) :
    IsQuadraticNorm K a (b * c) ↔ IsQuadraticNorm K a b := by
  rw [mul_comm]
  exact isQuadraticNorm_mul_iff_of_left hc

/-- The only non-formal input needed for multiplicativity is that the
product of two elements outside a fixed quadratic norm subgroup is a norm.
-/
theorem hilbertSymbol_map_mul_right_of_nonnorm_mul_closed
    (hclosed : ∀ (a b c : Kˣ),
      ¬IsQuadraticNorm K a b →
      ¬IsQuadraticNorm K a c →
      IsQuadraticNorm K a (b * c))
    (a b c : Kˣ) :
    hilbertSymbol K a (b * c) =
      hilbertSymbol K a b * hilbertSymbol K a c := by
  by_cases hb : IsQuadraticNorm K a b
  · have hbc : IsQuadraticNorm K a (b * c) ↔ IsQuadraticNorm K a c :=
      isQuadraticNorm_mul_iff_of_left hb
    by_cases hc : IsQuadraticNorm K a c
    · rw [(hilbertSymbol_eq_one_iff K a (b * c)).2 (hbc.mpr hc),
        (hilbertSymbol_eq_one_iff K a b).2 hb,
        (hilbertSymbol_eq_one_iff K a c).2 hc]
      norm_num
    · rw [(hilbertSymbol_eq_neg_one_iff K a (b * c)).2
          (fun h ↦ hc (hbc.mp h)),
        (hilbertSymbol_eq_one_iff K a b).2 hb,
        (hilbertSymbol_eq_neg_one_iff K a c).2 hc]
      norm_num
  · by_cases hc : IsQuadraticNorm K a c
    · have hbc : IsQuadraticNorm K a (b * c) ↔ IsQuadraticNorm K a b :=
        isQuadraticNorm_mul_iff_of_right hc
      rw [(hilbertSymbol_eq_neg_one_iff K a (b * c)).2
          (fun h ↦ hb (hbc.mp h)),
        (hilbertSymbol_eq_neg_one_iff K a b).2 hb,
        (hilbertSymbol_eq_one_iff K a c).2 hc]
      norm_num
    · rw [(hilbertSymbol_eq_one_iff K a (b * c)).2 (hclosed a b c hb hc),
        (hilbertSymbol_eq_neg_one_iff K a b).2 hb,
        (hilbertSymbol_eq_neg_one_iff K a c).2 hc]
      norm_num

/-- Conversely, multiplicativity forces the product of two non-norms to be
a norm.  Thus this closure statement is exactly, rather than merely
sufficient for, the missing Hilbert-symbol law. -/
theorem nonnorm_mul_closed_of_hilbertSymbol_map_mul_right
    (hmul : ∀ (a b c : Kˣ),
      hilbertSymbol K a (b * c) =
        hilbertSymbol K a b * hilbertSymbol K a c)
    (a b c : Kˣ)
    (hb : ¬IsQuadraticNorm K a b)
    (hc : ¬IsQuadraticNorm K a c) :
    IsQuadraticNorm K a (b * c) := by
  rw [← hilbertSymbol_eq_one_iff]
  rw [hmul, (hilbertSymbol_eq_neg_one_iff K a b).2 hb,
    (hilbertSymbol_eq_neg_one_iff K a c).2 hc]
  norm_num

/-- Exact logical equivalence between Hilbert-symbol multiplicativity and
the index-at-most-two closure property of every quadratic norm subgroup. -/
theorem hilbertSymbol_map_mul_right_iff_nonnorm_mul_closed :
    (∀ (a b c : Kˣ),
      hilbertSymbol K a (b * c) =
        hilbertSymbol K a b * hilbertSymbol K a c) ↔
    (∀ (a b c : Kˣ),
      ¬IsQuadraticNorm K a b →
      ¬IsQuadraticNorm K a c →
      IsQuadraticNorm K a (b * c)) := by
  constructor
  · exact nonnorm_mul_closed_of_hilbertSymbol_map_mul_right
  · intro hclosed
    exact hilbertSymbol_map_mul_right_of_nonnorm_mul_closed hclosed

end Bong.Dyadic
