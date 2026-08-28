/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanCoordinates
import Bong.Bong.Beli2009WeightIdealProof

/-!
# Signed norm generators in Beli (2009)

O'Meara 93:5 shows that the negative of a scalar norm generator is again a
norm generator.  This file packages that proved fact in the two-sign form
used by Beli (2009), Lemma 2.13(iii).
-/

namespace Bong

open Dyadic

universe u v

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}

/-- A scalar norm generator automatically supplies both signs required in
Beli (2009), Lemma 2.13(iii). -/
theorem IsNormGeneratorValue.bothSigns
    (ha : IsNormGeneratorValue q L a) :
    BothSignsNormGeneratorValue q L a :=
  ⟨ha, ha.neg⟩

/-- Multiplication by the square of a valuation unit preserves a scalar norm
generator.  This is the integral form of the square-class ambiguity in the
choice of the clearing factor in Beli's Lemma 2.13(iii). -/
theorem IsNormGeneratorValue.mul_square_of_ordUnit_zero
    (ha : IsNormGeneratorValue q L a) (s : Kˣ)
    (hs : ordUnit K s = 0) :
    IsNormGeneratorValue q L (a * s ^ 2) := by
  have hsIntegral : (s : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit, hs]
    norm_num
  let sO : IntegerRing K := ⟨s, hsIntegral⟩
  constructor
  · have hmem := integralSquare_mul_mem_normGroupSet q L ha.1 sO
    change (a : K) * (s : K) ^ 2 ∈ normGroupSet q L
    simpa only [sO, mul_comm] using hmem
  · rw [ha.2]
    apply (principalIdeal_eq_iff_ordUnit_eq a (a * s ^ 2)).2
    rw [ordUnit_mul, ordUnit_pow, hs]
    omega

end Lattice

end Bong
