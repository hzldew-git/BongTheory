/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorMonotonicity
import Bong.Bong.Properties

/-!
# Integral square shifts with a fixed normalized BONG value

If two BONG entries have the same valuation-unit factor, and their orders are
ordered and congruent modulo two, the second value is obtained from the first
by an integral uniformizer square.  This is the scalar calculation used twice
in Beli (2019), Lemma 9.7(i).
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- An ordered, parity-compatible change of order with unchanged normalized
value is multiplication by the square of an integral uniformizer power. -/
theorem exists_integralSquareShift_of_normalizedValue_eq
    (a : BONG V q L n) (b : BONG W r M n) (i : Fin n)
    (hle : a.order i ≤ b.order i)
    (hmod : Int.ModEq 2 (b.order i) (a.order i))
    (hnormalized : a.normalizedValue i = b.normalizedValue i) :
    ∃ s : Kˣ, (s : K) ∈ IntegerRing K ∧
      a.valueUnit i * s ^ 2 = b.valueUnit i := by
  rcases exists_nat_eq_add_two_mul_of_le_modEq_two hle hmod with
    ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K (k : Int)
  have haValue :
      uniformizerPowerUnit K (a.order i) * a.normalizedValue i =
        a.valueUnit i := by
    simpa [uniformizerPowerUnit] using
      a.uniformizer_zpow_mul_normalizedValue i
  refine ⟨s, uniformizerPowerUnit_nat_mem_integerRing k, ?_⟩
  calc
    a.valueUnit i * s ^ 2 =
        (uniformizerPowerUnit K (a.order i) * a.normalizedValue i) *
          uniformizerPowerUnit K (k : Int) ^ 2 := by
      rw [haValue]
    _ = uniformizerPowerUnit K
          (a.order i + 2 * (k : Int)) * a.normalizedValue i := by
      exact uniformizerParameter_mul_square
        (a.normalizedValue i) (a.order i) k
    _ = uniformizerPowerUnit K (b.order i) * b.normalizedValue i := by
      rw [← hk, hnormalized]
    _ = b.valueUnit i := by
      simpa [uniformizerPowerUnit] using
        b.uniformizer_zpow_mul_normalizedValue i

/-- Field-valued form of
`exists_integralSquareShift_of_normalizedValue_eq`, oriented as in the
second-value formula for `binaryIntegralSquareSubBONG`. -/
theorem exists_integralSquareShift_value_of_normalizedValue_eq
    (a : BONG V q L n) (b : BONG W r M n) (i : Fin n)
    (hle : a.order i ≤ b.order i)
    (hmod : Int.ModEq 2 (b.order i) (a.order i))
    (hnormalized : a.normalizedValue i = b.normalizedValue i) :
    ∃ s : Kˣ, (s : K) ∈ IntegerRing K ∧
      (s : K) ^ 2 * a.value i = b.value i := by
  rcases a.exists_integralSquareShift_of_normalizedValue_eq b i hle hmod
      hnormalized with ⟨s, hs, hvalue⟩
  refine ⟨s, hs, ?_⟩
  have hcoe := congrArg (fun z : Kˣ => (z : K)) hvalue
  simpa [mul_comm] using hcoe

end BONG

end Bong
