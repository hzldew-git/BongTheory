/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# He (2024): the dyadic discriminant--ramification criterion

This file supplies the concrete number-field arithmetic used in Section 8 of
Zilong He's *On classic n-universal quadratic forms over dyadic local fields*.
It proves that the field discriminant is odd exactly when every prime ideal
above two has ramification index one.

The proof combines mathlib's discriminant--unramifiedness criterion with its
characterization of unramified prime ideals by ramification index.  Thus this
part of the global argument is no longer retained as abstract arithmetic
proof data.
-/

namespace Bong

namespace HeClassic2024NumberField

open NumberField

/-- The number-field discriminant is odd. -/
def DiscriminantOdd (K : Type*) [Field K] [NumberField K] : Prop :=
  ¬ (2 : ℤ) ∣ NumberField.discr K

/-- A prime ideal of the ring of integers lies above the rational prime two. -/
def IsDyadicPrime (K : Type*) [Field K] [NumberField K]
    (P : Ideal (NumberField.RingOfIntegers K)) : Prop :=
  algebraMap ℤ (NumberField.RingOfIntegers K) 2 ∈ P

/-- The concrete discriminant--ramification equivalence used in He (2024),
Section 8. -/
theorem discriminantOdd_iff_forall_ramificationIdx_eq_one
    (K : Type*) [Field K] [NumberField K] :
    DiscriminantOdd K ↔
      ∀ (P : Ideal (NumberField.RingOfIntegers K)) (_ : P.IsPrime),
        IsDyadicPrime K P →
        P.ramificationIdx ℤ = 1 := by
  constructor
  · intro hOdd P hP hDyadic
    letI : P.IsPrime := hP
    have hUnramified : Algebra.IsUnramifiedAt ℤ P :=
      (NumberField.not_dvd_discr_iff_forall_mem
        K (NumberField.RingOfIntegers K) Int.prime_two).mp
          hOdd P hP hDyadic
    letI : Algebra.IsUnramifiedAt ℤ P := hUnramified
    exact Ideal.ramificationIdx_eq_one P ℤ
  · intro hIndex
    apply (NumberField.not_dvd_discr_iff_forall_mem
      K (NumberField.RingOfIntegers K) Int.prime_two).mpr
    intro P hP hDyadic
    letI : P.IsPrime := hP
    exact Ideal.ramificationIdx_eq_one_iff.mp
      (hIndex P hP hDyadic)

/-- Odd discriminant gives ramification index one at a specified dyadic
prime ideal. -/
theorem ramificationIdx_eq_one_of_discriminantOdd
    (K : Type*) [Field K] [NumberField K]
    (hOdd : DiscriminantOdd K)
    (P : Ideal (NumberField.RingOfIntegers K))
    (hP : P.IsPrime) (hDyadic : IsDyadicPrime K P) :
    P.ramificationIdx ℤ = 1 :=
  (discriminantOdd_iff_forall_ramificationIdx_eq_one K).mp
    hOdd P hP hDyadic

/-- If every dyadic prime ideal has ramification index one, then the
discriminant is odd. -/
theorem discriminantOdd_of_forall_ramificationIdx_eq_one
    (K : Type*) [Field K] [NumberField K]
    (hIndex : ∀ (P : Ideal (NumberField.RingOfIntegers K))
      (_ : P.IsPrime),
      IsDyadicPrime K P → P.ramificationIdx ℤ = 1) :
    DiscriminantOdd K :=
  (discriminantOdd_iff_forall_ramificationIdx_eq_one K).mpr hIndex

/-- An even discriminant produces a dyadic prime ideal whose ramification
index is not one. -/
theorem exists_dyadicPrime_ramificationIdx_ne_one_of_not_discriminantOdd
    (K : Type*) [Field K] [NumberField K]
    (hEven : ¬ DiscriminantOdd K) :
    ∃ P : Ideal (NumberField.RingOfIntegers K),
      P.IsPrime ∧ IsDyadicPrime K P ∧
      P.ramificationIdx ℤ ≠ 1 := by
  classical
  by_contra hExists
  apply hEven
  apply discriminantOdd_of_forall_ramificationIdx_eq_one K
  intro P hP hDyadic
  by_contra hNe
  exact hExists ⟨P, hP, hDyadic, hNe⟩

/-- Ramification indices at prime ideals of the ring of integers are
positive. -/
theorem ramificationIdx_pos
    (K : Type*) [Field K] [NumberField K]
    (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) :
    0 < P.ramificationIdx ℤ := by
  letI : P.IsPrime := hP
  exact Ideal.ramificationIdx_pos P ℤ

end HeClassic2024NumberField

end Bong
