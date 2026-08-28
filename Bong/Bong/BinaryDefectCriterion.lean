/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryRealization
import Bong.Dyadic.AbsoluteQuadraticDefect

/-!
# Beli's defect criterion for binary BONG parameters

This file identifies the operational integrality condition used by the
explicit binary model with the two cases in Beli 2003, Lemma 3.5.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The absolute quadratic defect of `a` is integral when `a` has a square
approximation with integral error. -/
def HasIntegralQuadraticDefect (a : Kˣ) : Prop :=
  ∃ x : K, (a : K) - x ^ 2 ∈ IntegerRing K

/-- The two cases in Beli 2003, Lemma 3.5. -/
def IsBeliBinaryParameterAdmissible (a : Kˣ) : Prop :=
  (¬IsSquare (-a) ∧ HasIntegralQuadraticDefect (-a)) ∨
    (IsSquare (-a) ∧
      -(2 * (ramificationIndex K : Int)) ≤ ordUnit K a)

/-- Every operationally admissible parameter has order at least `-2e`. -/
theorem IsBinaryParameterAdmissible.ordUnit_ge_neg_two_mul_e
    {a : Kˣ} (ha : IsBinaryParameterAdmissible a) :
    -(2 * (ramificationIndex K : Int)) ≤ ordUnit K a := by
  rcases ha with ⟨c, htwo, hdiag⟩
  by_cases haNonneg : 0 ≤ ordUnit K a
  · have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have haNeg : ordUnit K a < 0 := lt_of_not_ge haNonneg
  have hc : c ≠ 0 := by
    intro hc
    subst c
    have haMem : (a : K) ∈ IntegerRing K := by
      simpa using hdiag
    have := Lattice.ordUnit_nonneg_of_mem_integerRing a haMem
    omega
  let cu : Kˣ := Units.mk0 c hc
  have hcOrd : ord K c =
      ((ordUnit K cu : Int) : WithTop Int) := by
    exact (coe_ordUnit K cu).symm
  have haOrdNeg : ord K (a : K) < 0 := by
    rw [← coe_ordUnit]
    exact_mod_cast haNeg
  have hdiagOrd : 0 ≤ ord K (c ^ 2 + (a : K)) :=
    (mem_integerRing_iff K).1 hdiag
  have heqOrder : ord K (c ^ 2) = ord K (a : K) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsum := (ord K).map_add_eq_of_lt_left hlt
      rw [hsum] at hdiagOrd
      exact (not_lt_of_ge hdiagOrd) (hlt.trans haOrdNeg)
    · have hsum := (ord K).map_add_eq_of_lt_right hgt
      rw [hsum] at hdiagOrd
      exact (not_lt_of_ge hdiagOrd) haOrdNeg
  have haOrder : ordUnit K a = 2 * ordUnit K cu := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ← heqOrder, ord_pow, hcOrd]
    norm_cast
  have htwoOrd : 0 ≤ ord K ((2 : K) * c) :=
    (mem_integerRing_iff K).1 htwo
  have htwoInt :
      0 ≤ (ramificationIndex K : Int) + ordUnit K cu := by
    apply WithTop.coe_le_coe.mp
    rw [WithTop.coe_add, ramificationIndex_spec, ← hcOrd]
    simpa [ord_mul] using htwoOrd
  rw [haOrder]
  omega

/-- A binary-admissible parameter of odd order has nonnegative order. -/
theorem IsBinaryParameterAdmissible.ordUnit_nonneg_of_odd
    {a : Kˣ} (ha : IsBinaryParameterAdmissible a)
    (hodd : Odd (ordUnit K a)) :
    0 ≤ ordUnit K a := by
  by_contra hnonneg
  have haNeg : ordUnit K a < 0 := lt_of_not_ge hnonneg
  rcases ha with ⟨c, _htwo, hdiag⟩
  have hc : c ≠ 0 := by
    intro hc
    subst c
    have haMem : (a : K) ∈ IntegerRing K := by
      simpa using hdiag
    exact (not_lt_of_ge
      (Lattice.ordUnit_nonneg_of_mem_integerRing a haMem)) haNeg
  let cu : Kˣ := Units.mk0 c hc
  have hcOrd : ord K c =
      ((ordUnit K cu : Int) : WithTop Int) := by
    exact (coe_ordUnit K cu).symm
  have haOrdNeg : ord K (a : K) < 0 := by
    rw [← coe_ordUnit]
    exact_mod_cast haNeg
  have hdiagOrd : 0 ≤ ord K (c ^ 2 + (a : K)) :=
    (mem_integerRing_iff K).1 hdiag
  have heqOrder : ord K (c ^ 2) = ord K (a : K) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsum := (ord K).map_add_eq_of_lt_left hlt
      rw [hsum] at hdiagOrd
      exact (not_lt_of_ge hdiagOrd) (hlt.trans haOrdNeg)
    · have hsum := (ord K).map_add_eq_of_lt_right hgt
      rw [hsum] at hdiagOrd
      exact (not_lt_of_ge hdiagOrd) haOrdNeg
  have haOrder : ordUnit K a = 2 * ordUnit K cu := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ← heqOrder, ord_pow, hcOrd]
    norm_cast
  rcases hodd with ⟨z, hz⟩
  omega

variable [QuadraticDefectLaws K]

/-- Beli 2003, Lemma 3.5: the operational model condition is equivalent to
the nonsquare integral-defect case or the square order-bound case. -/
theorem isBinaryParameterAdmissible_iff_beli (a : Kˣ) :
    IsBinaryParameterAdmissible a ↔
      IsBeliBinaryParameterAdmissible a := by
  constructor
  · intro ha
    by_cases hsquare : IsSquare (-a)
    · exact Or.inr ⟨hsquare, ha.ordUnit_ge_neg_two_mul_e⟩
    · apply Or.inl
      refine ⟨hsquare, ?_⟩
      rcases ha with ⟨c, _, hdiag⟩
      refine ⟨c, ?_⟩
      have heq : ((-a : Kˣ) : K) - c ^ 2 =
          -(c ^ 2 + (a : K)) := by
        simp only [Units.val_neg]
        ring
      rw [heq]
      exact (IntegerRing K).neg_mem _ hdiag
  · intro ha
    rcases ha with ⟨hnonsquare, hdefect⟩ | ⟨hsquare, hlower⟩
    · rcases hdefect with ⟨x, hdiff⟩
      refine ⟨x, ?_, ?_⟩
      · exact Dyadic.two_mul_mem_integerRing_of_not_isSquare_of_sub_sq_mem
          hnonsquare hdiff
      · have heq : x ^ 2 + (a : K) =
            -(((-a : Kˣ) : K) - x ^ 2) := by
          simp only [Units.val_neg]
          ring
        rw [heq]
        exact (IntegerRing K).neg_mem _ hdiff
    · rcases hsquare with ⟨s, hs⟩
      have hsval : ((-a : Kˣ) : K) =
          (s : K) * (s : K) := congrArg Units.val hs
      have hnegOrder : ordUnit K (-a) =
          2 * ordUnit K s := by
        rw [hs, ordUnit_mul]
        omega
      have hordNeg : ordUnit K (-a) = ordUnit K a := by
        apply WithTop.coe_injective
        simpa using ord_neg K (a : K)
      have hsIntegral :
          0 ≤ (ramificationIndex K : Int) + ordUnit K s := by
        rw [hordNeg] at hnegOrder
        omega
      refine ⟨(s : K), ?_, ?_⟩
      · apply (mem_integerRing_iff K).2
        change 0 ≤ ord K ((2 : K) * (s : K))
        rw [ord_mul, ← ramificationIndex_spec, ← coe_ordUnit]
        exact_mod_cast hsIntegral
      · rw [pow_two, ← hsval]
        simp

/-- The integral-defect predicate agrees with the order-theoretic absolute
defect condition `ord(a) + d(a) ≥ 0`. -/
theorem hasIntegralQuadraticDefect_iff_nonnegativeAbsoluteDefect
    (a : Kˣ) :
    HasIntegralQuadraticDefect a ↔
      HasNonnegativeAbsoluteQuadraticDefect a := by
  rw [HasIntegralQuadraticDefect,
    hasNonnegativeAbsoluteQuadraticDefect_iff_exists_sub_sq_mem]

/-- The uniform order-and-defect form of the admissibility criterion used in
Beli 2006 and Beli 2009/2010. -/
theorem isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
    (a : Kˣ) :
    IsBinaryParameterAdmissible a ↔
      0 ≤ ordUnit K a + 2 * (ramificationIndex K : Int) ∧
        HasNonnegativeAbsoluteQuadraticDefect (-a) := by
  constructor
  · intro ha
    constructor
    · have hlower := ha.ordUnit_ge_neg_two_mul_e
      omega
    · apply
        (hasIntegralQuadraticDefect_iff_nonnegativeAbsoluteDefect
          (-a)).1
      rcases ha with ⟨c, _, hdiag⟩
      refine ⟨c, ?_⟩
      have heq : ((-a : Kˣ) : K) - c ^ 2 =
          -(c ^ 2 + (a : K)) := by
        simp only [Units.val_neg]
        ring
      rw [heq]
      exact (IntegerRing K).neg_mem _ hdiag
  · rintro ⟨hlower, hdefect⟩
    apply (isBinaryParameterAdmissible_iff_beli a).2
    by_cases hsquare : IsSquare (-a)
    · apply Or.inr
      constructor
      · exact hsquare
      · omega
    · apply Or.inl
      refine ⟨hsquare, ?_⟩
      exact
        (hasIntegralQuadraticDefect_iff_nonnegativeAbsoluteDefect
          (-a)).2 hdefect

/-- A refined square class satisfies Beli's binary criterion when one of its
representatives does. -/
def IsBeliBinaryInvariantClassAdmissible
    (A : UnitSquareClass K) : Prop :=
  ∃ a : Kˣ,
    unitSquareClass K a = A ∧ IsBeliBinaryParameterAdmissible a

/-- Class-level form of Beli 2003, Lemma 3.5. -/
theorem isBinaryInvariantClassAdmissible_iff_beli
    (A : UnitSquareClass K) :
    IsBinaryInvariantClassAdmissible A ↔
      IsBeliBinaryInvariantClassAdmissible A := by
  constructor <;> rintro ⟨a, ha, hcriterion⟩
  · exact ⟨a, ha, (isBinaryParameterAdmissible_iff_beli a).1
      hcriterion⟩
  · exact ⟨a, ha, (isBinaryParameterAdmissible_iff_beli a).2
      hcriterion⟩

end BONG

end Bong
