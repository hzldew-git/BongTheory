/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremTwo
import Bong.Bong.BeliLemma313II

/-!
# Beli (2003), Lemma 7.2

The half-integral defect comparison is represented in `WithTop ℚ`, so the
infinite defect and negative cutoffs require no truncation.  The combined
parameter in part (ii) is an actual field unit built from the normalized unit
parts of all input parameters.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

/-- The rationally embedded value `d(-a)`. -/
noncomputable def beliParameterDefectOrderQ (a : Kˣ) : WithTop ℚ :=
  WithTop.map (fun m : Nat => (m : ℚ)) (beliParameterDefect K a)

/-- The cutoff `e - R/2` in Lemma 7.2(i). -/
noncomputable def lemma72DefectThreshold (a : Kˣ) : ℚ :=
  (ramificationIndex K : ℚ) - (ordUnit K a : ℚ) / 2

/-- Multiplication by a valuation-unit square does not change `d(-a)`. -/
theorem beliParameterDefect_eq_of_unitSquareClass_eq
    {a b : Kˣ} (hclass : unitSquareClass K a = unitSquareClass K b) :
    beliParameterDefect K a = beliParameterDefect K b := by
  rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
      K hclass with ⟨s, hs, hab⟩
  have hscaled := beliParameterDefect_mul_valuationUnit_square K a s hs
  rw [hab] at hscaled
  exact hscaled.symm

/-- The exceptional `-1/4` class has infinite parameter defect. -/
theorem beliParameterDefectOrderQ_eq_top_of_negativeQuarter
    (a : Kˣ)
    (hclass : unitSquareClass K a =
      unitSquareClass K (negativeQuarterUnit K)) :
    beliParameterDefectOrderQ (K := K) a = ⊤ := by
  have hdefect := beliParameterDefect_eq_of_unitSquareClass_eq
    (K := K) hclass
  rw [beliParameterDefect_negativeQuarterUnit] at hdefect
  unfold beliParameterDefectOrderQ
  rw [hdefect]
  rfl

/-- The right-hand condition in Lemma 7.2(i). -/
def IsNegativeDiscriminantQuarterParameter (a : Kˣ) : Prop :=
  ordUnit K a = -(2 * (ramificationIndex K : Int)) ∧
    beliParameterDefect K a =
      ((2 * ramificationIndex K : Nat) : ℕ∞)

/-- The right-hand condition in Lemma 7.2(i).  The exceptional endpoint is
the class `-Δ/4`, not the hyperbolic class `-1/4`.  It is expressed here by
its intrinsic order-and-defect characterization, so the statement does not
depend on a chosen representative of the discriminant square class. -/
def SatisfiesLemma72UnitCriterion (a : Kˣ) : Prop :=
  Even (ordUnit K a) ∧
    (IsNegativeDiscriminantQuarterParameter (K := K) a ∨
      ((lemma72DefectThreshold (K := K) a : ℚ) : WithTop ℚ) <
        beliParameterDefectOrderQ (K := K) a)

/-- The combined parameter
`(-1)^(k-1) π^R ε₁⋯εₖ` in Lemma 7.2(ii). -/
noncomputable def lemma72CombinedParameter {k : Nat}
    (a : Fin k → Kˣ) (R : Int) : Kˣ :=
  (-1 : Kˣ) ^ (k - 1) * uniformizerPowerUnit K R *
    ∏ i, normalizedUnitPart K (a i)

/-- The combined parameter has exactly the prescribed order `R`. -/
theorem ordUnit_lemma72CombinedParameter {k : Nat}
    (a : Fin k → Kˣ) (R : Int) :
    ordUnit K (lemma72CombinedParameter (K := K) a R) = R := by
  classical
  have hpart : ∀ i : Fin k,
      ordUnit K (normalizedUnitPart K (a i)) = 0 := by
    intro i
    exact (isValuationUnit_iff_ordUnit_eq_zero K _).1
      (normalizedUnitPart_isValuationUnit K (a i))
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  have hprod : ∀ s : Finset (Fin k),
      ordUnit K (∏ i ∈ s, normalizedUnitPart K (a i)) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using hone
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, ordUnit_mul, hpart i, ih, zero_add]
  unfold lemma72CombinedParameter
  rw [ordUnit_mul, ordUnit_mul, ordUnit_pow,
    ordUnit_uniformizerPowerUnit, hprod Finset.univ, hnegOne]
  simp

/-- One admissible parameter whose binary `G` group is unit-bounded. -/
def IsLemma72UnitParameter (a : Kˣ) : Prop :=
  BONG.IsBinaryParameterAdmissible a ∧
    beliSpinorGroupRepresentative K a ≤
      valuationUnitSquareClassSubgroup K

end Dyadic

/-- The local norm-group classification and domination argument in Beli
(2003), Lemma 7.2.  This interface has no default instance. -/
class BeliLemma72Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  spinor_group_le_unit_iff
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a) :
    beliSpinorGroupRepresentative K a ≤
        valuationUnitSquareClassSubgroup K ↔
      SatisfiesLemma72UnitCriterion (K := K) a
  combined_parameter
    {k : Nat} (a : Fin k → Kˣ) (R : Int) :
    0 < k →
    (∀ i, IsLemma72UnitParameter (K := K) (a i)) →
    Even R → (∀ i, ordUnit K (a i) ≤ R) →
      IsLemma72UnitParameter (K := K)
        (lemma72CombinedParameter (K := K) a R)

namespace Dyadic

variable [BeliLemma72Laws K]

/-- Beli (2003), Lemma 7.2(i). -/
theorem beliLemma72_i
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a) :
    beliSpinorGroupRepresentative K a ≤
        valuationUnitSquareClassSubgroup K ↔
      SatisfiesLemma72UnitCriterion (K := K) a :=
  BeliLemma72Laws.spinor_group_le_unit_iff a ha

/-- The final defect lower bound in Lemma 7.2(i). -/
theorem beliLemma72_i_defect_lower_bound
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hunit : beliSpinorGroupRepresentative K a ≤
      valuationUnitSquareClassSubgroup K) :
    ((lemma72DefectThreshold (K := K) a : ℚ) : WithTop ℚ) ≤
      beliParameterDefectOrderQ (K := K) a := by
  rcases (beliLemma72_i (K := K) a ha).1 hunit with
    ⟨_heven, hquarter | hstrict⟩
  · rcases hquarter with ⟨horder, hdefect⟩
    unfold lemma72DefectThreshold beliParameterDefectOrderQ
    rw [horder, hdefect]
    change
      (((ramificationIndex K : ℚ) -
          ((-(2 * (ramificationIndex K : Int)) : Int) : ℚ) / 2 : ℚ) :
        WithTop ℚ) ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)
    have hhalf :
        ((-(2 * (ramificationIndex K : Int)) : Int) : ℚ) / 2 =
          -(ramificationIndex K : ℚ) := by
      push_cast
      ring
    have htwo : ((2 * ramificationIndex K : Nat) : ℚ) =
        2 * (ramificationIndex K : ℚ) := by
      norm_num
    rw [hhalf]
    rw [htwo]
    have hint :
        (ramificationIndex K : Int) - -(ramificationIndex K : Int) =
          2 * (ramificationIndex K : Int) := by
      ring
    exact_mod_cast hint.le
  · exact hstrict.le

/-- Beli (2003), Lemma 7.2(ii). -/
theorem beliLemma72_ii {k : Nat} (a : Fin k → Kˣ) (R : Int)
    (hk : 0 < k)
    (ha : ∀ i, IsLemma72UnitParameter (K := K) (a i))
    (hR : Even R) (horder : ∀ i, ordUnit K (a i) ≤ R) :
    IsLemma72UnitParameter (K := K)
      (lemma72CombinedParameter (K := K) a R) :=
  BeliLemma72Laws.combined_parameter a R hk ha hR horder

end Dyadic

end Bong
