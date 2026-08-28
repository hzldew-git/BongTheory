/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiscriminantClassProof
import Bong.Dyadic.UnramifiedNorm
import Bong.Dyadic.UnitDefectClassification

/-!
# Norms from the distinguished unramified quadratic extension

Using Hilbert-pairing bimultiplicativity, nondegeneracy, and the defect
criterion, this file proves that the norm group attached to the distinguished
discriminant unit consists exactly of the even-valuation square classes.
-/

namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [discriminant : DyadicDiscriminantClassLaws K]
  [HilbertSymbolLaws K]

private theorem quadraticDefect_ne_zero_of_unit
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    quadraticDefect K u ≠ 0 := by
  rcases exists_unit_squareRoot_mod_maximal K u hu with
    ⟨z, _hzUnit, hzError⟩
  have happrox : IsQuadraticApproximation K u 1 := by
    refine ⟨z, ?_⟩
    have hnormalized :
        1 - z ^ 2 / (u : K) = ((u : K) - z ^ 2) / (u : K) := by
      field_simp [Units.ne_zero u]
    rw [hnormalized, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, hu]
    simp only [neg_zero, add_zero]
    have hpositive : 0 < ord K ((u : K) - z ^ 2) := by
      rw [show (u : K) - z ^ 2 = -(z ^ 2 - (u : K)) by ring,
        ord_neg]
      exact hzError
    by_cases htop : ord K ((u : K) - z ^ 2) = ⊤
    · rw [htop]
      exact le_top
    · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hd] at hpositive ⊢
      have hdPositive : (0 : ℤ) < d := by exact_mod_cast hpositive
      exact_mod_cast (show (1 : ℤ) ≤ d by omega)
  have hdefect := natCast_le_quadraticDefect K happrox
  intro hzero
  rw [hzero] at hdefect
  simp at hdefect

private theorem discriminant_hilbert_eq_one_of_even_order
    (b : Kˣ) (heven : Even (ordUnit K b)) :
    hilbertSymbol K discriminant.discriminantUnit b = 1 := by
  rcases heven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let unitPart : Kˣ := b / s ^ 2
  have hsOrder : ordUnit K s = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have hunitOrder : ordUnit K unitPart = 0 := by
    dsimp only [unitPart]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow, hsOrder]
    omega
  have hunit : IsValuationUnit K (unitPart : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K unitPart).2 hunitOrder
  have hunitDefectNe : quadraticDefect K unitPart ≠ 0 :=
    quadraticDefect_ne_zero_of_unit unitPart hunit
  have hstrict : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K discriminant.discriminantUnit +
        quadraticDefect K unitPart := by
    rw [discriminant.discriminant_defect]
    have hpositive : (0 : ℕ∞) < quadraticDefect K unitPart :=
      pos_iff_ne_zero.mpr hunitDefectNe
    simpa using
      (ENat.add_lt_add_iff_left (ENat.coe_ne_top
        (2 * ramificationIndex K))).2 hpositive
  have hunitHilbert :
      hilbertSymbol K discriminant.discriminantUnit unitPart = 1 :=
    hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e K hstrict
  have hfactor : unitPart * s ^ 2 = b := by
    dsimp only [unitPart]
    simp
  rw [← hfactor, hilbertSymbol_mul_square_right]
  exact hunitHilbert

private theorem discriminant_not_square :
    ¬IsSquare discriminant.discriminantUnit := by
  intro hsquare
  have htop := quadraticDefect_eq_top_of_isSquare K hsquare
  rw [discriminant.discriminant_defect] at htop
  exact ENat.coe_ne_top _ htop

private theorem discriminant_hilbert_ne_one_of_odd_order
    (b : Kˣ) (hodd : Odd (ordUnit K b)) :
    hilbertSymbol K discriminant.discriminantUnit b ≠ 1 := by
  intro hb
  have htrivial : ∀ x : Kˣ,
      hilbertSymbol K discriminant.discriminantUnit x = 1 := by
    intro x
    rcases Int.even_or_odd (ordUnit K x) with hxEven | hxOdd
    · exact discriminant_hilbert_eq_one_of_even_order x hxEven
    · have hbxEven : Even (ordUnit K (b * x)) := by
        rw [ordUnit_mul]
        exact hodd.add_odd hxOdd
      have hproduct := discriminant_hilbert_eq_one_of_even_order
        (b * x) hbxEven
      rw [hilbertSymbol_mul_right, hb, one_mul] at hproduct
      exact hproduct
  exact discriminant_not_square (K := K)
    (HilbertSymbolLaws.nondegenerate discriminant.discriminantUnit htrivial)

noncomputable instance dyadicUnramifiedNormLawsProved :
    DyadicUnramifiedNormLaws K where
  discriminant_norm_iff_even_order b := by
    rw [← hilbertSymbol_eq_one_iff]
    constructor
    · intro hhilbert
      by_contra hnotEven
      have hodd : Odd (ordUnit K b) := Int.not_even_iff_odd.mp hnotEven
      exact discriminant_hilbert_ne_one_of_odd_order b hodd hhilbert
    · exact discriminant_hilbert_eq_one_of_even_order b

end Bong.Dyadic
