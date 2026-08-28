/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDiagonalLowSpinorOdd

/-!
# Low-defect binary spinor norms

This closes Xu (1993), Proposition 2.3(i), including the even-order
cancellation branch.  If the two diagonal terms have different orders, the
elementary valuation argument applies.  If they have the same order, the
extra cancellation in a represented value is a quadratic approximation to
`-a`; the low-defect inequality bounds that cancellation exactly strongly
enough for both reflection coefficients to be integral.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- In the nonnegative case-III low-defect range, every primitive anisotropic
vector of the diagonal lattice defines an integral reflection.  The proof
also covers odd order; the equal-term branch itself forces even order. -/
theorem primitive_isIntegralReflection_binaryDiagonal_of_low_defect
    (a : Kˣ)
    (hRnonneg : 0 ≤ ordUnit K a)
    (hRhigh : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hdefect : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K))) :
    Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) hz := by
  classical
  by_cases hUnequal : ∀ (hx0 : z 0 ≠ 0) (hy0 : z 1 ≠ 0),
      2 * ordUnit K (Units.mk0 (z 0) hx0) ≠
        ordUnit K a + 2 * ordUnit K (Units.mk0 (z 1) hy0)
  · exact primitive_isIntegralReflection_binaryDiagonal_of_low_of_unequal_terms
      a hRnonneg hRhigh hz hzMem hzPrimitive hUnequal
  · simp only [not_forall, not_not] at hUnequal
    rcases hUnequal with ⟨hx0z, hy0z, htermsEqual⟩
    let x : K := z 0
    let y : K := z 1
    have hx0 : x ≠ 0 := by simpa [x] using hx0z
    have hy0 : y ≠ 0 := by simpa [y] using hy0z
    let xu : Kˣ := Units.mk0 x hx0
    let yu : Kˣ := Units.mk0 y hy0
    have htermsEqual' :
        2 * ordUnit K xu = ordUnit K a + 2 * ordUnit K yu := by
      simpa [x, y, xu, yu] using htermsEqual
    have hzCoords := (mem_binaryModelLattice_iff z).1 hzMem
    have hxMem : x ∈ IntegerRing K := by simpa [x] using hzCoords 0
    have hyMem : y ∈ IntegerRing K := by simpa [y] using hzCoords 1
    have hxOrderNonneg : 0 ≤ ordUnit K xu :=
      Lattice.ordUnit_nonneg_of_mem_integerRing xu
        (by simpa [xu] using hxMem)
    have hyOrderNonneg : 0 ≤ ordUnit K yu :=
      Lattice.ordUnit_nonneg_of_mem_integerRing yu
        (by simpa [yu] using hyMem)
    have hprimitive :=
      (primitive_binaryModelLattice_iff_coordinate_unit z hzMem).1
        hzPrimitive
    have hyUnit : IsValuationUnit K y := by
      rcases hprimitive with hxUnit | hyUnit
      · have hxOrder : ordUnit K xu = 0 :=
          (isValuationUnit_iff_ordUnit_eq_zero K xu).1
            (by simpa [x, xu] using hxUnit)
        have hyOrder : ordUnit K yu = 0 := by omega
        simpa [y, yu] using
          (isValuationUnit_iff_ordUnit_eq_zero K yu).2 hyOrder
      · simpa [y] using hyUnit
    have hyOrder : ordUnit K yu = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K yu).1
        (by simpa [yu] using hyUnit)
    have hxOrderTwice : 2 * ordUnit K xu = ordUnit K a := by
      omega
    have hxOrdTop : ord K x = (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
      simpa [yu] using (coe_ordUnit K yu).symm
    have hqFormula :
        (QuadraticSpace.binaryModel a 0).quadratic z =
          x ^ 2 + (a : K) * y ^ 2 := by
      simp [QuadraticSpace.binaryModel_quadratic_apply, x, y]
    have hq0 : x ^ 2 + (a : K) * y ^ 2 ≠ 0 := by
      rw [← hqFormula]
      exact hz
    let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
    have hqOrdTop :
        ord K (x ^ 2 + (a : K) * y ^ 2) =
          (ordUnit K qU : WithTop Int) := by
      simpa [qU] using (coe_ordUnit K qU).symm
    have hxTermOrder :
        ord K (x ^ 2) =
          ((2 * ordUnit K xu : Int) : WithTop Int) := by
      rw [ord_pow, hxOrdTop]
      norm_cast
    have hyTermOrder :
        ord K ((a : K) * y ^ 2) =
          (ordUnit K a : WithTop Int) := by
      rw [ord_mul, ord_pow, ← coe_ordUnit K a, hyOrdTop, hyOrder]
      simp
    have hqLower : ordUnit K a ≤ ordUnit K qU := by
      apply WithTop.coe_le_coe.mp
      calc
        (ordUnit K a : WithTop Int) =
            min (ord K (x ^ 2)) (ord K ((a : K) * y ^ 2)) := by
          rw [hxTermOrder, hyTermOrder]
          norm_cast
          simp [hxOrderTwice]
        _ ≤ ord K (x ^ 2 + (a : K) * y ^ 2) :=
          min_ord_le_ord_add K _ _
        _ = (ordUnit K qU : WithTop Int) := hqOrdTop
    let n : Nat := Int.toNat (ordUnit K qU - ordUnit K a)
    have hnCast : (n : Int) = ordUnit K qU - ordUnit K a := by
      simpa only [n] using
        (Int.toNat_of_nonneg (show 0 ≤ ordUnit K qU - ordUnit K a by
          omega))
    have hnormalizedError :
        1 - (x / y) ^ 2 / ((-a : Kˣ) : K) =
          (x ^ 2 + (a : K) * y ^ 2) / ((a : K) * y ^ 2) := by
      change 1 - (x / y) ^ 2 / (-(a : K)) =
        (x ^ 2 + (a : K) * y ^ 2) / ((a : K) * y ^ 2)
      field_simp [Units.ne_zero a, hy0]
      ring
    have happ : IsQuadraticApproximation K (-a) n := by
      refine ⟨x / y, ?_⟩
      rw [hnormalizedError, div_eq_mul_inv, ord_mul,
        AddValuation.map_inv, hqOrdTop, hyTermOrder]
      norm_cast
      omega
    have hnDefect : (n : ℕ∞) ≤ beliParameterDefect K a := by
      unfold beliParameterDefect
      exact natCast_le_quadraticDefect K happ
    have hnBoundTop : ((2 * n : Nat) : ℕ∞) ≤
        (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
      calc
        ((2 * n : Nat) : ℕ∞) = 2 * (n : ℕ∞) := by norm_num
        _ ≤ 2 * beliParameterDefect K a :=
          mul_le_mul_left' hnDefect 2
        _ ≤ (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := hdefect
    have hnBound : 2 * n ≤ beliSpinorCaseIIILowerCutoff K a := by
      exact_mod_cast hnBoundTop
    have hcutoff : (beliSpinorCaseIIILowerCutoff K a : Int) =
        2 * (ramificationIndex K : Int) - ordUnit K a := by
      unfold beliSpinorCaseIIILowerCutoff
      rw [Int.toNat_of_nonneg]
      omega
    have hnBoundInt : 2 * (n : Int) ≤
        2 * (ramificationIndex K : Int) - ordUnit K a := by
      have hcast : 2 * (n : Int) ≤
          (beliSpinorCaseIIILowerCutoff K a : Int) := by
        exact_mod_cast hnBound
      rwa [hcutoff] at hcast
    have hqUpper : ordUnit K qU ≤
        (ramificationIndex K : Int) + ordUnit K xu := by
      omega
    have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    have hcoefficient_mem
        {w : K} (hw0 : w ≠ 0) (wu : Kˣ)
        (hwu : (wu : K) = w)
        (hbound : ordUnit K qU ≤
          (ramificationIndex K : Int) + ordUnit K wu) :
        2 * w / (x ^ 2 + (a : K) * y ^ 2) ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤
        ord K (2 * w / (x ^ 2 + (a : K) * y ^ 2))
      rw [div_eq_mul_inv, ord_mul, ord_mul, AddValuation.map_inv,
        ← ramificationIndex_spec, hqOrdTop]
      have hwOrd : ord K w = (ordUnit K wu : WithTop Int) := by
        rw [← hwu, ← coe_ordUnit]
      rw [hwOrd]
      exact_mod_cast (show 0 ≤
        (ramificationIndex K : Int) + ordUnit K wu - ordUnit K qU by
          omega)
    apply (isIntegralReflection_binaryDiagonal_iff_of_primitive
      a hz hzMem hzPrimitive).2
    constructor
    · rw [hqFormula]
      apply hcoefficient_mem hx0 xu
      · rfl
      · exact hqUpper
    · let aw : Kˣ := a * yu
      have haw : (aw : K) = (a : K) * y := by rfl
      rw [hqFormula]
      have hmem := hcoefficient_mem
        (mul_ne_zero (Units.ne_zero a) hy0) aw haw (by
          simp only [aw, ordUnit_mul, hyOrder, add_zero]
          omega)
      simpa [y, mul_assoc] using hmem

/-- Xu (1993), Proposition 2.3(i): throughout the nonnegative case-III
low-defect range the proper spinor image is the complete quadratic norm
square-class subgroup. -/
theorem spinorNormImage_binaryDiagonal_eq_norm_of_low_defect
    (a : Kˣ)
    (hRnonneg : 0 ≤ ordUnit K a)
    (hRhigh : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hdefect : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞)) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) =
      quadraticNormSquareClassSubgroup K (-a) := by
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (a : K)
    rw [← coe_ordUnit]
    exact_mod_cast hRnonneg
  apply spinorNormImage_binaryDiagonal_eq_norm_of_all_primitive_reflections
    a haIntegral
  intro z hz hzMem hzPrimitive
  exact primitive_isIntegralReflection_binaryDiagonal_of_low_defect
    a hRnonneg hRhigh hdefect hz hzMem hzPrimitive

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The complete nonnegative low-defect part of Beli (2003), Lemma 3.7,
without a `BinarySpinorLocalLaws` hypothesis. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_of_low_defect
    (b : BONG V q L 2)
    (hRnonneg : 0 ≤ b.binaryOrderGap)
    (hRhigh : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hdefect : 2 * beliParameterDefect K b.binaryParameter ≤
      (beliSpinorCaseIIILowerCutoff K b.binaryParameter : ℕ∞)) :
    Lattice.spinorNormImage (q := q) (L := L) =
      beliSpinorGroupRepresentative K b.binaryParameter := by
  have hparameterOrder : ordUnit K b.binaryParameter = b.binaryOrderGap :=
    b.binaryParameterOrder_eq_orderGap
  have hRnonneg' : 0 ≤ ordUnit K b.binaryParameter := by omega
  have hRhigh' : ordUnit K b.binaryParameter ≤
      2 * (ramificationIndex K : Int) := by omega
  have hquarter : unitSquareClass K b.binaryParameter ≠
      unitSquareClass K (negativeQuarterUnit K) := by
    intro hclass
    have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
    rw [hparameterOrder, ordUnit_negativeQuarterUnit] at horder
    have he : 0 < (ramificationIndex K : Int) := by
      exact_mod_cast ramificationIndex_pos K
    omega
  have hformula := beliSpinorGroupRepresentative_caseIII_low
    K b.binaryParameter b.binaryParameter_isBinaryParameterAdmissible
      hquarter (by omega) hdefect
  calc
    Lattice.spinorNormImage (q := q) (L := L) =
        Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel b.binaryParameter 0)
          (L := binaryModelLattice (K := K)) :=
      b.spinorNormImage_eq_diagonal_of_binaryOrderGap_nonneg hRnonneg
    _ = quadraticNormSquareClassSubgroup K (-b.binaryParameter) :=
      spinorNormImage_binaryDiagonal_eq_norm_of_low_defect
        b.binaryParameter hRnonneg' hRhigh' hdefect
    _ = beliSpinorGroupRepresentative K b.binaryParameter := by
      exact congrArg
        (fun H : Subgroup (SquareClass K) => (H : Set (SquareClass K)))
        hformula.symm

end BONG

end Bong
