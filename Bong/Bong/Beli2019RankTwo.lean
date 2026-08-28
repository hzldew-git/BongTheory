/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SameRankCommonSpace
import Bong.Bong.Beli2019RepresentationProblemReindex
import Bong.Bong.Beli2009BinaryRemarks
import Bong.Bong.AdjacentNormGeneratorChange
import Bong.Bong.Beli2019Lemma97
import Bong.Bong.Beli2019Lemma813
import Bong.Bong.Beli2019RepresentationTransitivity
import Bong.Bong.DiagonalBinaryRepresentation

/-!
# Beli (2019): the equal-norm binary base case

This file proves the rank-two equal-norm stopping case in the final induction.
After moving both lattices into one quadratic space, the quotient of their
first BONG values is a valuation unit.  Condition (ii) places its square
class in the alpha congruence group, while ambient unary representation puts
it in the determinant norm group.  Beli (2009), Remark 5.2, therefore permits
an adjacent norm-generator change.  The determinant square relation supplies
the remaining integral square shift, and Lemma 9.7(i) finishes the lattice
representation.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The equal-norm rank-two case of Beli (2019), Theorem 2.1. -/
theorem beli2019_rankTwo_equalNorm_sufficiency
    [alphaLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L 2) (b : GoodBONG r M 2)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl 1))
    (hfirst : a.order (0 : Fin 2) = b.order (0 : Fin 2)) :
    Lattice.Represents q r L M := by
  let D : Beli2019SameRankCommonSpace a b :=
    Beli2019SameRankCommonSpace.ofAmbient ambient
  let c : GoodBONG q D.sourceImage 2 := D.sourceImageBONG
  have hconditions : RepresentationConditions a c (Nat.le_refl 1) :=
    D.conditions conditions
  have hfirst' : a.order (0 : Fin 2) = c.order (0 : Fin 2) := by
    calc
      a.order (0 : Fin 2) = b.order (0 : Fin 2) := hfirst
      _ = c.order (0 : Fin 2) :=
        D.source_scalarAgreement.order_eq (0 : Fin 2)
  have huValuation : IsValuationUnit K
      (((c.valueUnit 0 / a.valueUnit 0 : Kˣ) : K)) := by
    change a.toBONG.order (0 : Fin 2) =
      c.toBONG.order (0 : Fin 2) at hfirst'
    apply (isValuationUnit_iff_ordUnit_eq_zero K
      (c.valueUnit 0 / a.valueUnit 0)).2
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    change ordUnit K (c.toBONG.valueUnit 0) +
      -ordUnit K (a.toBONG.valueUnit 0) = 0
    rw [← c.toBONG.order_eq_ordUnit, ← a.toBONG.order_eq_ordUnit,
      ← hfirst']
    simp
  let u : valuationUnitSubgroup K :=
    ⟨c.valueUnit 0 / a.valueUnit 0, huValuation⟩

  have haPrefix : a.prefixProduct 1 = a.valueUnit (0 : Fin 2) := by
    change a.toBONG.prefixProduct 1 = a.toBONG.valueUnit (0 : Fin 2)
    rw [a.toBONG.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_zero, one_mul]
    congr
  have hcPrefix : c.prefixProduct 1 = c.valueUnit (0 : Fin 2) := by
    change c.toBONG.prefixProduct 1 = c.toBONG.valueUnit (0 : Fin 2)
    rw [c.toBONG.prefixProduct_succ 0 (by omega),
      c.toBONG.prefixProduct_zero, one_mul]
    congr
  let first : RepresentationIndex 2 2 := firstRepresentationIndex 0 1
  have hconditionDefect := hconditions.defectCondition first
  have hrepresentationAlpha : a.representationAlpha c first =
      (a.alphaValue (0 : Fin 1) : WithTop ℚ) :=
    a.beli2019Lemma812_i c hfirst'
  rw [a.coe_representationAlphaValue c first,
    hrepresentationAlpha] at hconditionDefect
  have hrawDefect := hconditionDefect.trans
    (a.truncatedPrefixDefect_le_defect c 1 1 1)
  have hprefixProduct :
      (1 : Kˣ) * a.prefixProduct 1 * c.prefixProduct 1 =
        (u : Kˣ) * a.valueUnit 0 ^ 2 := by
    rw [haPrefix, hcPrefix]
    change 1 * a.valueUnit 0 * c.valueUnit 0 =
      (c.valueUnit 0 / a.valueUnit 0) * a.valueUnit 0 ^ 2
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm]
  rw [hprefixProduct, defectOrder_mul_square] at hrawDefect
  have hAlphaDefect :
      beli2009BinaryAlphaCut (K := K) a.toBONG.binaryParameter ≤
        defectOrder (K := K) (u : Kˣ) := by
    rw [a.binaryAlphaCut_parameter_eq]
    exact hrawDefect
  have huCongruence : valuationUnitClassHom K u ∈
      beli2009BinaryAlphaCongruenceGroup (K := K)
        a.toBONG.binaryParameter :=
    valuationUnitClassHom_mem_beli2009BinaryAlphaCongruenceGroup
      (K := K) a.toBONG.binaryParameter
        a.toBONG.binaryParameter_isBinaryParameterAdmissible u hAlphaDefect

  have hfull : DiagonalRepresents c.toBONG.value a.toBONG.value :=
    a.toBONG.diagonalRepresents_of_ambient c.toBONG
      (QuadraticSpace.represents_refl q)
  have hunaryPrefix :
      DiagonalRepresents
        (fun i : Fin 1 => c.toBONG.value ⟨i.val, i.isLt.trans_le (by omega)⟩)
        c.toBONG.value :=
    DiagonalRepresents.prefixOfLE c.toBONG.value (by omega)
  have hunary : DiagonalRepresents
      (fun i : Fin 1 => c.toBONG.value ⟨i.val, i.isLt.trans_le (by omega)⟩)
      a.toBONG.value := hunaryPrefix.trans hfull
  have huQuadraticNorm : IsQuadraticNorm K
      (-(a.valueUnit 0 * a.valueUnit 1)) (u : Kˣ) := by
    apply (DiagonalRepresents.unary_binary_iff_isQuadraticNorm
      (K := K) (a.valueUnit 0) (a.valueUnit 1) (c.valueUnit 0)).mp
    convert hunary using 1 <;> funext i <;> fin_cases i <;> rfl
  have huNorm : valuationUnitClassHom K u ∈
      quadraticNormValuationClassSubgroup K
        (-(a.valueUnit 0 * a.valueUnit 1)) := by
    refine ⟨u, ?_, rfl⟩
    exact huQuadraticNorm
  have huGenerator : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K a.toBONG.binaryParameter := by
    rw [(a.beli2009Remark52).2]
    exact ⟨huCongruence, huNorm⟩

  rcases a.toBONG.exists_binaryAdjacentMultiplierData u huGenerator with ⟨E⟩
  rcases BONG.exists_valueProduct_eq_mul_square a.toBONG c.toBONG with
    ⟨p, hp⟩
  let s₁ : Kˣ := p / (u : Kˣ)
  have hshift₀ : E.bong.valueUnit 0 * (1 : Kˣ) ^ 2 = c.valueUnit 0 := by
    rw [E.valueUnit_zero]
    change (c.valueUnit 0 / a.valueUnit 0) * a.valueUnit 0 * 1 ^ 2 =
      c.valueUnit 0
    simp [div_eq_mul_inv, mul_assoc]
  have hpBinary : c.valueUnit 0 * c.valueUnit 1 =
      (a.valueUnit 0 * a.valueUnit 1) * p ^ 2 := by
    simpa only [BONG.valueProduct_fin_two, GoodBONG.valueUnit] using hp
  have hshift₁ : E.bong.valueUnit 1 * s₁ ^ 2 = c.valueUnit 1 := by
    apply mul_left_cancel (a := c.valueUnit 0)
    rw [hpBinary]
    rw [E.valueUnit_one]
    change c.valueUnit 0 *
        ((c.valueUnit 0 / a.valueUnit 0) * a.valueUnit 1 *
          (p / (c.valueUnit 0 / a.valueUnit 0)) ^ 2) =
      a.valueUnit 0 * a.valueUnit 1 * p ^ 2
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]

  have hsecondOrder : a.order (1 : Fin 2) ≤ c.order (1 : Fin 2) := by
    rcases hconditions.orderCondition (1 : Fin 2) with h | h
    · exact h
    · rcases h with ⟨_, hiLarge, _⟩
      omega
  have huOrder : ordUnit K (u : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (u : Kˣ)).1 u.property
  have hESecondOrder : E.bong.order (1 : Fin 2) = a.order (1 : Fin 2) := by
    change E.bong.toBONG.order (1 : Fin 2) =
      a.toBONG.order (1 : Fin 2)
    rw [E.bong.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit]
    have hvalue : E.bong.toBONG.valueUnit (1 : Fin 2) =
        (u : Kˣ) * a.toBONG.valueUnit (1 : Fin 2) := E.valueUnit_one
    rw [hvalue, ordUnit_mul, huOrder, zero_add]
  have hshift₁Order := congrArg (ordUnit K) hshift₁
  rw [ordUnit_mul, ordUnit_pow] at hshift₁Order
  change E.bong.order (1 : Fin 2) + 2 * ordUnit K s₁ =
    c.order (1 : Fin 2) at hshift₁Order
  have hs₁Order : 0 ≤ ordUnit K s₁ := by
    rw [hESecondOrder] at hshift₁Order
    omega
  have hs₀Integral : ((1 : Kˣ) : K) ∈ IntegerRing K := by simp
  have hs₁Integral : (s₁ : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit]
    exact_mod_cast hs₁Order
  have himage : Lattice.Represents q q L D.sourceImage :=
    beli2019Lemma97_i_of_integralSquareShifts
      (structuralV := structural) (structuralW := structural)
      E.bong c 1 s₁ hs₀Integral hs₁Integral hshift₀ hshift₁
  exact D.represents_image_iff.mp himage

end BONG.GoodBONG

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Bundled equal-norm binary base case for the final rank-volume induction. -/
theorem not_counterexample_of_sourceIndex_eq_one_of_equalNorm
    [alphaLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hindex : p.sourceIndex = p.targetIndex)
    (hone : p.sourceIndex = 1) (hequal : p.EqualNorm) :
    ¬p.Counterexample := by
  letI : AddCommGroup p.Target := p.targetAddCommGroup
  letI : Module K p.Target := p.targetModule
  letI : AddCommGroup p.Source := p.sourceAddCommGroup
  letI : Module K p.Source := p.sourceModule
  let a := p.targetBONG.castLength
    (show p.targetIndex + 1 = 2 by omega)
  let b := p.sourceBONG.castLength
    (show p.sourceIndex + 1 = 2 by omega)
  let conditions' := representationConditions_castIndices
    p.targetBONG p.sourceBONG p.rankBound p.conditions
      (show p.targetIndex = 1 by omega) hone
  have hfirstRaw := (equalNorm_iff_firstOrder_eq p).mp hequal
  have hfirst : a.order (0 : Fin 2) = b.order (0 : Fin 2) := by
    dsimp only [a, b]
    rw [BONG.GoodBONG.order_castLength,
      BONG.GoodBONG.order_castLength]
    convert hfirstRaw using 1 <;> congr 1
  intro hp
  apply hp
  exact BONG.GoodBONG.beli2019_rankTwo_equalNorm_sufficiency
    (alphaLaws := alphaLaws) (structural := structural)
    a b p.ambient conditions' hfirst

end Beli2019RepresentationProblem

end Bong
