/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma66
import Bong.Bong.BeliLemma65Proof
import Bong.Bong.BeliLemma317
import Bong.Bong.BeliLemma318
import Bong.Bong.BeliLemma67Proof
import Bong.Bong.BinaryParameterSpinorMembership
import Bong.Bong.BinarySpinorLocalProof
import Bong.Bong.BinaryHyperbolicConverse
import Bong.Bong.PrefixIsometry
import Bong.Lattice.HyperbolicDiagonalSpinor
import Bong.Lattice.OmearaHyperbolicTransvection
import Bong.Lattice.OmearaHyperbolicSpinor
import Bong.Lattice.SpinorNormIsometry
import Bong.Lattice.SpinorNormMultiplicative
import Bong.Lattice.SpinorNormOrthogonalProduct

/-!
# Proof of Beli (2003), Lemma 6.6

This file supplies the geometric and spinor-norm constructions used in the
proof of Lemma 6.6.  In particular, the minimal rescaled binary prefix from
Lemma 6.5 is connected here to the explicit equal-value companion furnished
by Lemma 3.17.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- If an integral vector in a scaled hyperbolic plane has the same
valuation as the plane's basic norm, then both coordinates are valuation
units. -/
theorem hyperbolic_coordinates_are_units
    (a : Kˣ) (r : Int) (y : Fin 2 → K)
    (hbase : ord K (2 * (a : K)) = (r : WithTop Int))
    (hy : y ∈ Lattice.hyperbolicPlaneLattice (K := K))
    (hq : ord K ((QuadraticSpace.hyperbolicPlane a).quadratic y) =
      (r : WithTop Int)) :
    IsValuationUnit K (y 0) ∧ IsValuationUnit K (y 1) := by
  have hyCoords := (Lattice.mem_omearaPlaneLattice_iff y).1 hy
  have hqne : (QuadraticSpace.hyperbolicPlane a).quadratic y ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hq
    exact WithTop.top_ne_coe hq
  have hzero : y 0 ≠ 0 := by
    intro h
    apply hqne
    rw [QuadraticSpace.hyperbolicPlane_quadratic_apply, h]
    ring
  have hone : y 1 ≠ 0 := by
    intro h
    apply hqne
    rw [QuadraticSpace.hyperbolicPlane_quadratic_apply, h]
    ring
  let u0 : Kˣ := Units.mk0 (y 0) hzero
  let u1 : Kˣ := Units.mk0 (y 1) hone
  have hord0 : ord K (y 0) = (ordUnit K u0 : WithTop Int) := by
    simpa only [u0, Units.val_mk0] using (coe_ordUnit K u0).symm
  have hord1 : ord K (y 1) = (ordUnit K u1 : WithTop Int) := by
    simpa only [u1, Units.val_mk0] using (coe_ordUnit K u1).symm
  have hsum : ordUnit K u0 + ordUnit K u1 = 0 := by
    rw [QuadraticSpace.hyperbolicPlane_quadratic_apply] at hq
    rw [show 2 * (a : K) * (y 0 * y 1) =
        (2 * (a : K)) * (y 0 * y 1) by ring,
      ord_mul, hbase, ord_mul, hord0, hord1] at hq
    norm_cast at hq
    omega
  have h0 : 0 ≤ ordUnit K u0 := by
    have h := (mem_integerRing_iff K).1 hyCoords.1
    unfold Dyadic.IsIntegral at h
    rw [hord0] at h
    norm_cast at h
  have h1 : 0 ≤ ordUnit K u1 := by
    have h := (mem_integerRing_iff K).1 hyCoords.2
    unfold Dyadic.IsIntegral at h
    rw [hord1] at h
    norm_cast at h
  constructor
  · change ord K (y 0) = 0
    rw [hord0]
    norm_cast
    omega
  · change ord K (y 1) = 0
    rw [hord1]
    norm_cast
    omega

/-- Reflection in the first vector of the projected tail extends to an
integral reflection of the original lattice. -/
theorem tailHead_isIntegralReflection
    (b : BONG V q L (n + 2)) :
    Lattice.IsIntegralReflection (q := q) (L := L)
      (x := (b.tail.head : V)) b.tail.head_isAnisotropic := by
  exact Lattice.isIntegralReflection_of_projectedLattice
    b.head_isNormGenerator b.head_isAnisotropic
    b.tail.head_isAnisotropic
    (b.tail.head_isNormGenerator.isIntegralReflection
      b.tail.head_isAnisotropic)

/-- The tail-head reflection fixes the BONG head. -/
theorem reflection_tailHead_apply_head
    (b : BONG V q L (n + 2)) :
    q.reflectionLinearEquiv (b.tail.head : V)
        b.tail.head_isAnisotropic b.head = b.head := by
  rw [q.reflectionLinearEquiv_apply]
  have horth : q.bilin (b.tail.head : V) b.head = 0 := by
    rw [q.isSymm.eq]
    exact (q.mem_vectorOrthogonal_iff b.head (b.tail.head : V)).1
      (b.tail.head : q.vectorOrthogonal b.head).property
  rw [horth]
  simp

/-- The basic low-range rotation from Lemma 6.6: first reflect in the tail
head and then in `x_1-x`. -/
noncomputable def differenceTailRotation
    (b : BONG V q L (n + 3)) (x : V)
    (w : Lemma65DifferenceReflectionWitness b x) :
    Lattice.IntegralRotation q L :=
  Lattice.integralReflectionProduct w.anisotropic w.integral
    b.tail.head_isAnisotropic b.tailHead_isIntegralReflection

@[simp]
theorem differenceTailRotation_apply_head
    (b : BONG V q L (n + 3)) (x : V)
    (w : Lemma65DifferenceReflectionWitness b x)
    (heq : q.quadratic x = q.quadratic b.head) :
    (b.differenceTailRotation x w).apply b.head = x := by
  change q.reflectionLinearEquiv (b.head - x) w.anisotropic
    (q.reflectionLinearEquiv (b.tail.head : V)
      b.tail.head_isAnisotropic b.head) = x
  rw [b.reflection_tailHead_apply_head]
  exact q.reflectionLinearEquiv_sub_apply_left_of_quadratic_eq
    b.head x w.anisotropic heq.symm

/-- Spinor norm of the basic difference-tail rotation. -/
theorem differenceTailRotation_spinorNorm
    (b : BONG V q L (n + 3)) (x : V)
    (w : Lemma65DifferenceReflectionWitness b x) :
    (b.differenceTailRotation x w).spinorNorm =
      Lattice.reflectionSpinorClass (q := q) w.anisotropic *
        Lattice.reflectionSpinorClass (q := q)
          (x := (b.tail.head : V)) b.tail.head_isAnisotropic := by
  change Lattice.integralSpinorNorm
      (Lattice.integralReflection (q := q) (L := L)
          w.anisotropic w.integral *
        Lattice.integralReflection (q := q) (L := L)
          (x := (b.tail.head : V)) b.tail.head_isAnisotropic
            b.tailHead_isIntegralReflection) = _
  rw [Lattice.integralSpinorNorm_mul,
    Lattice.integralSpinorNorm_integralReflection,
    Lattice.integralSpinorNorm_integralReflection]

/-- The two-difference-reflection rotation used when the target projection is
not initially a norm generator. -/
noncomputable def differenceDifferenceRotation
    (b : BONG V q L (n + 3)) (x₀ x₁ : V)
    (w₀ : Lemma65DifferenceReflectionWitness b x₀)
    (w₁ : Lemma65DifferenceReflectionWitness b x₁) :
    Lattice.IntegralRotation q L :=
  Lattice.integralReflectionProduct w₀.anisotropic w₀.integral
    w₁.anisotropic w₁.integral

@[simp]
theorem differenceDifferenceRotation_apply_head
    (b : BONG V q L (n + 3)) (x x₀ x₁ : V)
    (w₀ : Lemma65DifferenceReflectionWitness b x₀)
    (w₁ : Lemma65DifferenceReflectionWitness b x₁)
    (hx₁Value : q.quadratic x₁ = q.quadratic b.head)
    (hx₁ :
      q.reflectionLinearEquiv (b.head - x₀) w₀.anisotropic x = x₁) :
    (b.differenceDifferenceRotation x₀ x₁ w₀ w₁).apply b.head = x := by
  change q.reflectionLinearEquiv (b.head - x₀) w₀.anisotropic
    (q.reflectionLinearEquiv (b.head - x₁) w₁.anisotropic b.head) = x
  rw [w₁.map_head hx₁Value]
  rw [← hx₁]
  exact q.reflectionLinearEquiv_involutive
    (b.head - x₀) w₀.anisotropic x

/-- Spinor norm of the two-difference-reflection rotation. -/
theorem differenceDifferenceRotation_spinorNorm
    (b : BONG V q L (n + 3)) (x₀ x₁ : V)
    (w₀ : Lemma65DifferenceReflectionWitness b x₀)
    (w₁ : Lemma65DifferenceReflectionWitness b x₁) :
    (b.differenceDifferenceRotation x₀ x₁ w₀ w₁).spinorNorm =
      Lattice.reflectionSpinorClass (q := q) w₀.anisotropic *
        Lattice.reflectionSpinorClass (q := q) w₁.anisotropic := by
  change Lattice.integralSpinorNorm
      (Lattice.integralReflection (q := q) (L := L)
          w₀.anisotropic w₀.integral *
        Lattice.integralReflection (q := q) (L := L)
          w₁.anisotropic w₁.integral) = _
  rw [Lattice.integralSpinorNorm_mul,
    Lattice.integralSpinorNorm_integralReflection,
    Lattice.integralSpinorNorm_integralReflection]

/-- Reflection in the BONG head is integral. -/
theorem head_isIntegralReflection (b : BONG V q L (n + 1)) :
    Lattice.IsIntegralReflection (q := q) (L := L)
      b.head_isAnisotropic :=
  b.head_isNormGenerator.isIntegralReflection b.head_isAnisotropic

/-- The high-range plus-sign rotation: reflect first in the BONG head and
then in `x_1+x`. -/
noncomputable def sumHeadRotation
    (b : BONG V q L (n + 1)) (x : V)
    (hsum : q.IsAnisotropic (b.head + x))
    (hintegral : Lattice.IsIntegralReflection (q := q) (L := L) hsum) :
    Lattice.IntegralRotation q L :=
  Lattice.integralReflectionProduct hsum hintegral
    b.head_isAnisotropic b.head_isIntegralReflection

@[simp]
theorem sumHeadRotation_apply_head
    (b : BONG V q L (n + 1)) (x : V)
    (hsum : q.IsAnisotropic (b.head + x))
    (hintegral : Lattice.IsIntegralReflection (q := q) (L := L) hsum)
    (heq : q.quadratic x = q.quadratic b.head) :
    (b.sumHeadRotation x hsum hintegral).apply b.head = x := by
  change q.reflectionLinearEquiv (b.head + x) hsum
    (q.reflectionLinearEquiv b.head b.head_isAnisotropic b.head) = x
  rw [q.reflectionLinearEquiv_apply_self]
  rw [map_neg,
    q.reflectionLinearEquiv_add_apply_left_of_quadratic_eq
      b.head x hsum heq.symm]
  simp

/-- Spinor norm of the plus-sign rotation. -/
theorem sumHeadRotation_spinorNorm
    (b : BONG V q L (n + 1)) (x : V)
    (hsum : q.IsAnisotropic (b.head + x))
    (hintegral : Lattice.IsIntegralReflection (q := q) (L := L) hsum) :
    (b.sumHeadRotation x hsum hintegral).spinorNorm =
      Lattice.reflectionSpinorClass (q := q) hsum *
        Lattice.reflectionSpinorClass (q := q) b.head_isAnisotropic := by
  change Lattice.integralSpinorNorm
      (Lattice.integralReflection (q := q) (L := L) hsum hintegral *
        Lattice.integralReflection (q := q) (L := L)
          b.head_isAnisotropic b.head_isIntegralReflection) = _
  rw [Lattice.integralSpinorNorm_mul,
    Lattice.integralSpinorNorm_integralReflection,
    Lattice.integralSpinorNorm_integralReflection]

/-- The reflection product attached to an equal-value vector is measured by
the spinor group of its normalized projection factor.  This is Lemma 3.18(i)
applied to the standard binary model `p = 1-a²`, followed by removal of the
square `Q(x₁)²`. -/
theorem headDifferenceReflectionProduct_mem_projectionFactorSpinorGroup
    (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (w : Lemma65DifferenceReflectionWitness b x)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0) :
    Lattice.reflectionSpinorClass (q := q) b.head_isAnisotropic *
        Lattice.reflectionSpinorClass (q := q) w.anisotropic ∈
      beliSpinorGroup K
        (unitSquareClass K (S.projectionFactorUnit x hfactorNe)) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  have hp : (p : K) = 1 - a ^ 2 := by
    rfl
  have htwo : (2 : K) * a ∈ IntegerRing K := by
    exact Lattice.two_projectionCoefficient_mem_integerRing
      q L b.head x b.head_isNormGenerator b.head_isAnisotropic hx
  have hdiff : q.quadratic (b.head - x) =
      2 * (1 - a) * q.quadratic b.head := by
    simpa only [a] using S.quadratic_head_sub_eq_two_mul_one_sub_mul x heq
  have hcoefficient : (2 : K) * (1 - a) ≠ 0 := by
    intro hzero
    apply w.anisotropic
    rw [hdiff, hzero, zero_mul]
  have hmodel := squareClass_two_mul_one_sub_mem_beliSpinorGroup
    (K := K) a p hp htwo hcoefficient
  let headUnit : Kˣ := Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let differenceUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x)) w.anisotropic
  let coefficientUnit : Kˣ := Units.mk0 (2 * (1 - a)) hcoefficient
  have hunit : headUnit * differenceUnit =
      coefficientUnit * headUnit ^ 2 := by
    apply Units.ext
    simp only [headUnit, differenceUnit, coefficientUnit, Units.val_mul,
      Units.val_mk0, Units.val_pow_eq_pow_val]
    rw [hdiff]
    ring
  change squareClass K headUnit * squareClass K differenceUnit ∈
    beliSpinorGroup K (unitSquareClass K p)
  change squareClass K (headUnit * differenceUnit) ∈
    beliSpinorGroup K (unitSquareClass K p)
  rw [hunit, squareClass_mul_square]
  exact hmodel

/-- Standard-model form of Beli (2003), Lemma 3.18(iii).  At parameter
order above `2e`, if the difference reflection has the critical order
`2e`, its product with the first coordinate reflection belongs to the
auxiliary group `G'(p)`. -/
theorem squareClass_two_mul_one_sub_mem_auxiliarySpinorGroup
    (a : K) (p : Kˣ)
    (hp : (p : K) = 1 - a ^ 2)
    (htwo : (2 : K) * a ∈ IntegerRing K)
    (hne : (2 : K) * (1 - a) ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) < ordUnit K p)
    (hcritical : ord K (2 * (1 - a)) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int)) :
    squareClass K (Units.mk0 (2 * (1 - a)) hne) ∈
      beliAuxiliarySpinorGroup K p hpLow := by
  have hdiag : a ^ 2 + (p : K) ∈ IntegerRing K := by
    rw [hp]
    convert (IntegerRing K).one_mem using 1 <;> ring
  let model := binaryModelBONG p a htwo hdiag
  let first : Fin 2 → K := QuadraticSpace.binaryModelFirst
  let second : Fin 2 → K := QuadraticSpace.binaryModelSecond
  have hfirst : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel p a)
      (binaryModelLattice (K := K)) first := by
    simpa only [first] using binaryModelFirst_isNormGenerator p a htwo hdiag
  have hsecondMem : second ∈ binaryModelLattice (K := K) := by
    simpa only [second] using binaryModelSecond_mem p a
  have hfirstValue :
      (QuadraticSpace.binaryModel p a).quadratic first = 1 := by
    simp only [first, QuadraticSpace.binaryModel_quadratic_first]
  have hsecondValue :
      (QuadraticSpace.binaryModel p a).quadratic second = 1 := by
    simp only [second, QuadraticSpace.binaryModel_quadratic_second, hp]
    ring
  have hsecond : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel p a)
      (binaryModelLattice (K := K)) second := by
    refine ⟨hsecondMem, ?_⟩
    calc
      Lattice.normIdeal (QuadraticSpace.binaryModel p a)
          (binaryModelLattice (K := K)) =
          Lattice.principalIdeal (K := K)
            ((QuadraticSpace.binaryModel p a).quadratic first) :=
        hfirst.normIdeal_eq
      _ = Lattice.principalIdeal (K := K)
          ((QuadraticSpace.binaryModel p a).quadratic second) := by
        rw [hfirstValue, hsecondValue]
  have heq : (QuadraticSpace.binaryModel p a).quadratic first =
      (QuadraticSpace.binaryModel p a).quadratic second := by
    rw [hfirstValue, hsecondValue]
  have hsubValue :
      (QuadraticSpace.binaryModel p a).quadratic (first - second) =
        2 * (1 - a) := by
    rw [QuadraticSpace.binaryModel_quadratic_apply]
    simp only [first, second, QuadraticSpace.binaryModelFirst,
      QuadraticSpace.binaryModelSecond, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
      Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero,
      zero_sub, one_pow]
    rw [hp]
    ring
  have hsub : (QuadraticSpace.binaryModel p a).IsAnisotropic
      (first - second) := by
    rw [QuadraticSpace.IsAnisotropic, hsubValue]
    exact hne
  have hparameterClass : unitSquareClass K model.binaryParameter =
      unitSquareClass K p := by
    simpa only [binaryUnitSquareClass] using
      binaryModelBONG_binaryUnitSquareClass p a htwo hdiag
  have hparameterOrder : ordUnit K model.binaryParameter = ordUnit K p :=
    ordUnit_eq_of_unitSquareClass_eq (K := K) hparameterClass
  have hgap : 2 * (ramificationIndex K : Int) <
      model.binaryOrderGap := by
    rw [← model.binaryParameterOrder_eq_orderGap]
    change 2 * (ramificationIndex K : Int) <
      ordUnit K model.binaryParameter
    rw [hparameterOrder]
    exact hpLow
  have hminusOrder :
      ord K ((QuadraticSpace.binaryModel p a).quadratic (first - second)) =
        ord K ((QuadraticSpace.binaryModel p a).quadratic first) +
          ord K (2 : K) + ord K (2 : K) := by
    rw [hsubValue, hfirstValue, ord_one, hcritical,
      ← ramificationIndex_spec]
    norm_cast
    ring
  have hmem :=
    model.equalNormGenerator_reflectionProduct_mem_auxiliarySpinorGroup
      first second hfirst hsecond heq hsub hgap hminusOrder
  change squareClass K
      (Units.mk0
          ((QuadraticSpace.binaryModel p a).quadratic first)
          (model.isAnisotropic_of_isNormGenerator_binary hfirst) *
        Units.mk0
          ((QuadraticSpace.binaryModel p a).quadratic (first - second))
          hsub) ∈
    beliAuxiliarySpinorGroupRepresentative K model.binaryParameter at hmem
  have hgroup :
      beliAuxiliarySpinorGroupRepresentative K model.binaryParameter =
        beliAuxiliarySpinorGroupRepresentative K p :=
    beliAuxiliarySpinorGroupRepresentative_eq_of_unitSquareClass_eq K
      hparameterClass
  rw [hgroup] at hmem
  have hunit :
      Units.mk0
          ((QuadraticSpace.binaryModel p a).quadratic first)
          (model.isAnisotropic_of_isNormGenerator_binary hfirst) *
        Units.mk0
          ((QuadraticSpace.binaryModel p a).quadratic (first - second))
          hsub =
        Units.mk0 (2 * (1 - a)) hne := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, hfirstValue, hsubValue, one_mul]
  change squareClass K (Units.mk0 (2 * (1 - a)) hne) ∈
    beliAuxiliarySpinorGroupRepresentative K p
  rwa [hunit] at hmem

/-- The critical equal-value reflection product for the ambient BONG lies
in the auxiliary spinor group of its projection factor. -/
theorem headDifferenceReflectionProduct_mem_projectionFactorAuxiliarySpinorGroup
    (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (w : Lemma65DifferenceReflectionWitness b x)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hcritical : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    Lattice.reflectionSpinorClass (q := q) b.head_isAnisotropic *
        Lattice.reflectionSpinorClass (q := q) w.anisotropic ∈
      beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow := by
  let alpha : K := q.bilin b.head x / q.quadratic b.head
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  have hp : (p : K) = 1 - alpha ^ 2 := rfl
  have htwo : (2 : K) * alpha ∈ IntegerRing K := by
    exact Lattice.two_projectionCoefficient_mem_integerRing
      q L b.head x b.head_isNormGenerator b.head_isAnisotropic hx
  have hdiff : q.quadratic (b.head - x) =
      2 * (1 - alpha) * q.quadratic b.head := by
    simpa only [alpha] using
      S.quadratic_head_sub_eq_two_mul_one_sub_mul x heq
  have hcoefficient : (2 : K) * (1 - alpha) ≠ 0 := by
    intro hzero
    apply w.anisotropic
    rw [hdiff, hzero, zero_mul]
  have hcoefficientOrder : ord K (2 * (1 - alpha)) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) := by
    rw [hdiff, ord_mul, ← b.value_zero_eq_quadratic_head,
      ← b.coe_order] at hcritical
    by_cases hcoefficientZero : (2 : K) * (1 - alpha) = 0
    · exact (hcoefficient hcoefficientZero).elim
    · let coefficient : Kˣ :=
        Units.mk0 (2 * (1 - alpha)) hcoefficientZero
      have hcoefficientFinite : ord K (2 * (1 - alpha)) =
          (ordUnit K coefficient : WithTop Int) := by
        simpa only [coefficient, Units.val_mk0] using
          (coe_ordUnit K coefficient).symm
      rw [hcoefficientFinite] at hcritical ⊢
      norm_cast at hcritical ⊢
      omega
  have hmodel := squareClass_two_mul_one_sub_mem_auxiliarySpinorGroup
    (K := K) alpha p hp htwo hcoefficient (by simpa only [p] using hpLow)
      hcoefficientOrder
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let differenceUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x)) w.anisotropic
  let coefficientUnit : Kˣ :=
    Units.mk0 (2 * (1 - alpha)) hcoefficient
  have hunit : headUnit * differenceUnit =
      coefficientUnit * headUnit ^ 2 := by
    apply Units.ext
    simp only [headUnit, differenceUnit, coefficientUnit, Units.val_mul,
      Units.val_mk0, Units.val_pow_eq_pow_val]
    rw [hdiff]
    ring
  change squareClass K headUnit * squareClass K differenceUnit ∈
    beliAuxiliarySpinorGroup K p (by simpa only [p] using hpLow)
  change squareClass K (headUnit * differenceUnit) ∈
    beliAuxiliarySpinorGroup K p (by simpa only [p] using hpLow)
  rw [hunit, squareClass_mul_square]
  exact hmodel

/-- The two coordinate reflections in the first binary BONG block have
spinor class equal to the adjacent parameter.  Paragraph 3.16 therefore
places their product in the first binary spinor group. -/
theorem headTailReflectionProduct_mem_adjacentSpinorGroup
    (b : BONG V q L (n + 3)) :
    Lattice.reflectionSpinorClass (q := q) b.head_isAnisotropic *
        Lattice.reflectionSpinorClass (q := q)
          (x := (b.tail.head : V)) b.tail.head_isAnisotropic ∈
      beliSpinorGroup K (b.adjacentUnitSquareClass 0 (by simp)) := by
  let P := b.prefixWitness 2 (by omega)
  have hparameter : P.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [P.valueUnit_eq, P.valueUnit_eq]
    congr 2
  have hadjacent : squareClass K (b.adjacentParameter 0 (by simp)) ∈
      beliSpinorGroup K (b.adjacentUnitSquareClass 0 (by simp)) := by
    have hmem := P.bong.binaryParameter_mem_beliSpinorGroup
    unfold binaryUnitSquareClass at hmem
    unfold adjacentUnitSquareClass
    rwa [hparameter] at hmem
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let tailUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.tail.head : V)) b.tail.head_isAnisotropic
  have hhead : headUnit = b.valueUnit 0 := by
    apply Units.ext
    simp only [headUnit, Units.val_mk0, coe_valueUnit]
    exact b.value_zero_eq_quadratic_head.symm
  have htail : tailUnit = b.valueUnit 1 := by
    apply Units.ext
    simp only [tailUnit, Units.val_mk0, coe_valueUnit]
    calc
      q.quadratic (b.tail.head : V) = b.tail.value 0 := by
        exact b.tail.value_zero_eq_quadratic_head.symm
      _ = b.value 1 := b.value_tail 0
  have hproduct : headUnit * tailUnit =
      b.adjacentParameter 0 (by simp) * headUnit ^ 2 := by
    rw [hhead, htail]
    unfold adjacentParameter
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm]
    ac_rfl
  change squareClass K (headUnit * tailUnit) ∈
    beliSpinorGroup K (b.adjacentUnitSquareClass 0 (by simp))
  rw [hproduct, squareClass_mul_square]
  exact hadjacent

/-- Once the projection-factor binary group is contained in the target
group, the low-range difference--tail rotation has the required spinor
norm.  The two occurrences of the head reflection cancel in square classes. -/
theorem differenceTailRotation_spinorNorm_mem_of_projectionFactor_le
    (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (w : Lemma65DifferenceReflectionWitness b x)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hle : beliSpinorGroup K
        (unitSquareClass K (S.projectionFactorUnit x hfactorNe)) ≤
      b.lemma66SharpHeadFactor) :
    (b.differenceTailRotation x w).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let differenceUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x)) w.anisotropic
  let tailUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.tail.head : V)) b.tail.head_isAnisotropic
  have hdifference : squareClass K headUnit * squareClass K differenceUnit ∈
      b.lemma66SharpHeadFactor := by
    apply hle
    exact b.headDifferenceReflectionProduct_mem_projectionFactorSpinorGroup
      S x hx heq w hfactorNe
  have htail : squareClass K headUnit * squareClass K tailUnit ∈
      b.lemma66SharpHeadFactor := by
    apply (show beliSpinorGroup K
        (b.adjacentUnitSquareClass 0 (by simp)) ≤
      b.lemma66SharpHeadFactor from le_sup_left)
    exact b.headTailReflectionProduct_mem_adjacentSpinorGroup
  have hproduct := b.lemma66SharpHeadFactor.mul_mem hdifference htail
  have hheadSq : squareClass K headUnit * squareClass K headUnit = 1 := by
    simpa only [pow_two] using squareClass_sq_eq_one headUnit
  rw [b.differenceTailRotation_spinorNorm]
  change squareClass K differenceUnit * squareClass K tailUnit ∈
    b.lemma66SharpHeadFactor
  convert hproduct using 1
  calc
    squareClass K differenceUnit * squareClass K tailUnit =
        (squareClass K headUnit * squareClass K headUnit) *
          (squareClass K differenceUnit * squareClass K tailUnit) := by
            rw [hheadSq, one_mul]
    _ = (squareClass K headUnit * squareClass K differenceUnit) *
        (squareClass K headUnit * squareClass K tailUnit) := by ac_rfl

/-- Two difference reflections have target spinor norm as soon as the two
associated projection-factor spinor groups are contained in the target. -/
theorem differenceDifferenceRotation_spinorNorm_mem_of_projectionFactors_le
    (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) (x₀ x₁ : V)
    (hx₀ : x₀ ∈ L) (hx₁ : x₁ ∈ L)
    (heq₀ : q.quadratic x₀ = q.quadratic b.head)
    (heq₁ : q.quadratic x₁ = q.quadratic b.head)
    (w₀ : Lemma65DifferenceReflectionWitness b x₀)
    (w₁ : Lemma65DifferenceReflectionWitness b x₁)
    (hfactorNe₀ :
      1 - (q.bilin b.head x₀ / q.quadratic b.head) ^ 2 ≠ 0)
    (hfactorNe₁ :
      1 - (q.bilin b.head x₁ / q.quadratic b.head) ^ 2 ≠ 0)
    (hle₀ : beliSpinorGroup K
        (unitSquareClass K (S.projectionFactorUnit x₀ hfactorNe₀)) ≤
      b.lemma66SharpHeadFactor)
    (hle₁ : beliSpinorGroup K
        (unitSquareClass K (S.projectionFactorUnit x₁ hfactorNe₁)) ≤
      b.lemma66SharpHeadFactor) :
    (b.differenceDifferenceRotation x₀ x₁ w₀ w₁).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let differenceUnit₀ : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x₀)) w₀.anisotropic
  let differenceUnit₁ : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x₁)) w₁.anisotropic
  have h₀ : squareClass K headUnit * squareClass K differenceUnit₀ ∈
      b.lemma66SharpHeadFactor := by
    apply hle₀
    exact b.headDifferenceReflectionProduct_mem_projectionFactorSpinorGroup
      S x₀ hx₀ heq₀ w₀ hfactorNe₀
  have h₁ : squareClass K headUnit * squareClass K differenceUnit₁ ∈
      b.lemma66SharpHeadFactor := by
    apply hle₁
    exact b.headDifferenceReflectionProduct_mem_projectionFactorSpinorGroup
      S x₁ hx₁ heq₁ w₁ hfactorNe₁
  have hproduct := b.lemma66SharpHeadFactor.mul_mem h₀ h₁
  have hheadSq : squareClass K headUnit * squareClass K headUnit = 1 := by
    simpa only [pow_two] using squareClass_sq_eq_one headUnit
  rw [b.differenceDifferenceRotation_spinorNorm]
  change squareClass K differenceUnit₀ * squareClass K differenceUnit₁ ∈
    b.lemma66SharpHeadFactor
  convert hproduct using 1
  calc
    squareClass K differenceUnit₀ * squareClass K differenceUnit₁ =
        (squareClass K headUnit * squareClass K headUnit) *
          (squareClass K differenceUnit₀ * squareClass K differenceUnit₁) := by
            rw [hheadSq, one_mul]
    _ = (squareClass K headUnit * squareClass K differenceUnit₀) *
        (squareClass K headUnit * squareClass K differenceUnit₁) := by ac_rfl

/-- The plus-sign rotation is the difference-reflection construction applied
to `-x`; commutativity of square classes reverses the two reflection factors. -/
theorem sumHeadRotation_spinorNorm_mem_of_projectionFactor_neg_le
    (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hsum : q.IsAnisotropic (b.head + x))
    (hintegral : Lattice.IsIntegralReflection (q := q) (L := L) hsum)
    (hfactorNe :
      1 - (q.bilin b.head (-x) / q.quadratic b.head) ^ 2 ≠ 0)
    (hle : beliSpinorGroup K
        (unitSquareClass K (S.projectionFactorUnit (-x) hfactorNe)) ≤
      b.lemma66SharpHeadFactor) :
    (b.sumHeadRotation x hsum hintegral).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  have hxneg : -x ∈ L := L.neg_mem hx
  have heqneg : q.quadratic (-x) = q.quadratic b.head := by
    rw [q.quadratic_neg, heq]
  let wneg : Lemma65DifferenceReflectionWitness b (-x) :=
    ⟨by simpa only [sub_neg_eq_add] using hsum,
      by simpa only [sub_neg_eq_add] using hintegral⟩
  have hmem := b.headDifferenceReflectionProduct_mem_projectionFactorSpinorGroup
    S (-x) hxneg heqneg wneg hfactorNe
  have htarget := hle hmem
  rw [b.sumHeadRotation_spinorNorm]
  have hsumClass : Lattice.reflectionSpinorClass (q := q) hsum =
      Lattice.reflectionSpinorClass (q := q) wneg.anisotropic := by
    unfold Lattice.reflectionSpinorClass
    congr 1
    apply Units.ext
    simp only [Units.val_mk0, sub_neg_eq_add]
  rw [hsumClass]
  simpa only [mul_comm] using htarget

/-- High-range analogue of the difference--tail spinor calculation.  The
critical reflection product is measured by `G'` rather than `G`. -/
theorem differenceTailRotation_spinorNorm_mem_of_projectionFactorAuxiliary_le
    (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (w : Lemma65DifferenceReflectionWitness b x)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hcritical : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int))
    (hle : beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor) :
    (b.differenceTailRotation x w).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let differenceUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x)) w.anisotropic
  let tailUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.tail.head : V)) b.tail.head_isAnisotropic
  have hdifference : squareClass K headUnit * squareClass K differenceUnit ∈
      b.lemma66SharpHeadFactor := by
    apply hle
    exact b.headDifferenceReflectionProduct_mem_projectionFactorAuxiliarySpinorGroup
      S x hx heq w hfactorNe hpLow hcritical
  have htail : squareClass K headUnit * squareClass K tailUnit ∈
      b.lemma66SharpHeadFactor := by
    apply (show beliSpinorGroup K
        (b.adjacentUnitSquareClass 0 (by simp)) ≤
      b.lemma66SharpHeadFactor from le_sup_left)
    exact b.headTailReflectionProduct_mem_adjacentSpinorGroup
  have hproduct := b.lemma66SharpHeadFactor.mul_mem hdifference htail
  have hheadSq : squareClass K headUnit * squareClass K headUnit = 1 := by
    simpa only [pow_two] using squareClass_sq_eq_one headUnit
  rw [b.differenceTailRotation_spinorNorm]
  change squareClass K differenceUnit * squareClass K tailUnit ∈
    b.lemma66SharpHeadFactor
  convert hproduct using 1
  calc
    squareClass K differenceUnit * squareClass K tailUnit =
        (squareClass K headUnit * squareClass K headUnit) *
          (squareClass K differenceUnit * squareClass K tailUnit) := by
            rw [hheadSq, one_mul]
    _ = (squareClass K headUnit * squareClass K differenceUnit) *
        (squareClass K headUnit * squareClass K tailUnit) := by ac_rfl

/-- Plus-sign counterpart of the preceding high-range spinor calculation,
obtained by applying the critical auxiliary-group statement to `-x`. -/
theorem sumHeadRotation_spinorNorm_mem_of_projectionFactorNegAuxiliary_le
    (b : BONG V q L (n + 3))
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hsum : q.IsAnisotropic (b.head + x))
    (hintegral : Lattice.IsIntegralReflection (q := q) (L := L) hsum)
    (hfactorNe :
      1 - (q.bilin b.head (-x) / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit (-x) hfactorNe))
    (hcritical : ord K (q.quadratic (b.head + x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int))
    (hle : beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit (-x) hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor) :
    (b.sumHeadRotation x hsum hintegral).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  have hxneg : -x ∈ L := L.neg_mem hx
  have heqneg : q.quadratic (-x) = q.quadratic b.head := by
    rw [q.quadratic_neg, heq]
  let wneg : Lemma65DifferenceReflectionWitness b (-x) :=
    ⟨by simpa only [sub_neg_eq_add] using hsum,
      by simpa only [sub_neg_eq_add] using hintegral⟩
  have hcriticalNeg : ord K (q.quadratic (b.head - (-x))) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int) := by
    simpa only [sub_neg_eq_add] using hcritical
  have hmem :=
    b.headDifferenceReflectionProduct_mem_projectionFactorAuxiliarySpinorGroup
      S (-x) hxneg heqneg wneg hfactorNe hpLow hcriticalNeg
  have htarget := hle hmem
  rw [b.sumHeadRotation_spinorNorm]
  have hsumClass : Lattice.reflectionSpinorClass (q := q) hsum =
      Lattice.reflectionSpinorClass (q := q) wneg.anisotropic := by
    unfold Lattice.reflectionSpinorClass
    congr 1
    apply Units.ext
    simp only [Units.val_mk0, sub_neg_eq_add]
  rw [hsumClass]
  simpa only [mul_comm] using htarget

/-- Intrinsic form of the critical reflection-product calculation.  Unlike
the setup-indexed version, this statement can be used in the exceptional
branch, where the projection factor is defined before choosing any least
head rescaling. -/
theorem headDifferenceReflectionProduct_mem_projectionFactorAuxiliarySpinorGroupIntrinsic
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (w : Lemma65DifferenceReflectionWitness b x)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe))
    (hcritical : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    Lattice.reflectionSpinorClass (q := q) b.head_isAnisotropic *
        Lattice.reflectionSpinorClass (q := q) w.anisotropic ∈
      beliAuxiliarySpinorGroup K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe)
          hpLow := by
  let alpha : K := q.bilin b.head x / q.quadratic b.head
  let p : Kˣ :=
    Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe
  have hp : (p : K) = 1 - alpha ^ 2 := rfl
  have htwo : (2 : K) * alpha ∈ IntegerRing K := by
    exact Lattice.two_projectionCoefficient_mem_integerRing
      q L b.head x b.head_isNormGenerator b.head_isAnisotropic hx
  have hdiff : q.quadratic (b.head - x) =
      2 * (1 - alpha) * q.quadratic b.head := by
    simpa only [alpha] using
      Lemma65Setup.quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic
        b x heq
  have hcoefficient : (2 : K) * (1 - alpha) ≠ 0 := by
    intro hzero
    apply w.anisotropic
    rw [hdiff, hzero, zero_mul]
  have hcoefficientOrder : ord K (2 * (1 - alpha)) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) := by
    rw [hdiff, ord_mul, ← b.value_zero_eq_quadratic_head,
      ← b.coe_order] at hcritical
    let coefficient : Kˣ :=
      Units.mk0 (2 * (1 - alpha)) hcoefficient
    have hcoefficientFinite : ord K (2 * (1 - alpha)) =
        (ordUnit K coefficient : WithTop Int) := by
      simpa only [coefficient, Units.val_mk0] using
        (coe_ordUnit K coefficient).symm
    rw [hcoefficientFinite] at hcritical ⊢
    norm_cast at hcritical ⊢
    omega
  have hmodel := squareClass_two_mul_one_sub_mem_auxiliarySpinorGroup
    (K := K) alpha p hp htwo hcoefficient (by simpa only [p] using hpLow)
      hcoefficientOrder
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let differenceUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x)) w.anisotropic
  let coefficientUnit : Kˣ :=
    Units.mk0 (2 * (1 - alpha)) hcoefficient
  have hunit : headUnit * differenceUnit =
      coefficientUnit * headUnit ^ 2 := by
    apply Units.ext
    simp only [headUnit, differenceUnit, coefficientUnit, Units.val_mul,
      Units.val_mk0, Units.val_pow_eq_pow_val]
    rw [hdiff]
    ring
  change squareClass K headUnit * squareClass K differenceUnit ∈
    beliAuxiliarySpinorGroup K p (by simpa only [p] using hpLow)
  change squareClass K (headUnit * differenceUnit) ∈
    beliAuxiliarySpinorGroup K p (by simpa only [p] using hpLow)
  rw [hunit, squareClass_mul_square]
  exact hmodel

/-- Intrinsic exceptional-branch analogue of the high-range
difference--tail spinor calculation. -/
theorem differenceTailRotation_spinorNorm_mem_of_projectionFactorAuxiliaryIntrinsic_le
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (w : Lemma65DifferenceReflectionWitness b x)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe))
    (hcritical : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int))
    (hle : beliAuxiliarySpinorGroup K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe)
          hpLow ≤ b.lemma66SharpHeadFactor) :
    (b.differenceTailRotation x w).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let differenceUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x)) w.anisotropic
  let tailUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.tail.head : V)) b.tail.head_isAnisotropic
  have hdifference : squareClass K headUnit * squareClass K differenceUnit ∈
      b.lemma66SharpHeadFactor := by
    apply hle
    exact
      b.headDifferenceReflectionProduct_mem_projectionFactorAuxiliarySpinorGroupIntrinsic
        x hx heq w hfactorNe hpLow hcritical
  have htail : squareClass K headUnit * squareClass K tailUnit ∈
      b.lemma66SharpHeadFactor := by
    apply (show beliSpinorGroup K
        (b.adjacentUnitSquareClass 0 (by simp)) ≤
      b.lemma66SharpHeadFactor from le_sup_left)
    exact b.headTailReflectionProduct_mem_adjacentSpinorGroup
  have hproduct := b.lemma66SharpHeadFactor.mul_mem hdifference htail
  have hheadSq : squareClass K headUnit * squareClass K headUnit = 1 := by
    simpa only [pow_two] using squareClass_sq_eq_one headUnit
  rw [b.differenceTailRotation_spinorNorm]
  change squareClass K differenceUnit * squareClass K tailUnit ∈
    b.lemma66SharpHeadFactor
  convert hproduct using 1
  calc
    squareClass K differenceUnit * squareClass K tailUnit =
        (squareClass K headUnit * squareClass K headUnit) *
          (squareClass K differenceUnit * squareClass K tailUnit) := by
            rw [hheadSq, one_mul]
    _ = (squareClass K headUnit * squareClass K differenceUnit) *
        (squareClass K headUnit * squareClass K tailUnit) := by ac_rfl

/-- Intrinsic plus-sign counterpart, obtained from the preceding theorem at
`-x`. -/
theorem sumHeadRotation_spinorNorm_mem_of_projectionFactorNegAuxiliaryIntrinsic_le
    (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hsum : q.IsAnisotropic (b.head + x))
    (hintegral : Lattice.IsIntegralReflection (q := q) (L := L) hsum)
    (hfactorNe :
      1 - (q.bilin b.head (-x) / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b (-x) hfactorNe))
    (hcritical : ord K (q.quadratic (b.head + x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int))
    (hle : beliAuxiliarySpinorGroup K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b (-x) hfactorNe)
          hpLow ≤ b.lemma66SharpHeadFactor) :
    (b.sumHeadRotation x hsum hintegral).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  have hxneg : -x ∈ L := L.neg_mem hx
  have heqneg : q.quadratic (-x) = q.quadratic b.head := by
    rw [q.quadratic_neg, heq]
  let wneg : Lemma65DifferenceReflectionWitness b (-x) :=
    ⟨by simpa only [sub_neg_eq_add] using hsum,
      by simpa only [sub_neg_eq_add] using hintegral⟩
  have hcriticalNeg : ord K (q.quadratic (b.head - (-x))) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int) := by
    simpa only [sub_neg_eq_add] using hcritical
  have hmem :=
    b.headDifferenceReflectionProduct_mem_projectionFactorAuxiliarySpinorGroupIntrinsic
      (-x) hxneg heqneg wneg hfactorNe hpLow hcriticalNeg
  have htarget := hle hmem
  rw [b.sumHeadRotation_spinorNorm]
  have hsumClass : Lattice.reflectionSpinorClass (q := q) hsum =
      Lattice.reflectionSpinorClass (q := q) wneg.anisotropic := by
    unfold Lattice.reflectionSpinorClass
    congr 1
    apply Units.ext
    simp only [Units.val_mk0, sub_neg_eq_add]
  rw [hsumClass]
  simpa only [mul_comm] using htarget

/-- Degenerate projection-factor endpoint for the difference-sign
construction.  If `1-a²=0`, anisotropy of `x₁-x` excludes `a=1`, hence
`a=-1` and `Q(x₁-x)=4Q(x₁)`.  Its square class is therefore the head square
class, so the difference--tail rotation has the first adjacent binary
spinor class. -/
theorem differenceTailRotation_spinorNorm_mem_of_projectionFactor_eq_zero
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (w : Lemma65DifferenceReflectionWitness b x)
    (hfactorZero :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 = 0) :
    (b.differenceTailRotation x w).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  let alpha : K := q.bilin b.head x / q.quadratic b.head
  have halphaSq : alpha ^ 2 = 1 := by
    have h := sub_eq_zero.mp hfactorZero
    simpa only [alpha] using h.symm
  have halphaNeOne : alpha ≠ 1 := by
    intro halpha
    apply w.anisotropic
    rw [Lemma65Setup.quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic
      b x heq]
    change 2 * (1 - alpha) * q.quadratic b.head = 0
    rw [halpha]
    ring
  have halphaNeg : alpha = -1 :=
    (sq_eq_one_iff.mp halphaSq).resolve_left halphaNeOne
  have hdifferenceValue : q.quadratic (b.head - x) =
      (2 : K) ^ 2 * q.quadratic b.head := by
    rw [Lemma65Setup.quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic
      b x heq]
    change 2 * (1 - alpha) * q.quadratic b.head = _
    rw [halphaNeg]
    ring
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let differenceUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.head - x)) w.anisotropic
  let twoUnit : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let tailUnit : Kˣ :=
    Units.mk0 (q.quadratic (b.tail.head : V)) b.tail.head_isAnisotropic
  have hdifferenceUnit : differenceUnit = headUnit * twoUnit ^ 2 := by
    apply Units.ext
    simp only [differenceUnit, headUnit, twoUnit, Units.val_mk0,
      Units.val_mul, Units.val_pow_eq_pow_val]
    rw [hdifferenceValue]
    ring
  have hdifferenceClass : squareClass K differenceUnit =
      squareClass K headUnit := by
    rw [hdifferenceUnit, squareClass_mul_square]
  have htarget : squareClass K headUnit * squareClass K tailUnit ∈
      b.lemma66SharpHeadFactor := by
    apply (show beliSpinorGroup K
        (b.adjacentUnitSquareClass 0 (by simp)) ≤
      b.lemma66SharpHeadFactor from le_sup_left)
    exact b.headTailReflectionProduct_mem_adjacentSpinorGroup
  rw [b.differenceTailRotation_spinorNorm]
  change squareClass K differenceUnit * squareClass K tailUnit ∈
    b.lemma66SharpHeadFactor
  rwa [hdifferenceClass]

/-- Degenerate projection-factor endpoint for the plus-sign construction.
Applied to `-x`, the same argument gives `Q(x₁+x)=4Q(x₁)`; multiplying by
the head reflection leaves a square, so the spinor norm is trivial. -/
theorem sumHeadRotation_spinorNorm_mem_of_projectionFactorNeg_eq_zero
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hsum : q.IsAnisotropic (b.head + x))
    (hintegral : Lattice.IsIntegralReflection (q := q) (L := L) hsum)
    (hfactorZero :
      1 - (q.bilin b.head (-x) / q.quadratic b.head) ^ 2 = 0) :
    (b.sumHeadRotation x hsum hintegral).spinorNorm ∈
      b.lemma66SharpHeadFactor := by
  let alpha : K := q.bilin b.head (-x) / q.quadratic b.head
  have heqneg : q.quadratic (-x) = q.quadratic b.head := by
    rw [q.quadratic_neg, heq]
  have halphaSq : alpha ^ 2 = 1 := by
    have h := sub_eq_zero.mp hfactorZero
    simpa only [alpha] using h.symm
  have halphaNeOne : alpha ≠ 1 := by
    intro halpha
    apply hsum
    have hvalue :=
      Lemma65Setup.quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic
        b (-x) heqneg
    rw [sub_neg_eq_add] at hvalue
    rw [hvalue]
    change 2 * (1 - alpha) * q.quadratic b.head = 0
    rw [halpha]
    ring
  have halphaNeg : alpha = -1 :=
    (sq_eq_one_iff.mp halphaSq).resolve_left halphaNeOne
  have hsumValue : q.quadratic (b.head + x) =
      (2 : K) ^ 2 * q.quadratic b.head := by
    have hvalue :=
      Lemma65Setup.quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic
        b (-x) heqneg
    rw [sub_neg_eq_add] at hvalue
    rw [hvalue]
    change 2 * (1 - alpha) * q.quadratic b.head = _
    rw [halphaNeg]
    ring
  let headUnit : Kˣ :=
    Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let sumUnit : Kˣ := Units.mk0 (q.quadratic (b.head + x)) hsum
  let twoUnit : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have hsumUnit : sumUnit = headUnit * twoUnit ^ 2 := by
    apply Units.ext
    simp only [sumUnit, headUnit, twoUnit, Units.val_mk0,
      Units.val_mul, Units.val_pow_eq_pow_val]
    rw [hsumValue]
    ring
  have hsumClass : squareClass K sumUnit = squareClass K headUnit := by
    rw [hsumUnit, squareClass_mul_square]
  rw [b.sumHeadRotation_spinorNorm]
  change squareClass K sumUnit * squareClass K headUnit ∈
    b.lemma66SharpHeadFactor
  have hheadSq : squareClass K headUnit * squareClass K headUnit = 1 := by
    simpa only [pow_two] using squareClass_sq_eq_one headUnit
  rw [hsumClass, hheadSq]
  exact b.lemma66SharpHeadFactor.one_mem

/-- A hyperbolic first binary prefix has the endpoint gap `-2e`.  The
parity needed in the older formulation is forced by volume monotonicity and
is therefore not an additional hypothesis. -/
theorem firstBinary_orderGap_eq_neg_two_mul_ramificationIndex
    (b : BONG V q L (n + 3)) (hH : b.FirstBinaryIsHyperbolic) :
    b.order 1 - b.order 0 =
      -(2 * (ramificationIndex K : Int)) := by
  let P := b.prefixWitness 2 (by omega)
  have hrestricted : Lattice.ContainsScaledHyperbolicPlane
      (q.restrict P.carrier P.nondegenerate) P.lattice
      ((P.bong.order 0 + P.bong.order 1) / 2) := by
    apply containsScaledHyperbolicPlane_restrict P.quadraticSublattice
    change P.quadraticSublattice.ContainsScaledHyperbolicPlane
      ((b.order 0 + b.order 1) / 2) at hH
    have hscale : (P.bong.order 0 + P.bong.order 1) / 2 =
        (b.order 0 + b.order 1) / 2 := by
      rw [P.order_eq, P.order_eq]
      simp [SegmentWitness.sourceIndex]
    rwa [hscale]
  have hgap :=
    P.bong.binaryOrderGap_eq_neg_two_mul_ramificationIndex_of_contains_natural
      hrestricted
  change P.bong.order 1 - P.bong.order 0 =
      -(2 * (ramificationIndex K : Int)) at hgap
  rw [P.order_eq, P.order_eq] at hgap
  simpa [SegmentWitness.sourceIndex] using hgap

/-- Property B separates a hyperbolic first binary prefix from the remaining
coordinates, so the coordinate cut after the first two vectors is an actual
orthogonal lattice splitting. -/
theorem hasTwoBlockSplit_two_of_firstBinary_hyperbolic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hH : b.FirstBinaryIsHyperbolic) :
    b.HasTwoBlockSplit 2 (by omega) := by
  have hgap :=
    b.firstBinary_orderGap_eq_neg_two_mul_ramificationIndex hH
  let i0 : Fin (n + 3) := ⟨0, by omega⟩
  have hzeroThirdRaw :=
    hB.hasPropertyA i0 (by simp [i0])
  have hzeroThird : b.order 0 < b.order 2 := by
    convert hzeroThirdRaw using 1 <;>
      congr 1 <;> apply Fin.ext <;> simp [i0]
  apply b.exists_twoBlockSplit_of_leftOrders_le_rightHead
      2 (by omega) (by omega)
  intro i
  rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
  fin_cases i
  · change b.order 0 ≤ b.order 2
    exact hzeroThird.le
  · change b.order 1 ≤ b.order 2
    have hePosNat := ramificationIndex_pos K
    have hePos : 0 < (ramificationIndex K : Int) := by exact_mod_cast hePosNat
    omega

/-- In the exceptional residue-two branch the intrinsic projection has order
strictly above `R₁+2e`, using the directly constructed once-rescaled tail. -/
theorem exceptional_projection_order_lower
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional) :
    (((b.order 0 + 2 * (ramificationIndex K : Int) + 1 : Int)) :
        WithTop Int) ≤
      ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (b.lemma65Projection x)) := by
  let E := Lemma65Setup.exceptionalProjectionWitnessIntrinsic
    b hB x hx heq hexceptional.1 hexceptional.2.1 hexceptional.2.2
  have hdeep :=
    (E.tailRescaleOne.bong.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one
      (b.lemma65Projection x)).1
        ⟨E.projection_mem, E.projection_not_generator⟩ |>.2
  have htailOrder : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have hrescaledOrder : E.tailRescaleOne.bong.order 0 = b.order 1 + 2 := by
    rw [E.tailRescaleOne.order_zero_eq, htailOrder]
    norm_num
  rw [hrescaledOrder] at hdeep
  have hgap := hexceptional.1
  unfold lemma62Gap at hgap
  convert hdeep using 1 <;> norm_cast <;> omega

/-- Exceptional counterpart of the dyadic sign choice in Lemma 6.6. -/
theorem exceptional_head_sub_or_add_order_eq
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional) :
    ord K (q.quadratic (b.head - x)) =
        ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
          WithTop Int) ∨
      ord K (q.quadratic (b.head + x)) =
        ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
          WithTop Int) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  have hprojectionLower :=
    b.exceptional_projection_order_lower hB x hx heq hexceptional
  have hprojectionEq :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection x) =
        (1 - a ^ 2) * q.quadratic b.head := by
    simpa only [a] using
      Lemma65Setup.quadratic_lemma65Projection_eq_one_sub_sq_mul_intrinsic
        b x heq
  have hheadOrder : ord K (q.quadratic b.head) =
      (b.order 0 : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  have hfactorLarge :
      ord K (2 : K) + ord K (2 : K) < ord K (1 - a ^ 2) := by
    rw [hprojectionEq, ord_mul, hheadOrder] at hprojectionLower
    by_cases hfactorZero : 1 - a ^ 2 = 0
    · rw [hfactorZero, ord_zero]
      rw [← ramificationIndex_spec]
      exact WithTop.coe_lt_top _
    · let factor : Kˣ := Units.mk0 (1 - a ^ 2) hfactorZero
      have hfactorOrder : ord K (1 - a ^ 2) =
          (ordUnit K factor : WithTop Int) := by
        simpa only [factor, Units.val_mk0] using
          (coe_ordUnit K factor).symm
      rw [hfactorOrder, ← ramificationIndex_spec]
      rw [hfactorOrder] at hprojectionLower
      norm_cast at hprojectionLower ⊢
      omega
  have hlinear :=
    one_sub_one_add_order_dichotomy_of_two_ord_two_lt a hfactorLarge
  have hsubValue : q.quadratic (b.head - x) =
      2 * (1 - a) * q.quadratic b.head := by
    simpa only [a] using
      Lemma65Setup.quadratic_head_sub_eq_two_mul_one_sub_mul_intrinsic
        b x heq
  have haddValue : q.quadratic (b.head + x) =
      2 * (1 + a) * q.quadratic b.head := by
    simpa only [a] using
      Lemma65Setup.quadratic_head_add_eq_two_mul_one_add_mul_intrinsic
        b x heq
  rcases hlinear with hminus | hplus
  · left
    rw [hsubValue, ord_mul, ord_mul, hminus.1,
      ← ramificationIndex_spec, hheadOrder]
    norm_cast
    omega
  · right
    rw [haddValue, ord_mul, ord_mul, hplus.1,
      ← ramificationIndex_spec, hheadOrder]
    norm_cast
    omega

/-- Geometric transport in the exceptional branch of Lemma 6.6. -/
theorem exists_exceptionalRotation_apply_head
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional) :
    ∃ f : Lattice.IntegralRotation q L, f.apply b.head = x := by
  rcases b.exceptional_head_sub_or_add_order_eq
      hB x hx heq hexceptional with hsub | hadd
  · let haniso := lemma65Difference_isAnisotropic_of_order_eq b x hsub
    have hintegral : Lattice.IsIntegralReflection (L := L) haniso :=
      Lemma65Setup.exceptional_reflection_integral_proved
        b hB x hx heq hexceptional hsub
    let w : Lemma65DifferenceReflectionWitness b x :=
      ⟨haniso, hintegral⟩
    exact ⟨b.differenceTailRotation x w,
      b.differenceTailRotation_apply_head x w heq⟩
  · have hxneg : -x ∈ L := L.neg_mem hx
    have heqneg : q.quadratic (-x) = q.quadratic b.head := by
      rw [q.quadratic_neg, heq]
    have hsumOrder : ord K (q.quadratic (b.head - (-x))) =
        ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
          WithTop Int) := by
      simpa only [sub_neg_eq_add] using hadd
    let hsum := lemma65Difference_isAnisotropic_of_order_eq b (-x) hsumOrder
    have hintegral : Lattice.IsIntegralReflection (L := L) hsum :=
      Lemma65Setup.exceptional_reflection_integral_proved
        b hB (-x) hxneg heqneg hexceptional hsumOrder
    refine ⟨b.sumHeadRotation x ?_ ?_, ?_⟩
    · simpa only [sub_neg_eq_add] using hsum
    · simpa only [sub_neg_eq_add] using hintegral
    · exact b.sumHeadRotation_apply_head x _ _ heq

namespace Lemma65Setup

variable {b : BONG V q L (n + 3)}

/-- The binary parameter of the initial two-vector prefix of the intermediate
lattice is exactly the parameter obtained by rescaling the original second
BONG vector by `pi^k`. -/
theorem intermediateBinaryPrefix_binaryParameter (S : b.Lemma65Setup) :
    (S.intermediateBONG.prefixWitness 2 (by omega)).bong.binaryParameter =
      b.headSecondRescaledParameter S.k := by
  let P := S.intermediateBONG.prefixWitness 2 (by omega)
  change P.bong.valueUnit 1 / P.bong.valueUnit 0 = _
  rw [P.valueUnit_eq, P.valueUnit_eq]
  have hzero : P.sourceIndex (0 : Fin 2) = (0 : Fin (n + 3)) := by
    apply Fin.ext
    simp [P, SegmentWitness.sourceIndex]
  have hone : P.sourceIndex (1 : Fin 2) = (1 : Fin (n + 3)) := by
    apply Fin.ext
    simp [P, SegmentWitness.sourceIndex]
  rw [hzero, hone, S.intermediateBONG_valueUnit_zero,
    S.intermediateBONG_valueUnit_one]
  unfold headSecondRescaledParameter adjacentParameter
  change uniformizerPowerUnit K (S.k : Int) ^ 2 * b.valueUnit 1 /
      b.valueUnit 0 =
    (b.valueUnit 1 / b.valueUnit 0) *
      uniformizerPowerUnit K (S.k : Int) ^ 2
  rw [mul_div_assoc, mul_comm]

/-- Rescaling the second vector can only decrease the associated binary
spinor group.  Consequently every minimal-rescaling base group occurring in
Lemma 6.6 is already contained in its target group `H`. -/
theorem beliSpinorGroup_headSecondRescaledParameter_le_sharpHeadFactor
    (S : b.Lemma65Setup) :
    beliSpinorGroup K
        (unitSquareClass K (b.headSecondRescaledParameter S.k)) ≤
      b.lemma66SharpHeadFactor := by
  have hle : beliSpinorGroup K
        (unitSquareClass K
          (b.adjacentParameter 0 (by simp) *
            uniformizerPowerUnit K (S.k : Int) ^ 2)) ≤
      beliSpinorGroup K
        (unitSquareClass K (b.adjacentParameter 0 (by simp))) :=
    beliSpinorGroup_mul_integral_square_le_of_admissible
      (b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp))
      (uniformizerPowerUnit K (S.k : Int))
      (uniformizerPowerUnit_nat_mem_integerRing S.k)
  apply le_trans (by
    simpa only [headSecondRescaledParameter] using hle)
  exact le_sup_left

/-- If the target projection is a norm generator of the final rescaled tail,
its normalized factor has the final binary order `R₂+2k-R₁`. -/
theorem ordUnit_projectionFactorUnit_of_tailRescale_isNormGenerator
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    ordUnit K (S.projectionFactorUnit x hfactorNe) =
      b.order 1 + 2 * (S.k : Int) - b.order 0 := by
  have hprojection := S.ord_quadratic_projection_of_isNormGenerator
    x hgenerator
  have hfactor := S.ord_quadratic_projection_eq_head_add_projectionFactor
    x heq hfactorNe
  rw [hprojection] at hfactor
  norm_cast at hfactor ⊢
  omega

/-- A norm-generator projection cannot have vanishing normalized projection
factor.  Indeed its quadratic value is nonzero in the positive-dimensional
rescaled tail, while the projection identity writes that value as the factor
times the head value. -/
theorem projectionFactor_ne_zero_of_tailRescale_isNormGenerator
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0 := by
  have hfin : 0 < Module.finrank K (q.vectorOrthogonal b.head) := by
    rw [← S.tailRescale.bong.length_eq_finrank]
    omega
  have hanisotropic := hgenerator.isAnisotropic_of_finrank_pos hfin
  intro hzero
  apply hanisotropic
  rw [S.quadratic_projection_eq_one_sub_sq_mul x heq, hzero, zero_mul]

/-- Exact value-ratio identity behind Beli's notation
`Q(y) = Z Q(πᵏx₂)`: the normalized projection factor is the final
rescaled first parameter times the norm-generator value ratio in the final
rescaled tail. -/
theorem projectionFactorUnit_eq_headSecondRescaledParameter_mul_tailRatio
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    S.projectionFactorUnit x hfactorNe =
      b.headSecondRescaledParameter S.k *
        S.tailRescale.bong.normGeneratorValueRatioUnit
          (S.projection x) hgenerator := by
  let πk : K := ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K)
  have htailValue : S.tailRescale.bong.value 0 =
      πk ^ 2 * b.value 1 := by
    calc
      S.tailRescale.bong.value 0 =
          (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
            (S.tailRescale.bong.ambientVector 0) :=
        (S.tailRescale.bong.quadratic_ambientVector 0).symm
      _ = q.quadratic (πk • b.ambientVector 1) := by
        change q.quadratic
            ((S.tailRescale.bong.ambientVector 0 :
              q.vectorOrthogonal b.head) : V) = _
        rw [S.coe_tailRescale_ambientVector_zero]
      _ = πk ^ 2 * b.value 1 := by
        rw [q.quadratic_smul, b.quadratic_ambientVector]
  have hprojection := S.quadratic_projection_eq_one_sub_sq_mul x heq
  apply Units.ext
  simp only [coe_projectionFactorUnit, headSecondRescaledParameter,
    Units.val_mul, adjacentParameter, Units.val_div_eq_div_val,
    normGeneratorValueRatioUnit, Units.val_mk0, coe_valueUnit,
    Units.val_pow_eq_pow_val]
  have hindex :
      (⟨(0 : Fin (n + 3)).1 + 1, by simp⟩ : Fin (n + 3)) = 1 :=
    Fin.ext rfl
  rw [hindex, ← b.value_zero_eq_quadratic_head]
  rw [← b.value_zero_eq_quadratic_head] at hprojection
  rw [hprojection, htailValue]
  dsimp only [πk]
  field_simp [b.value_ne_zero 0, b.value_ne_zero 1,
    Units.ne_zero (uniformizerPowerUnit K (S.k : Int))]
  rw [mul_div_cancel_right₀ _
    (Units.ne_zero (uniformizerPowerUnit K (S.k : Int)))]

/-- The zeroth value of the final rescaled tail is the head value times the
corresponding rescaled binary parameter.  This is the unnormalized identity
needed to divide Lemma 6.2/6.3 value-set congruences by `Q(x₁)`. -/
theorem tailRescale_value_zero_eq_headSecondRescaledParameter_mul_headValue
    (S : b.Lemma65Setup) :
    S.tailRescale.bong.value 0 =
      (b.headSecondRescaledParameter S.k : K) * q.quadratic b.head := by
  let pik : K := ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K)
  have htailValue : S.tailRescale.bong.value 0 =
      pik ^ 2 * b.value 1 := by
    calc
      S.tailRescale.bong.value 0 =
          (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
            (S.tailRescale.bong.ambientVector 0) :=
        (S.tailRescale.bong.quadratic_ambientVector 0).symm
      _ = q.quadratic (pik • b.ambientVector 1) := by
        change q.quadratic
            ((S.tailRescale.bong.ambientVector 0 :
              q.vectorOrthogonal b.head) : V) = _
        rw [S.coe_tailRescale_ambientVector_zero]
      _ = pik ^ 2 * b.value 1 := by
        rw [q.quadratic_smul, b.quadratic_ambientVector]
  rw [htailValue, ← b.value_zero_eq_quadratic_head]
  simp only [headSecondRescaledParameter, adjacentParameter,
    Units.val_mul, Units.val_div_eq_div_val, coe_valueUnit,
    Units.val_pow_eq_pow_val]
  have hindex :
      (⟨(0 : Fin (n + 3)).1 + 1, by simp⟩ : Fin (n + 3)) = 1 :=
    Fin.ext rfl
  rw [hindex]
  dsimp only [pik]
  field_simp [b.value_ne_zero 0,
    Units.ne_zero (uniformizerPowerUnit K (S.k : Int))]

/-- At exponent zero the rescaled-tail BONG has exactly the same unit-valued
entries as the original tail. -/
theorem tailRescale_valueUnit_eq_of_k_eq_zero
    (S : b.Lemma65Setup) (hk : S.k = 0)
    (i : Fin (n + 2)) :
    S.tailRescale.bong.valueUnit i = b.tail.valueUnit i := by
  apply Units.ext
  simp only [coe_valueUnit]
  rw [← S.tailRescale.bong.quadratic_ambientVector i,
    ← b.tail.quadratic_ambientVector i]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [S.tailRescale.ambientVector_zero, hk]
    simp [uniformizerPowerUnit]
  · rw [S.tailRescale.ambientVector_succ]

/-- Hence every order of the exponent-zero rescaled tail agrees with the
corresponding order of the original tail. -/
theorem tailRescale_order_eq_of_k_eq_zero
    (S : b.Lemma65Setup) (hk : S.k = 0)
    (i : Fin (n + 2)) :
    S.tailRescale.bong.order i = b.tail.order i := by
  rw [S.tailRescale.bong.order_eq_ordUnit, b.tail.order_eq_ordUnit,
    S.tailRescale_valueUnit_eq_of_k_eq_zero hk i]

/-- Normalized adjacent defects are unchanged at exponent zero. -/
theorem tailRescale_normalizedAdjacentDefectOrder_eq_of_k_eq_zero
    (S : b.Lemma65Setup) (hk : S.k = 0)
    (i : Fin (n + 1)) :
    S.tailRescale.bong.normalizedAdjacentDefectOrder i =
      b.tail.normalizedAdjacentDefectOrder i := by
  unfold normalizedAdjacentDefectOrder normalizedAdjacentProduct normalizedValue
  rw [S.tailRescale_valueUnit_eq_of_k_eq_zero hk i.castSucc,
    S.tailRescale_valueUnit_eq_of_k_eq_zero hk i.succ,
    S.tailRescale_order_eq_of_k_eq_zero hk i.castSucc,
    S.tailRescale_order_eq_of_k_eq_zero hk i.succ]

/-- Property B transfers to a zero-rescaled tail because all order and defect
data in Definition 10 are unchanged. -/
theorem tailRescale_hasPropertyB_of_k_eq_zero
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (hk : S.k = 0) :
    S.tailRescale.bong.HasPropertyB := by
  have htailB : b.tail.HasPropertyB := hB.tail_for_lemma62
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [S.tailRescale_order_eq_of_k_eq_zero hk i,
      S.tailRescale_order_eq_of_k_eq_zero hk ⟨i.1 + 2, hi⟩]
    exact htailB.hasPropertyA i hi
  · intro i htrigger
    have htriggerTail : b.tail.propertyBTrigger i := by
      unfold propertyBTrigger at htrigger ⊢
      rw [S.tailRescale_order_eq_of_k_eq_zero hk i.succ,
        S.tailRescale_order_eq_of_k_eq_zero hk i.castSucc,
        S.tailRescale_normalizedAdjacentDefectOrder_eq_of_k_eq_zero hk i]
        at htrigger
      exact htrigger
    rcases htailB.2 i htriggerTail with ⟨hleft, hright⟩
    constructor
    · intro j hj
      rw [S.tailRescale_order_eq_of_k_eq_zero hk i.castSucc,
        S.tailRescale_order_eq_of_k_eq_zero hk j]
      exact hleft j hj
    · intro k hkIndex
      rw [S.tailRescale_order_eq_of_k_eq_zero hk k,
        S.tailRescale_order_eq_of_k_eq_zero hk i.succ]
      exact hright k hkIndex

/-- At exponent one, the original tail itself realizes the inverse head
rescaling of the rescaled tail. -/
noncomputable def tailRescaleInverseWitness_of_k_eq_one
    (S : b.Lemma65Setup) (hk : S.k = 1) :
    S.tailRescale.bong.HeadInverseRescaleWitness where
  lattice := L.projectedLattice q b.head b.head_isAnisotropic
  bong := b.tail
  ambientVector_zero := by
    rw [S.tailRescale.ambientVector_zero, hk]
    simp [uniformizerPowerUnit, smul_smul, uniformizer_ne_zero K]
  ambientVector_succ i := (S.tailRescale.ambientVector_succ i).symm

/-- In Beli's short-shift cases (`k=0` or `k=1`), the final rescaled tail
satisfies exactly the disjunctive Property-B hypothesis of Lemma 6.3(i). -/
theorem exists_tailRescale_propertyBOrInverse_of_k_le_one
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (hk : S.k ≤ 1) :
    ∃ w : S.tailRescale.bong.HeadInverseRescaleWitness,
      S.tailRescale.bong.HasPropertyBOrInverse w := by
  have hkCases : S.k = 0 ∨ S.k = 1 := by omega
  rcases hkCases with hkZero | hkOne
  · let w := S.tailRescale.bong.headInverseRescaleWitness
    exact ⟨w, Or.inl (S.tailRescale_hasPropertyB_of_k_eq_zero hB hkZero)⟩
  · let w := S.tailRescaleInverseWitness_of_k_eq_one hkOne
    refine ⟨w, Or.inr ?_⟩
    change b.tail.HasPropertyB
    exact hB.tail_for_lemma62

/-- Unit-valued form of the head rescaling in the final tail. -/
theorem tailRescale_valueUnit_zero (S : b.Lemma65Setup) :
    S.tailRescale.bong.valueUnit 0 =
      uniformizerPowerUnit K (S.k : Int) ^ 2 * b.tail.valueUnit 0 := by
  apply Units.ext
  simp only [coe_valueUnit, Units.val_mul, Units.val_pow_eq_pow_val]
  rw [← S.tailRescale.bong.quadratic_ambientVector 0,
    S.tailRescale.ambientVector_zero,
    QuadraticSpace.quadratic_smul,
    b.tail.quadratic_ambientVector]

/-- Head rescaling does not change the normalized unit part of the first
tail value. -/
theorem tailRescale_normalizedValue_zero (S : b.Lemma65Setup) :
    S.tailRescale.bong.normalizedValue 0 = b.tail.normalizedValue 0 := by
  unfold normalizedValue
  rw [S.tailRescale_valueUnit_zero, S.tailRescale.order_zero_eq]
  unfold uniformizerPowerUnit
  have hpow :
      (uniformizerUnit K ^ (S.k : Int)) ^ 2 =
        uniformizerUnit K ^ (2 * (S.k : Int)) := by
    rw [pow_two, ← zpow_add]
    congr 2
    omega
  calc
    (uniformizerUnit K ^ (S.k : Int)) ^ 2 * b.tail.valueUnit 0 *
          uniformizerUnit K ^ (-(b.tail.order 0 + 2 * (S.k : Int))) =
        b.tail.valueUnit 0 *
          (uniformizerUnit K ^ (2 * (S.k : Int)) *
            uniformizerUnit K ^ (-(b.tail.order 0 + 2 * (S.k : Int)))) := by
      rw [hpow]
      ac_rfl
    _ = b.tail.valueUnit 0 * uniformizerUnit K ^ (-b.tail.order 0) := by
      rw [← zpow_add]
      congr 2
      omega

/-- The second normalized tail value is unchanged by a head rescaling. -/
theorem tailRescale_normalizedValue_one (S : b.Lemma65Setup) :
    S.tailRescale.bong.normalizedValue 1 = b.tail.normalizedValue 1 := by
  have horder : S.tailRescale.bong.order 1 = b.tail.order 1 := by
    simpa using S.tailRescale.order_succ_eq (0 : Fin (n + 1))
  have hvalue : S.tailRescale.bong.valueUnit 1 = b.tail.valueUnit 1 := by
    apply Units.ext
    simp only [coe_valueUnit]
    rw [← S.tailRescale.bong.quadratic_ambientVector 1,
      ← b.tail.quadratic_ambientVector 1]
    exact congrArg
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (S.tailRescale.ambientVector_succ (0 : Fin (n + 1)))
  unfold normalizedValue
  rw [horder, hvalue]

/-- Therefore the normalized product governing the first adjacent pair of
the tail is invariant under its head rescaling. -/
theorem tailRescale_normalizedAdjacentProduct_zero (S : b.Lemma65Setup) :
    S.tailRescale.bong.normalizedAdjacentProduct 0 =
      b.tail.normalizedAdjacentProduct 0 := by
  have hzero : S.tailRescale.bong.normalizedValue
        (0 : Fin (n + 1)).castSucc =
      b.tail.normalizedValue (0 : Fin (n + 1)).castSucc := by
    simpa using S.tailRescale_normalizedValue_zero
  have hone : S.tailRescale.bong.normalizedValue
        (0 : Fin (n + 1)).succ =
      b.tail.normalizedValue (0 : Fin (n + 1)).succ := by
    simpa using S.tailRescale_normalizedValue_one
  unfold normalizedAdjacentProduct
  rw [hzero, hone]

/-- The corresponding defect order is the original defect at the second
adjacent pair. -/
theorem tailRescale_normalizedAdjacentDefectOrder_zero
    (S : b.Lemma65Setup) :
    S.tailRescale.bong.normalizedAdjacentDefectOrder 0 =
      b.normalizedAdjacentDefectOrder 1 := by
  calc
    S.tailRescale.bong.normalizedAdjacentDefectOrder 0 =
        b.tail.normalizedAdjacentDefectOrder 0 := by
      unfold normalizedAdjacentDefectOrder
      rw [S.tailRescale_normalizedAdjacentProduct_zero]
    _ = b.normalizedAdjacentDefectOrder 1 := by
      simpa using b.normalizedAdjacentDefectOrder_tail (0 : Fin (n + 1))

/-- In the low-range branch `k ≤ 1`, every norm-generator value ratio of
the final rescaled tail lies in the upper binary group attached to its first
adjacent parameter.  This is the precise use of Lemma 6.3(i) in Beli's proof
of Lemma 6.6. -/
theorem tailRescale_normGeneratorValueRatioClass_mem_upper_of_k_le_one
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (hk : S.k ≤ 1)
    (y : q.vectorOrthogonal b.head)
    (hy : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice y) :
    S.tailRescale.bong.normGeneratorValueRatioClass y hy ∈
      beliNormGeneratorUpperGroup K
        (S.tailRescale.bong.adjacentParameter 0 (by simp)) := by
  rcases S.exists_tailRescale_propertyBOrInverse_of_k_le_one hB hk with
    ⟨w, hw⟩
  exact (S.tailRescale.bong.beliLemma63_i w hw).2 ⟨y, hy, rfl⟩

/-- The first gap of the final rescaled tail is the original second gap with
the head shift `2k` removed. -/
theorem tailRescale_lemma62Gap_eq (S : b.Lemma65Setup) :
    S.tailRescale.bong.lemma62Gap =
      b.order 2 - b.order 1 - 2 * (S.k : Int) := by
  have hone : S.tailRescale.bong.order 1 = b.tail.order 1 := by
    simpa using S.tailRescale.order_succ_eq (0 : Fin (n + 1))
  have htailZero : b.tail.order 0 = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOne : b.tail.order 1 = b.order 2 := by
    rw [b.order_tail]
    congr 1
  unfold lemma62Gap
  rw [hone, S.tailRescale.order_zero_eq, htailZero, htailOne]
  omega

/-- Equivalently, the original second gap is the rescaled-tail gap plus
`2k`. -/
theorem secondGap_eq_tailRescale_lemma62Gap_add (S : b.Lemma65Setup) :
    b.order 2 - b.order 1 =
      S.tailRescale.bong.lemma62Gap + 2 * (S.k : Int) := by
  rw [S.tailRescale_lemma62Gap_eq]
  omega

/-- The first adjacent parameter of the rescaled tail is the original
second adjacent parameter multiplied by the inverse square of the head
rescaling factor. -/
theorem tailRescale_adjacentParameter_zero_eq_original_mul_inv_square
    (S : b.Lemma65Setup) :
    S.tailRescale.bong.adjacentParameter 0 (by simp) =
      b.adjacentParameter 1 (by simp) *
        (uniformizerPowerUnit K (S.k : Int))⁻¹ ^ 2 := by
  have hone : S.tailRescale.bong.valueUnit 1 = b.tail.valueUnit 1 := by
    apply Units.ext
    simp only [coe_valueUnit]
    rw [← S.tailRescale.bong.quadratic_ambientVector 1,
      ← b.tail.quadratic_ambientVector 1]
    exact congrArg
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (S.tailRescale.ambientVector_succ (0 : Fin (n + 1)))
  have htailParameter : b.tail.adjacentParameter 0 (by simp) =
      b.adjacentParameter 1 (by simp) := by
    unfold adjacentParameter
    rw [b.valueUnit_tail, b.valueUnit_tail]
    congr 2 <;> apply Fin.ext <;> rfl
  rw [← htailParameter]
  unfold adjacentParameter
  change S.tailRescale.bong.valueUnit (1 : Fin (n + 2)) /
      S.tailRescale.bong.valueUnit 0 =
    (b.tail.valueUnit (1 : Fin (n + 2)) / b.tail.valueUnit 0) *
      (uniformizerPowerUnit K (S.k : Int))⁻¹ ^ 2
  rw [hone, S.tailRescale_valueUnit_zero]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  exact (mul_assoc (b.tail.valueUnit 1)
    ((b.tail.valueUnit 0)⁻¹ : Kˣ)
    ((uniformizerPowerUnit K (S.k : Int) ^ 2)⁻¹ : Kˣ)).symm

/-- Consequently the parameter defect used by Lemma 6.2 on the rescaled
tail is exactly the defect of the original second adjacent parameter. -/
theorem tailRescale_parameterDefect_zero_eq_original_second
    (S : b.Lemma65Setup) :
    beliParameterDefect K
        (S.tailRescale.bong.adjacentParameter 0 (by simp)) =
      beliParameterDefect K (b.adjacentParameter 1 (by simp)) := by
  rw [S.tailRescale_adjacentParameter_zero_eq_original_mul_inv_square]
  unfold beliParameterDefect
  rw [← neg_mul, quadraticDefect_mul_square]

/-- The corresponding finite natural defect is unchanged as well. -/
theorem tailRescale_parameterDefectNat_zero_eq_original_second
    (S : b.Lemma65Setup) :
    beliParameterDefectNat K
        (S.tailRescale.bong.adjacentParameter 0 (by simp)) =
      beliParameterDefectNat K (b.adjacentParameter 1 (by simp)) := by
  unfold beliParameterDefectNat
  rw [S.tailRescale_parameterDefect_zero_eq_original_second]

/-- The two shifted adjacent gaps telescope to `R₃-R₁`. -/
theorem finalHeadGap_add_tailRescaleGap (S : b.Lemma65Setup) :
    (b.order 1 + 2 * (S.k : Int) - b.order 0) +
        S.tailRescale.bong.lemma62Gap =
      b.order 2 - b.order 0 := by
  rw [S.tailRescale_lemma62Gap_eq]
  omega

/-- In the low range the second adjacent pair of the original BONG cannot
trigger Property B: its left neighbour is bounded above by `2e`. -/
theorem not_propertyBTrigger_one_of_lowRange
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) :
    ¬ b.propertyBTrigger (1 : Fin (n + 2)) := by
  intro htrigger
  have hleft := (hB.2 (1 : Fin (n + 2)) htrigger).1
    (0 : Fin (n + 3)) (by simp)
  change 2 * (ramificationIndex K : Int) + 1 ≤
    b.order 1 - b.order 0 at hleft
  unfold Lemma65LowRange at hlow
  omega

/-- Numerical consequence of the preceding non-trigger: the original second
gap is either beyond `2e+1`, or it is even and its normalized defect is above
the Property-B cutoff. -/
theorem secondGap_large_or_even_high_of_lowRange
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) :
    2 * (ramificationIndex K : Int) + 1 < b.order 2 - b.order 1 ∨
      (Even (b.order 2 - b.order 1) ∧
        b.order 2 - b.order 1 ≤ 2 * (ramificationIndex K : Int) ∧
        ((((ramificationIndex K : ℚ) -
          ((b.order 2 - b.order 1 : Int) : ℚ) / 2) : ℚ) :
            WithTop ℚ) < b.normalizedAdjacentDefectOrder 1) := by
  simpa using b.not_propertyBTrigger_iff_large_or_even_high
    (1 : Fin (n + 2)) (S.not_propertyBTrigger_one_of_lowRange hB hlow)

/-- If the rescaled-tail gap is below `2e`, the large-gap alternative is
impossible for `k ≤ 1`; hence that tail gap is even. -/
theorem tailRescale_lemma62Gap_even_of_lt_two_e
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (hT : S.tailRescale.bong.lemma62Gap <
      2 * (ramificationIndex K : Int)) :
    Even S.tailRescale.bong.lemma62Gap := by
  rcases S.secondGap_large_or_even_high_of_lowRange hB hlow with
      hlarge | ⟨heven, _hupper, _hdefect⟩
  · rw [S.secondGap_eq_tailRescale_lemma62Gap_add] at hlarge
    omega
  · rcases heven with ⟨r, hr⟩
    rw [S.secondGap_eq_tailRescale_lemma62Gap_add] at hr
    refine ⟨r - S.k, ?_⟩
    omega

/-- For an even rescaled-tail gap at most `2e`, Property B gives the lower
bound `d(-ε₂ε₃) ≥ e-T/2` used in Beli's low-range estimate. -/
theorem tailRescale_normalizedAdjacentDefectOrder_lower
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hlow : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (hT : S.tailRescale.bong.lemma62Gap ≤
      2 * (ramificationIndex K : Int))
    (heven : Even S.tailRescale.bong.lemma62Gap) :
    (((((ramificationIndex K : ℚ) -
        ((S.tailRescale.bong.lemma62Gap : Int) : ℚ) / 2) : ℚ) :
          WithTop ℚ)) ≤
      S.tailRescale.bong.normalizedAdjacentDefectOrder 0 := by
  rcases S.secondGap_large_or_even_high_of_lowRange hB hlow with
      hlarge | ⟨_hsecondEven, _hsecondUpper, hdefect⟩
  · have hTEq : S.tailRescale.bong.lemma62Gap =
        2 * (ramificationIndex K : Int) := by
      rw [S.secondGap_eq_tailRescale_lemma62Gap_add] at hlarge
      omega
    rw [hTEq]
    have hnonneg : (0 : WithTop ℚ) ≤
        S.tailRescale.bong.normalizedAdjacentDefectOrder 0 := by
      unfold normalizedAdjacentDefectOrder
      cases quadraticDefect K
          (S.tailRescale.bong.normalizedAdjacentProduct 0) with
      | top =>
          change (0 : WithTop ℚ) ≤ ⊤
          exact le_top
      | coe d =>
          change (0 : WithTop ℚ) ≤ ((d : ℚ) : WithTop ℚ)
          norm_cast
          positivity
    convert hnonneg using 1 <;> norm_num
  · rw [← S.tailRescale_normalizedAdjacentDefectOrder_zero] at hdefect
    unfold normalizedAdjacentDefectOrder at hdefect ⊢
    cases hd : quadraticDefect K
        (S.tailRescale.bong.normalizedAdjacentProduct 0) with
    | top =>
        change _ ≤ (⊤ : WithTop ℚ)
        exact le_top
    | coe d =>
        rw [hd] at hdefect
        change
          (((ramificationIndex K : ℚ) -
              ((b.order 2 - b.order 1 : Int) : ℚ) / 2 : ℚ) :
                WithTop ℚ) < ((d : ℚ) : WithTop ℚ) at hdefect
        change
          (((ramificationIndex K : ℚ) -
              (S.tailRescale.bong.lemma62Gap : ℚ) / 2 : ℚ) :
                WithTop ℚ) ≤ ((d : ℚ) : WithTop ℚ)
        norm_cast at hdefect ⊢
        simp only [← Rat.intCast_div_eq_divInt] at hdefect ⊢
        rcases heven with ⟨t, ht⟩
        have hkCases : S.k = 0 ∨ S.k = 1 := by omega
        rcases hkCases with hkZero | hkOne
        · have hkZeroInt : (S.k : Int) = 0 := by omega
          rw [S.secondGap_eq_tailRescale_lemma62Gap_add, hkZeroInt, ht]
            at hdefect
          rw [ht]
          push_cast at hdefect ⊢
          norm_num at hdefect ⊢
          linarith
        · have hkOneInt : (S.k : Int) = 1 := by omega
          rw [S.secondGap_eq_tailRescale_lemma62Gap_add, hkOneInt, ht]
            at hdefect
          rw [ht]
          push_cast at hdefect ⊢
          norm_num at hdefect ⊢
          ring_nf at hdefect ⊢
          have hdefectInt :
              (-1 : Int) + (ramificationIndex K : Int) - t < (d : Int) := by
            exact_mod_cast hdefect
          have hgoalInt :
              (ramificationIndex K : Int) - t ≤ (d : Int) := by
            omega
          have hgoalRat :
              (ramificationIndex K : ℚ) - (t : ℚ) ≤ (d : ℚ) := by
            exact_mod_cast hgoalInt
          linarith

/-- Lemma 6.3(i), together with Property B, forces every value ratio in the
final rescaled tail to have defect at least `e + T/2`, where `T` is the first
gap of that tail.  This is the quantitative input to Corollary 3.15(ii). -/
theorem tailRescale_normGeneratorValueRatio_defect_lower
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hRange : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (y : q.vectorOrthogonal b.head)
    (hy : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice y) :
    ((Int.toNat ((ramificationIndex K : Int) +
        S.tailRescale.bong.lemma62Gap / 2) : Nat) : ℕ∞) ≤
      quadraticDefect K
        (S.tailRescale.bong.normGeneratorValueRatioUnit y hy) := by
  let tail := S.tailRescale.bong
  let a : Kˣ := tail.adjacentParameter 0 (by simp)
  let z := tail.normGeneratorValueRatioValuationUnit y hy
  have hmember : valuationUnitClassHom K z ∈
      beliNormGeneratorUpperGroup K a := by
    simpa only [tail, a, z, normGeneratorValueRatioClass] using
      S.tailRescale_normGeneratorValueRatioClass_mem_upper_of_k_le_one
        hB hk y hy
  have haOrder : ordUnit K a = tail.lemma62Gap := by
    simpa only [a, tail] using tail.ordUnit_adjacentParameter_zero
  by_cases hlarge : 2 * (ramificationIndex K : Int) < tail.lemma62Gap
  · have hlargeA : 2 * (ramificationIndex K : Int) < ordUnit K a := by
      rwa [haOrder]
    rw [beliNormGeneratorUpperGroup_of_two_e_lt K a hlargeA] at hmember
    have hclass : valuationUnitClassHom K z = 1 := by
      simpa only [Subgroup.mem_bot] using hmember
    have hfieldClass := congrArg (valuationUnitClassToSquareClass K) hclass
    have hsquare : IsSquare (z : Kˣ) := by
      change (z : Kˣ) ∈ Subgroup.square Kˣ
      apply (QuotientGroup.eq_one_iff (z : Kˣ)).1
      change squareClass K (z : Kˣ) = 1
      simpa only [valuationUnitClassToSquareClass_apply, map_one] using hfieldClass
    have htop : quadraticDefect K (z : Kˣ) = ⊤ :=
      quadraticDefect_eq_top_of_isSquare K hsquare
    change _ ≤ quadraticDefect K (z : Kˣ)
    rw [htop]
    exact le_top
  · have hTUpper : tail.lemma62Gap ≤
        2 * (ramificationIndex K : Int) := by omega
    have hTEven : Even tail.lemma62Gap := by
      rcases lt_or_eq_of_le hTUpper with hTlt | hTEq
      · exact S.tailRescale_lemma62Gap_even_of_lt_two_e
          hB hRange hk (by simpa only [tail] using hTlt)
      · rw [hTEq]
        exact even_two_mul (ramificationIndex K : Int)
    have hnotLargeA : ¬ 2 * (ramificationIndex K : Int) < ordUnit K a := by
      rwa [haOrder]
    by_cases hlowDefect : 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞)
    · rw [beliNormGeneratorUpperGroup_of_low_defect K a hnotLargeA
          hlowDefect] at hmember
      have hzDefect := natCast_le_quadraticDefect_of_unitClass_mem
        z (beliLowDefectExponent K a) hmember
      have hparameterEq : beliParameterDefect K a =
          quadraticDefect K (tail.normalizedAdjacentProduct 0) := by
        unfold beliParameterDefect
        have h :=
          tail.quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
            (0 : Fin (n + 1)) hTEven
        simpa only [a, tail, Fin.castSucc_zero] using h
      have hparameterFinite : beliParameterDefect K a ≠ ⊤ := by
        intro htop
        rw [htop] at hlowDefect
        simp at hlowDefect
      have hnormalizedFinite :
          quadraticDefect K (tail.normalizedAdjacentProduct 0) ≠ ⊤ := by
        rwa [← hparameterEq]
      let d : Nat :=
        (quadraticDefect K (tail.normalizedAdjacentProduct 0)).toNat
      have hnormalizedCoe :
          quadraticDefect K (tail.normalizedAdjacentProduct 0) = (d : ℕ∞) := by
        exact (ENat.coe_toNat hnormalizedFinite).symm
      have hdefectOrder :=
        S.tailRescale_normalizedAdjacentDefectOrder_lower hB hRange hk
          (by simpa only [tail] using hTUpper)
          (by simpa only [tail] using hTEven)
      unfold normalizedAdjacentDefectOrder at hdefectOrder
      change
        (((((ramificationIndex K : ℚ) -
            ((tail.lemma62Gap : Int) : ℚ) / 2) : ℚ) : WithTop ℚ)) ≤
          WithTop.map (fun m : Nat ↦ (m : ℚ))
            (quadraticDefect K (tail.normalizedAdjacentProduct 0))
          at hdefectOrder
      rw [hnormalizedCoe] at hdefectOrder
      change
        (((ramificationIndex K : ℚ) -
            ((tail.lemma62Gap : Int) : ℚ) / 2 : ℚ) : WithTop ℚ) ≤
          ((d : ℚ) : WithTop ℚ) at hdefectOrder
      norm_cast at hdefectOrder
      simp only [← Rat.intCast_div_eq_divInt] at hdefectOrder
      rcases hTEven with ⟨t, ht⟩
      rw [ht] at hdefectOrder
      push_cast at hdefectOrder
      norm_num at hdefectOrder
      have hdefectInt :
          (ramificationIndex K : Int) ≤ (d : Int) + t := by
        exact_mod_cast hdefectOrder
      have hhalf : tail.lemma62Gap / 2 = t := by omega
      have hexponentInt :
          (ramificationIndex K : Int) + tail.lemma62Gap / 2 ≤
            tail.lemma62Gap + (d : Int) := by
        rw [hhalf, ht]
        omega
      have hparameterNat : beliParameterDefectNat K a = d := by
        unfold beliParameterDefectNat
        rw [hparameterEq, hnormalizedCoe]
        simp only [ENat.toNat_coe]
      have hexponentNat :
          Int.toNat ((ramificationIndex K : Int) + tail.lemma62Gap / 2) ≤
            beliLowDefectExponent K a := by
        unfold beliLowDefectExponent
        rw [haOrder, hparameterNat]
        exact Int.toNat_le_toNat hexponentInt
      change _ ≤ quadraticDefect K (z : Kˣ)
      exact (show
        (Int.toNat ((ramificationIndex K : Int) + tail.lemma62Gap / 2) : ℕ∞) ≤
          (beliLowDefectExponent K a : ℕ∞) by exact_mod_cast hexponentNat).trans
        hzDefect
    · rw [beliNormGeneratorUpperGroup_of_high_defect K a hnotLargeA
          hlowDefect] at hmember
      have hzDefect := natCast_le_quadraticDefect_of_unitClass_mem
        z (beliHighDefectExponent K a) hmember
      have hexponent : beliHighDefectExponent K a =
          Int.toNat ((ramificationIndex K : Int) + tail.lemma62Gap / 2) := by
        unfold beliHighDefectExponent
        rw [haOrder]
      change _ ≤ quadraticDefect K (z : Kˣ)
      rwa [← hexponent]

/-- Away from the finite-defect equality boundary, every low-order even
parameter allowed by Lemma 3.17 lies in the high-defect range required by
Corollary 3.15(ii). -/
theorem BeliLemma317ParameterCases.not_lowDefect_of_not_boundary
    (R : Int) (epsilon : Kˣ)
    (hepsilon : IsValuationUnit K (epsilon : K))
    (hadmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon))
    (hRUpper : R ≤ 2 * (ramificationIndex K : Int))
    (hREven : Even R)
    (hcases : BeliLemma317ParameterCases (K := K) R epsilon)
    (hnotBoundary : ¬
      (quadraticDefect K (-epsilon) ≠ ⊤ ∧
        R = 2 * (ramificationIndex K : Int) -
          2 * ((quadraticDefect K (-epsilon)).toNat : Int))) :
    ¬ 2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) := by
  simp only [BeliLemma317ParameterCases] at hcases
  rcases hcases with htooLarge | hboundary | hinterior | hendpoint
  · omega
  · exact (hnotBoundary hboundary).elim
  · intro hlow
    rcases hinterior.1 with htop | ⟨hfinite, habove⟩
    · rw [htop] at hlow
      simp at hlow
    · have hcutNonneg :
          0 ≤ 2 * (ramificationIndex K : Int) - R := by omega
      have hlowNat := hlow
      rw [← ENat.coe_toNat hfinite] at hlowNat
      norm_cast at hlowNat
      have hcutCast :
          (Int.toNat (2 * (ramificationIndex K : Int) - R) : Int) =
            2 * (ramificationIndex K : Int) - R := by
        rw [Int.toNat_of_nonneg hcutNonneg]
      have hlowInt :
          2 * ((quadraticDefect K (-epsilon)).toNat : Int) ≤
            (Int.toNat (2 * (ramificationIndex K : Int) - R) : Int) := by
        exact_mod_cast hlowNat
      rw [hcutCast] at hlowInt
      omega
  · intro hlow
    rcases hendpoint.1 with hREnd | hquarter
    · have hnegativeUnit : IsValuationUnit K ((-epsilon : Kˣ) : K) := by
        change ord K (-((epsilon : K))) = 0
        change ord K (epsilon : K) = 0 at hepsilon
        simpa only [ord_neg] using hepsilon
      have hone : (1 : ℕ∞) ≤ quadraticDefect K (-epsilon) :=
        one_le_quadraticDefect_of_unit (-epsilon) hnegativeUnit
      have hpositive : (0 : ℕ∞) <
          2 * quadraticDefect K (-epsilon) := by
        have : (0 : ℕ∞) < quadraticDefect K (-epsilon) :=
          lt_of_lt_of_le (by simp) hone
        positivity
      have hzero : 2 * quadraticDefect K (-epsilon) ≤ 0 := by
        simpa only [hREnd, sub_self, Int.toNat_zero, ENat.coe_zero] using hlow
      exact (not_lt_of_ge hzero) hpositive
    · have hsquare : IsSquare
          (-(uniformizerPowerUnit K R * epsilon)) :=
        isSquare_neg_of_unitSquareClass_eq_negativeQuarter hquarter
      have htopParameter : beliParameterDefect K
          (uniformizerPowerUnit K R * epsilon) = ⊤ := by
        unfold beliParameterDefect
        exact quadraticDefect_eq_top_of_isSquare K hsquare
      have hdefectEq : beliParameterDefect K
          (uniformizerPowerUnit K R * epsilon) =
            quadraticDefect K (-epsilon) :=
        beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
          (K := K) R epsilon hepsilon hREven
      rw [hdefectEq] at htopParameter
      rw [htopParameter] at hlow
      simp at hlow

/-- Normalizing the exact identity `p = aZ` preserves the value-ratio factor
because `p` and the shifted base parameter have the same order. -/
theorem normalizedUnitPart_projectionFactorUnit_eq_base_mul_tailRatio
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    normalizedUnitPart K (S.projectionFactorUnit x hfactorNe) =
      normalizedUnitPart K (b.headSecondRescaledParameter S.k) *
        S.tailRescale.bong.normGeneratorValueRatioUnit
          (S.projection x) hgenerator := by
  have hp := S.projectionFactorUnit_eq_headSecondRescaledParameter_mul_tailRatio
    x heq hfactorNe hgenerator
  have hpOrder := S.ordUnit_projectionFactorUnit_of_tailRescale_isNormGenerator
    x heq hfactorNe hgenerator
  have haOrder := b.ordUnit_headSecondRescaledParameter S.k
  unfold normalizedUnitPart
  rw [hpOrder, haOrder, hp]
  ac_rfl

/-- Rescaling the second BONG vector changes only the uniformizer power, so
the normalized unit part remains that of the original first adjacent
parameter. -/
theorem normalizedUnitPart_headSecondRescaledParameter
    (S : b.Lemma65Setup) :
    normalizedUnitPart K (b.headSecondRescaledParameter S.k) =
      normalizedUnitPart K (b.adjacentParameter 0 (by simp)) := by
  rw [b.headSecondRescaledParameter_eq_normalized]
  exact normalizedUnitPart_uniformizerPower_mul_valuationUnit
    (b.lemma62Gap + 2 * (S.k : Int))
    (normalizedUnitPart K (b.adjacentParameter 0 (by simp)))
    (normalizedUnitPart_isValuationUnit K _)

/-- The normalized projection parameter is the original normalized first
parameter times the final-tail norm-generator value ratio. -/
theorem normalizedUnitPart_projectionFactorUnit_eq_original_mul_tailRatio
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    normalizedUnitPart K (S.projectionFactorUnit x hfactorNe) =
      normalizedUnitPart K (b.adjacentParameter 0 (by simp)) *
        S.tailRescale.bong.normGeneratorValueRatioUnit
          (S.projection x) hgenerator := by
  rw [S.normalizedUnitPart_projectionFactorUnit_eq_base_mul_tailRatio
    x heq hfactorNe hgenerator,
    S.normalizedUnitPart_headSecondRescaledParameter]

/-- If the first rescaled-tail gap is above `2e`, Lemma 6.3(i) makes every
value ratio a square. -/
theorem tailRescale_normGeneratorValueRatio_defect_eq_top_of_two_e_lt
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (hk : S.k ≤ 1)
    (y : q.vectorOrthogonal b.head)
    (hy : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice y)
    (hlarge : 2 * (ramificationIndex K : Int) <
      S.tailRescale.bong.lemma62Gap) :
    quadraticDefect K
        (S.tailRescale.bong.normGeneratorValueRatioUnit y hy) = ⊤ := by
  let tail := S.tailRescale.bong
  let a : Kˣ := tail.adjacentParameter 0 (by simp)
  let z := tail.normGeneratorValueRatioValuationUnit y hy
  have hmember : valuationUnitClassHom K z ∈
      beliNormGeneratorUpperGroup K a := by
    simpa only [tail, a, z, normGeneratorValueRatioClass] using
      S.tailRescale_normGeneratorValueRatioClass_mem_upper_of_k_le_one
        hB hk y hy
  have haOrder : ordUnit K a = tail.lemma62Gap := by
    simpa only [a, tail] using tail.ordUnit_adjacentParameter_zero
  have hlargeA : 2 * (ramificationIndex K : Int) < ordUnit K a := by
    rw [haOrder]
    simpa only [tail] using hlarge
  rw [beliNormGeneratorUpperGroup_of_two_e_lt K a hlargeA] at hmember
  have hclass : valuationUnitClassHom K z = 1 := by
    simpa only [Subgroup.mem_bot] using hmember
  have hfieldClass := congrArg (valuationUnitClassToSquareClass K) hclass
  have hsquare : IsSquare (z : Kˣ) := by
    change (z : Kˣ) ∈ Subgroup.square Kˣ
    apply (QuotientGroup.eq_one_iff (z : Kˣ)).1
    change squareClass K (z : Kˣ) = 1
    simpa only [valuationUnitClassToSquareClass_apply, map_one] using hfieldClass
  change quadraticDefect K (z : Kˣ) = ⊤
  exact quadraticDefect_eq_top_of_isSquare K hsquare

/-- The Corollary 3.15(ii) congruence factor produced by a tail value ratio is
contained in the sharp depth of Lemma 6.6. -/
theorem tailRatio_corollary315Factor_le_sharpCongruence
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hRange : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (y : q.vectorOrthogonal b.head)
    (hy : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice y) :
    beliCorollary315EvenCongruenceFactor (K := K)
        (b.order 1 + 2 * (S.k : Int) - b.order 0)
        (quadraticDefect K
          (S.tailRescale.bong.normGeneratorValueRatioUnit y hy)) ≤
      b.lemma66SharpCongruenceFactor := by
  let R : Int := b.order 1 + 2 * (S.k : Int) - b.order 0
  let T : Int := S.tailRescale.bong.lemma62Gap
  let Z : Kˣ := S.tailRescale.bong.normGeneratorValueRatioUnit y hy
  have hREven : Even R := by
    simpa only [R] using S.lowRange_gap_even hRange
  have hRUpper : R ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [R, Lemma65LowRange] using hRange
  by_cases hZTop : quadraticDefect K Z = ⊤
  · rw [hZTop, beliCorollary315EvenCongruenceFactor_top]
    exact bot_le
  · have hTUpper : T ≤ 2 * (ramificationIndex K : Int) := by
      by_contra hnot
      have hlarge : 2 * (ramificationIndex K : Int) <
          S.tailRescale.bong.lemma62Gap := by
        simpa only [T] using lt_of_not_ge hnot
      exact hZTop
        (S.tailRescale_normGeneratorValueRatio_defect_eq_top_of_two_e_lt
          hB hk y hy hlarge)
    have hTEven : Even T := by
      rcases lt_or_eq_of_le hTUpper with hlt | heqT
      · simpa only [T] using
          S.tailRescale_lemma62Gap_even_of_lt_two_e hB hRange hk
            (by simpa only [T] using hlt)
      · rw [heqT]
        exact even_two_mul (ramificationIndex K : Int)
    have hTLower : -(2 * (ramificationIndex K : Int)) ≤ T := by
      have hadmissible :=
        S.tailRescale.bong.adjacentParameter_isBinaryParameterAdmissible
          0 (by simp)
      have hlower := hadmissible.ordUnit_ge_neg_two_mul_e
      rw [S.tailRescale.bong.ordUnit_adjacentParameter_zero] at hlower
      simpa only [T] using hlower
    have hNNonneg :
        0 ≤ (ramificationIndex K : Int) + T / 2 := by
      rcases hTEven with ⟨t, ht⟩
      omega
    have hZLower := S.tailRescale_normGeneratorValueRatio_defect_lower
      hB hRange hk y hy
    change
      (Int.toNat ((ramificationIndex K : Int) + T / 2) : ℕ∞) ≤
        quadraticDefect K Z at hZLower
    let d : Nat := (quadraticDefect K Z).toNat
    have hZCoe : quadraticDefect K Z = (d : ℕ∞) :=
      (ENat.coe_toNat hZTop).symm
    rw [hZCoe] at hZLower
    norm_cast at hZLower
    have hNCast :
        (Int.toNat ((ramificationIndex K : Int) + T / 2) : Int) =
          (ramificationIndex K : Int) + T / 2 := by
      rw [Int.toNat_of_nonneg hNNonneg]
    have hdLower :
        (ramificationIndex K : Int) + T / 2 ≤ (d : Int) := by
      have hdNatCast :
          (Int.toNat ((ramificationIndex K : Int) + T / 2) : Int) ≤
            (d : Int) := by
        exact_mod_cast hZLower
      simpa only [hNCast] using hdNatCast
    have hsum : R + T = b.order 2 - b.order 0 := by
      simpa only [R, T] using S.finalHeadGap_add_tailRescaleGap
    have hexponent :
        (R + T + 1) / 2 ≤
          R / 2 + (d : Int) - (ramificationIndex K : Int) := by
      rcases hREven with ⟨r, hr⟩
      rcases hTEven with ⟨t, ht⟩
      omega
    rw [beliCorollary315EvenCongruenceFactor_of_ne_top
      (K := K) R (quadraticDefect K Z) hZTop]
    unfold lemma66SharpCongruenceFactor lemma66SharpDepth
    apply principalUnitSquareClassSubgroup_anti K
    apply Int.toNat_le_toNat
    rw [← hsum]
    exact hexponent

/-- The final-tail value ratio itself is above the Corollary 3.15(ii)
low-defect cutoff.  The strictness comes from Property A's inequality
`R₁ < R₃`. -/
theorem tailRescale_normGeneratorValueRatio_not_lowDefect
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hRange : b.Lemma65LowRange S) (hk : S.k ≤ 1)
    (y : q.vectorOrthogonal b.head)
    (hy : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice y) :
    ¬ 2 * quadraticDefect K
          (S.tailRescale.bong.normGeneratorValueRatioUnit y hy) ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) -
            (b.order 1 + 2 * (S.k : Int) - b.order 0)) : ℕ∞) := by
  let R : Int := b.order 1 + 2 * (S.k : Int) - b.order 0
  let T : Int := S.tailRescale.bong.lemma62Gap
  let Z : Kˣ := S.tailRescale.bong.normGeneratorValueRatioUnit y hy
  by_cases hlarge : 2 * (ramificationIndex K : Int) < T
  · have htop : quadraticDefect K Z = ⊤ := by
      exact S.tailRescale_normGeneratorValueRatio_defect_eq_top_of_two_e_lt
        hB hk y hy (by simpa only [T] using hlarge)
    change ¬2 * quadraticDefect K Z ≤ _
    rw [htop]
    simp
  · have hTUpper : T ≤ 2 * (ramificationIndex K : Int) := by omega
    have hTEven : Even T := by
      rcases lt_or_eq_of_le hTUpper with hlt | heqT
      · simpa only [T] using
          S.tailRescale_lemma62Gap_even_of_lt_two_e hB hRange hk
            (by simpa only [T] using hlt)
      · rw [heqT]
        exact even_two_mul (ramificationIndex K : Int)
    have hTLower : -(2 * (ramificationIndex K : Int)) ≤ T := by
      have hadmissible :=
        S.tailRescale.bong.adjacentParameter_isBinaryParameterAdmissible
          0 (by simp)
      have hlower := hadmissible.ordUnit_ge_neg_two_mul_e
      rw [S.tailRescale.bong.ordUnit_adjacentParameter_zero] at hlower
      simpa only [T] using hlower
    have hRUpper : R ≤ 2 * (ramificationIndex K : Int) := by
      simpa only [R, Lemma65LowRange] using hRange
    have hsum : R + T = b.order 2 - b.order 0 := by
      simpa only [R, T] using S.finalHeadGap_add_tailRescaleGap
    have hsumPos : 0 < R + T := by
      rw [hsum]
      exact sub_pos.mpr (hB.1 0 (by simp))
    have hNNonneg :
        0 ≤ (ramificationIndex K : Int) + T / 2 := by
      rcases hTEven with ⟨t, ht⟩
      omega
    have hcutNonneg :
        0 ≤ 2 * (ramificationIndex K : Int) - R := by omega
    have hcutCast :
        (Int.toNat (2 * (ramificationIndex K : Int) - R) : Int) =
          2 * (ramificationIndex K : Int) - R := by
      rw [Int.toNat_of_nonneg hcutNonneg]
    have hNCast :
        (Int.toNat ((ramificationIndex K : Int) + T / 2) : Int) =
          (ramificationIndex K : Int) + T / 2 := by
      rw [Int.toNat_of_nonneg hNNonneg]
    have hnatLt :
        Int.toNat (2 * (ramificationIndex K : Int) - R) <
          2 * Int.toNat ((ramificationIndex K : Int) + T / 2) := by
      have hcastLt :
          (Int.toNat (2 * (ramificationIndex K : Int) - R) : Int) <
            2 * (Int.toNat
              ((ramificationIndex K : Int) + T / 2) : Int) := by
        rw [hcutCast, hNCast]
        rcases hTEven with ⟨t, ht⟩
        omega
      exact_mod_cast hcastLt
    have hcutLt :
        (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) <
          2 * (Int.toNat
            ((ramificationIndex K : Int) + T / 2) : ℕ∞) := by
      exact_mod_cast hnatLt
    have hZLower := S.tailRescale_normGeneratorValueRatio_defect_lower
      hB hRange hk y hy
    change
      (Int.toNat ((ramificationIndex K : Int) + T / 2) : ℕ∞) ≤
        quadraticDefect K Z at hZLower
    change ¬2 * quadraticDefect K Z ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞)
    intro hlow
    have htwice := mul_le_mul_left' hZLower (2 : ℕ∞)
    exact (not_le_of_gt hcutLt) (htwice.trans hlow)

/-- Away from the finite-defect boundary, the normalized projection parameter
also lies above the Corollary 3.15(ii) cutoff.  Its defect dominates the
minimum of the base defect and the tail value-ratio defect. -/
theorem normalizedProjectionParameter_not_lowDefect_of_nonboundary
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (hRange : b.Lemma65LowRange S)
    (hnotBoundary : ¬(
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))) :
    ¬ 2 * quadraticDefect K
          (-(normalizedUnitPart K
            (S.projectionFactorUnit x hfactorNe))) ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) -
            (b.order 1 + 2 * (S.k : Int) - b.order 0)) : ℕ∞) := by
  let R : Int := b.order 1 + 2 * (S.k : Int) - b.order 0
  let epsilon : Kˣ :=
    normalizedUnitPart K (b.adjacentParameter 0 (by simp))
  let eta : Kˣ := normalizedUnitPart K
    (S.projectionFactorUnit x hfactorNe)
  let Z : Kˣ := S.tailRescale.bong.normGeneratorValueRatioUnit
    (S.projection x) hgenerator
  have hk : S.k ≤ 1 :=
    (S.lowRange_boundary_or_k_le_one hRange).resolve_left hnotBoundary
  have hRUpper : R ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [R, Lemma65LowRange] using hRange
  have hREven : Even R := by
    simpa only [R] using S.lowRange_gap_even hRange
  have hRFormula : R = b.lemma62Gap + 2 * (S.k : Int) := by
    simp only [R, lemma62Gap]
    omega
  have hepsilon : IsValuationUnit K (epsilon : K) := by
    simpa only [epsilon] using normalizedUnitPart_isValuationUnit K
      (b.adjacentParameter 0 (by simp))
  have hbaseEq : uniformizerPowerUnit K R * epsilon =
      b.headSecondRescaledParameter S.k := by
    rw [hRFormula]
    simpa only [epsilon] using
      (b.headSecondRescaledParameter_eq_normalized S.k).symm
  have hbaseAdmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon) := by
    rw [hbaseEq]
    exact b.headSecondRescaledParameter_isBinaryParameterAdmissible S.k
  have hcases : BeliLemma317ParameterCases (K := K) R epsilon := by
    rw [hRFormula]
    simpa only [epsilon] using S.finalParameterCases
  have hnotBoundary' : ¬
      (quadraticDefect K (-epsilon) ≠ ⊤ ∧
        R = 2 * (ramificationIndex K : Int) -
          2 * ((quadraticDefect K (-epsilon)).toNat : Int)) := by
    rw [hRFormula]
    simpa only [epsilon] using hnotBoundary
  have hbaseNotLow : ¬2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) :=
    BeliLemma317ParameterCases.not_lowDefect_of_not_boundary
      R epsilon hepsilon hbaseAdmissible hRUpper hREven hcases hnotBoundary'
  have hratioNotLow : ¬2 * quadraticDefect K Z ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) := by
    simpa only [R, Z] using
      S.tailRescale_normGeneratorValueRatio_not_lowDefect
        hB hRange hk (S.projection x) hgenerator
  have heta : eta = epsilon * Z := by
    simpa only [eta, epsilon, Z] using
      S.normalizedUnitPart_projectionFactorUnit_eq_original_mul_tailRatio
        x heq hfactorNe hgenerator
  have hnegEta : -eta = (-epsilon) * Z := by
    rw [heta]
    simp only [neg_mul]
  have hdom := quadraticDefect_mul_ge_min K (-epsilon) Z
  rw [← hnegEta] at hdom
  change ¬2 * quadraticDefect K (-eta) ≤
    (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞)
  intro hlow
  have hbaseAbove :
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) <
        2 * quadraticDefect K (-epsilon) := lt_of_not_ge hbaseNotLow
  have hratioAbove :
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) <
        2 * quadraticDefect K Z := lt_of_not_ge hratioNotLow
  have hminAbove :
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) <
        2 * min (quadraticDefect K (-epsilon)) (quadraticDefect K Z) := by
    rw [mul_min]
    exact lt_min hbaseAbove hratioAbove
  have htwice := mul_le_mul_left' hdom (2 : ℕ∞)
  exact (not_le_of_gt hminAbove) (htwice.trans hlow)

/-- In the nonboundary low range, Corollary 3.15(ii) puts the binary spinor
group of every norm-generator projection factor inside the sharp target `H`.
-/
theorem projectionFactorSpinorGroup_le_sharpHeadFactor_of_lowRange_nonboundary
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (hRange : b.Lemma65LowRange S)
    (hnotBoundary : ¬(
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))) :
    beliSpinorGroup K
        (unitSquareClass K (S.projectionFactorUnit x hfactorNe)) ≤
      b.lemma66SharpHeadFactor := by
  let R : Int := b.order 1 + 2 * (S.k : Int) - b.order 0
  let epsilon : Kˣ :=
    normalizedUnitPart K (b.adjacentParameter 0 (by simp))
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  let eta : Kˣ := normalizedUnitPart K p
  let Z : Kˣ := S.tailRescale.bong.normGeneratorValueRatioUnit
    (S.projection x) hgenerator
  have hk : S.k ≤ 1 :=
    (S.lowRange_boundary_or_k_le_one hRange).resolve_left hnotBoundary
  have hRUpper : R ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [R, Lemma65LowRange] using hRange
  have hREven : Even R := by
    simpa only [R] using S.lowRange_gap_even hRange
  have hRFormula : R = b.lemma62Gap + 2 * (S.k : Int) := by
    simp only [R, lemma62Gap]
    omega
  have hepsilon : IsValuationUnit K (epsilon : K) := by
    simpa only [epsilon] using normalizedUnitPart_isValuationUnit K
      (b.adjacentParameter 0 (by simp))
  have hetaUnit : IsValuationUnit K (eta : K) := by
    simpa only [eta, p] using normalizedUnitPart_isValuationUnit K p
  have hbaseEq : uniformizerPowerUnit K R * epsilon =
      b.headSecondRescaledParameter S.k := by
    rw [hRFormula]
    simpa only [epsilon] using
      (b.headSecondRescaledParameter_eq_normalized S.k).symm
  have hpOrder : ordUnit K p = R := by
    simpa only [p, R] using
      S.ordUnit_projectionFactorUnit_of_tailRescale_isNormGenerator
        x heq hfactorNe hgenerator
  have hpEq : uniformizerPowerUnit K R * eta = p := by
    rw [← hpOrder]
    simpa only [eta] using uniformizerPower_mul_normalizedUnitPart K p
  have hbaseAdmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon) := by
    rw [hbaseEq]
    exact b.headSecondRescaledParameter_isBinaryParameterAdmissible S.k
  have hpAdmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * eta) := by
    rw [hpEq]
    simpa only [p] using
      S.projectionFactorUnit_isBinaryParameterAdmissible x hx hfactorNe
  have hcases : BeliLemma317ParameterCases (K := K) R epsilon := by
    rw [hRFormula]
    simpa only [epsilon] using S.finalParameterCases
  have hnotBoundary' : ¬
      (quadraticDefect K (-epsilon) ≠ ⊤ ∧
        R = 2 * (ramificationIndex K : Int) -
          2 * ((quadraticDefect K (-epsilon)).toNat : Int)) := by
    rw [hRFormula]
    simpa only [epsilon] using hnotBoundary
  have hbaseNotLow : ¬2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) :=
    BeliLemma317ParameterCases.not_lowDefect_of_not_boundary
      R epsilon hepsilon hbaseAdmissible hRUpper hREven hcases hnotBoundary'
  have hetaNotLow : ¬2 * quadraticDefect K (-eta) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) := by
    simpa only [eta, p, R] using
      S.normalizedProjectionParameter_not_lowDefect_of_nonboundary
        hB x hx heq hfactorNe hgenerator hRange hnotBoundary
  have hcor := beliSpinorGroupRepresentative_sup_of_even_order
    (K := K) R epsilon eta hepsilon hetaUnit hbaseAdmissible hpAdmissible
      hRUpper hREven hbaseNotLow hetaNotLow
  have heta : eta = epsilon * Z := by
    simpa only [eta, p, epsilon, Z] using
      S.normalizedUnitPart_projectionFactorUnit_eq_original_mul_tailRatio
        x heq hfactorNe hgenerator
  have hproduct : epsilon * eta = Z * epsilon ^ 2 := by
    rw [heta]
    simp only [pow_two]
    ac_rfl
  have hproductDefect : quadraticDefect K (epsilon * eta) =
      quadraticDefect K Z := by
    rw [hproduct, quadraticDefect_mul_square]
  rw [hbaseEq, hpEq, hproductDefect] at hcor
  have hpLe : beliSpinorGroupRepresentative K p ≤
      beliCorollary315EvenCongruenceFactor (K := K) R
          (quadraticDefect K Z) ⊔
        beliSpinorGroupRepresentative K
          (b.headSecondRescaledParameter S.k) := by
    have hle : beliSpinorGroupRepresentative K p ≤
        beliSpinorGroupRepresentative K
            (b.headSecondRescaledParameter S.k) ⊔
          beliSpinorGroupRepresentative K p := le_sup_right
    rwa [hcor] at hle
  have hfactorLe :
      beliCorollary315EvenCongruenceFactor (K := K) R
          (quadraticDefect K Z) ≤ b.lemma66SharpCongruenceFactor := by
    simpa only [R, Z] using
      S.tailRatio_corollary315Factor_le_sharpCongruence
        hB hRange hk (S.projection x) hgenerator
  have hbaseLe : beliSpinorGroupRepresentative K
        (b.headSecondRescaledParameter S.k) ≤
      b.lemma66SharpHeadFactor := by
    simpa only [← beliSpinorGroup_unitSquareClass] using
      S.beliSpinorGroup_headSecondRescaledParameter_le_sharpHeadFactor
  change beliSpinorGroupRepresentative K p ≤ b.lemma66SharpHeadFactor
  exact hpLe.trans (sup_le (hfactorLe.trans le_sup_right) hbaseLe)

/-- A quadratic norm hyperplane together with a sufficiently shallow
principal-unit layer generates the full square-class group. -/
theorem quadraticNorm_sup_principalUnit_eq_top_of_defect_add_le
    (a : Kˣ) (alpha d : Nat) (halpha : 0 < alpha)
    (hdefect : quadraticDefect K a = (d : ℕ∞))
    (hbound : alpha + d ≤ 2 * ramificationIndex K) :
    quadraticNormSquareClassSubgroup K a ⊔
        principalUnitSquareClassSubgroup K alpha = ⊤ := by
  have hnot : ¬principalUnitSquareClassSubgroup K alpha ≤
      quadraticNormSquareClassSubgroup K a := by
    rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff
      K a alpha halpha, hdefect]
    norm_cast
    omega
  rw [quadraticNormSquareClassSubgroup_eq_ker] at hnot ⊢
  simpa using inf_ker_sup_eq_of_le_of_not_le
    (squareClassHilbertCharacter K a) ⊤
    (principalUnitSquareClassSubgroup K alpha) le_top hnot

/-- At the finite-defect boundary the spinor group of the minimally shifted
first parameter is exactly the quadratic norm hyperplane of the normalized
base unit. -/
theorem beliSpinorGroup_headSecondRescaledParameter_eq_norm_of_boundary
    (S : b.Lemma65Setup)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)) :
    beliSpinorGroup K
        (unitSquareClass K (b.headSecondRescaledParameter S.k)) =
      quadraticNormSquareClassSubgroup K
        (-(normalizedUnitPart K
          (b.adjacentParameter 0 (by simp)))) := by
  let R : Int := b.lemma62Gap + 2 * (S.k : Int)
  let epsilon : Kˣ :=
    normalizedUnitPart K (b.adjacentParameter 0 (by simp))
  let d := quadraticDefect K (-epsilon)
  let A : Kˣ := b.headSecondRescaledParameter S.k
  have hdFinite : d ≠ ⊤ := by
    simpa only [d, epsilon] using hboundary.1
  have hRBoundary : R = 2 * (ramificationIndex K : Int) -
      2 * (d.toNat : Int) := by
    simpa only [R, d, epsilon] using hboundary.2
  have hREven : Even R := by
    refine ⟨(ramificationIndex K : Int) - (d.toNat : Int), ?_⟩
    omega
  have hepsilon : IsValuationUnit K (epsilon : K) := by
    simpa only [epsilon] using normalizedUnitPart_isValuationUnit K
      (b.adjacentParameter 0 (by simp))
  have hAeq : uniformizerPowerUnit K R * epsilon = A := by
    simpa only [R, epsilon, A] using
      (b.headSecondRescaledParameter_eq_normalized S.k).symm
  have hAOrder : ordUnit K A = R := by
    have h := b.ordUnit_headSecondRescaledParameter S.k
    simpa only [A] using h.trans (by
      simp only [R, lemma62Gap]
      omega)
  have hAAdmissible : IsBinaryParameterAdmissible A := by
    simpa only [A] using
      b.headSecondRescaledParameter_isBinaryParameterAdmissible S.k
  have hADefect : beliParameterDefect K A = d := by
    rw [← hAeq,
      beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) R epsilon hepsilon hREven]
  have hAFinite : beliParameterDefect K A ≠ ⊤ := by
    rw [hADefect]
    exact hdFinite
  have hRUpper : ordUnit K A ≤ 2 * (ramificationIndex K : Int) := by
    rw [hAOrder, hRBoundary]
    omega
  have hcutNonneg : 0 ≤ 2 * (ramificationIndex K : Int) - ordUnit K A := by
    omega
  have hcut : beliSpinorCaseIIILowerCutoff K A = 2 * d.toNat := by
    unfold beliSpinorCaseIIILowerCutoff
    rw [hAOrder, hRBoundary]
    omega
  have hdefectLow : 2 * beliParameterDefect K A ≤
      (beliSpinorCaseIIILowerCutoff K A : ℕ∞) := by
    rw [hADefect, hcut, ← ENat.coe_toNat hdFinite]
    norm_cast
  have hquarter : unitSquareClass K A ≠
      unitSquareClass K (negativeQuarterUnit K) := by
    intro hclass
    rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
      K hclass with ⟨s, hs, hAs⟩
    have hinvariant := beliParameterDefect_mul_valuationUnit_square K A s hs
    rw [hAs, beliParameterDefect_negativeQuarterUnit] at hinvariant
    exact hAFinite hinvariant.symm
  have hformula := beliSpinorGroupRepresentative_caseIII_low
    K A hAAdmissible hquarter hRUpper hdefectLow
  change beliSpinorGroupRepresentative K A = _
  rw [hformula]
  rcases hREven with ⟨r, hr⟩
  have hpower : uniformizerPowerUnit K R =
      uniformizerPowerUnit K r ^ 2 := by
    rw [hr]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
  have hnegative : -A = (-epsilon) * uniformizerPowerUnit K r ^ 2 := by
    rw [← hAeq, hpower]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hnegative, quadraticNormSquareClassSubgroup_mul_square]

/-- In the boundary branch, if the first gap of the final tail is at most
`2e`, the norm hyperplane and the sharp congruence layer already generate all
square classes; hence `H` is the full group. -/
theorem lemma66SharpHeadFactor_eq_top_of_lowRange_boundary_tailGap_le
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int))
    (hTUpper : S.tailRescale.bong.lemma62Gap ≤
      2 * (ramificationIndex K : Int)) :
    b.lemma66SharpHeadFactor = ⊤ := by
  let epsilon : Kˣ :=
    normalizedUnitPart K (b.adjacentParameter 0 (by simp))
  let d := quadraticDefect K (-epsilon)
  let alpha : Nat := b.lemma66SharpDepth
  have hdFinite : d ≠ ⊤ := by
    simpa only [d, epsilon] using hboundary.1
  have hboundaryEq : b.lemma62Gap + 2 * (S.k : Int) =
      2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
    simpa only [d, epsilon] using hboundary.2
  have hsum := S.finalHeadGap_add_tailRescaleGap
  have hgapPos : 0 < b.order 2 - b.order 0 :=
    sub_pos.mpr (hB.1 0 (by simp))
  have hdepthNonneg :
      0 ≤ (b.order 2 - b.order 0 + 1) / 2 := by omega
  have halphaCast : (alpha : Int) =
      (b.order 2 - b.order 0 + 1) / 2 := by
    simp only [alpha, lemma66SharpDepth]
    rw [Int.toNat_of_nonneg hdepthNonneg]
  have halpha : 0 < alpha := by
    have halphaInt : (0 : Int) < (alpha : Int) := by
      rw [halphaCast]
      omega
    exact_mod_cast halphaInt
  have htotalUpper : b.order 2 - b.order 0 ≤
      4 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
    have hfinalEq : b.order 1 + 2 * (S.k : Int) - b.order 0 =
        2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) := by
      unfold lemma62Gap at hboundaryEq
      omega
    omega
  have hboundInt : (alpha : Int) + (d.toNat : Int) ≤
      2 * (ramificationIndex K : Int) := by
    rw [halphaCast]
    omega
  have hbound : alpha + d.toNat ≤ 2 * ramificationIndex K := by
    exact_mod_cast hboundInt
  have hsup : quadraticNormSquareClassSubgroup K (-epsilon) ⊔
      principalUnitSquareClassSubgroup K alpha = ⊤ :=
    quadraticNorm_sup_principalUnit_eq_top_of_defect_add_le
      (-epsilon) alpha d.toNat halpha
        (ENat.coe_toNat hdFinite).symm hbound
  have hbaseEq :=
    S.beliSpinorGroup_headSecondRescaledParameter_eq_norm_of_boundary
      hboundary
  have hbaseLe :=
    S.beliSpinorGroup_headSecondRescaledParameter_le_sharpHeadFactor
  apply top_unique
  rw [← hsup]
  apply sup_le
  · rw [← hbaseEq]
    exact hbaseLe
  · change b.lemma66SharpCongruenceFactor ≤ b.lemma66SharpHeadFactor
    exact le_sup_right

/-- A literal unary orthogonal split gives the square-residue description
`Q(L) ⊆ a₁ · 𝒪² + 𝔭^{R₂}`.  This is the elementary value-set
calculation used in the odd high branch of Lemma 6.6. -/
theorem quadraticValueSet_subset_scaled_of_unarySplit
    (c : BONG V q L (n + 2))
    (hsplit : c.HasTwoBlockSplit 1 (by omega)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (c.value 0)
        (Lattice.powerIdeal (K := K) (c.order 1)) := by
  rcases hsplit with ⟨T⟩
  let I : Lattice.CoefficientIdeal (K := K) :=
    Lattice.powerIdeal (K := K) (c.order 1)
  have hleftValue : T.left.bong.value 0 = c.value 0 := by
    calc
      T.left.bong.value 0 = c.value (T.left.sourceIndex 0) :=
        T.left.value_eq 0
      _ = c.value 0 := by congr 1
  have hleft : Lattice.quadraticValueSet
      (q.restrict T.left.carrier T.left.nondegenerate) T.left.lattice ⊆
        Lattice.scaledIntegralSquareResidueSet (c.value 0) I := by
    intro z hz
    rw [Lattice.mem_quadraticValueSet_iff] at hz
    rcases hz with ⟨v, hv, rfl⟩
    let qleft := q.restrict T.left.carrier T.left.nondegenerate
    have hheadNe : T.left.bong.head ≠ 0 := by
      intro hzero
      apply T.left.bong.head_isAnisotropic
      rw [hzero]
      exact qleft.quadratic_zero
    obtain ⟨a, ha⟩ :=
      (finrank_eq_one_iff_of_nonzero' T.left.bong.head hheadNe).mp
        T.left.bong.length_eq_finrank.symm v
    have hvEq : v = a • T.left.bong.head := ha.symm
    have hprojection : qleft.quadratic
        (qleft.orthogonalProjection T.left.bong.head v) = 0 := by
      rw [hvEq, map_smul,
        qleft.orthogonalProjection_self T.left.bong.head_isAnisotropic,
        smul_zero, qleft.quadratic_zero]
    have hscaled :=
      T.left.bong.quadraticValue_mem_scaled_of_projection_quadratic_zero
        v hv hprojection I
    simpa only [hleftValue] using hscaled
  let j0 : Fin (n + 2 - 1) := ⟨0, by omega⟩
  have hrightOrder : T.right.bong.order j0 = c.order 1 := by
    calc
      T.right.bong.order j0 = c.order (T.right.sourceIndex j0) :=
        T.right.order_eq j0
      _ = c.order 1 := by congr 1
  have hright : Lattice.quadraticValueSet
      (q.restrict T.right.carrier T.right.nondegenerate) T.right.lattice ⊆
        I := by
    intro z hz
    rw [Lattice.mem_quadraticValueSet_iff] at hz
    rcases hz with ⟨v, hv, rfl⟩
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.restrict T.right.carrier T.right.nondegenerate)
      T.right.lattice hv
    have hnormEq := normIdeal_eq_powerIdeal_order_mk_zero
      T.right.bong (by omega)
    change Lattice.normIdeal
        (q.restrict T.right.carrier T.right.nondegenerate)
          T.right.lattice =
      Lattice.powerIdeal (K := K) (T.right.bong.order j0) at hnormEq
    rw [hnormEq, hrightOrder] at hnorm
    exact hnorm
  exact T.quadraticValueSet_subset_scaled_of_blocks
    (c.value 0) I hleft hright

/-- If a BONG splits orthogonally after its unary head and the complementary
norm begins more than `2e` deeper, every norm-generator value ratio is a
square.  This is the square-residue argument used in the second half of
Beli's boundary case (3). -/
theorem normGeneratorValueRatio_defect_eq_top_of_unarySplit_gap_gt_two_e
    (c : BONG V q L (n + 2))
    (hsplit : c.HasTwoBlockSplit 1 (by omega))
    (hgap : 2 * (ramificationIndex K : Int) < c.lemma62Gap)
    (y : V) (hy : Lattice.IsNormGenerator q L y) :
    quadraticDefect K (c.normGeneratorValueRatioUnit y hy) = ⊤ := by
  rcases hsplit with ⟨T⟩
  let I : Lattice.CoefficientIdeal (K := K) :=
    Lattice.powerIdeal (K := K) (c.order 1)
  have hleftValue : T.left.bong.value 0 = c.value 0 := by
    calc
      T.left.bong.value 0 = c.value (T.left.sourceIndex 0) :=
        T.left.value_eq 0
      _ = c.value 0 := by congr 1
  have hleft : Lattice.quadraticValueSet
      (q.restrict T.left.carrier T.left.nondegenerate) T.left.lattice ⊆
        Lattice.scaledIntegralSquareResidueSet (c.value 0) I := by
    intro z hz
    rw [Lattice.mem_quadraticValueSet_iff] at hz
    rcases hz with ⟨v, hv, rfl⟩
    let qleft := q.restrict T.left.carrier T.left.nondegenerate
    have hheadNe : T.left.bong.head ≠ 0 := by
      intro hzero
      apply T.left.bong.head_isAnisotropic
      rw [hzero]
      exact qleft.quadratic_zero
    obtain ⟨a, ha⟩ :=
      (finrank_eq_one_iff_of_nonzero' T.left.bong.head hheadNe).mp
        T.left.bong.length_eq_finrank.symm v
    have hvEq : v = a • T.left.bong.head := ha.symm
    have hprojection : qleft.quadratic
        (qleft.orthogonalProjection T.left.bong.head v) = 0 := by
      rw [hvEq, map_smul,
        qleft.orthogonalProjection_self T.left.bong.head_isAnisotropic,
        smul_zero, qleft.quadratic_zero]
    have hscaled :=
      T.left.bong.quadraticValue_mem_scaled_of_projection_quadratic_zero
        v hv hprojection I
    simpa only [hleftValue] using hscaled
  let j0 : Fin (n + 2 - 1) := ⟨0, by omega⟩
  have hrightOrder : T.right.bong.order j0 =
      c.order 1 := by
    calc
      T.right.bong.order j0 = c.order (T.right.sourceIndex j0) :=
        T.right.order_eq j0
      _ = c.order 1 := by congr 1
  have hright : Lattice.quadraticValueSet
      (q.restrict T.right.carrier T.right.nondegenerate) T.right.lattice ⊆
        I := by
    intro z hz
    rw [Lattice.mem_quadraticValueSet_iff] at hz
    rcases hz with ⟨v, hv, rfl⟩
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.restrict T.right.carrier T.right.nondegenerate)
      T.right.lattice hv
    have hnormEq := normIdeal_eq_powerIdeal_order_mk_zero
      T.right.bong (by omega)
    change Lattice.normIdeal
        (q.restrict T.right.carrier T.right.nondegenerate)
          T.right.lattice =
      Lattice.powerIdeal (K := K) (T.right.bong.order j0) at hnormEq
    rw [hnormEq, hrightOrder] at hnorm
    exact hnorm
  have hvalues : Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (c.value 0) I :=
    T.quadraticValueSet_subset_scaled_of_blocks
      (c.value 0) I hleft hright
  let r : Nat := Int.toNat c.lemma62Gap
  have hgapPos : 0 < c.lemma62Gap := by
    have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hrCast : (r : Int) = c.lemma62Gap := by
    simp only [r]
    rw [Int.toNat_of_nonneg hgapPos.le]
  have hexponent : c.order 0 + (r : Int) ≤ c.order 1 := by
    rw [hrCast]
    unfold lemma62Gap
    omega
  have hmember :=
    c.normGeneratorValueRatioClass_mem_principal_of_quadraticValues
      (c.order 1) r hexponent hvalues y hy
  have hrDeep : 2 * ramificationIndex K < r := by
    exact_mod_cast (show
      2 * (ramificationIndex K : Int) < (r : Int) by
        rw [hrCast]
        exact hgap)
  rw [principalUnitValuationClassSubgroup_eq_bot_of_two_mul_e_lt
    (K := K) r hrDeep] at hmember
  have hclass : c.normGeneratorValueRatioClass y hy = 1 := by
    simpa only [Subgroup.mem_bot] using hmember
  have hfieldClass := congrArg (valuationUnitClassToSquareClass K) hclass
  have hsquare : IsSquare (c.normGeneratorValueRatioUnit y hy) := by
    change (c.normGeneratorValueRatioUnit y hy) ∈ Subgroup.square Kˣ
    apply (QuotientGroup.eq_one_iff
      (c.normGeneratorValueRatioUnit y hy)).1
    change squareClass K (c.normGeneratorValueRatioUnit y hy) = 1
    simpa only [normGeneratorValueRatioClass,
      normGeneratorValueRatioValuationUnit,
      valuationUnitClassToSquareClass_apply, map_one] using hfieldClass
  exact quadraticDefect_eq_top_of_isSquare K hsquare

/-- In Beli's finite-defect boundary branch the rescaled projected tail
splits after its unary head.  The strict third-order inequality supplied by
the minimal admissible exponent is exactly the order separation required by
the coordinate-splitting criterion. -/
theorem tailRescale_hasTwoBlockSplit_one_of_boundaryOrderData
    (S : b.Lemma65Setup) (D : S.BoundaryOrderData) :
    S.tailRescale.bong.HasTwoBlockSplit 1 (by omega) := by
  apply S.tailRescale.bong.exists_twoBlockSplit_of_leftOrders_le_rightHead
    1 (by omega) (by omega)
  intro i
  fin_cases i
  rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
  change S.tailRescale.bong.order 0 ≤ S.tailRescale.bong.order 1
  have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOne : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
    rw [b.order_tail]
    congr 1
  rw [S.tailRescale.order_zero_eq, htailZero]
  rw [show S.tailRescale.bong.order 1 = b.tail.order 1 by
    simpa using S.tailRescale.order_succ_eq (0 : Fin (n + 1)), htailOne]
  exact D.tailOrder_lt_third.le

/-- Multiplication by a square which is itself a valuation unit does not
change the refined unit-square class.  The square root is automatically a
valuation unit because its doubled order is zero. -/
theorem unitSquareClass_mul_eq_of_isSquare_valuationUnit
    (a z : Kˣ) (hzUnit : IsValuationUnit K (z : K))
    (hzSquare : IsSquare z) :
    unitSquareClass K (a * z) = unitSquareClass K a := by
  rcases hzSquare with ⟨s, hs⟩
  have hsOrder : ordUnit K s = 0 := by
    have h := congrArg (ordUnit K) hs
    rw [ordUnit_mul,
      (isValuationUnit_iff_ordUnit_eq_zero K z).1 hzUnit] at h
    omega
  have hsUnit : IsValuationUnit K (s : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K s).2 hsOrder
  have hzPow : z = s ^ 2 := by simpa only [pow_two] using hs
  rw [hzPow]
  exact unitSquareClass_mul_unit_square K a s hsUnit

/-- In the finite-defect boundary branch, every norm-generator projection
factor has binary spinor group contained in the sharp target.  For a shallow
tail the target is the full square-class group; for a deep tail the value
ratio is a valuation-unit square, so the projection factor has the same
refined class as the minimally shifted base parameter. -/
theorem projectionFactorSpinorGroup_le_sharpHeadFactor_of_lowRange_boundary
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (hRange : b.Lemma65LowRange S)
    (hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)) :
    beliSpinorGroup K
        (unitSquareClass K (S.projectionFactorUnit x hfactorNe)) ≤
      b.lemma66SharpHeadFactor := by
  by_cases htail : S.tailRescale.bong.lemma62Gap ≤
      2 * (ramificationIndex K : Int)
  · rw [S.lemma66SharpHeadFactor_eq_top_of_lowRange_boundary_tailGap_le
      hB hboundary htail]
    exact le_top
  · have htailDeep : 2 * (ramificationIndex K : Int) <
        S.tailRescale.bong.lemma62Gap := lt_of_not_ge htail
    let D := S.boundaryOrderData hB hboundary
    have hsplit :=
      S.tailRescale_hasTwoBlockSplit_one_of_boundaryOrderData D
    have hratioTop :=
      normGeneratorValueRatio_defect_eq_top_of_unarySplit_gap_gt_two_e
        S.tailRescale.bong hsplit htailDeep (S.projection x) hgenerator
    have hratioSquare : IsSquare
        (S.tailRescale.bong.normGeneratorValueRatioUnit
          (S.projection x) hgenerator) :=
      (quadraticDefect_eq_top_iff_isSquare (K := K) _).1 hratioTop
    have hratioUnit : IsValuationUnit K
        (S.tailRescale.bong.normGeneratorValueRatioUnit
          (S.projection x) hgenerator : K) :=
      S.tailRescale.bong.normGeneratorValueRatioUnit_isValuationUnit
        (S.projection x) hgenerator
    have hclass :
        unitSquareClass K (S.projectionFactorUnit x hfactorNe) =
          unitSquareClass K (b.headSecondRescaledParameter S.k) := by
      rw [S.projectionFactorUnit_eq_headSecondRescaledParameter_mul_tailRatio
        x heq hfactorNe hgenerator]
      exact unitSquareClass_mul_eq_of_isSquare_valuationUnit
        (b.headSecondRescaledParameter S.k)
        (S.tailRescale.bong.normGeneratorValueRatioUnit
          (S.projection x) hgenerator) hratioUnit hratioSquare
    rw [hclass]
    exact S.beliSpinorGroup_headSecondRescaledParameter_le_sharpHeadFactor

/-- Uniform low-range projection-factor bound.  The finite-defect equality
is precisely the boundary split; its negation is the Corollary 3.15(ii)
branch. -/
theorem projectionFactorSpinorGroup_le_sharpHeadFactor_of_lowRange
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (hRange : b.Lemma65LowRange S) :
    beliSpinorGroup K
        (unitSquareClass K (S.projectionFactorUnit x hfactorNe)) ≤
      b.lemma66SharpHeadFactor := by
  by_cases hboundary :
      (quadraticDefect K
          (-(normalizedUnitPart K
            (b.adjacentParameter 0 (by simp))))) ≠ ⊤ ∧
        b.lemma62Gap + 2 * (S.k : Int) =
          2 * (ramificationIndex K : Int) -
            2 * ((quadraticDefect K
              (-(normalizedUnitPart K
                (b.adjacentParameter 0 (by simp))))).toNat : Int)
  · exact S.projectionFactorSpinorGroup_le_sharpHeadFactor_of_lowRange_boundary
      hB x hx heq hfactorNe hgenerator hRange hboundary
  · exact
      S.projectionFactorSpinorGroup_le_sharpHeadFactor_of_lowRange_nonboundary
        hB x hx heq hfactorNe hgenerator hRange hboundary

/-- The minimal admissible binary prefix produces the auxiliary vector `x_0`
used in Lemma 6.6.  It is an actual vector of the original lattice, has the
same quadratic value as the BONG head, and its projection is a norm generator
of the rescaled tail. -/
theorem exists_auxiliaryEqualValueGenerator (S : b.Lemma65Setup) :
    ∃ x₀ : V,
      x₀ ∈ L ∧
        q.quadratic x₀ = q.quadratic b.head ∧
        Lattice.IsNormGenerator
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          S.tailRescale.lattice (S.projection x₀) := by
  let P := S.intermediateBONG.prefixWitness 2 (by omega)
  have hsome : HasSomeEqualNormGeneratorBasis P.bong.binaryParameter := by
    rw [show P.bong.binaryParameter = b.headSecondRescaledParameter S.k by
      simpa only [P] using S.intermediateBinaryPrefix_binaryParameter]
    exact S.admissible
  rcases P.bong.exists_equalValueCompanion_of_hasSome hsome with
    ⟨x₀, alpha, beta, _halpha, hbeta, hx₀Generator, hx₀Value,
      _hx₀Formula, hx₀Projection⟩
  have hhead : ((P.bong.head : P.carrier) : V) = b.head := by
    calc
      ((P.bong.head : P.carrier) : V) =
          (P.bong.ambientVector 0 : V) := by
            rw [P.bong.ambientVector_zero_eq_head]
      _ = S.intermediateBONG.ambientVector (P.sourceIndex 0) :=
        P.ambientVector_eq 0
      _ = S.intermediateBONG.ambientVector 0 := by
        congr 1
      _ = b.head := S.intermediateBONG_ambientVector_zero
  have htailHead :
      (((P.bong.tail.head :
          (q.restrict P.carrier P.nondegenerate).vectorOrthogonal
            P.bong.head) : P.carrier) : V) =
        ((S.tailRescale.bong.head :
          q.vectorOrthogonal b.head) : V) := by
    calc
      (((P.bong.tail.head :
            (q.restrict P.carrier P.nondegenerate).vectorOrthogonal
              P.bong.head) : P.carrier) : V) =
          ((P.bong.tail.ambientVector 0 : P.carrier) : V) := by
            rw [P.bong.tail.ambientVector_zero_eq_head]
      _ = (P.bong.ambientVector 1 : V) := by
        exact congrArg Subtype.val (P.bong.coe_ambientVector_tail 0)
      _ = S.intermediateBONG.ambientVector (P.sourceIndex 1) :=
        P.ambientVector_eq 1
      _ = S.intermediateBONG.ambientVector 1 := by
        congr 1
      _ = ((uniformizerPowerUnit K (S.k : Int) : Kˣ) : K) •
          b.ambientVector 1 := S.intermediateBONG_ambientVector_one
      _ = (S.tailRescale.bong.ambientVector 0 : V) :=
        S.coe_tailRescale_ambientVector_zero.symm
      _ = ((S.tailRescale.bong.head :
          q.vectorOrthogonal b.head) : V) := by
        rw [S.tailRescale.bong.ambientVector_zero_eq_head]
  have hx₀ProjectionAmbient :
      S.projection (x₀ : V) = beta • S.tailRescale.bong.head := by
    apply Subtype.ext
    change q.orthogonalProjection b.head (x₀ : V) =
      beta • ((S.tailRescale.bong.head :
        q.vectorOrthogonal b.head) : V)
    rw [q.orthogonalProjection_apply]
    have hp := congrArg Subtype.val hx₀Projection
    change
      (q.restrict P.carrier P.nondegenerate).orthogonalProjection
          P.bong.head x₀ =
        beta • (P.bong.tail.head : P.carrier) at hp
    rw [(q.restrict P.carrier P.nondegenerate).orthogonalProjection_apply]
      at hp
    have hpV := congrArg Subtype.val hp
    change
      (x₀ : V) -
          ((q.bilin (P.bong.head : P.carrier) x₀ /
              q.quadratic (P.bong.head : P.carrier)) : K) •
            (P.bong.head : V) =
        beta • (((P.bong.tail.head :
          (q.restrict P.carrier P.nondegenerate).vectorOrthogonal
            P.bong.head) : P.carrier) : V) at hpV
    rw [hhead, htailHead] at hpV
    exact hpV
  have hx₀Intermediate : (x₀ : V) ∈ S.intermediateLattice :=
    P.contained x₀ hx₀Generator.mem
  have hx₀L : (x₀ : V) ∈ L :=
    (S.mem_intermediateLattice_iff (x₀ : V)).1 hx₀Intermediate |>.1
  have hx₀ValueAmbient : q.quadratic (x₀ : V) =
      q.quadratic b.head := by
    change q.quadratic (x₀ : V) =
      q.quadratic ((P.bong.head : P.carrier) : V) at hx₀Value
    rwa [hhead] at hx₀Value
  have hbetaNe : beta ≠ 0 := by
    intro hzero
    rw [hzero, IsValuationUnit] at hbeta
    simpa using hbeta
  let betaUnit : Kˣ := Units.mk0 beta hbetaNe
  have hprojectionGenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (beta • S.tailRescale.bong.head) := by
    simpa only [betaUnit, Units.val_mk0] using
      S.tailRescale.bong.head_isNormGenerator.smul_valuationUnit
        betaUnit hbeta
  refine ⟨(x₀ : V), hx₀L, hx₀ValueAmbient, ?_⟩
  rwa [hx₀ProjectionAmbient]

/-- The complete low-range part of Lemma 6.6.  Whether or not the target
projection is already a norm generator, one or two applications of Lemma
6.5(ii)--(iii) produce an integral rotation carrying the BONG head to the
target vector; the projection-factor bounds above place its spinor norm in
the sharp target subgroup. -/
theorem exists_lowRangeRotation_apply_head_mem_lemma66SharpHeadFactor
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧
        f.spinorNorm ∈ b.lemma66SharpHeadFactor := by
  by_cases hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)
  · rcases b.beliLemma65_ii hB S x hx heq hlow hgenerator with ⟨w⟩
    have hfactorNe :=
      S.projectionFactor_ne_zero_of_tailRescale_isNormGenerator
        x heq hgenerator
    have hfactorLe :=
      S.projectionFactorSpinorGroup_le_sharpHeadFactor_of_lowRange
        hB x hx heq hfactorNe hgenerator hlow
    refine ⟨b.differenceTailRotation x w,
      b.differenceTailRotation_apply_head x w heq, ?_⟩
    exact b.differenceTailRotation_spinorNorm_mem_of_projectionFactor_le
      S x hx heq w hfactorNe hfactorLe
  · rcases S.exists_auxiliaryEqualValueGenerator with
      ⟨x₀, hx₀L, hx₀Value, hx₀Generator⟩
    rcases b.beliLemma65_ii hB S x₀ hx₀L hx₀Value hlow
        hx₀Generator with ⟨w₀⟩
    let x₁ : V :=
      q.reflectionLinearEquiv (b.head - x₀) w₀.anisotropic x
    have hx₁L : x₁ ∈ L := by
      exact w₀.integral x hx
    have hx₁Value : q.quadratic x₁ = q.quadratic b.head := by
      calc
        q.quadratic x₁ = q.quadratic x := by
          exact (q.reflectionIsometry (b.head - x₀)
            w₀.anisotropic).map_quadratic x
        _ = q.quadratic b.head := heq
    have hx₁Generator : Lattice.IsNormGenerator
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        S.tailRescale.lattice (S.projection x₁) := by
      exact b.beliLemma65_iii_with hB S x₀ hx₀L hx₀Value hlow
        hx₀Generator w₀ x hx heq hgenerator
    rcases b.beliLemma65_ii hB S x₁ hx₁L hx₁Value hlow
        hx₁Generator with ⟨w₁⟩
    have hfactorNe₀ :=
      S.projectionFactor_ne_zero_of_tailRescale_isNormGenerator
        x₀ hx₀Value hx₀Generator
    have hfactorNe₁ :=
      S.projectionFactor_ne_zero_of_tailRescale_isNormGenerator
        x₁ hx₁Value hx₁Generator
    have hfactorLe₀ :=
      S.projectionFactorSpinorGroup_le_sharpHeadFactor_of_lowRange
        hB x₀ hx₀L hx₀Value hfactorNe₀ hx₀Generator hlow
    have hfactorLe₁ :=
      S.projectionFactorSpinorGroup_le_sharpHeadFactor_of_lowRange
        hB x₁ hx₁L hx₁Value hfactorNe₁ hx₁Generator hlow
    refine ⟨b.differenceDifferenceRotation x₀ x₁ w₀ w₁,
      b.differenceDifferenceRotation_apply_head x x₀ x₁
        w₀ w₁ hx₁Value rfl, ?_⟩
    exact
      b.differenceDifferenceRotation_spinorNorm_mem_of_projectionFactors_le
        S x₀ x₁ hx₀L hx₁L hx₀Value hx₁Value w₀ w₁
          hfactorNe₀ hfactorNe₁ hfactorLe₀ hfactorLe₁

/-- Geometric projection of the complete low-range statement. -/
theorem exists_lowRangeRotation_apply_head
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S) :
    ∃ f : Lattice.IntegralRotation q L, f.apply b.head = x := by
  rcases S.exists_lowRangeRotation_apply_head_mem_lemma66SharpHeadFactor
      hB x hx heq hlow with ⟨f, hf, _⟩
  exact ⟨f, hf⟩

/-- Property B makes the natural-number sharp depth equal to the literal
ceiling `(R₃-R₁+1)/2` in `Int`. -/
theorem lemma66SharpDepth_cast
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB) :
    (b.lemma66SharpDepth : Int) =
      (b.order 2 - b.order 0 + 1) / 2 := by
  have h02 : b.order 0 < b.order 2 := hB.1 0 (by simp)
  unfold lemma66SharpDepth
  rw [Int.toNat_of_nonneg]
  omega

/-- If the second adjacent binary spinor group is its quadratic norm
hyperplane, properness of `H'` forces the sharp depth plus that norm
parameter's defect beyond `2e`.  This is the group-theoretic numerical
step used in the difficult even high branch of Lemma 6.6. -/
theorem two_e_lt_lemma66SharpDepth_add_tailParameterDefectNat
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤)
    (hgroup : beliSpinorGroupRepresentative K
        (b.adjacentParameter 1 (by simp)) =
      quadraticNormSquareClassSubgroup K
        (-(b.adjacentParameter 1 (by simp))))
    (hfinite : beliParameterDefect K
        (b.adjacentParameter 1 (by simp)) ≠ ⊤) :
    2 * ramificationIndex K <
      b.lemma66SharpDepth +
        beliParameterDefectNat K
          (b.adjacentParameter 1 (by simp)) := by
  let a : Kˣ := b.adjacentParameter 1 (by simp)
  let d : Nat := beliParameterDefectNat K a
  have hdefect : quadraticDefect K (-a) = (d : ℕ∞) := by
    have hfiniteA : quadraticDefect K (-a) ≠ ⊤ := by
      simpa only [a, beliParameterDefect] using hfinite
    change quadraticDefect K (-a) =
      ((quadraticDefect K (-a)).toNat : ℕ∞)
    exact (ENat.coe_toNat hfiniteA).symm
  change 2 * ramificationIndex K < b.lemma66SharpDepth + d
  by_contra hnot
  have hbound : b.lemma66SharpDepth + d ≤
      2 * ramificationIndex K := by omega
  have halpha : 0 < b.lemma66SharpDepth := by
    have h02 : b.order 0 < b.order 2 := hB.1 0 (by simp)
    unfold lemma66SharpDepth
    omega
  have htop : quadraticNormSquareClassSubgroup K (-a) ⊔
      principalUnitSquareClassSubgroup K b.lemma66SharpDepth = ⊤ :=
    quadraticNorm_sup_principalUnit_eq_top_of_defect_add_le
      (-a) b.lemma66SharpDepth d halpha hdefect hbound
  apply hproper
  unfold lemma66SharpTailFactor lemma66SharpCongruenceFactor
    adjacentUnitSquareClass
  rw [beliSpinorGroup_unitSquareClass]
  change beliSpinorGroupRepresentative K a ⊔
      principalUnitSquareClassSubgroup K b.lemma66SharpDepth = ⊤
  rw [hgroup]
  exact htop

/-- Coordinate-free form of Lemma 3.13(i): every auxiliary binary spinor
group of order `R>2e` lies in the principal-unit layer of depth `R-2e`. -/
theorem beliAuxiliarySpinorGroup_le_principal_of_order
    (p : Kˣ)
    (hp : 2 * (ramificationIndex K : Int) < ordUnit K p) :
    beliAuxiliarySpinorGroup K p hp ≤
      principalUnitSquareClassSubgroup K
        (Int.toNat
          (ordUnit K p - 2 * (ramificationIndex K : Int))) := by
  let epsilon : Kˣ := normalizedUnitPart K p
  have hepsilon : IsValuationUnit K (epsilon : K) :=
    normalizedUnitPart_isValuationUnit K p
  have h := beliAuxiliarySpinorGroup_le_principalUnitSquareClassSubgroup
    (K := K) (ordUnit K p) epsilon hepsilon hp
  have hpEq : uniformizerPowerUnit K (ordUnit K p) * epsilon = p :=
    uniformizerPower_mul_normalizedUnitPart K p
  simpa only [hpEq] using h

/-- The distinguished dyadic discriminant square class lies in the depth
`2e` principal-unit layer. -/
theorem discriminantSquareClass_mem_principalUnit_twoE :
    squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∈
      principalUnitSquareClassSubgroup K (2 * ramificationIndex K) := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  refine ⟨delta, ?_, rfl⟩
  exact discriminantUnit_mem_principalUnitSubgroup_twoE (K := K)

/-- An odd-order quadratic parameter does not norm the distinguished
discriminant class. -/
theorem discriminantSquareClass_not_mem_quadraticNorm_of_odd
    (a : Kˣ) (hodd : Odd (ordUnit K a)) :
    squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∉
      quadraticNormSquareClassSubgroup K (-a) := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have hoddNeg : Odd (ordUnit K (-a)) := by simpa using hodd
  have hhilbert : hilbertSymbol K delta (-a) ≠ 1 := by
    simpa only [delta] using
      hilbertSymbol_discriminant_ne_one_of_odd_order (-a) hoddNeg
  rw [quadraticNormSquareClassSubgroup_eq_ker]
  intro hmem
  change squareClassHilbertCharacter K (-a) (squareClass K delta) = 1 at hmem
  rw [squareClassHilbertCharacter_apply] at hmem
  apply hhilbert
  rw [hilbertSymbol_comm]
  exact hmem

/-- If the dyadic discriminant class is absent from the sharp head factor,
then the sharp congruence depth must lie strictly beyond `2e`; otherwise
the universal inclusion `Delta ∈ U_(2e)` would put it in that factor. -/
theorem two_e_lt_lemma66SharpDepth_of_discriminant_not_mem
    (b : BONG V q L (n + 3))
    (hdelta : squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∉
      b.lemma66SharpHeadFactor) :
    2 * ramificationIndex K < b.lemma66SharpDepth := by
  by_contra hnot
  have hdepthLe : b.lemma66SharpDepth ≤ 2 * ramificationIndex K := by
    omega
  apply hdelta
  unfold lemma66SharpHeadFactor
  apply (show b.lemma66SharpCongruenceFactor ≤
      beliSpinorGroup K (b.adjacentUnitSquareClass 0 (by simp)) ⊔
        b.lemma66SharpCongruenceFactor from le_sup_right)
  unfold lemma66SharpCongruenceFactor
  apply principalUnitSquareClassSubgroup_anti K hdepthLe
  exact discriminantSquareClass_mem_principalUnit_twoE (K := K)

/-- For an admissible odd parameter in the middle range, adjoining the
distinguished discriminant class to its full binary spinor group fills the
entire principal layer `U_(R-2e)`.  This is the `Δ ∈ H` branch in
Beli's proof of Lemma 6.6. -/
theorem principalUnit_order_sub_twoE_le_of_odd_spinor_and_discriminant
    (a : Kˣ) (H : Subgroup (SquareClass K))
    (ha : IsBinaryParameterAdmissible a)
    (hodd : Odd (ordUnit K a))
    (hRlow : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hspinor : beliSpinorGroupRepresentative K a ≤ H)
    (hdelta : squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∈ H) :
    principalUnitSquareClassSubgroup K
        (Int.toNat
          (ordUnit K a - 2 * (ramificationIndex K : Int))) ≤ H := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let m : Nat := Int.toNat
    (ordUnit K a - 2 * (ramificationIndex K : Int))
  have hdefect : beliParameterDefect K a = 0 := by
    unfold beliParameterDefect
    exact quadraticDefect_eq_zero_of_odd_ordUnit (-a) (by simpa using hodd)
  have hdefectNat : beliParameterDefectNat K a = 0 := by
    unfold beliParameterDefectNat
    rw [hdefect]
    simp
  have hcut : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞) := by
    rw [hdefect]
    simp
  have hexponent : beliSpinorCaseIILowExponent K a = m := by
    unfold beliSpinorCaseIILowExponent
    rw [hdefectNat]
    simp only [Nat.cast_zero, add_zero]
    rfl
  have hauxFormula := beliAuxiliarySpinorGroup_caseII_low
    (K := K) a hRlow hRhigh hcut
  rw [hexponent] at hauxFormula
  have hquarter := unitSquareClass_ne_negativeQuarter_of_two_e_lt
    (K := K) a hRlow
  have hfullFormula :=
    beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
      K a ha hquarter hRlow
  have hauxLeH : beliAuxiliarySpinorGroup K a hRlow ≤ H := by
    apply (show beliAuxiliarySpinorGroup K a hRlow ≤
      beliSpinorGroupRepresentative K a by
        rw [hfullFormula]
        exact le_sup_right) |>.trans
    exact hspinor
  have hinfLeH : principalUnitSquareClassSubgroup K m ⊓
      quadraticNormSquareClassSubgroup K (-a) ≤ H := by
    rw [← hauxFormula]
    exact hauxLeH
  have hmLe : m ≤ 2 * ramificationIndex K := by
    dsimp only [m]
    have hnonneg : 0 ≤
        ordUnit K a - 2 * (ramificationIndex K : Int) := by omega
    have hmCast : (m : Int) =
        ordUnit K a - 2 * (ramificationIndex K : Int) := by
      rw [Int.toNat_of_nonneg hnonneg]
    exact_mod_cast (show (m : Int) ≤
      2 * (ramificationIndex K : Int) by omega)
  have hdeltaLayer : squareClass K delta ∈
      principalUnitSquareClassSubgroup K m := by
    apply principalUnitSquareClassSubgroup_anti K hmLe
    simpa only [delta] using
      (discriminantSquareClass_mem_principalUnit_twoE (K := K))
  have hdeltaNotNorm : squareClass K delta ∉
      quadraticNormSquareClassSubgroup K (-a) := by
    simpa only [delta] using
      discriminantSquareClass_not_mem_quadraticNorm_of_odd
        (K := K) a hodd
  have hcyclicLayer : cyclicSquareClassSubgroup K delta ≤
      principalUnitSquareClassSubgroup K m :=
    (Subgroup.zpowers_le).2 hdeltaLayer
  have hcyclicNotNorm : ¬cyclicSquareClassSubgroup K delta ≤
      quadraticNormSquareClassSubgroup K (-a) := by
    intro hle
    exact hdeltaNotNorm (hle (Subgroup.mem_zpowers (squareClass K delta)))
  have hfill := inf_ker_sup_eq_of_le_of_not_le
    (squareClassHilbertCharacter K (-a))
    (principalUnitSquareClassSubgroup K m)
    (cyclicSquareClassSubgroup K delta) hcyclicLayer (by
      rw [← quadraticNormSquareClassSubgroup_eq_ker K (-a)]
      exact hcyclicNotNorm)
  rw [← quadraticNormSquareClassSubgroup_eq_ker K (-a)] at hfill
  rw [← hfill]
  apply sup_le hinfLeH
  apply (Subgroup.zpowers_le).2
  simpa only [delta] using hdelta

/-- Corollary 3.15(i), in the precise upper-bound form used in the high
range of Lemma 6.6.  Two parameters of the same order `R > 2e` have their
auxiliary groups related by the defect of the product of their normalized
unit parts.  A lower bound on that defect therefore puts the second
auxiliary group inside the indicated principal-unit layer together with the
first full binary spinor group. -/
theorem beliAuxiliarySpinorGroup_le_principal_sup_base_of_same_order
    (R : Int) (epsilon eta : Kˣ) (m : Nat)
    (hepsilon : IsValuationUnit K (epsilon : K))
    (heta : IsValuationUnit K (eta : K))
    (hbaseAdmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon))
    (htargetAdmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * eta))
    (hRlow : 2 * (ramificationIndex K : Int) < R)
    (hRhigh : R ≤ 4 * (ramificationIndex K : Int))
    (hdepth : quadraticDefect K (epsilon * eta) = ⊤ ∨
      (m : Int) ≤
        R - 2 * (ramificationIndex K : Int) +
          ((quadraticDefect K (epsilon * eta)).toNat : Int)) :
    beliAuxiliarySpinorGroup K
        (uniformizerPowerUnit K R * eta)
        (by
          rw [ordUnit_uniformizerPower_mul_valuationUnit eta heta R]
          exact hRlow) ≤
      principalUnitSquareClassSubgroup K m ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * epsilon) := by
  let a : Kˣ := uniformizerPowerUnit K R * epsilon
  let c : Kˣ := uniformizerPowerUnit K R * eta
  let D : ℕ∞ := quadraticDefect K (epsilon * eta)
  let A : Subgroup (SquareClass K) :=
    beliAuxiliarySpinorGroup K a (by
      dsimp only [a]
      rw [ordUnit_uniformizerPower_mul_valuationUnit epsilon hepsilon R]
      exact hRlow)
  let C : Subgroup (SquareClass K) :=
    beliAuxiliarySpinorGroup K c (by
      dsimp only [c]
      rw [ordUnit_uniformizerPower_mul_valuationUnit eta heta R]
      exact hRlow)
  let F : Subgroup (SquareClass K) :=
    beliLemma314CongruenceFactor (K := K)
      (R - 2 * (ramificationIndex K : Int)) D
  have hsup : A ⊔ C = F ⊔ A := by
    dsimp only [A, C, F, a, c, D]
    exact beliAuxiliarySpinorGroup_sup
      (K := K) R epsilon eta hepsilon heta hRlow hRhigh
  have hCle : C ≤ F ⊔ A := by
    have h : C ≤ A ⊔ C := le_sup_right
    rwa [hsup] at h
  have hFle : F ≤ principalUnitSquareClassSubgroup K m := by
    by_cases hDtop : D = ⊤
    · rw [show F = ⊥ by
        dsimp only [F]
        rw [hDtop, beliLemma314CongruenceFactor_top]]
      exact bot_le
    · rw [show F = principalUnitSquareClassSubgroup K
          (Int.toNat
            (R - 2 * (ramificationIndex K : Int) +
              (D.toNat : Int))) by
        dsimp only [F]
        rw [beliLemma314CongruenceFactor_of_ne_top
          (K := K) (R - 2 * (ramificationIndex K : Int)) D hDtop]]
      apply principalUnitSquareClassSubgroup_anti K
      have hsumNonneg : 0 ≤
          R - 2 * (ramificationIndex K : Int) + (D.toNat : Int) := by
        have hDnonneg : (0 : Int) ≤ (D.toNat : Int) := by positivity
        omega
      have hdepth' := hdepth.resolve_left hDtop
      change (m : Int) ≤
        R - 2 * (ramificationIndex K : Int) + (D.toNat : Int) at hdepth'
      rw [← Int.toNat_of_nonneg hsumNonneg] at hdepth'
      exact_mod_cast hdepth'
  have hAle : A ≤ beliSpinorGroupRepresentative K a := by
    have hquarter : unitSquareClass K a ≠
        unitSquareClass K (negativeQuarterUnit K) := by
      apply unitSquareClass_ne_negativeQuarter_of_two_e_lt
      dsimp only [a]
      rw [ordUnit_uniformizerPower_mul_valuationUnit epsilon hepsilon R]
      exact hRlow
    have hformula :=
      beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
        K a hbaseAdmissible hquarter (by
          dsimp only [a]
          rw [ordUnit_uniformizerPower_mul_valuationUnit epsilon hepsilon R]
          exact hRlow)
    rw [hformula]
    exact le_sup_right
  change C ≤ principalUnitSquareClassSubgroup K m ⊔
    beliSpinorGroupRepresentative K a
  exact hCle.trans (sup_le (hFle.trans le_sup_left) (hAle.trans le_sup_right))

/-- Coordinate-free form of the preceding Corollary 3.15(i) estimate.
Two admissible parameters of the same order above `2e` may be compared
directly; the defect of their quotient is the defect of the product of
their normalized unit parts, since the two expressions differ by a square.
-/
theorem beliAuxiliarySpinorGroup_le_principal_sup_base_of_same_order_units
    (a p : Kˣ) (m : Nat)
    (ha : IsBinaryParameterAdmissible a)
    (hp : IsBinaryParameterAdmissible p)
    (horder : ordUnit K p = ordUnit K a)
    (hlow : 2 * (ramificationIndex K : Int) < ordUnit K p)
    (hhigh : ordUnit K p ≤ 4 * (ramificationIndex K : Int))
    (hdepth : quadraticDefect K (p * a⁻¹) = ⊤ ∨
      (m : Int) ≤
        ordUnit K p - 2 * (ramificationIndex K : Int) +
          ((quadraticDefect K (p * a⁻¹)).toNat : Int)) :
    beliAuxiliarySpinorGroup K p hlow ≤
      principalUnitSquareClassSubgroup K m ⊔
        beliSpinorGroupRepresentative K a := by
  let R : Int := ordUnit K p
  let epsilon : Kˣ := normalizedUnitPart K a
  let eta : Kˣ := normalizedUnitPart K p
  have hepsilon : IsValuationUnit K (epsilon : K) := by
    simpa only [epsilon] using normalizedUnitPart_isValuationUnit K a
  have heta : IsValuationUnit K (eta : K) := by
    simpa only [eta] using normalizedUnitPart_isValuationUnit K p
  have haFactor : uniformizerPowerUnit K R * epsilon = a := by
    dsimp only [R, epsilon]
    rw [horder]
    exact uniformizerPower_mul_normalizedUnitPart K a
  have hpFactor : uniformizerPowerUnit K R * eta = p := by
    simpa only [R, eta] using uniformizerPower_mul_normalizedUnitPart K p
  have hproduct : epsilon * eta = (p * a⁻¹) * epsilon ^ 2 := by
    rw [← haFactor, ← hpFactor]
    simp only [mul_inv_rev, inv_mul_cancel₀, mul_one]
    simp [pow_two, mul_assoc, mul_comm, mul_left_comm]
  have hdefect : quadraticDefect K (epsilon * eta) =
      quadraticDefect K (p * a⁻¹) := by
    rw [hproduct, quadraticDefect_mul_square]
  have hbaseAdmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon) := by
    rwa [haFactor]
  have htargetAdmissible : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * eta) := by
    rwa [hpFactor]
  have hRlow : 2 * (ramificationIndex K : Int) < R := by
    simpa only [R] using hlow
  have hRhigh : R ≤ 4 * (ramificationIndex K : Int) := by
    simpa only [R] using hhigh
  have hdepth' : quadraticDefect K (epsilon * eta) = ⊤ ∨
      (m : Int) ≤
        R - 2 * (ramificationIndex K : Int) +
          ((quadraticDefect K (epsilon * eta)).toNat : Int) := by
    simpa only [R, hdefect] using hdepth
  have hle :=
    beliAuxiliarySpinorGroup_le_principal_sup_base_of_same_order
      (K := K) R epsilon eta m hepsilon heta hbaseAdmissible
        htargetAdmissible hRlow hRhigh hdepth'
  simpa only [haFactor, hpFactor] using hle

/-- The square-residue reduction used uniformly in the high range of
Beli's Lemma 6.6.  If an admissible target parameter `p` is represented by
`a * O^2` modulo `p^t`, with both `t` and `ord(p)` above `2e`, then its
auxiliary spinor group is generated by the depth-`t-2e` congruence layer
and the binary spinor group of `a`.

The proof includes both cases in Beli's argument.  If the square term is at
least as deep as the error, Lemma 3.13(i) applies directly.  Otherwise the
square term has the same order as `p`; the quotient defect is at least the
relative error depth, and Corollary 3.15(i) applies after the integral
square change from `a` to that term. -/
theorem beliAuxiliarySpinorGroup_le_of_mem_scaledIntegralSquareResidueSet
    (a p : Kˣ) (t : Int)
    (ha : IsBinaryParameterAdmissible a)
    (hp : IsBinaryParameterAdmissible p)
    (ht : 2 * (ramificationIndex K : Int) < t)
    (hpLow : 2 * (ramificationIndex K : Int) < ordUnit K p)
    (hresidue : (p : K) ∈
      Lattice.scaledIntegralSquareResidueSet (a : K)
        (Lattice.powerIdeal (K := K) t)) :
    beliAuxiliarySpinorGroup K p hpLow ≤
      principalUnitSquareClassSubgroup K
          (Int.toNat (t - 2 * (ramificationIndex K : Int))) ⊔
        beliSpinorGroupRepresentative K a := by
  let R : Int := ordUnit K p
  let m : Nat := Int.toNat (t - 2 * (ramificationIndex K : Int))
  have hmCast : (m : Int) =
      t - 2 * (ramificationIndex K : Int) := by
    dsimp only [m]
    rw [Int.toNat_of_nonneg]
    omega
  by_cases herrorFirst : t ≤ R
  · let eta : Kˣ := normalizedUnitPart K p
    have heta : IsValuationUnit K (eta : K) := by
      simpa only [eta] using normalizedUnitPart_isValuationUnit K p
    have hpFactor : uniformizerPowerUnit K R * eta = p := by
      simpa only [R, eta] using uniformizerPower_mul_normalizedUnitPart K p
    have hRlow : 2 * (ramificationIndex K : Int) < R := by
      simpa only [R] using hpLow
    have haux :=
      beliAuxiliarySpinorGroup_le_principalUnitSquareClassSubgroup
        (K := K) R eta heta hRlow
    have hmLe : m ≤
        Int.toNat (R - 2 * (ramificationIndex K : Int)) := by
      rw [show m = Int.toNat
          (t - 2 * (ramificationIndex K : Int)) by rfl]
      exact Int.toNat_le_toNat (by omega)
    have hprincipal : principalUnitSquareClassSubgroup K
          (Int.toNat (R - 2 * (ramificationIndex K : Int))) ≤
        principalUnitSquareClassSubgroup K m :=
      principalUnitSquareClassSubgroup_anti K hmLe
    have haux' : beliAuxiliarySpinorGroup K p hpLow ≤
        principalUnitSquareClassSubgroup K m := by
      simpa only [hpFactor] using haux.trans hprincipal
    exact haux'.trans le_sup_left
  · have hRlt : R < t := lt_of_not_ge herrorFirst
    rcases hresidue with ⟨c, hcError⟩
    let main : K := (a : K) * (c : K) ^ 2
    have herrorOrder : (t : WithTop Int) ≤
        ord K ((p : K) - main) := by
      exact (Lattice.mem_powerIdeal_iff (K := K) t _).1 hcError
    have hpOrder : ord K (p : K) = (R : WithTop Int) := by
      simpa only [R] using (coe_ordUnit K p).symm
    have hcNe : (c : K) ≠ 0 := by
      intro hc
      have hmainZero : main = 0 := by
        simp [main, hc]
      have hbad : (t : WithTop Int) ≤ (R : WithTop Int) := by
        rw [← hpOrder]
        simpa only [hmainZero, sub_zero] using herrorOrder
      exact (not_le_of_gt hRlt) (WithTop.coe_le_coe.mp hbad)
    let cUnit : Kˣ := Units.mk0 (c : K) hcNe
    have hcIntegral : (cUnit : K) ∈ IntegerRing K := by
      simpa only [cUnit, Units.val_mk0] using c.property
    let shifted : Kˣ := a * cUnit ^ 2
    have hshiftedValue : (shifted : K) = main := by
      rfl
    have herrorOrder' : (t : WithTop Int) ≤
        ord K ((p : K) - (shifted : K)) := by
      rwa [hshiftedValue]
    have hpLtError : ord K (p : K) <
        ord K ((p : K) - (shifted : K)) := by
      rw [hpOrder]
      exact (WithTop.coe_lt_coe.mpr hRlt).trans_le herrorOrder'
    have hshiftedOrderValue : ord K (shifted : K) = ord K (p : K) := by
      have hidentity : (shifted : K) =
          (p : K) - ((p : K) - (shifted : K)) := by ring
      rw [hidentity]
      exact (ord K).map_sub_eq_of_lt_left hpLtError
    have hsameOrder : ordUnit K p = ordUnit K shifted := by
      apply WithTop.coe_injective
      rw [coe_ordUnit K p, coe_ordUnit K shifted]
      exact hshiftedOrderValue.symm
    have hshiftedAdmissible : IsBinaryParameterAdmissible shifted := by
      exact ha.mul_integral_square hcIntegral
    by_cases hRveryHigh : 4 * (ramificationIndex K : Int) < R
    · rw [beliAuxiliarySpinorGroup_caseI K p hpLow (by
          simpa only [R] using hRveryHigh)]
      exact bot_le
    · have hRhigh : ordUnit K p ≤
          4 * (ramificationIndex K : Int) := by
        simpa only [R] using le_of_not_gt hRveryHigh
      let d : Nat := Int.toNat (t - R)
      have hdCast : (d : Int) = t - R := by
        dsimp only [d]
        rw [Int.toNat_of_nonneg]
        omega
      have hrelativeError :
          ((ordUnit K p + (d : Int) : Int) : WithTop Int) ≤
            ord K ((p : K) - (shifted : K)) := by
        have hsum : ordUnit K p + (d : Int) = t := by
          rw [show ordUnit K p = R by rfl, hdCast]
          omega
        rw [hsum]
        exact herrorOrder'
      have hdefectLower : (d : ℕ∞) ≤
          quadraticDefect K (p * shifted⁻¹) :=
        quadraticDefect_div_ge_of_sub_order
          (K := K) p shifted d hsameOrder hrelativeError
      have hdepth : quadraticDefect K (p * shifted⁻¹) = ⊤ ∨
          (m : Int) ≤
            ordUnit K p - 2 * (ramificationIndex K : Int) +
              ((quadraticDefect K (p * shifted⁻¹)).toNat : Int) := by
        by_cases htop : quadraticDefect K (p * shifted⁻¹) = ⊤
        · exact Or.inl htop
        · right
          have hdLe : d ≤
              (quadraticDefect K (p * shifted⁻¹)).toNat := by
            rw [← ENat.coe_toNat htop] at hdefectLower
            exact_mod_cast hdefectLower
          have hdLeInt : (d : Int) ≤
              ((quadraticDefect K (p * shifted⁻¹)).toNat : Int) := by
            exact_mod_cast hdLe
          rw [hdCast] at hdLeInt
          rw [hmCast, show ordUnit K p = R by rfl]
          omega
      have hcompare :=
        beliAuxiliarySpinorGroup_le_principal_sup_base_of_same_order_units
          (K := K) shifted p m hshiftedAdmissible hp hsameOrder hpLow
            hRhigh hdepth
      have hbaseLe : beliSpinorGroupRepresentative K shifted ≤
          beliSpinorGroupRepresentative K a := by
        exact beliSpinorGroup_mul_integral_square_le_of_admissible
          ha cUnit hcIntegral
      exact hcompare.trans (sup_le le_sup_left (hbaseLe.trans le_sup_right))

/-- Divide an absolute quadratic-value congruence in the rescaled tail by
the head value.  The resulting relative congruence is exactly the one for
the projection parameter used by the high-range auxiliary-group argument.
-/
theorem projectionFactorUnit_mem_scaledIntegralSquareResidueSet
    (S : b.Lemma65Setup) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (t : Int)
    (hresidue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) ∈
        Lattice.scaledIntegralSquareResidueSet
          (S.tailRescale.bong.value 0)
          (Lattice.powerIdeal (K := K) t)) :
    (S.projectionFactorUnit x hfactorNe : K) ∈
      Lattice.scaledIntegralSquareResidueSet
        (b.headSecondRescaledParameter S.k : K)
        (Lattice.powerIdeal (K := K) (t - b.order 0)) := by
  rcases hresidue with ⟨c, hcError⟩
  refine ⟨c, (Lattice.mem_powerIdeal_iff
    (K := K) (t - b.order 0) _).2 ?_⟩
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  let a : Kˣ := b.headSecondRescaledParameter S.k
  let qy : K :=
    (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (S.projection x)
  have hprojection : qy = (p : K) * q.quadratic b.head := by
    dsimp only [qy, p]
    simpa only [coe_projectionFactorUnit] using
      S.quadratic_projection_eq_one_sub_sq_mul x heq
  have htail : S.tailRescale.bong.value 0 =
      (a : K) * q.quadratic b.head := by
    simpa only [a] using
      S.tailRescale_value_zero_eq_headSecondRescaledParameter_mul_headValue
  have hidentity :
      qy - S.tailRescale.bong.value 0 * (c : K) ^ 2 =
        q.quadratic b.head * ((p : K) - (a : K) * (c : K) ^ 2) := by
    rw [hprojection, htail]
    ring
  have herrorOrder : (t : WithTop Int) ≤
      ord K (qy - S.tailRescale.bong.value 0 * (c : K) ^ 2) :=
    (Lattice.mem_powerIdeal_iff (K := K) t _).1 hcError
  rw [hidentity, ord_mul] at herrorOrder
  have hheadOrder : ord K (q.quadratic b.head) =
      (b.order 0 : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  rw [hheadOrder] at herrorOrder
  change ((t - b.order 0 : Int) : WithTop Int) ≤
    ord K ((p : K) - (a : K) * (c : K) ^ 2)
  by_cases hzero : (p : K) - (a : K) * (c : K) ^ 2 = 0
  · rw [hzero, ord_zero]
    exact le_top
  · let error : Kˣ :=
      Units.mk0 ((p : K) - (a : K) * (c : K) ^ 2) hzero
    have herrorValue :
        ord K ((p : K) - (a : K) * (c : K) ^ 2) =
          (ordUnit K error : WithTop Int) := by
      simpa only [error, Units.val_mk0] using (coe_ordUnit K error).symm
    rw [herrorValue] at herrorOrder ⊢
    norm_cast at herrorOrder ⊢
    omega

/-- A value-set estimate at the single universal exponent
`R₁ + 2e + ceil((R₃-R₁)/2)` is enough for the whole high-range spinor
argument.  After division by `Q(x₁)`, the square-residue theorem above
produces exactly the sharp congruence factor in Lemma 6.6. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_residue
    (S : b.Lemma65Setup) (hB : b.HasPropertyB) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hresidue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) ∈
        Lattice.scaledIntegralSquareResidueSet
          (S.tailRescale.bong.value 0)
          (Lattice.powerIdeal (K := K)
            (b.order 0 + 2 * (ramificationIndex K : Int) +
              (b.lemma66SharpDepth : Int)))) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  let a : Kˣ := b.headSecondRescaledParameter S.k
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  let t : Int := 2 * (ramificationIndex K : Int) +
    (b.lemma66SharpDepth : Int)
  have halphaPos : 0 < b.lemma66SharpDepth := by
    have h02 : b.order 0 < b.order 2 := hB.1 0 (by simp)
    unfold lemma66SharpDepth
    omega
  have ht : 2 * (ramificationIndex K : Int) < t := by
    dsimp only [t]
    have halphaPosInt : (0 : Int) < (b.lemma66SharpDepth : Int) := by
      exact_mod_cast halphaPos
    omega
  have hrelativeResidue : (p : K) ∈
      Lattice.scaledIntegralSquareResidueSet (a : K)
        (Lattice.powerIdeal (K := K) t) := by
    have h := S.projectionFactorUnit_mem_scaledIntegralSquareResidueSet
      x heq hfactorNe
        (b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int)) hresidue
    have hexponent :
        b.order 0 + 2 * (ramificationIndex K : Int) +
              (b.lemma66SharpDepth : Int) - b.order 0 = t := by
      dsimp only [t]
      omega
    rw [hexponent] at h
    simpa only [p, a] using h
  have ha : IsBinaryParameterAdmissible a := by
    simpa only [a] using
      b.headSecondRescaledParameter_isBinaryParameterAdmissible S.k
  have hp : IsBinaryParameterAdmissible p := by
    exact S.projectionFactorUnit_isBinaryParameterAdmissible
      x hx hfactorNe
  have hle :=
    beliAuxiliarySpinorGroup_le_of_mem_scaledIntegralSquareResidueSet
      (K := K) a p t ha hp ht (by simpa only [p] using hpLow)
        hrelativeResidue
  have hdepth : Int.toNat
      (t - 2 * (ramificationIndex K : Int)) =
        b.lemma66SharpDepth := by
    dsimp only [t]
    simp
  rw [hdepth] at hle
  apply hle.trans
  apply sup_le
  · exact le_sup_right
  · exact S.beliSpinorGroup_headSecondRescaledParameter_le_sharpHeadFactor

/-- Any rescaled-tail value-set estimate whose absolute precision reaches
the universal sharp exponent yields the required auxiliary-group bound.
This packages the common final step in all high-range subcases. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_tailValueSet
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (t : Int)
    (htarget : b.order 0 + 2 * (ramificationIndex K : Int) +
        (b.lemma66SharpDepth : Int) ≤ t)
    (hvalues : Lattice.quadraticValueSet
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        S.tailRescale.lattice ⊆
      Lattice.scaledIntegralSquareResidueSet
        (S.tailRescale.bong.value 0)
        (Lattice.powerIdeal (K := K) t)) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  have hprojectionMem : S.projection x ∈ S.tailRescale.lattice :=
    (b.beliLemma65_i hB S x hx heq).1 hnotExceptional
  have hqValue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) ∈
        Lattice.quadraticValueSet
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          S.tailRescale.lattice := by
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨S.projection x, hprojectionMem, rfl⟩
  have hbase := hvalues hqValue
  have hideal : Lattice.powerIdeal (K := K) t ≤
      Lattice.powerIdeal (K := K)
        (b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int)) :=
    (Lattice.powerIdeal_le_iff (K := K) _ _).2 htarget
  have hresidue := Lattice.scaledIntegralSquareResidueSet_mono
    (S.tailRescale.bong.value 0) hideal hbase
  exact
    S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_residue
      hB x hx heq hfactorNe hpLow hresidue

/-- The first order of the rescaled tail in ambient BONG notation. -/
theorem tailRescale_order_zero_eq_original (S : b.Lemma65Setup) :
    S.tailRescale.bong.order 0 =
      b.order 1 + 2 * (S.k : Int) := by
  have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  rw [S.tailRescale.order_zero_eq, htailZero]

/-- The second order of the rescaled tail is the third ambient BONG order. -/
theorem tailRescale_order_one_eq_original (S : b.Lemma65Setup) :
    S.tailRescale.bong.order 1 = b.order 2 := by
  have htailOne : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
    rw [b.order_tail]
    congr 1
  rw [show S.tailRescale.bong.order 1 = b.tail.order 1 by
    simpa using S.tailRescale.order_succ_eq (0 : Fin (n + 1)), htailOne]

/-- Outside the exceptional residue-two branch, membership of the projected
vector in the least rescaled tail gives the basic order comparison used in
the high-range proof of Lemma 6.6:
`R₂ + 2k - R₁ ≤ ord(1-a²)`. -/
theorem headRescaledGap_le_ord_projectionFactor_of_not_exceptional
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hnotExceptional : ¬b.Lemma65Exceptional) :
    b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
      ordUnit K (S.projectionFactorUnit x hfactorNe) := by
  have hprojectionMem : S.projection x ∈ S.tailRescale.lattice :=
    (b.beliLemma65_i hB S x hx heq).1 hnotExceptional
  have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
    (q.orthogonalSpace b.head b.head_isAnisotropic)
    S.tailRescale.lattice hprojectionMem
  rw [S.tailRescale.bong.normIdeal_eq_powerIdeal_order_zero] at hnorm
  have horder :=
    (Lattice.mem_powerIdeal_iff
      (K := K) (S.tailRescale.bong.order 0) _).1 hnorm
  have htailOrder : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  rw [S.tailRescale.order_zero_eq, htailOrder] at horder
  rw [S.ord_quadratic_projection_eq_head_add_projectionFactor
    x heq hfactorNe] at horder
  norm_cast at horder
  omega

/-- Odd high-range branch of Lemma 6.6 when the distinguished
discriminant class already belongs to the sharp target.  The odd binary
parameter fills the principal layer at its own order, and the projected
factor lies in a deeper layer because its order can only increase. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_odd_of_discriminant_mem
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hgapOdd : Odd b.lemma62Gap)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hpHigh : ordUnit K (S.projectionFactorUnit x hfactorNe) ≤
      4 * (ramificationIndex K : Int))
    (hdelta : squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∈
      b.lemma66SharpHeadFactor) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  let a : Kˣ := b.headSecondRescaledParameter S.k
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  have hRleP : ordUnit K a ≤ ordUnit K p := by
    dsimp only [a, p]
    rw [b.ordUnit_headSecondRescaledParameter]
    exact S.headRescaledGap_le_ord_projectionFactor_of_not_exceptional
      hB x hx heq hfactorNe hnotExceptional
  have ha : IsBinaryParameterAdmissible a := by
    simpa only [a] using
      b.headSecondRescaledParameter_isBinaryParameterAdmissible S.k
  have hoddA : Odd (ordUnit K a) := by
    rw [show ordUnit K a =
        b.lemma62Gap + 2 * (S.k : Int) by
      dsimp only [a]
      rw [b.ordUnit_headSecondRescaledParameter]
      unfold lemma62Gap
      omega]
    rcases hgapOdd with ⟨r, hr⟩
    refine ⟨r + (S.k : Int), ?_⟩
    omega
  have hRlow : 2 * (ramificationIndex K : Int) < ordUnit K a := by
    dsimp only [a]
    rw [b.ordUnit_headSecondRescaledParameter]
    change 2 * (ramificationIndex K : Int) + 1 ≤
      b.order 1 + 2 * (S.k : Int) - b.order 0 at hhigh
    omega
  have hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int) :=
    hRleP.trans (by simpa only [p] using hpHigh)
  have hspinor : beliSpinorGroupRepresentative K a ≤
      b.lemma66SharpHeadFactor := by
    simpa only [a, ← beliSpinorGroup_unitSquareClass] using
      S.beliSpinorGroup_headSecondRescaledParameter_le_sharpHeadFactor
  have hbaseLayer :=
    principalUnit_order_sub_twoE_le_of_odd_spinor_and_discriminant
      (K := K) a b.lemma66SharpHeadFactor ha hoddA hRlow hRhigh
        hspinor hdelta
  have hpAux := beliAuxiliarySpinorGroup_le_principal_of_order
    (K := K) p (by simpa only [p] using hpLow)
  have hdepthLe : Int.toNat
        (ordUnit K a - 2 * (ramificationIndex K : Int)) ≤
      Int.toNat (ordUnit K p - 2 * (ramificationIndex K : Int)) :=
    Int.toNat_le_toNat (by omega)
  have hfiltration : principalUnitSquareClassSubgroup K
        (Int.toNat (ordUnit K p - 2 * (ramificationIndex K : Int))) ≤
      principalUnitSquareClassSubgroup K
        (Int.toNat (ordUnit K a - 2 * (ramificationIndex K : Int))) :=
    principalUnitSquareClassSubgroup_anti K hdepthLe
  exact hpAux.trans (hfiltration.trans hbaseLayer)

/-- Complementary odd high-range branch.  If the distinguished
discriminant class is absent from the sharp target, the sharp depth is
strictly larger than `2e`.  Hence the third BONG order is beyond `4e`, while
the projected factor remains in the middle range.  The rescaled tail then
splits after its unary head and its full quadratic value set has the square
residue precision required by the universal high-range reduction. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_odd_of_discriminant_not_mem
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hpHigh : ordUnit K (S.projectionFactorUnit x hfactorNe) ≤
      4 * (ramificationIndex K : Int))
    (hdelta : squareClass K
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∉
      b.lemma66SharpHeadFactor) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  let c := S.tailRescale.bong
  have hprojectionMem : S.projection x ∈ S.tailRescale.lattice :=
    (b.beliLemma65_i hB S x hx heq).1 hnotExceptional
  have hRleP :=
    S.headRescaledGap_le_ord_projectionFactor_of_not_exceptional
      hB x hx heq hfactorNe hnotExceptional
  have hshiftedUpper :
      b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
        4 * (ramificationIndex K : Int) :=
    hRleP.trans hpHigh
  have hdepthLarge :=
    two_e_lt_lemma66SharpDepth_of_discriminant_not_mem
      (K := K) b hdelta
  have hdepthCast := lemma66SharpDepth_cast (K := K) b hB
  have hthirdGapLarge :
      4 * (ramificationIndex K : Int) + 1 ≤
        b.order 2 - b.order 0 := by
    have hdepthLargeInt :
        2 * (ramificationIndex K : Int) <
          (b.lemma66SharpDepth : Int) := by
      exact_mod_cast hdepthLarge
    rw [hdepthCast] at hdepthLargeInt
    omega
  have hcZero : c.order 0 = b.order 1 + 2 * (S.k : Int) := by
    dsimp only [c]
    have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    rw [S.tailRescale.order_zero_eq, htailZero]
  have hcOne : c.order 1 = b.order 2 := by
    dsimp only [c]
    have htailOne : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
      rw [b.order_tail]
      congr 1
    rw [show S.tailRescale.bong.order 1 = b.tail.order 1 by
      simpa using S.tailRescale.order_succ_eq (0 : Fin (n + 1)), htailOne]
  have hcStrict : c.order 0 < c.order 1 := by
    rw [hcZero, hcOne]
    omega
  have hsplit : c.HasTwoBlockSplit 1 (by omega) := by
    apply c.exists_twoBlockSplit_of_leftOrders_le_rightHead
      1 (by omega) (by omega)
    intro i
    fin_cases i
    rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
    change c.order 0 ≤ c.order 1
    exact hcStrict.le
  have hvalues := quadraticValueSet_subset_scaled_of_unarySplit c hsplit
  have hqValue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) ∈
        Lattice.quadraticValueSet
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          S.tailRescale.lattice := by
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨S.projection x, hprojectionMem, rfl⟩
  have hbase := hvalues hqValue
  have htarget :
      b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int) ≤ c.order 1 := by
    rw [hcOne, hdepthCast]
    omega
  have hideal : Lattice.powerIdeal (K := K) (c.order 1) ≤
      Lattice.powerIdeal (K := K)
        (b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int)) :=
    (Lattice.powerIdeal_le_iff (K := K) _ _).2 htarget
  have hresidue := Lattice.scaledIntegralSquareResidueSet_mono
    (c.value 0) hideal hbase
  exact
    S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_residue
      hB x hx heq hfactorNe hpLow (by simpa only [c] using hresidue)

/-- Complete nonexceptional odd high-range auxiliary-group estimate. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_odd
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hgapOdd : Odd b.lemma62Gap)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hpHigh : ordUnit K (S.projectionFactorUnit x hfactorNe) ≤
      4 * (ramificationIndex K : Int)) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  by_cases hdelta : squareClass K
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit ∈
        b.lemma66SharpHeadFactor
  · exact
      S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_odd_of_discriminant_mem
        hB x hx heq hfactorNe hhigh hnotExceptional hgapOdd hpLow hpHigh
          hdelta
  · exact
      S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_odd_of_discriminant_not_mem
        hB x hx heq hfactorNe hhigh hnotExceptional hpLow hpHigh hdelta

/-- In a nonexceptional even high-range branch the minimal rescaling is
zero or one.  The odd endpoint is excluded by parity and the only remaining
even endpoint has `k = 1`. -/
theorem k_le_one_of_highRange_even_not_exceptional
    (S : b.Lemma65Setup) (hhigh : b.Lemma65HighRange S)
    (hgapEven : Even b.lemma62Gap)
    (hnotExceptional : ¬b.Lemma65Exceptional) :
    S.k ≤ 1 := by
  rcases S.highRange_cases hhigh with
    hkZero | hodd | htwoE | hexceptional
  · omega
  · rcases hgapEven with ⟨r, hr⟩
    rcases hodd.1 with ⟨s, hs⟩
    omega
  · omega
  · exact (hnotExceptional hexceptional.1).elim

/-- Even nonexceptional high branch when the first gap of the rescaled tail
itself exceeds `2e`.  Lemma 6.2(ii)(a) supplies precision at the second tail
order, and the sum of the two high gaps is already large enough for the
sharp exponent. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_gt
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hgapEven : Even b.lemma62Gap)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hTlarge : 2 * (ramificationIndex K : Int) <
      S.tailRescale.bong.lemma62Gap) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  have hk := S.k_le_one_of_highRange_even_not_exceptional
    hhigh hgapEven hnotExceptional
  rcases S.exists_tailRescale_propertyBOrInverse_of_k_le_one hB hk with
    ⟨w, hw⟩
  have htailOrder : S.tailRescale.bong.order 0 ≤
      S.tailRescale.bong.order 1 := by
    unfold lemma62Gap at hTlarge
    omega
  have hvalues :=
    S.tailRescale.bong.beliLemma62_ii_a w hw htailOrder
  have hdepthCast := lemma66SharpDepth_cast (K := K) b hB
  have hsum := S.finalHeadGap_add_tailRescaleGap
  have htarget :
      b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int) ≤
        S.tailRescale.bong.order 1 := by
    rw [S.tailRescale_order_one_eq_original, hdepthCast]
    change 2 * (ramificationIndex K : Int) + 1 ≤
      b.order 1 + 2 * (S.k : Int) - b.order 0 at hhigh
    omega
  exact
    S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_tailValueSet
      hB x hx heq hfactorNe hnotExceptional hpLow
        (S.tailRescale.bong.order 1) htarget hvalues

/-- Even original first gap, but odd shallow gap in the rescaled tail.  The
original second adjacent parameter then has odd order at most `2e+1`, so its
binary spinor group is its quadratic norm hyperplane.  Properness of `H'`
forces the sharp depth beyond `2e`; Lemma 6.2(ii)(a) then has enough
precision. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_odd
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hgapEven : Even b.lemma62Gap)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hTupper : S.tailRescale.bong.lemma62Gap ≤
      2 * (ramificationIndex K : Int))
    (hTodd : Odd S.tailRescale.bong.lemma62Gap) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  have hk := S.k_le_one_of_highRange_even_not_exceptional
    hhigh hgapEven hnotExceptional
  rcases S.exists_tailRescale_propertyBOrInverse_of_k_le_one hB hk with
    ⟨w, hw⟩
  have hTnonneg : 0 ≤ S.tailRescale.bong.lemma62Gap := by
    have ha := S.tailRescale.bong.adjacentParameter_isBinaryParameterAdmissible
      0 (by simp)
    have hnonneg := ha.ordUnit_nonneg_of_odd (by
      rw [S.tailRescale.bong.ordUnit_adjacentParameter_zero]
      exact hTodd)
    rw [S.tailRescale.bong.ordUnit_adjacentParameter_zero] at hnonneg
    exact hnonneg
  have htailOrder : S.tailRescale.bong.order 0 ≤
      S.tailRescale.bong.order 1 := by
    unfold lemma62Gap at hTnonneg
    omega
  have hvalues :=
    S.tailRescale.bong.beliLemma62_ii_a w hw htailOrder
  let a : Kˣ := b.adjacentParameter 1 (by simp)
  have ha : IsBinaryParameterAdmissible a := by
    simpa only [a] using
      b.adjacentParameter_isBinaryParameterAdmissible 1 (by simp)
  have haOrder : ordUnit K a =
      S.tailRescale.bong.lemma62Gap + 2 * (S.k : Int) := by
    have hambient : ordUnit K a = b.order 2 - b.order 1 := by
      dsimp only [a]
      convert b.ordUnit_adjacentParameter (1 : Fin (n + 3)) (by simp)
        using 1 <;> congr 1
    exact hambient.trans S.secondGap_eq_tailRescale_lemma62Gap_add
  have haOdd : Odd (ordUnit K a) := by
    rw [haOrder]
    rcases hTodd with ⟨r, hr⟩
    refine ⟨r + (S.k : Int), ?_⟩
    omega
  have haUpper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) + 1 := by
    rw [haOrder]
    rcases hTodd with ⟨r, hr⟩
    omega
  have hgroup := beliSpinorGroupRepresentative_eq_norm_of_odd_trigger
    (K := K) a ha haOdd haUpper
  have hdefectZero : beliParameterDefect K a = 0 := by
    unfold beliParameterDefect
    exact quadraticDefect_eq_zero_of_odd_ordUnit (-a) (by simpa using haOdd)
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    rw [hdefectZero]
    exact ENat.zero_ne_top
  have hproperNumerical :=
    two_e_lt_lemma66SharpDepth_add_tailParameterDefectNat
      (K := K) b hB hproper (by simpa only [a] using hgroup)
        (by simpa only [a] using hfinite)
  have hdefectNatZero : beliParameterDefectNat K a = 0 := by
    unfold beliParameterDefectNat
    rw [hdefectZero]
    simp
  have hdepthLarge : 2 * ramificationIndex K <
      b.lemma66SharpDepth := by
    simpa only [a, hdefectNatZero, add_zero] using hproperNumerical
  have hdepthCast := lemma66SharpDepth_cast (K := K) b hB
  have hdepthLargeInt : 2 * (ramificationIndex K : Int) <
      (b.lemma66SharpDepth : Int) := by
    exact_mod_cast hdepthLarge
  have hthirdGapLarge :
      4 * (ramificationIndex K : Int) + 1 ≤
        b.order 2 - b.order 0 := by
    rw [hdepthCast] at hdepthLargeInt
    omega
  have htarget :
      b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int) ≤
        S.tailRescale.bong.order 1 := by
    rw [S.tailRescale_order_one_eq_original, hdepthCast]
    omega
  exact
    S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_tailValueSet
      hB x hx heq hfactorNe hnotExceptional hpLow
        (S.tailRescale.bong.order 1) htarget hvalues

/-- Even shallow tail gap in the high-defect range.  Lemma 6.2(ii)(c)
gives the midpoint-plus-`e` exponent; parity of both high-range gaps makes
that exponent at least the universal sharp exponent. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_even_highDefect
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hgapEven : Even b.lemma62Gap)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hTupper : S.tailRescale.bong.lemma62Gap ≤
      2 * (ramificationIndex K : Int))
    (hTeven : Even S.tailRescale.bong.lemma62Gap)
    (hdefect : (S.tailRescale.bong.lemma62DefectCutoff : ℕ∞) ≤
      beliParameterDefect K
        (S.tailRescale.bong.adjacentParameter 0 (by simp))) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  have hk := S.k_le_one_of_highRange_even_not_exceptional
    hhigh hgapEven hnotExceptional
  rcases S.exists_tailRescale_propertyBOrInverse_of_k_le_one hB hk with
    ⟨w, hw⟩
  have hvalues := S.tailRescale.bong.beliLemma62_ii_c
    w hw hTeven hTupper hdefect
  have hdepthCast := lemma66SharpDepth_cast (K := K) b hB
  have htarget :
      b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int) ≤
        S.tailRescale.bong.lemma62HighExponent := by
    unfold lemma62HighExponent
    rw [S.tailRescale_order_zero_eq_original,
      S.tailRescale_order_one_eq_original, hdepthCast]
    change 2 * (ramificationIndex K : Int) + 1 ≤
      b.order 1 + 2 * (S.k : Int) - b.order 0 at hhigh
    rcases hgapEven with ⟨r, hr⟩
    unfold lemma62Gap at hr
    rcases hTeven with ⟨t, ht⟩
    rw [S.tailRescale_lemma62Gap_eq] at ht
    omega
  exact
    S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_tailValueSet
      hB x hx heq hfactorNe hnotExceptional hpLow
        S.tailRescale.bong.lemma62HighExponent htarget hvalues

/-- Even shallow tail gap in the strict low-defect range.  The additional
`2k` in the numerical hypothesis is exactly what converts the rescaled-tail
cutoff into the original second-parameter cutoff.  Thus that binary spinor
group is its norm hyperplane; properness of `H'` yields
`2e < alpha + d`, while Lemma 6.2(ii)(b) supplies precision `R₃+d`. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_even_lowDefect
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hgapEven : Even b.lemma62Gap)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe))
    (hTupper : S.tailRescale.bong.lemma62Gap ≤
      2 * (ramificationIndex K : Int))
    (hTeven : Even S.tailRescale.bong.lemma62Gap)
    (hfinite : beliParameterDefect K
        (b.adjacentParameter 1 (by simp)) ≠ ⊤)
    (hlow : 2 * (S.k : Int) +
        2 * (beliParameterDefectNat K
          (b.adjacentParameter 1 (by simp)) : Int) ≤
      2 * (ramificationIndex K : Int) -
        S.tailRescale.bong.lemma62Gap) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  let a : Kˣ := b.adjacentParameter 1 (by simp)
  let d : Nat := beliParameterDefectNat K a
  have hk := S.k_le_one_of_highRange_even_not_exceptional
    hhigh hgapEven hnotExceptional
  rcases S.exists_tailRescale_propertyBOrInverse_of_k_le_one hB hk with
    ⟨w, hw⟩
  have hfiniteA : beliParameterDefect K a ≠ ⊤ := by
    simpa only [a] using hfinite
  have hdefectCoe : beliParameterDefect K a = (d : ℕ∞) := by
    dsimp only [d, beliParameterDefectNat]
    exact (ENat.coe_toNat hfiniteA).symm
  have hcutCast :=
    S.tailRescale.bong.lemma62DefectCutoff_cast hTeven hTupper
  have hdLeCutInt : (d : Int) ≤
      (S.tailRescale.bong.lemma62DefectCutoff : Int) := by
    rw [hcutCast]
    rcases hTeven with ⟨t, ht⟩
    change 2 * (S.k : Int) + 2 * (d : Int) ≤
      2 * (ramificationIndex K : Int) -
        S.tailRescale.bong.lemma62Gap at hlow
    omega
  have hdLeCutNat : d ≤ S.tailRescale.bong.lemma62DefectCutoff := by
    exact_mod_cast hdLeCutInt
  have htailDefect : beliParameterDefect K
        (S.tailRescale.bong.adjacentParameter 0 (by simp)) ≤
      (S.tailRescale.bong.lemma62DefectCutoff : ℕ∞) := by
    rw [S.tailRescale_parameterDefect_zero_eq_original_second]
    rw [show beliParameterDefect K (b.adjacentParameter 1 (by simp)) =
        (d : ℕ∞) by simpa only [a] using hdefectCoe]
    exact_mod_cast hdLeCutNat
  have hvalues := S.tailRescale.bong.beliLemma62_ii_b
    w hw hTeven hTupper htailDefect
  have ha : IsBinaryParameterAdmissible a := by
    simpa only [a] using
      b.adjacentParameter_isBinaryParameterAdmissible 1 (by simp)
  have haOrder : ordUnit K a =
      S.tailRescale.bong.lemma62Gap + 2 * (S.k : Int) := by
    have hambient : ordUnit K a = b.order 2 - b.order 1 := by
      dsimp only [a]
      convert b.ordUnit_adjacentParameter (1 : Fin (n + 3)) (by simp)
        using 1 <;> congr 1
    exact hambient.trans S.secondGap_eq_tailRescale_lemma62Gap_add
  have haUpper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) := by
    rw [haOrder]
    change 2 * (S.k : Int) + 2 * (d : Int) ≤
      2 * (ramificationIndex K : Int) -
        S.tailRescale.bong.lemma62Gap at hlow
    have hdNonneg : (0 : Int) ≤ (d : Int) := by positivity
    omega
  have hcutNonneg : 0 ≤
      2 * (ramificationIndex K : Int) - ordUnit K a := by omega
  have hcaseCutCast :
      (beliSpinorCaseIIILowerCutoff K a : Int) =
        2 * (ramificationIndex K : Int) - ordUnit K a := by
    unfold beliSpinorCaseIIILowerCutoff
    rw [Int.toNat_of_nonneg hcutNonneg]
  have hcaseDefectNat : 2 * d ≤ beliSpinorCaseIIILowerCutoff K a := by
    have hInt : 2 * (d : Int) ≤
        (beliSpinorCaseIIILowerCutoff K a : Int) := by
      rw [hcaseCutCast, haOrder]
      change 2 * (S.k : Int) + 2 * (d : Int) ≤
        2 * (ramificationIndex K : Int) -
          S.tailRescale.bong.lemma62Gap at hlow
      omega
    exact_mod_cast hInt
  have hcaseDefect : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
    rw [hdefectCoe]
    exact_mod_cast hcaseDefectNat
  have hgroup := beliSpinorGroupRepresentative_eq_norm_of_low_defect
    (K := K) a ha haUpper hcaseDefect hfiniteA
  have hproperNumerical :=
    two_e_lt_lemma66SharpDepth_add_tailParameterDefectNat
      (K := K) b hB hproper (by simpa only [a] using hgroup)
        (by simpa only [a] using hfiniteA)
  have hproperInt : 2 * (ramificationIndex K : Int) <
      (b.lemma66SharpDepth : Int) + (d : Int) := by
    exact_mod_cast (show 2 * ramificationIndex K <
      b.lemma66SharpDepth + d by
        simpa only [a, d] using hproperNumerical)
  have hdepthCast := lemma66SharpDepth_cast (K := K) b hB
  have htarget :
      b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int) ≤
        S.tailRescale.bong.lemma62LowExponent := by
    unfold lemma62LowExponent lemma62DefectNat
    rw [S.tailRescale_order_one_eq_original,
      S.tailRescale_parameterDefectNat_zero_eq_original_second]
    change b.order 0 + 2 * (ramificationIndex K : Int) +
        (b.lemma66SharpDepth : Int) ≤ b.order 2 + (d : Int)
    rw [hdepthCast] at hproperInt ⊢
    omega
  exact
    S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_tailValueSet
      hB x hx heq hfactorNe hnotExceptional hpLow
        S.tailRescale.bong.lemma62LowExponent htarget hvalues

/-- Complete nonexceptional even high-range auxiliary-group estimate.  The
rescaled-tail gap first separates into deep, odd shallow, and even shallow
cases.  In the last case the finite defect is split at the shifted cutoff
that makes Lemma 6.2(b) and (c) exhaustive, including the infinite-defect
endpoint. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hgapEven : Even b.lemma62Gap)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe)) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  by_cases hTlarge : 2 * (ramificationIndex K : Int) <
      S.tailRescale.bong.lemma62Gap
  · exact
      S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_gt
        hB x hx heq hfactorNe hhigh hnotExceptional hgapEven hpLow hTlarge
  · have hTupper : S.tailRescale.bong.lemma62Gap ≤
        2 * (ramificationIndex K : Int) := by omega
    rcases Int.even_or_odd S.tailRescale.bong.lemma62Gap with
      hTeven | hTodd
    · let a : Kˣ := b.adjacentParameter 1 (by simp)
      by_cases hfinite : beliParameterDefect K a ≠ ⊤
      · let d : Nat := beliParameterDefectNat K a
        by_cases hlow : 2 * (S.k : Int) + 2 * (d : Int) ≤
            2 * (ramificationIndex K : Int) -
              S.tailRescale.bong.lemma62Gap
        · exact
            S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_even_lowDefect
              hB x hx heq hfactorNe hhigh hnotExceptional hgapEven hproper
                hpLow hTupper hTeven (by simpa only [a] using hfinite)
                  (by simpa only [a, d] using hlow)
        · have hk := S.k_le_one_of_highRange_even_not_exceptional
              hhigh hgapEven hnotExceptional
          have hdefectCoe : beliParameterDefect K a = (d : ℕ∞) := by
            dsimp only [d, beliParameterDefectNat]
            exact (ENat.coe_toNat hfinite).symm
          have hcutCast :=
            S.tailRescale.bong.lemma62DefectCutoff_cast hTeven hTupper
          have hcutLeInt :
              (S.tailRescale.bong.lemma62DefectCutoff : Int) ≤ (d : Int) := by
            rw [hcutCast]
            rcases hTeven with ⟨t, ht⟩
            have hkNonneg : (0 : Int) ≤ (S.k : Int) := by positivity
            omega
          have hcutLeNat : S.tailRescale.bong.lemma62DefectCutoff ≤ d := by
            exact_mod_cast hcutLeInt
          have htailHigh :
              (S.tailRescale.bong.lemma62DefectCutoff : ℕ∞) ≤
                beliParameterDefect K
                  (S.tailRescale.bong.adjacentParameter 0 (by simp)) := by
            rw [S.tailRescale_parameterDefect_zero_eq_original_second]
            rw [show beliParameterDefect K
                (b.adjacentParameter 1 (by simp)) = (d : ℕ∞) by
              simpa only [a] using hdefectCoe]
            exact_mod_cast hcutLeNat
          exact
            S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_even_highDefect
              hB x hx heq hfactorNe hhigh hnotExceptional hgapEven hpLow
                hTupper hTeven htailHigh
      · have htop : beliParameterDefect K a = ⊤ := not_ne_iff.mp hfinite
        have htailHigh :
            (S.tailRescale.bong.lemma62DefectCutoff : ℕ∞) ≤
              beliParameterDefect K
                (S.tailRescale.bong.adjacentParameter 0 (by simp)) := by
          rw [S.tailRescale_parameterDefect_zero_eq_original_second]
          rw [show beliParameterDefect K
              (b.adjacentParameter 1 (by simp)) = ⊤ by
            simpa only [a] using htop]
          exact le_top
        exact
          S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_even_highDefect
            hB x hx heq hfactorNe hhigh hnotExceptional hgapEven hpLow
              hTupper hTeven htailHigh
    · exact
        S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even_tailGap_odd
          hB x hx heq hfactorNe hhigh hnotExceptional hgapEven hproper
            hpLow hTupper hTodd

/-- Uniform nonexceptional high-range auxiliary-group bound.  Parameters
above `4e` have trivial auxiliary group; in the middle range the original
first gap's parity selects the completed odd or even proof. -/
theorem projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_nonexceptional
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K (S.projectionFactorUnit x hfactorNe)) :
    beliAuxiliarySpinorGroup K
        (S.projectionFactorUnit x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  let p : Kˣ := S.projectionFactorUnit x hfactorNe
  by_cases hpVeryHigh : 4 * (ramificationIndex K : Int) < ordUnit K p
  · rw [beliAuxiliarySpinorGroup_caseI K p
      (by simpa only [p] using hpLow) hpVeryHigh]
    exact bot_le
  · have hpHigh : ordUnit K p ≤ 4 * (ramificationIndex K : Int) := by
      omega
    rcases Int.even_or_odd b.lemma62Gap with hgapEven | hgapOdd
    · exact
        S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_even
          hB x hx heq hfactorNe hhigh hnotExceptional hgapEven hproper hpLow
    · exact
        S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_odd
          hB x hx heq hfactorNe hhigh hnotExceptional hgapOdd hpLow
            (by simpa only [p] using hpHigh)

/-- In the high range the orthogonal projection of an equal-value lattice
vector has order strictly above `R_1+2e`.  The exceptional residue-two branch
uses the once-rescaled tail and its non-generator conclusion; every other
branch uses membership in the final rescaled tail. -/
theorem highRange_projection_order_lower
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S) :
    (((b.order 0 + 2 * (ramificationIndex K : Int) + 1 : Int)) :
        WithTop Int) ≤
      ord K ((q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
        (S.projection x)) := by
  by_cases hexceptional : b.Lemma65Exceptional
  · rcases (b.beliLemma65_i hB S x hx heq).2 hexceptional with
      ⟨_kTwo, ⟨E⟩⟩
    have hdeep :=
      (E.tailRescaleOne.bong.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one
        (S.projection x)).1
          ⟨E.projection_mem, E.projection_not_generator⟩ |>.2
    have htailOrder : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    have hrescaledOrder : E.tailRescaleOne.bong.order 0 = b.order 1 + 2 := by
      rw [E.tailRescaleOne.order_zero_eq, htailOrder]
      norm_num
    rw [hrescaledOrder] at hdeep
    have hgap := hexceptional.1
    unfold lemma62Gap at hgap
    convert hdeep using 1 <;> norm_cast <;> omega
  · have hprojectionMem : S.projection x ∈ S.tailRescale.lattice :=
      (b.beliLemma65_i hB S x hx heq).1 hexceptional
    have hnorm := Lattice.quadratic_mem_normIdeal_of_mem
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice hprojectionMem
    rw [S.tailRescale.bong.normIdeal_eq_powerIdeal_order_zero] at hnorm
    have horder :=
      (Lattice.mem_powerIdeal_iff
        (K := K) (S.tailRescale.bong.order 0) _).1 hnorm
    have htailOrder : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
      rw [b.order_tail]
      congr 1
    rw [S.tailRescale.order_zero_eq, htailOrder] at horder
    have hbound :
        (((b.order 0 + 2 * (ramificationIndex K : Int) + 1 : Int)) :
            WithTop Int) ≤
          ((b.order 1 + 2 * (S.k : Int) : Int) : WithTop Int) := by
      norm_cast
      change 2 * (ramificationIndex K : Int) + 1 ≤
        b.order 1 + 2 * (S.k : Int) - b.order 0 at hhigh
      omega
    exact hbound.trans horder

/-- In the high range, exactly one of the two equal-value reflection
vectors has the critical order required by Lemma 6.5(iv).  This is the
valuation-theoretic sign choice in Beli's proof of Lemma 6.6. -/
theorem highRange_head_sub_or_add_order_eq
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S) :
    ord K (q.quadratic (b.head - x)) =
        ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
          WithTop Int) ∨
      ord K (q.quadratic (b.head + x)) =
        ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
          WithTop Int) := by
  let a : K := q.bilin b.head x / q.quadratic b.head
  have hprojectionLower :=
    S.highRange_projection_order_lower hB x hx heq hhigh
  have hprojectionEq :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (S.projection x) =
        (1 - a ^ 2) * q.quadratic b.head := by
    simpa only [a] using S.quadratic_projection_eq_one_sub_sq_mul x heq
  have hheadOrder : ord K (q.quadratic b.head) =
      (b.order 0 : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  have hfactorLarge :
      ord K (2 : K) + ord K (2 : K) < ord K (1 - a ^ 2) := by
    rw [hprojectionEq, ord_mul, hheadOrder] at hprojectionLower
    by_cases hfactorZero : 1 - a ^ 2 = 0
    · rw [hfactorZero, ord_zero]
      rw [← ramificationIndex_spec]
      exact WithTop.coe_lt_top _
    · let factor : Kˣ := Units.mk0 (1 - a ^ 2) hfactorZero
      have hfactorOrder : ord K (1 - a ^ 2) =
          (ordUnit K factor : WithTop Int) := by
        simpa only [factor, Units.val_mk0] using
          (coe_ordUnit K factor).symm
      rw [hfactorOrder, ← ramificationIndex_spec]
      rw [hfactorOrder] at hprojectionLower
      norm_cast at hprojectionLower ⊢
      omega
  have hlinear :=
    one_sub_one_add_order_dichotomy_of_two_ord_two_lt a hfactorLarge
  have hsubValue : q.quadratic (b.head - x) =
      2 * (1 - a) * q.quadratic b.head := by
    simpa only [a] using
      S.quadratic_head_sub_eq_two_mul_one_sub_mul x heq
  have haddValue : q.quadratic (b.head + x) =
      2 * (1 + a) * q.quadratic b.head := by
    simpa only [a] using
      S.quadratic_head_add_eq_two_mul_one_add_mul x heq
  rcases hlinear with hminus | hplus
  · left
    rw [hsubValue, ord_mul, ord_mul, hminus.1,
      ← ramificationIndex_spec, hheadOrder]
    norm_cast
    omega
  · right
    rw [haddValue, ord_mul, ord_mul, hplus.1,
      ← ramificationIndex_spec, hheadOrder]
    norm_cast
    omega

/-- The high-range geometric part of Lemma 6.6.  The dyadic sign dichotomy
chooses either the difference reflection followed by the tail-head
reflection, or the sum reflection followed by the head reflection. -/
theorem exists_highRangeRotation_apply_head
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S) :
    ∃ f : Lattice.IntegralRotation q L, f.apply b.head = x := by
  rcases S.highRange_head_sub_or_add_order_eq hB x hx heq hhigh with
    hsub | hadd
  · let haniso := lemma65Difference_isAnisotropic_of_order_eq b x hsub
    have hintegral : Lattice.IsIntegralReflection (L := L) haniso :=
      b.beliLemma65_iv hB S x hx heq hhigh hsub
    let w : Lemma65DifferenceReflectionWitness b x :=
      ⟨haniso, hintegral⟩
    exact ⟨b.differenceTailRotation x w,
      b.differenceTailRotation_apply_head x w heq⟩
  · have hxneg : -x ∈ L := L.neg_mem hx
    have heqneg : q.quadratic (-x) = q.quadratic b.head := by
      rw [q.quadratic_neg, heq]
    have hsumOrder : ord K (q.quadratic (b.head - (-x))) =
        ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
          WithTop Int) := by
      simpa only [sub_neg_eq_add] using hadd
    let hsum := lemma65Difference_isAnisotropic_of_order_eq b (-x) hsumOrder
    have hintegral : Lattice.IsIntegralReflection (L := L) hsum :=
      b.beliLemma65_iv hB S (-x) hxneg heqneg hhigh hsumOrder
    refine ⟨b.sumHeadRotation x ?_ ?_, ?_⟩
    · simpa only [sub_neg_eq_add] using hsum
    · simpa only [sub_neg_eq_add] using hintegral
    · exact b.sumHeadRotation_apply_head x _ _ heq

/-- Complete nonexceptional high-range part of Lemma 6.6, including the
vanishing projection-factor endpoints.  For a nonzero factor, high range
and projected-tail membership put its order above `2e`; the completed odd
and even auxiliary-group estimates then control the critical reflection.
-/
theorem exists_highRangeRotation_apply_head_mem_lemma66SharpHeadFactor_of_not_exceptional
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧
        f.spinorNorm ∈ b.lemma66SharpHeadFactor := by
  rcases S.highRange_head_sub_or_add_order_eq hB x hx heq hhigh with
    hsub | hadd
  · let haniso := lemma65Difference_isAnisotropic_of_order_eq b x hsub
    have hintegral : Lattice.IsIntegralReflection (L := L) haniso :=
      b.beliLemma65_iv hB S x hx heq hhigh hsub
    let w : Lemma65DifferenceReflectionWitness b x :=
      ⟨haniso, hintegral⟩
    refine ⟨b.differenceTailRotation x w,
      b.differenceTailRotation_apply_head x w heq, ?_⟩
    by_cases hfactorZero :
        1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 = 0
    · exact
        b.differenceTailRotation_spinorNorm_mem_of_projectionFactor_eq_zero
          x heq w hfactorZero
    · have hpLower :=
        S.headRescaledGap_le_ord_projectionFactor_of_not_exceptional
          hB x hx heq hfactorZero hnotExceptional
      have hpLow : 2 * (ramificationIndex K : Int) <
          ordUnit K (S.projectionFactorUnit x hfactorZero) := by
        change 2 * (ramificationIndex K : Int) + 1 ≤
          b.order 1 + 2 * (S.k : Int) - b.order 0 at hhigh
        omega
      have haux :=
        S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_nonexceptional
          hB x hx heq hfactorZero hhigh hnotExceptional hproper hpLow
      exact
        b.differenceTailRotation_spinorNorm_mem_of_projectionFactorAuxiliary_le
          S x hx heq w hfactorZero hpLow hsub haux
  · have hxneg : -x ∈ L := L.neg_mem hx
    have heqneg : q.quadratic (-x) = q.quadratic b.head := by
      rw [q.quadratic_neg, heq]
    have hsumOrder : ord K (q.quadratic (b.head - (-x))) =
        ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
          WithTop Int) := by
      simpa only [sub_neg_eq_add] using hadd
    let hsumNeg :=
      lemma65Difference_isAnisotropic_of_order_eq b (-x) hsumOrder
    have hintegralNeg : Lattice.IsIntegralReflection (L := L) hsumNeg :=
      b.beliLemma65_iv hB S (-x) hxneg heqneg hhigh hsumOrder
    have hsum : q.IsAnisotropic (b.head + x) := by
      simpa only [sub_neg_eq_add] using hsumNeg
    have hintegral : Lattice.IsIntegralReflection (L := L) hsum := by
      simpa only [sub_neg_eq_add] using hintegralNeg
    refine ⟨b.sumHeadRotation x hsum hintegral,
      b.sumHeadRotation_apply_head x hsum hintegral heq, ?_⟩
    by_cases hfactorZero :
        1 - (q.bilin b.head (-x) / q.quadratic b.head) ^ 2 = 0
    · exact
        b.sumHeadRotation_spinorNorm_mem_of_projectionFactorNeg_eq_zero
          x heq hsum hintegral hfactorZero
    · have hpLower :=
        S.headRescaledGap_le_ord_projectionFactor_of_not_exceptional
          hB (-x) hxneg heqneg hfactorZero hnotExceptional
      have hpLow : 2 * (ramificationIndex K : Int) <
          ordUnit K (S.projectionFactorUnit (-x) hfactorZero) := by
        change 2 * (ramificationIndex K : Int) + 1 ≤
          b.order 1 + 2 * (S.k : Int) - b.order 0 at hhigh
        omega
      have haux :=
        S.projectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_high_nonexceptional
          hB (-x) hxneg heqneg hfactorZero hhigh hnotExceptional hproper hpLow
      exact
        b.sumHeadRotation_spinorNorm_mem_of_projectionFactorNegAuxiliary_le
          S x hx heq hsum hintegral hfactorZero hpLow hadd haux

/-- Geometric transport in Lemma 6.6, conditional only on the concrete
minimal-rescaling setup.  The low and high ranges are exhaustive because
all BONG orders are integral. -/
theorem exists_rotation_apply_head_of_setup
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    ∃ f : Lattice.IntegralRotation q L, f.apply b.head = x := by
  by_cases hlow : b.Lemma65LowRange S
  · exact S.exists_lowRangeRotation_apply_head hB x hx heq hlow
  · have hhigh : b.Lemma65HighRange S := by
      change ¬(b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
          2 * (ramificationIndex K : Int)) at hlow
      change 2 * (ramificationIndex K : Int) + 1 ≤
        b.order 1 + 2 * (S.k : Int) - b.order 0
      omega
    exact S.exists_highRangeRotation_apply_head hB x hx heq hhigh

/-- Spinor-complete nonexceptional form of Lemma 6.6 for a fixed least
rescaling setup. -/
theorem exists_rotation_apply_head_mem_lemma66SharpHeadFactor_of_setup_not_exceptional
    (S : b.Lemma65Setup) (hB : b.HasPropertyB)
    (hnotExceptional : ¬b.Lemma65Exceptional)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧
        f.spinorNorm ∈ b.lemma66SharpHeadFactor := by
  by_cases hlow : b.Lemma65LowRange S
  · exact S.exists_lowRangeRotation_apply_head_mem_lemma66SharpHeadFactor
      hB x hx heq hlow
  · have hhigh : b.Lemma65HighRange S := by
      change ¬(b.order 1 + 2 * (S.k : Int) - b.order 0 ≤
          2 * (ramificationIndex K : Int)) at hlow
      change 2 * (ramificationIndex K : Int) + 1 ≤
        b.order 1 + 2 * (S.k : Int) - b.order 0
      omega
    exact
      S.exists_highRangeRotation_apply_head_mem_lemma66SharpHeadFactor_of_not_exceptional
        hB x hx heq hhigh hnotExceptional hproper

end Lemma65Setup

namespace HeadRescaleWitness

variable {c : BONG V q L (n + 2)}

/-- A one-step head rescaling has the original lattice as its inverse-head
rescaling.  This is the intrinsic witness needed to apply Lemma 6.2 to the
exceptional once-rescaled tail. -/
noncomputable def inverseWitness_of_one
    (W : c.HeadRescaleWitness 1) :
    W.bong.HeadInverseRescaleWitness where
  lattice := L
  bong := c
  ambientVector_zero := by
    rw [W.ambientVector_zero]
    simp [uniformizerPowerUnit, smul_smul, uniformizer_ne_zero K]
  ambientVector_succ i := (W.ambientVector_succ i).symm

/-- The first order after one head rescaling. -/
theorem order_zero_eq_add_two (W : c.HeadRescaleWitness 1) :
    W.bong.order 0 = c.order 0 + 2 := by
  rw [W.order_zero_eq]
  norm_num

/-- The second order is unchanged by a head rescaling. -/
theorem order_one_eq (W : c.HeadRescaleWitness 1) :
    W.bong.order 1 = c.order 1 := by
  simpa using W.order_succ_eq (0 : Fin (n + 1))

/-- Unit-valued first coefficient after one head rescaling. -/
theorem valueUnit_zero_eq (W : c.HeadRescaleWitness 1) :
    W.bong.valueUnit 0 =
      uniformizerPowerUnit K (1 : Int) ^ 2 * c.valueUnit 0 := by
  apply Units.ext
  simp only [coe_valueUnit, Units.val_mul, Units.val_pow_eq_pow_val]
  rw [← W.bong.quadratic_ambientVector 0, W.ambientVector_zero,
    QuadraticSpace.quadratic_smul, c.quadratic_ambientVector]
  norm_num

/-- Unit-valued second coefficient is unchanged. -/
theorem valueUnit_one_eq (W : c.HeadRescaleWitness 1) :
    W.bong.valueUnit 1 = c.valueUnit 1 := by
  apply Units.ext
  simp only [coe_valueUnit]
  rw [← W.bong.quadratic_ambientVector 1,
    ← c.quadratic_ambientVector 1]
  exact congrArg q.quadratic
    (W.ambientVector_succ (0 : Fin (n + 1)))

/-- The first adjacent parameter loses the square of the one-step scaling
factor. -/
theorem adjacentParameter_zero_eq_mul_inv_square
    (W : c.HeadRescaleWitness 1) :
    W.bong.adjacentParameter 0 (by simp) =
      c.adjacentParameter 0 (by simp) *
        (uniformizerPowerUnit K (1 : Int))⁻¹ ^ 2 := by
  unfold adjacentParameter
  change W.bong.valueUnit (1 : Fin (n + 2)) / W.bong.valueUnit 0 =
    (c.valueUnit (1 : Fin (n + 2)) / c.valueUnit 0) *
      (uniformizerPowerUnit K (1 : Int))⁻¹ ^ 2
  rw [W.valueUnit_one_eq, W.valueUnit_zero_eq]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  exact (mul_assoc (c.valueUnit 1) ((c.valueUnit 0)⁻¹ : Kˣ)
    ((uniformizerPowerUnit K (1 : Int) ^ 2)⁻¹ : Kˣ)).symm

/-- Multiplication by the inverse square does not change the parameter
defect. -/
theorem parameterDefect_zero_eq
    (W : c.HeadRescaleWitness 1) :
    beliParameterDefect K (W.bong.adjacentParameter 0 (by simp)) =
      beliParameterDefect K (c.adjacentParameter 0 (by simp)) := by
  rw [W.adjacentParameter_zero_eq_mul_inv_square]
  unfold beliParameterDefect
  rw [← neg_mul, quadraticDefect_mul_square]

/-- Natural-valued version of the preceding defect identity. -/
theorem parameterDefectNat_zero_eq
    (W : c.HeadRescaleWitness 1) :
    beliParameterDefectNat K (W.bong.adjacentParameter 0 (by simp)) =
      beliParameterDefectNat K (c.adjacentParameter 0 (by simp)) := by
  unfold beliParameterDefectNat
  rw [W.parameterDefect_zero_eq]

end HeadRescaleWitness

/-- Rescaling the original second BONG coefficient by any integral power
can only decrease its binary spinor group. -/
theorem beliSpinorGroup_headSecondRescaledParameter_le_sharpHeadFactor_nat
    (b : BONG V q L (n + 3)) (k : Nat) :
    beliSpinorGroup K
        (unitSquareClass K (b.headSecondRescaledParameter k)) ≤
      b.lemma66SharpHeadFactor := by
  have hle : beliSpinorGroup K
        (unitSquareClass K
          (b.adjacentParameter 0 (by simp) *
            uniformizerPowerUnit K (k : Int) ^ 2)) ≤
      beliSpinorGroup K
        (unitSquareClass K (b.adjacentParameter 0 (by simp))) :=
    beliSpinorGroup_mul_integral_square_le_of_admissible
      (b.adjacentParameter_isBinaryParameterAdmissible 0 (by simp))
      (uniformizerPowerUnit K (k : Int))
      (uniformizerPowerUnit_nat_mem_integerRing k)
  apply le_trans (by
    simpa only [headSecondRescaledParameter] using hle)
  exact le_sup_left

/-- The zeroth value of an arbitrary head-rescaled tail is the ambient head
value times the corresponding rescaled second parameter. -/
theorem HeadRescaleWitness.value_zero_eq_headSecondRescaledParameter_mul_headValue
    (b : BONG V q L (n + 3)) {k : Nat}
    (W : b.tail.HeadRescaleWitness k) :
    W.bong.value 0 =
      (b.headSecondRescaledParameter k : K) * q.quadratic b.head := by
  let pik : K := ((uniformizerPowerUnit K (k : Int) : Kˣ) : K)
  have hcoe : (W.bong.ambientVector 0 : V) =
      pik • b.ambientVector 1 := by
    have h := congrArg Subtype.val W.ambientVector_zero
    change (W.bong.ambientVector 0 : V) =
      pik • (b.tail.ambientVector 0 : V) at h
    rw [b.coe_ambientVector_tail] at h
    exact h
  have htailValue : W.bong.value 0 = pik ^ 2 * b.value 1 := by
    calc
      W.bong.value 0 =
          (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
            (W.bong.ambientVector 0) :=
        (W.bong.quadratic_ambientVector 0).symm
      _ = q.quadratic (pik • b.ambientVector 1) := by
        change q.quadratic (W.bong.ambientVector 0 : V) = _
        rw [hcoe]
      _ = pik ^ 2 * b.value 1 := by
        rw [q.quadratic_smul, b.quadratic_ambientVector]
  rw [htailValue, ← b.value_zero_eq_quadratic_head]
  simp only [headSecondRescaledParameter, adjacentParameter,
    Units.val_mul, Units.val_div_eq_div_val, coe_valueUnit,
    Units.val_pow_eq_pow_val]
  have hindex :
      (⟨(0 : Fin (n + 3)).1 + 1, by simp⟩ : Fin (n + 3)) = 1 :=
    Fin.ext rfl
  rw [hindex]
  dsimp only [pik]
  field_simp [b.value_ne_zero 0,
    Units.ne_zero (uniformizerPowerUnit K (k : Int))]

/-- Passing from the once-rescaled to the twice-rescaled binary parameter
multiplies by the square of the uniformizer. -/
theorem headSecondRescaledParameter_two_eq_one_mul_uniformizer_square
    (b : BONG V q L (n + 3)) :
    b.headSecondRescaledParameter 2 =
      b.headSecondRescaledParameter 1 *
        uniformizerPowerUnit K (1 : Int) ^ 2 := by
  unfold headSecondRescaledParameter
  have hpower : uniformizerPowerUnit K (2 : Int) =
      uniformizerPowerUnit K (1 : Int) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    norm_num
  norm_num
  rw [hpower]
  simp only [pow_two]
  ac_rfl

/-- Square-coefficient promotion used in Beli's exceptional case.  If both
`z` and the error term have order strictly above the order of `a`, then the
integral coefficient in `z = a c² + error` is divisible by the
uniformizer.  Thus the same residue can be written with leading coefficient
`a π²`. -/
theorem mem_scaledIntegralSquareResidueSet_mul_uniformizer_square_of_deep
    (a z : K) (R t : Int)
    (ha : ord K a = (R : WithTop Int))
    (hz : ((R + 1 : Int) : WithTop Int) ≤ ord K z)
    (ht : R + 1 ≤ t)
    (hmem : z ∈ Lattice.scaledIntegralSquareResidueSet a
      (Lattice.powerIdeal (K := K) t)) :
    z ∈ Lattice.scaledIntegralSquareResidueSet
      (a * (((uniformizerPowerUnit K (1 : Int) : Kˣ) : K) ^ 2))
      (Lattice.powerIdeal (K := K) t) := by
  rcases hmem with ⟨c, hcError⟩
  by_cases hcZero : (c : K) = 0
  · refine ⟨0, ?_⟩
    have hzT : z ∈ Lattice.powerIdeal (K := K) t := by
      simpa [hcZero] using hcError
    simpa using hzT
  · have hzIdeal : z ∈ Lattice.powerIdeal (K := K) (R + 1) :=
      (Lattice.mem_powerIdeal_iff (K := K) (R + 1) z).2 hz
    have hideal : Lattice.powerIdeal (K := K) t ≤
        Lattice.powerIdeal (K := K) (R + 1) :=
      (Lattice.powerIdeal_le_iff (K := K) _ _).2 ht
    have hcErrorDeep : z - a * (c : K) ^ 2 ∈
        Lattice.powerIdeal (K := K) (R + 1) := hideal hcError
    have htermIdeal : a * (c : K) ^ 2 ∈
        Lattice.powerIdeal (K := K) (R + 1) := by
      have hsub :=
        (Lattice.powerIdeal (K := K) (R + 1)).sub_mem hzIdeal hcErrorDeep
      convert hsub using 1 <;> ring
    have htermOrder :=
      (Lattice.mem_powerIdeal_iff (K := K) (R + 1)
        (a * (c : K) ^ 2)).1 htermIdeal
    let cUnit : Kˣ := Units.mk0 (c : K) hcZero
    have hcOrder : ord K (c : K) =
        (ordUnit K cUnit : WithTop Int) := by
      simpa only [cUnit, Units.val_mk0] using (coe_ordUnit K cUnit).symm
    rw [ord_mul, ord_pow, ha, hcOrder] at htermOrder
    have hcOne : (1 : Int) ≤ ordUnit K cUnit := by
      norm_cast at htermOrder
      simp only [two_nsmul] at htermOrder
      omega
    let dK : K := (c : K) / uniformizer K
    have hdIntegral : dK ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤ ord K ((c : K) / uniformizer K)
      have hord : ord K (uniformizer K) ≤ ord K (c : K) := by
        rw [ord_uniformizer, hcOrder]
        exact_mod_cast hcOne
      rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv]
      obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp
        ((ord_eq_top_iff K).not.mpr (uniformizer_ne_zero K))
      rw [← hd] at hord ⊢
      have h := add_le_add_right hord (-(d : WithTop Int))
      simpa [add_assoc, add_comm] using h
    let d : IntegerRing K := ⟨dK, hdIntegral⟩
    have hcEq : (c : K) = uniformizer K * (d : K) := by
      dsimp only [d, dK]
      field_simp [uniformizer_ne_zero K]
    refine ⟨d, ?_⟩
    convert hcError using 1
    rw [hcEq]
    simp only [uniformizerPowerUnit, Units.val_pow_eq_pow_val,
      coe_uniformizerUnit, zpow_one]
    ring

/-- Intrinsic form of division by the ambient head value.  An absolute
projection congruence based at the `k`-times rescaled second value becomes
the corresponding relative congruence for `1-a²`. -/
theorem lemma65ProjectionFactorUnitIntrinsic_mem_scaledIntegralSquareResidueSet
    (b : BONG V q L (n + 3)) (x : V)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (k : Nat) (t : Int)
    (hresidue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection x) ∈
        Lattice.scaledIntegralSquareResidueSet
          ((b.headSecondRescaledParameter k : K) * q.quadratic b.head)
          (Lattice.powerIdeal (K := K) t)) :
    (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe : K) ∈
      Lattice.scaledIntegralSquareResidueSet
        (b.headSecondRescaledParameter k : K)
        (Lattice.powerIdeal (K := K) (t - b.order 0)) := by
  rcases hresidue with ⟨c, hcError⟩
  refine ⟨c, (Lattice.mem_powerIdeal_iff
    (K := K) (t - b.order 0) _).2 ?_⟩
  let p : Kˣ :=
    Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe
  let a : Kˣ := b.headSecondRescaledParameter k
  let qy : K :=
    (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (b.lemma65Projection x)
  have hprojection : qy = (p : K) * q.quadratic b.head := by
    dsimp only [qy, p]
    simpa only [Lemma65Setup.coe_lemma65ProjectionFactorUnitIntrinsic] using
      Lemma65Setup.quadratic_lemma65Projection_eq_one_sub_sq_mul_intrinsic
        b x heq
  have hidentity :
      qy - ((a : K) * q.quadratic b.head) * (c : K) ^ 2 =
        q.quadratic b.head * ((p : K) - (a : K) * (c : K) ^ 2) := by
    rw [hprojection]
    ring
  have herrorOrder : (t : WithTop Int) ≤
      ord K (qy - ((a : K) * q.quadratic b.head) * (c : K) ^ 2) :=
    (Lattice.mem_powerIdeal_iff (K := K) t _).1 (by
      simpa only [qy, a] using hcError)
  rw [hidentity, ord_mul] at herrorOrder
  have hheadOrder : ord K (q.quadratic b.head) =
      (b.order 0 : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  rw [hheadOrder] at herrorOrder
  change ((t - b.order 0 : Int) : WithTop Int) ≤
    ord K ((p : K) - (a : K) * (c : K) ^ 2)
  by_cases hzero : (p : K) - (a : K) * (c : K) ^ 2 = 0
  · rw [hzero, ord_zero]
    exact le_top
  · let error : Kˣ :=
      Units.mk0 ((p : K) - (a : K) * (c : K) ^ 2) hzero
    have herrorValue :
        ord K ((p : K) - (a : K) * (c : K) ^ 2) =
          (ordUnit K error : WithTop Int) := by
      simpa only [error, Units.val_mk0] using (coe_ordUnit K error).symm
    rw [herrorValue] at herrorOrder ⊢
    norm_cast at herrorOrder ⊢
    omega

/-- Intrinsic high-range auxiliary-group bound from the universal absolute
projection congruence.  Unlike the setup-based version, this also applies
to the exceptional branch where only the once-rescaled tail exists. -/
theorem lemma65ProjectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_residue
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (k : Nat)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe))
    (hresidue :
      (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          (b.lemma65Projection x) ∈
        Lattice.scaledIntegralSquareResidueSet
          ((b.headSecondRescaledParameter k : K) * q.quadratic b.head)
          (Lattice.powerIdeal (K := K)
            (b.order 0 + 2 * (ramificationIndex K : Int) +
              (b.lemma66SharpDepth : Int)))) :
    beliAuxiliarySpinorGroup K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic
          b x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  let a : Kˣ := b.headSecondRescaledParameter k
  let p : Kˣ :=
    Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe
  let t : Int := 2 * (ramificationIndex K : Int) +
    (b.lemma66SharpDepth : Int)
  have halphaPos : 0 < b.lemma66SharpDepth := by
    have h02 : b.order 0 < b.order 2 := hB.1 0 (by simp)
    unfold lemma66SharpDepth
    omega
  have ht : 2 * (ramificationIndex K : Int) < t := by
    dsimp only [t]
    have halphaPosInt : (0 : Int) < (b.lemma66SharpDepth : Int) := by
      exact_mod_cast halphaPos
    omega
  have hrelativeResidue : (p : K) ∈
      Lattice.scaledIntegralSquareResidueSet (a : K)
        (Lattice.powerIdeal (K := K) t) := by
    have h :=
      lemma65ProjectionFactorUnitIntrinsic_mem_scaledIntegralSquareResidueSet
        b x heq hfactorNe k
          (b.order 0 + 2 * (ramificationIndex K : Int) +
            (b.lemma66SharpDepth : Int)) hresidue
    have hexponent :
        b.order 0 + 2 * (ramificationIndex K : Int) +
              (b.lemma66SharpDepth : Int) - b.order 0 = t := by
      dsimp only [t]
      omega
    rw [hexponent] at h
    simpa only [p, a] using h
  have ha : IsBinaryParameterAdmissible a := by
    simpa only [a] using
      b.headSecondRescaledParameter_isBinaryParameterAdmissible k
  have hp : IsBinaryParameterAdmissible p := by
    simpa only [p] using
      Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic_isBinaryParameterAdmissible
        b x hx hfactorNe
  have hle :=
    Lemma65Setup.beliAuxiliarySpinorGroup_le_of_mem_scaledIntegralSquareResidueSet
      (K := K) a p t ha hp ht (by simpa only [p] using hpLow)
        hrelativeResidue
  have hdepth : Int.toNat
      (t - 2 * (ramificationIndex K : Int)) =
        b.lemma66SharpDepth := by
    dsimp only [t]
    simp
  rw [hdepth] at hle
  apply hle.trans
  apply sup_le
  · exact le_sup_right
  · exact b.beliSpinorGroup_headSecondRescaledParameter_le_sharpHeadFactor_nat k

/-- Common final step for every exceptional value-set subcase.  Lemma 6.2
is applied to the once-rescaled tail; depth of the exceptional projection
then promotes its square coefficient once more, producing the twice-
rescaled parameter required by the high-range auxiliary group. -/
theorem exceptionalProjectionFactorAuxiliarySpinorGroup_le_of_tailValueSet
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe))
    (t : Int)
    (htarget : b.order 0 + 2 * (ramificationIndex K : Int) +
        (b.lemma66SharpDepth : Int) ≤ t)
    (hvalues : Lattice.quadraticValueSet
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        (Lemma65Setup.exceptionalProjectionWitnessIntrinsic
          b hB x hx heq hexceptional.1 hexceptional.2.1
            hexceptional.2.2).tailRescaleOne.lattice ⊆
      Lattice.scaledIntegralSquareResidueSet
        ((Lemma65Setup.exceptionalProjectionWitnessIntrinsic
          b hB x hx heq hexceptional.1 hexceptional.2.1
            hexceptional.2.2).tailRescaleOne.bong.value 0)
        (Lattice.powerIdeal (K := K) t)) :
    beliAuxiliarySpinorGroup K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic
          b x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  let E := Lemma65Setup.exceptionalProjectionWitnessIntrinsic
    b hB x hx heq hexceptional.1 hexceptional.2.1 hexceptional.2.2
  let W := E.tailRescaleOne
  let qy : K :=
    (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (b.lemma65Projection x)
  have hqValue : qy ∈ Lattice.quadraticValueSet
      (q.orthogonalSpace b.head b.head_isAnisotropic) W.lattice := by
    rw [Lattice.mem_quadraticValueSet_iff]
    exact ⟨b.lemma65Projection x, E.projection_mem, rfl⟩
  have hbase : qy ∈ Lattice.scaledIntegralSquareResidueSet
      (W.bong.value 0) (Lattice.powerIdeal (K := K) t) := by
    exact hvalues hqValue
  let target : Int := b.order 0 + 2 * (ramificationIndex K : Int) +
    (b.lemma66SharpDepth : Int)
  have hideal : Lattice.powerIdeal (K := K) t ≤
      Lattice.powerIdeal (K := K) target :=
    (Lattice.powerIdeal_le_iff (K := K) _ _).2 (by
      simpa only [target] using htarget)
  have hbaseTarget : qy ∈ Lattice.scaledIntegralSquareResidueSet
      (W.bong.value 0) (Lattice.powerIdeal (K := K) target) :=
    Lattice.scaledIntegralSquareResidueSet_mono
      (W.bong.value 0) hideal hbase
  let R : Int := b.order 0 + 2 * (ramificationIndex K : Int)
  have htailOrder : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have hWOrder : W.bong.order 0 = R := by
    dsimp only [W]
    rw [E.tailRescaleOne.order_zero_eq_add_two, htailOrder]
    dsimp only [R]
    have hgap := hexceptional.1
    unfold lemma62Gap at hgap
    omega
  have hWValueOrder : ord K (W.bong.value 0) = (R : WithTop Int) := by
    rw [← W.bong.coe_order, hWOrder]
  have hqDeep : ((R + 1 : Int) : WithTop Int) ≤ ord K qy := by
    have h := b.exceptional_projection_order_lower
      hB x hx heq hexceptional
    simpa only [R, qy] using h
  have hdepthPos : 0 < b.lemma66SharpDepth := by
    have h02 : b.order 0 < b.order 2 := hB.1 0 (by simp)
    unfold lemma66SharpDepth
    omega
  have htargetDeep : R + 1 ≤ target := by
    dsimp only [R, target]
    have hdepthPosInt : (0 : Int) < (b.lemma66SharpDepth : Int) := by
      exact_mod_cast hdepthPos
    omega
  have hpromoted :=
    mem_scaledIntegralSquareResidueSet_mul_uniformizer_square_of_deep
      (W.bong.value 0) qy R target hWValueOrder hqDeep htargetDeep
        hbaseTarget
  have hWValue :=
    W.value_zero_eq_headSecondRescaledParameter_mul_headValue b
  have hparameter :=
    b.headSecondRescaledParameter_two_eq_one_mul_uniformizer_square
  have hbaseEq : W.bong.value 0 *
        (((uniformizerPowerUnit K (1 : Int) : Kˣ) : K) ^ 2) =
      (b.headSecondRescaledParameter 2 : K) * q.quadratic b.head := by
    rw [hWValue, hparameter]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hbaseEq] at hpromoted
  exact
    b.lemma65ProjectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor_of_residue
      hB x hx heq hfactorNe 2 hpLow (by
        simpa only [target, qy] using hpromoted)

/-- Complete auxiliary-group estimate in the exceptional residue-two
branch.  The once-rescaled tail is split exactly according to Lemma
6.2(a), (b), and (c); the finite/infinite defect alternatives are
exhaustive. -/
theorem exceptionalProjectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤)
    (hfactorNe :
      1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 ≠ 0)
    (hpLow : 2 * (ramificationIndex K : Int) <
      ordUnit K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic b x hfactorNe)) :
    beliAuxiliarySpinorGroup K
        (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic
          b x hfactorNe) hpLow ≤
      b.lemma66SharpHeadFactor := by
  let E := Lemma65Setup.exceptionalProjectionWitnessIntrinsic
    b hB x hx heq hexceptional.1 hexceptional.2.1 hexceptional.2.2
  let W := E.tailRescaleOne
  let wInv := W.inverseWitness_of_one
  have hw : W.bong.HasPropertyBOrInverse wInv := by
    exact Or.inr hB.tail_for_lemma62
  have htailZero : b.tail.order (0 : Fin (n + 2)) = b.order 1 := by
    rw [b.order_tail]
    congr 1
  have htailOne : b.tail.order (1 : Fin (n + 2)) = b.order 2 := by
    rw [b.order_tail]
    congr 1
  have hWzero : W.bong.order 0 = b.order 1 + 2 := by
    calc
      W.bong.order 0 = b.tail.order 0 + 2 := by
        simpa only [W] using E.tailRescaleOne.order_zero_eq_add_two
      _ = b.order 1 + 2 := by rw [htailZero]
  have hWone : W.bong.order 1 = b.order 2 := by
    calc
      W.bong.order 1 = b.tail.order 1 := by
        simpa only [W] using E.tailRescaleOne.order_one_eq
      _ = b.order 2 := htailOne
  have hWgap : W.bong.lemma62Gap = b.order 2 - b.order 1 - 2 := by
    unfold lemma62Gap
    rw [hWzero, hWone]
    omega
  have htailParameter : b.tail.adjacentParameter 0 (by simp) =
      b.adjacentParameter 1 (by simp) := by
    unfold adjacentParameter
    rw [b.valueUnit_tail, b.valueUnit_tail]
    congr 2 <;> apply Fin.ext <;> rfl
  have hdefectEq : beliParameterDefect K
        (W.bong.adjacentParameter 0 (by simp)) =
      beliParameterDefect K (b.adjacentParameter 1 (by simp)) := by
    rw [W.parameterDefect_zero_eq, htailParameter]
  have hdefectNatEq : beliParameterDefectNat K
        (W.bong.adjacentParameter 0 (by simp)) =
      beliParameterDefectNat K (b.adjacentParameter 1 (by simp)) := by
    unfold beliParameterDefectNat
    rw [hdefectEq]
  let a : Kˣ := b.adjacentParameter 1 (by simp)
  have ha : IsBinaryParameterAdmissible a := by
    simpa only [a] using
      b.adjacentParameter_isBinaryParameterAdmissible 1 (by simp)
  have haOrder : ordUnit K a = W.bong.lemma62Gap + 2 := by
    have hambient : ordUnit K a = b.order 2 - b.order 1 := by
      dsimp only [a]
      convert b.ordUnit_adjacentParameter (1 : Fin (n + 3)) (by simp)
        using 1 <;> congr 1
    rw [hambient, hWgap]
    omega
  by_cases hTlarge : 2 * (ramificationIndex K : Int) < W.bong.lemma62Gap
  · have htailOrder : W.bong.order 0 ≤ W.bong.order 1 := by
      unfold lemma62Gap at hTlarge
      omega
    have hvalues := W.bong.beliLemma62_ii_a wInv hw htailOrder
    have hdepthCast :=
      Lemma65Setup.lemma66SharpDepth_cast (K := K) b hB
    have htarget : b.order 0 + 2 * (ramificationIndex K : Int) +
          (b.lemma66SharpDepth : Int) ≤ W.bong.order 1 := by
      have hfirstGap := hexceptional.1
      unfold lemma62Gap at hfirstGap
      rw [hWgap] at hTlarge
      rw [hWone, hdepthCast]
      omega
    exact
      b.exceptionalProjectionFactorAuxiliarySpinorGroup_le_of_tailValueSet
        hB x hx heq hexceptional hfactorNe hpLow (W.bong.order 1) htarget
          (by simpa only [E, W] using hvalues)
  · have hTupper : W.bong.lemma62Gap ≤
        2 * (ramificationIndex K : Int) := by omega
    rcases Int.even_or_odd W.bong.lemma62Gap with hTeven | hTodd
    · let d : Nat := beliParameterDefectNat K a
      by_cases hfinite : beliParameterDefect K a ≠ ⊤
      · by_cases hlow : 2 + 2 * (d : Int) ≤
            2 * (ramificationIndex K : Int) - W.bong.lemma62Gap
        · have hdefectCoe : beliParameterDefect K a = (d : ℕ∞) := by
            dsimp only [d, beliParameterDefectNat]
            exact (ENat.coe_toNat hfinite).symm
          have hcutCast := W.bong.lemma62DefectCutoff_cast hTeven hTupper
          have hdLeCutInt : (d : Int) ≤
              (W.bong.lemma62DefectCutoff : Int) := by
            rw [hcutCast]
            rcases hTeven with ⟨r, hr⟩
            omega
          have hdLeCutNat : d ≤ W.bong.lemma62DefectCutoff := by
            exact_mod_cast hdLeCutInt
          have htailDefect : beliParameterDefect K
                (W.bong.adjacentParameter 0 (by simp)) ≤
              (W.bong.lemma62DefectCutoff : ℕ∞) := by
            rw [hdefectEq]
            rw [show beliParameterDefect K
                (b.adjacentParameter 1 (by simp)) = (d : ℕ∞) by
              simpa only [a] using hdefectCoe]
            exact_mod_cast hdLeCutNat
          have hvalues := W.bong.beliLemma62_ii_b
            wInv hw hTeven hTupper htailDefect
          have haUpper : ordUnit K a ≤
              2 * (ramificationIndex K : Int) := by
            rw [haOrder]
            have hdNonneg : (0 : Int) ≤ (d : Int) := by positivity
            omega
          have hcutNonneg : 0 ≤
              2 * (ramificationIndex K : Int) - ordUnit K a := by omega
          have hcaseCutCast :
              (beliSpinorCaseIIILowerCutoff K a : Int) =
                2 * (ramificationIndex K : Int) - ordUnit K a := by
            unfold beliSpinorCaseIIILowerCutoff
            rw [Int.toNat_of_nonneg hcutNonneg]
          have hcaseDefectNat : 2 * d ≤
              beliSpinorCaseIIILowerCutoff K a := by
            have hInt : 2 * (d : Int) ≤
                (beliSpinorCaseIIILowerCutoff K a : Int) := by
              rw [hcaseCutCast, haOrder]
              omega
            exact_mod_cast hInt
          have hcaseDefect : 2 * beliParameterDefect K a ≤
              (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
            rw [hdefectCoe]
            exact_mod_cast hcaseDefectNat
          have hgroup := beliSpinorGroupRepresentative_eq_norm_of_low_defect
            (K := K) a ha haUpper hcaseDefect hfinite
          have hproperNumerical :=
            Lemma65Setup.two_e_lt_lemma66SharpDepth_add_tailParameterDefectNat
              (K := K) b hB hproper (by simpa only [a] using hgroup)
                (by simpa only [a] using hfinite)
          have hproperInt : 2 * (ramificationIndex K : Int) <
              (b.lemma66SharpDepth : Int) + (d : Int) := by
            exact_mod_cast (show 2 * ramificationIndex K <
              b.lemma66SharpDepth + d by
                simpa only [a, d] using hproperNumerical)
          have hdepthCast :=
            Lemma65Setup.lemma66SharpDepth_cast (K := K) b hB
          have htarget : b.order 0 + 2 * (ramificationIndex K : Int) +
                (b.lemma66SharpDepth : Int) ≤
              W.bong.lemma62LowExponent := by
            unfold lemma62LowExponent lemma62DefectNat
            rw [hWone, hdefectNatEq]
            change b.order 0 + 2 * (ramificationIndex K : Int) +
                (b.lemma66SharpDepth : Int) ≤ b.order 2 + (d : Int)
            rw [hdepthCast] at hproperInt ⊢
            omega
          exact
            b.exceptionalProjectionFactorAuxiliarySpinorGroup_le_of_tailValueSet
              hB x hx heq hexceptional hfactorNe hpLow
                W.bong.lemma62LowExponent htarget
                  (by simpa only [E, W] using hvalues)
        · have hdefectCoe : beliParameterDefect K a = (d : ℕ∞) := by
            dsimp only [d, beliParameterDefectNat]
            exact (ENat.coe_toNat hfinite).symm
          have hcutCast := W.bong.lemma62DefectCutoff_cast hTeven hTupper
          have hcutLeInt :
              (W.bong.lemma62DefectCutoff : Int) ≤ (d : Int) := by
            rw [hcutCast]
            rcases hTeven with ⟨r, hr⟩
            omega
          have hcutLeNat : W.bong.lemma62DefectCutoff ≤ d := by
            exact_mod_cast hcutLeInt
          have htailHigh :
              (W.bong.lemma62DefectCutoff : ℕ∞) ≤
                beliParameterDefect K
                  (W.bong.adjacentParameter 0 (by simp)) := by
            rw [hdefectEq]
            rw [show beliParameterDefect K
                (b.adjacentParameter 1 (by simp)) = (d : ℕ∞) by
              simpa only [a] using hdefectCoe]
            exact_mod_cast hcutLeNat
          have hvalues := W.bong.beliLemma62_ii_c
            wInv hw hTeven hTupper htailHigh
          have hdepthCast :=
            Lemma65Setup.lemma66SharpDepth_cast (K := K) b hB
          have htarget : b.order 0 + 2 * (ramificationIndex K : Int) +
                (b.lemma66SharpDepth : Int) ≤
              W.bong.lemma62HighExponent := by
            unfold lemma62HighExponent
            rw [hWzero, hWone, hdepthCast]
            have hgap := hexceptional.1
            unfold lemma62Gap at hgap
            rw [hWgap] at hTeven
            rcases hTeven with ⟨r, hr⟩
            omega
          exact
            b.exceptionalProjectionFactorAuxiliarySpinorGroup_le_of_tailValueSet
              hB x hx heq hexceptional hfactorNe hpLow
                W.bong.lemma62HighExponent htarget
                  (by simpa only [E, W] using hvalues)
      · have htop : beliParameterDefect K a = ⊤ := not_ne_iff.mp hfinite
        have htailHigh :
            (W.bong.lemma62DefectCutoff : ℕ∞) ≤
              beliParameterDefect K
                (W.bong.adjacentParameter 0 (by simp)) := by
          rw [hdefectEq]
          rw [show beliParameterDefect K
              (b.adjacentParameter 1 (by simp)) = ⊤ by
            simpa only [a] using htop]
          exact le_top
        have hvalues := W.bong.beliLemma62_ii_c
          wInv hw hTeven hTupper htailHigh
        have hdepthCast :=
          Lemma65Setup.lemma66SharpDepth_cast (K := K) b hB
        have htarget : b.order 0 + 2 * (ramificationIndex K : Int) +
              (b.lemma66SharpDepth : Int) ≤
            W.bong.lemma62HighExponent := by
          unfold lemma62HighExponent
          rw [hWzero, hWone, hdepthCast]
          have hgap := hexceptional.1
          unfold lemma62Gap at hgap
          rw [hWgap] at hTeven
          rcases hTeven with ⟨r, hr⟩
          omega
        exact
          b.exceptionalProjectionFactorAuxiliarySpinorGroup_le_of_tailValueSet
            hB x hx heq hexceptional hfactorNe hpLow
              W.bong.lemma62HighExponent htarget
                (by simpa only [E, W] using hvalues)
    · have hTnonneg : 0 ≤ W.bong.lemma62Gap := by
        have hWA := W.bong.adjacentParameter_isBinaryParameterAdmissible
          0 (by simp)
        have hnonneg := hWA.ordUnit_nonneg_of_odd (by
          rw [W.bong.ordUnit_adjacentParameter_zero]
          exact hTodd)
        rw [W.bong.ordUnit_adjacentParameter_zero] at hnonneg
        exact hnonneg
      have htailOrder : W.bong.order 0 ≤ W.bong.order 1 := by
        unfold lemma62Gap at hTnonneg
        omega
      have hvalues := W.bong.beliLemma62_ii_a wInv hw htailOrder
      have haOdd : Odd (ordUnit K a) := by
        rw [haOrder]
        rcases hTodd with ⟨r, hr⟩
        refine ⟨r + 1, ?_⟩
        omega
      have haUpper : ordUnit K a ≤
          2 * (ramificationIndex K : Int) + 1 := by
        rw [haOrder]
        rcases hTodd with ⟨r, hr⟩
        omega
      have hgroup := beliSpinorGroupRepresentative_eq_norm_of_odd_trigger
        (K := K) a ha haOdd haUpper
      have hdefectZero : beliParameterDefect K a = 0 := by
        unfold beliParameterDefect
        exact quadraticDefect_eq_zero_of_odd_ordUnit (-a)
          (by simpa using haOdd)
      have hfinite : beliParameterDefect K a ≠ ⊤ := by
        rw [hdefectZero]
        exact ENat.zero_ne_top
      have hproperNumerical :=
        Lemma65Setup.two_e_lt_lemma66SharpDepth_add_tailParameterDefectNat
          (K := K) b hB hproper (by simpa only [a] using hgroup)
            (by simpa only [a] using hfinite)
      have hdefectNatZero : beliParameterDefectNat K a = 0 := by
        unfold beliParameterDefectNat
        rw [hdefectZero]
        simp
      have hdepthLarge : 2 * ramificationIndex K <
          b.lemma66SharpDepth := by
        simpa only [a, hdefectNatZero, add_zero] using hproperNumerical
      have hdepthCast :=
        Lemma65Setup.lemma66SharpDepth_cast (K := K) b hB
      have hdepthLargeInt : 2 * (ramificationIndex K : Int) <
          (b.lemma66SharpDepth : Int) := by
        exact_mod_cast hdepthLarge
      have htarget : b.order 0 + 2 * (ramificationIndex K : Int) +
            (b.lemma66SharpDepth : Int) ≤ W.bong.order 1 := by
        rw [hdepthCast] at hdepthLargeInt
        rw [hWone, hdepthCast]
        omega
      exact
        b.exceptionalProjectionFactorAuxiliarySpinorGroup_le_of_tailValueSet
          hB x hx heq hexceptional hfactorNe hpLow (W.bong.order 1) htarget
            (by simpa only [E, W] using hvalues)

/-- Spinor-complete exceptional branch of Beli (2003), Lemma 6.6.  The
critical sign is supplied by the once-rescaled exceptional tail.  A nonzero
projection factor has order strictly above `2e`, so the preceding exhaustive
Lemma 6.2 analysis controls its auxiliary spinor group; the zero endpoints
are handled directly. -/
theorem exists_exceptionalRotation_apply_head_mem_lemma66SharpHeadFactor
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hexceptional : b.Lemma65Exceptional)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧
        f.spinorNorm ∈ b.lemma66SharpHeadFactor := by
  rcases b.exceptional_head_sub_or_add_order_eq
      hB x hx heq hexceptional with hsub | hadd
  · let haniso := lemma65Difference_isAnisotropic_of_order_eq b x hsub
    have hintegral : Lattice.IsIntegralReflection (L := L) haniso :=
      Lemma65Setup.exceptional_reflection_integral_proved
        b hB x hx heq hexceptional hsub
    let w : Lemma65DifferenceReflectionWitness b x :=
      ⟨haniso, hintegral⟩
    refine ⟨b.differenceTailRotation x w,
      b.differenceTailRotation_apply_head x w heq, ?_⟩
    by_cases hfactorZero :
        1 - (q.bilin b.head x / q.quadratic b.head) ^ 2 = 0
    · exact
        b.differenceTailRotation_spinorNorm_mem_of_projectionFactor_eq_zero
          x heq w hfactorZero
    · have hprojectionLower :=
        b.exceptional_projection_order_lower hB x hx heq hexceptional
      have hprojectionOrder :=
        Lemma65Setup.ord_quadratic_lemma65Projection_eq_head_add_factorIntrinsic
          b x heq hfactorZero
      have hpLow : 2 * (ramificationIndex K : Int) <
          ordUnit K
            (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic
              b x hfactorZero) := by
        rw [hprojectionOrder] at hprojectionLower
        norm_cast at hprojectionLower
        omega
      have haux :=
        b.exceptionalProjectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor
          hB x hx heq hexceptional hproper hfactorZero hpLow
      exact
        b.differenceTailRotation_spinorNorm_mem_of_projectionFactorAuxiliaryIntrinsic_le
          x hx heq w hfactorZero hpLow hsub haux
  · have hxneg : -x ∈ L := L.neg_mem hx
    have heqneg : q.quadratic (-x) = q.quadratic b.head := by
      rw [q.quadratic_neg, heq]
    have hsumOrder : ord K (q.quadratic (b.head - (-x))) =
        ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
          WithTop Int) := by
      simpa only [sub_neg_eq_add] using hadd
    let hsumNeg :=
      lemma65Difference_isAnisotropic_of_order_eq b (-x) hsumOrder
    have hintegralNeg : Lattice.IsIntegralReflection (L := L) hsumNeg :=
      Lemma65Setup.exceptional_reflection_integral_proved
        b hB (-x) hxneg heqneg hexceptional hsumOrder
    have hsum : q.IsAnisotropic (b.head + x) := by
      simpa only [sub_neg_eq_add] using hsumNeg
    have hintegral : Lattice.IsIntegralReflection (L := L) hsum := by
      simpa only [sub_neg_eq_add] using hintegralNeg
    refine ⟨b.sumHeadRotation x hsum hintegral,
      b.sumHeadRotation_apply_head x hsum hintegral heq, ?_⟩
    by_cases hfactorZero :
        1 - (q.bilin b.head (-x) / q.quadratic b.head) ^ 2 = 0
    · exact
        b.sumHeadRotation_spinorNorm_mem_of_projectionFactorNeg_eq_zero
          x heq hsum hintegral hfactorZero
    · have hprojectionLower :=
        b.exceptional_projection_order_lower
          hB (-x) hxneg heqneg hexceptional
      have hprojectionOrder :=
        Lemma65Setup.ord_quadratic_lemma65Projection_eq_head_add_factorIntrinsic
          b (-x) heqneg hfactorZero
      have hpLow : 2 * (ramificationIndex K : Int) <
          ordUnit K
            (Lemma65Setup.lemma65ProjectionFactorUnitIntrinsic
              b (-x) hfactorZero) := by
        rw [hprojectionOrder] at hprojectionLower
        norm_cast at hprojectionLower
        omega
      have haux :=
        b.exceptionalProjectionFactorAuxiliarySpinorGroup_le_sharpHeadFactor
          hB (-x) hxneg heqneg hexceptional hproper hfactorZero hpLow
      exact
        b.sumHeadRotation_spinorNorm_mem_of_projectionFactorNegAuxiliaryIntrinsic_le
          x hx heq hsum hintegral hfactorZero hpLow hadd haux

/-- Geometric part of Beli (2003), Lemma 6.6 for a nonhyperbolic first
binary block, with no externally supplied least-rescaling setup.  The
ordinary branch uses the canonical setup; the exceptional branch uses the
paper's once-rescaled tail. -/
theorem exists_rotation_apply_head_of_not_firstBinary_hyperbolic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hnotHyperbolic : ¬b.FirstBinaryIsHyperbolic)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    ∃ f : Lattice.IntegralRotation q L, f.apply b.head = x := by
  by_cases hexceptional : b.Lemma65Exceptional
  · exact b.exists_exceptionalRotation_apply_head
      hB x hx heq hexceptional
  · let S := b.lemma65Setup_of_not_exceptional
      hB hnotHyperbolic hexceptional
    exact S.exists_rotation_apply_head_of_setup hB x hx heq

/-- Geometric transport in Beli (2003), Lemma 6.6 when the first binary
prefix is hyperbolic.  The explicit Eichler transformation and hyperbolic
diagonal map are both proper, so no determinant-correcting reflection is
introduced. -/
theorem exists_rotation_apply_head_mem_lemma66SharpHeadFactor_of_firstBinary_hyperbolic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hH : b.FirstBinaryIsHyperbolic)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧
        f.spinorNorm ∈ b.lemma66SharpHeadFactor := by
  rcases b.hasTwoBlockSplit_two_of_firstBinary_hyperbolic hB hH with ⟨T⟩
  let P := b.prefixWitness 2 (by omega)
  have hPH : Lattice.ContainsScaledHyperbolicPlane
      (q.restrict P.carrier P.nondegenerate) P.lattice
      ((P.bong.order 0 + P.bong.order 1) / 2) := by
    have hscale : (P.bong.order 0 + P.bong.order 1) / 2 =
        (b.order 0 + b.order 1) / 2 := by
      rw [P.order_eq, P.order_eq]
      simp [BONG.SegmentWitness.sourceIndex]
    apply BONG.containsScaledHyperbolicPlane_restrict P.quadraticSublattice
    rw [hscale]
    exact hH
  let eP := Classical.choice
    (P.bong.isIsometric_hyperbolicPlane_of_contains_natural hPH)
  let eTP := T.leftPrefixWitness.latticeIsometry P
  let eLeft := eTP.trans eP
  let a : Kˣ := uniformizerPowerUnit K
    ((P.bong.order 0 + P.bong.order 1) / 2)
  let identify := T.toProductLatticeIsometry.symm.trans
    (eLeft.orthogonalProductBasic
      (Lattice.Isometry.refl
        (q.restrict T.right.carrier T.right.nondegenerate)
        T.right.lattice))
  let xb := identify.toLinearEquiv b.head
  let xx := identify.toLinearEquiv x
  have hxbT : T.toProductLatticeIsometry.symm.toLinearEquiv b.head =
      (T.left.bong.head, 0) := by
    rw [← T.coe_left_head_eq_head_of_cut_two]
    exact T.toProductLatticeIsometry_symm_apply_left T.left.bong.head
  have hxbSecond : xb.2 = 0 := by
    change (identify.toLinearEquiv b.head).2 = 0
    change (eLeft.toLinearEquiv
      (T.toProductLatticeIsometry.symm.toLinearEquiv b.head).1,
      (T.toProductLatticeIsometry.symm.toLinearEquiv b.head).2).2 = 0
    rw [hxbT]
  have hxxMem : xx ∈ Lattice.product
      (Lattice.hyperbolicPlaneLattice (K := K)) T.right.lattice := by
    exact (identify.map_mem x).1 hx
  have hxxRight : xx.2 ∈ T.right.lattice :=
    (Lattice.mem_product_iff.mp hxxMem).2
  have hgap := b.firstBinary_orderGap_eq_neg_two_mul_ramificationIndex hH
  have hPzero : P.bong.order 0 = b.order 0 := by
    rw [P.order_eq]
    congr 1
  have hPone : P.bong.order 1 = b.order 1 := by
    rw [P.order_eq]
    congr 1
  have hbase : ord K (2 * (a : K)) = (b.order 0 : WithTop Int) := by
    rw [ord_mul, ← ramificationIndex_spec, ← coe_ordUnit K a]
    simp only [a, ordUnit_uniformizerPowerUnit]
    change ((ramificationIndex K : Int) : WithTop Int) +
        ((P.bong.order 0 + P.bong.order 1) / 2 : Int) =
      (b.order 0 : WithTop Int)
    norm_cast
    rw [hPzero, hPone]
    omega
  have hheadOrder : ord K (q.quadratic b.head) =
      (b.order 0 : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  have hxxTotal : ord K
      (((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        (q.restrict T.right.carrier T.right.nondegenerate)).quadratic xx) =
      (b.order 0 : WithTop Int) := by
    rw [identify.map_quadratic, heq, hheadOrder]
  let rightZero : Fin (n + 3 - 2) := ⟨0, by omega⟩
  have hrightNorm : Lattice.normIdeal
      (q.restrict T.right.carrier T.right.nondegenerate) T.right.lattice =
      Lattice.powerIdeal (T.right.bong.order rightZero) :=
    T.right.bong.normIdeal_eq_powerIdeal_order_zero
  have hrightQmem := Lattice.quadratic_mem_normIdeal_of_mem
    (q.restrict T.right.carrier T.right.nondegenerate)
    T.right.lattice hxxRight
  rw [hrightNorm] at hrightQmem
  have hrightLowerLocal :=
    (Lattice.mem_powerIdeal_iff (K := K) (T.right.bong.order rightZero) _).1
      hrightQmem
  have hrightOrder : T.right.bong.order rightZero = b.order 2 := by
    rw [T.right.order_eq]
    congr 1
  rw [hrightOrder] at hrightLowerLocal
  have hzeroThird : b.order 0 < b.order 2 := hB.1 0 (by simp)
  have htotal_lt_right :
      ord K
          (((QuadraticSpace.hyperbolicPlane a).orthogonalSum
            (q.restrict T.right.carrier T.right.nondegenerate)).quadratic xx) <
        ord K ((q.restrict T.right.carrier T.right.nondegenerate).quadratic xx.2) := by
    rw [hxxTotal]
    exact (WithTop.coe_lt_coe.mpr hzeroThird).trans_le hrightLowerLocal
  have hxxLeftOrder :
      ord K ((QuadraticSpace.hyperbolicPlane a).quadratic xx.1) =
        (b.order 0 : WithTop Int) := by
    have hdecomp :
        (QuadraticSpace.hyperbolicPlane a).quadratic xx.1 =
          (((QuadraticSpace.hyperbolicPlane a).orthogonalSum
            (q.restrict T.right.carrier T.right.nondegenerate)).quadratic xx) -
          (q.restrict T.right.carrier T.right.nondegenerate).quadratic xx.2 := by
      rw [QuadraticSpace.orthogonalSum_quadratic_apply]
      ring
    rw [hdecomp, (ord K).map_sub_eq_of_lt_left htotal_lt_right, hxxTotal]
  have hxxLeftMem : xx.1 ∈ Lattice.hyperbolicPlaneLattice (K := K) :=
    (Lattice.mem_product_iff.mp hxxMem).1
  have hxxUnits := hyperbolic_coordinates_are_units a (b.order 0)
    xx.1 hbase hxxLeftMem hxxLeftOrder
  let beta : K := xx.1 1
  have hbetaUnit : IsValuationUnit K beta := hxxUnits.2
  have hbetaNe : beta ≠ 0 := by
    intro hzero
    have htop : ord K beta = ⊤ := by rw [hzero, ord_zero]
    unfold IsValuationUnit at hbetaUnit
    rw [htop] at hbetaUnit
    exact WithTop.top_ne_coe hbetaUnit
  let betaU : Kˣ := Units.mk0 beta hbetaNe
  have hbetaUOrder : ordUnit K betaU = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K betaU).1 (by
      simpa only [betaU, Units.val_mk0] using hbetaUnit)
  have hscaleExponent :
      (P.bong.order 0 + P.bong.order 1) / 2 =
        b.order 0 - (ramificationIndex K : Int) := by
    rw [hPzero, hPone]
    omega
  have haOrder : ordUnit K a =
      b.order 0 - (ramificationIndex K : Int) := by
    simp only [a, ordUnit_uniformizerPowerUnit, hscaleExponent]
  have hrightNormB : Lattice.normIdeal
      (q.restrict T.right.carrier T.right.nondegenerate) T.right.lattice =
      Lattice.powerIdeal (b.order 2) := by
    rw [hrightNorm, hrightOrder]
  have hscaleLe : Lattice.scaleIdeal
      (q.restrict T.right.carrier T.right.nondegenerate) T.right.lattice ≤
      Lattice.powerIdeal
        (b.order 2 - (ramificationIndex K : Int)) :=
    Lattice.scaleIdeal_le_powerIdeal_sub_ramification_of_normIdeal_eq
      (b.order 2) hrightNormB
  let z : T.right.carrier :=
    (-((betaU⁻¹ : Kˣ) : K)) • xx.2
  have hbetaInvUnit : IsValuationUnit K ((betaU⁻¹ : Kˣ) : K) := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K (betaU⁻¹)).2
    rw [ordUnit_inv, hbetaUOrder, neg_zero]
  have hbetaInvMem : -((betaU⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
    apply (IntegerRing K).neg_mem
    exact (mem_integerRing_iff K).2 hbetaInvUnit.ge
  have hzL : z ∈ T.right.lattice := by
    let c : IntegerRing K :=
      ⟨-((betaU⁻¹ : Kˣ) : K), hbetaInvMem⟩
    have hc := T.right.lattice.smul_mem c hxxRight
    change (-((betaU⁻¹ : Kˣ) : K)) • xx.2 ∈ T.right.lattice at hc
    exact hc
  have hzDual : z ∈ Lattice.dualLattice
      ((q.restrict T.right.carrier T.right.nondegenerate).rescaleUnit a⁻¹)
      T.right.lattice := by
    rw [Lattice.mem_dualLattice_iff]
    intro y hy
    have hbilinScale := Lattice.bilin_mem_scaleIdeal_of_mem
      (q.restrict T.right.carrier T.right.nondegenerate)
      T.right.lattice hxxRight hy
    have hbilinPower := hscaleLe hbilinScale
    have hbilinOrder :=
      (Lattice.mem_powerIdeal_iff (K := K)
        (b.order 2 - (ramificationIndex K : Int)) _).1 hbilinPower
    rw [mem_integerRing_iff]
    unfold Dyadic.IsIntegral
    have haInvOrder : ord K ((a⁻¹ : Kˣ) : K) =
        ((-(b.order 0 - (ramificationIndex K : Int)) : Int) : WithTop Int) := by
      rw [← coe_ordUnit K (a⁻¹), ordUnit_inv, haOrder]
    have hbetaInvOrder : ord K ((betaU⁻¹ : Kˣ) : K) = 0 := by
      rw [← coe_ordUnit K (betaU⁻¹), ordUnit_inv, hbetaUOrder]
      norm_num
    rw [QuadraticSpace.rescaleUnit_bilin_apply]
    simp only [z, LinearMap.BilinForm.smul_left, smul_eq_mul]
    change 0 ≤ ord K (((a⁻¹ : Kˣ) : K) *
      ((-((betaU⁻¹ : Kˣ) : K)) *
        (q.restrict T.right.carrier T.right.nondegenerate).bilin xx.2 y))
    rw [ord_mul, haInvOrder, ord_mul, ord_neg, hbetaInvOrder, zero_add]
    have harith :
        ((0 : Int) : WithTop Int) ≤
          ((-(b.order 0 - (ramificationIndex K : Int)) +
            (b.order 2 - (ramificationIndex K : Int)) : Int) : WithTop Int) := by
      norm_cast
      omega
    have hshift := add_le_add_left hbilinOrder
      ((-(b.order 0 - (ramificationIndex K : Int)) : Int) : WithTop Int)
    exact harith.trans (by
      simpa only [WithTop.coe_add, add_comm] using hshift)
  have haInvOrder : ord K ((a⁻¹ : Kˣ) : K) =
      ((-(b.order 0 - (ramificationIndex K : Int)) : Int) : WithTop Int) := by
    rw [← coe_ordUnit K (a⁻¹), ordUnit_inv, haOrder]
  have hbetaInvOrder : ord K ((betaU⁻¹ : Kˣ) : K) = 0 := by
    rw [← coe_ordUnit K (betaU⁻¹), ordUnit_inv, hbetaUOrder]
    norm_num
  have hzQuadraticLower :
      ((-(b.order 0 - (ramificationIndex K : Int)) + b.order 2 : Int) :
          WithTop Int) ≤
        ord K
          (((q.restrict T.right.carrier T.right.nondegenerate).rescaleUnit
            a⁻¹).quadratic z) := by
    rw [QuadraticSpace.rescaleUnit_quadratic]
    simp only [z, QuadraticSpace.quadratic_smul]
    rw [ord_mul, haInvOrder, ord_mul, ord_pow, ord_neg,
      hbetaInvOrder]
    simp only [nsmul_zero, zero_add]
    have hshift := add_le_add_left hrightLowerLocal
      ((-(b.order 0 - (ramificationIndex K : Int)) : Int) : WithTop Int)
    simpa only [WithTop.coe_add, add_comm] using hshift
  let s : K :=
    ((q.restrict T.right.carrier T.right.nondegenerate).rescaleUnit
      a⁻¹).quadratic z / 2
  have hquadratic :
      ((q.restrict T.right.carrier T.right.nondegenerate).rescaleUnit
        a⁻¹).quadratic z = 2 * s := by
    dsimp only [s]
    field_simp
  have hs : s ∈ IntegerRing K := by
    rw [mem_integerRing_iff]
    unfold Dyadic.IsIntegral
    have htwoInv : ord K ((2 : K)⁻¹) =
        ((-(ramificationIndex K : Int) : Int) : WithTop Int) := by
      rw [AddValuation.map_inv, ← ramificationIndex_spec]
      rfl
    change 0 ≤ ord K
      ((((q.restrict T.right.carrier T.right.nondegenerate).rescaleUnit
        a⁻¹).quadratic z) / 2)
    rw [div_eq_mul_inv, ord_mul, htwoInv]
    change (0 : WithTop Int) ≤
      ord K (((q.restrict T.right.carrier T.right.nondegenerate).rescaleUnit
        a⁻¹).quadratic z) +
        ((-(ramificationIndex K : Int) : Int) : WithTop Int)
    have harith :
        ((0 : Int) : WithTop Int) ≤
          ((-(b.order 0 - (ramificationIndex K : Int)) + b.order 2 -
            (ramificationIndex K : Int) : Int) : WithTop Int) := by
      norm_cast
      omega
    have hshift := add_le_add_right hzQuadraticLower
      ((-(ramificationIndex K : Int) : Int) : WithTop Int)
    exact harith.trans (by
      simpa only [WithTop.coe_add, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using hshift)
  let eichler := Lattice.hyperbolicEichlerLatticeIsometry_scaled
    a (q.restrict T.right.carrier T.right.nondegenerate)
    T.right.lattice z hzL hzDual s hquadratic hs
  let xt := eichler.toLinearEquiv xx
  have hxtSecond : xt.2 = 0 := by
    change (eichler.toLinearEquiv xx).2 = 0
    rw [Lattice.hyperbolicEichlerLatticeIsometry_scaled_apply_second]
    simp only [z, betaU, beta, Units.val_inv_eq_inv_val,
      Units.val_mk0, smul_smul]
    have hcoordNe : xx.1 1 ≠ 0 := by simpa only [beta] using hbetaNe
    have hcoef : xx.1 1 * -(xx.1 1)⁻¹ = (-1 : K) := by
      field_simp [hcoordNe]
    rw [hcoef]
    simp
  have hxtMem : xt ∈ Lattice.product
      (Lattice.hyperbolicPlaneLattice (K := K)) T.right.lattice :=
    (eichler.map_mem xx).1 hxxMem
  have hxtLeftMem : xt.1 ∈ Lattice.hyperbolicPlaneLattice (K := K) :=
    (Lattice.mem_product_iff.mp hxtMem).1
  have hxtLeftValue :
      (QuadraticSpace.hyperbolicPlane a).quadratic xt.1 =
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
          (q.restrict T.right.carrier T.right.nondegenerate)).quadratic xx := by
    have hmap := eichler.map_quadratic xx
    rw [QuadraticSpace.orthogonalSum_quadratic_apply, hxtSecond,
      (q.restrict T.right.carrier T.right.nondegenerate).quadratic_zero,
      add_zero] at hmap
    exact hmap
  have hxtLeftOrder :
      ord K ((QuadraticSpace.hyperbolicPlane a).quadratic xt.1) =
        (b.order 0 : WithTop Int) := by
    rw [hxtLeftValue, hxxTotal]
  have hxtUnits := hyperbolic_coordinates_are_units a (b.order 0)
    xt.1 hbase hxtLeftMem hxtLeftOrder
  have hxbMem : xb ∈ Lattice.product
      (Lattice.hyperbolicPlaneLattice (K := K)) T.right.lattice :=
    (identify.map_mem b.head).1 b.head_isNormGenerator.mem
  have hxbLeftMem : xb.1 ∈ Lattice.hyperbolicPlaneLattice (K := K) :=
    (Lattice.mem_product_iff.mp hxbMem).1
  have hxbLeftValue :
      (QuadraticSpace.hyperbolicPlane a).quadratic xb.1 =
        q.quadratic b.head := by
    have hmap := identify.map_quadratic b.head
    rw [QuadraticSpace.orthogonalSum_quadratic_apply, hxbSecond,
      (q.restrict T.right.carrier T.right.nondegenerate).quadratic_zero,
      add_zero] at hmap
    exact hmap
  have hxbLeftOrder :
      ord K ((QuadraticSpace.hyperbolicPlane a).quadratic xb.1) =
        (b.order 0 : WithTop Int) := by
    rw [hxbLeftValue, hheadOrder]
  have hxbUnits := hyperbolic_coordinates_are_units a (b.order 0)
    xb.1 hbase hxbLeftMem hxbLeftOrder
  have hxtZeroNe : xt.1 0 ≠ 0 := by
    intro hzero
    have hunit := hxtUnits.1
    unfold IsValuationUnit at hunit
    rw [hzero, ord_zero] at hunit
    exact WithTop.top_ne_coe hunit
  have hxbZeroNe : xb.1 0 ≠ 0 := by
    intro hzero
    have hunit := hxbUnits.1
    unfold IsValuationUnit at hunit
    rw [hzero, ord_zero] at hunit
    exact WithTop.top_ne_coe hunit
  let xtZeroU : Kˣ := Units.mk0 (xt.1 0) hxtZeroNe
  let xbZeroU : Kˣ := Units.mk0 (xb.1 0) hxbZeroNe
  let t : Kˣ := xtZeroU * xbZeroU⁻¹
  have hxtZeroOrder : ordUnit K xtZeroU = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K xtZeroU).1 (by
      simpa only [xtZeroU, Units.val_mk0] using hxtUnits.1)
  have hxbZeroOrder : ordUnit K xbZeroU = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K xbZeroU).1 (by
      simpa only [xbZeroU, Units.val_mk0] using hxbUnits.1)
  have htOrder : ordUnit K t = 0 := by
    change ordUnit K (xtZeroU * xbZeroU⁻¹) = 0
    rw [ordUnit_mul, ordUnit_inv, hxtZeroOrder, hxbZeroOrder]
    norm_num
  have htUnit : IsValuationUnit K (t : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K t).2 htOrder
  let diagonal := Lattice.scaledHyperbolicDiagonalLatticeIsometry a t htUnit
  let diagonalProduct := diagonal.orthogonalProductBasic
    (Lattice.Isometry.refl
      (q.restrict T.right.carrier T.right.nondegenerate) T.right.lattice)
  have hleftValues :
      (QuadraticSpace.hyperbolicPlane a).quadratic xt.1 =
        (QuadraticSpace.hyperbolicPlane a).quadratic xb.1 := by
    rw [hxtLeftValue, identify.map_quadratic, heq, hxbLeftValue]
  have hproducts : xt.1 0 * xt.1 1 = xb.1 0 * xb.1 1 := by
    rw [QuadraticSpace.hyperbolicPlane_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply] at hleftValues
    have hcoef : (2 : K) * (a : K) ≠ 0 :=
      mul_ne_zero (by norm_num) (Units.ne_zero a)
    exact mul_left_cancel₀ hcoef hleftValues
  have hdiagonalHead : diagonalProduct.toLinearEquiv xb = xt := by
    apply Prod.ext
    · funext i
      fin_cases i
      · change (t : K) * xb.1 0 = xt.1 0
        simp only [t, xtZeroU, xbZeroU, Units.val_mul,
          Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp [hxbZeroNe]
      · change ((t⁻¹ : Kˣ) : K) * xb.1 1 = xt.1 1
        simp only [t, xtZeroU, xbZeroU, Units.val_inv_eq_inv_val,
          Units.val_mul, Units.val_mk0]
        field_simp [hxtZeroNe, hxbZeroNe]
        exact hproducts.symm
    · change xb.2 = xt.2
      rw [hxbSecond, hxtSecond]
  let modelF : Lattice.IntegralOrthogonalGroup
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        (q.restrict T.right.carrier T.right.nondegenerate))
      (Lattice.product (Lattice.hyperbolicPlaneLattice (K := K))
        T.right.lattice) :=
    diagonalProduct.trans eichler.symm
  have hdiagonalDet :
      LinearEquiv.det diagonalProduct.toLinearEquiv = 1 := by
    rw [Lattice.Isometry.det_orthogonalProductBasic]
    change LinearEquiv.det
        (Lattice.hyperbolicDiagonalLinearEquiv t) *
      LinearEquiv.det (LinearEquiv.refl K T.right.carrier) = 1
    rw [Lattice.det_hyperbolicDiagonalLinearEquiv,
      LinearEquiv.det_refl, mul_one]
  have heichlerDet : LinearEquiv.det eichler.toLinearEquiv = 1 := by
    exact Lattice.det_hyperbolicEichlerLatticeIsometry_scaled
      a (q.restrict T.right.carrier T.right.nondegenerate)
      T.right.lattice z hzL hzDual s hquadratic hs
  have hmodelFDet : LinearEquiv.det modelF.toLinearEquiv = 1 := by
    change LinearEquiv.det
      (diagonalProduct.toLinearEquiv.trans eichler.toLinearEquiv.symm) = 1
    rw [LinearEquiv.det_trans, LinearEquiv.det_symm, map_inv,
      heichlerDet, inv_one,
      hdiagonalDet, one_mul]
  let modelRotation : Lattice.IntegralRotation
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        (q.restrict T.right.carrier T.right.nondegenerate))
      (Lattice.product (Lattice.hyperbolicPlaneLattice (K := K))
        T.right.lattice) :=
    ⟨modelF, hmodelFDet⟩
  have hdiagonalSpinor : Lattice.integralSpinorNorm diagonal =
      squareClass K t := by
    exact Lattice.integralSpinorNorm_scaledHyperbolicDiagonalLatticeIsometry
      a t htUnit
  have hdiagonalProductSpinor :
      Lattice.integralSpinorNorm diagonalProduct = squareClass K t := by
    rw [Lattice.integralSpinorNorm_orthogonalProductBasic_refl]
    exact hdiagonalSpinor
  have heichlerSpinor : Lattice.integralSpinorNorm eichler = 1 := by
    exact Lattice.integralSpinorNorm_hyperbolicEichlerLatticeIsometry_scaled
      (q := q.restrict T.right.carrier T.right.nondegenerate)
      (L := T.right.lattice) a z hzL hzDual s hquadratic hs
  have heichlerInvSpinor : Lattice.integralSpinorNorm eichler.symm = 1 := by
    change Lattice.integralSpinorNorm (eichler⁻¹) = 1
    rw [← Lattice.integralSpinorNormHom_apply]
    simp only [map_inv, Lattice.integralSpinorNormHom_apply,
      heichlerSpinor, inv_one]
  have hmodelSpinor : modelRotation.spinorNorm = squareClass K t := by
    change Lattice.integralSpinorNorm modelF = squareClass K t
    change Lattice.integralSpinorNorm
      (eichler.symm * diagonalProduct) = squareClass K t
    rw [Lattice.integralSpinorNorm_mul, heichlerInvSpinor,
      hdiagonalProductSpinor, one_mul]
  have hmodelF : modelF.toLinearEquiv xb = xx := by
    change eichler.toLinearEquiv.symm
      (diagonalProduct.toLinearEquiv xb) = xx
    rw [hdiagonalHead]
    exact eichler.toLinearEquiv.symm_apply_apply xx
  let f : Lattice.IntegralRotation q L :=
    modelRotation.conjugateAutomorphism identify.symm
  have hfspinor : f.spinorNorm = squareClass K t := by
    exact
      (modelRotation.spinorNorm_conjugateAutomorphism identify.symm).trans
        hmodelSpinor
  have htMem : squareClass K t ∈ valuationUnitSquareClassSubgroup K := by
    refine ⟨t, htUnit, rfl⟩
  have hPclass : P.bong.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K) :=
    P.bong.binaryUnitSquareClass_eq_negativeQuarter_of_isometry_hyperbolicPlane
      a eP
  have hparameter : P.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [P.valueUnit_eq, P.valueUnit_eq]
    congr 2
  have hclass : b.adjacentUnitSquareClass 0 (by simp) =
      unitSquareClass K (negativeQuarterUnit K) := by
    unfold adjacentUnitSquareClass
    rw [← hparameter]
    exact hPclass
  have hgroup :
      beliSpinorGroup K (b.adjacentUnitSquareClass 0 (by simp)) =
        valuationUnitSquareClassSubgroup K := by
    rw [hclass, beliSpinorGroup_unitSquareClass]
    exact beliSpinorGroupRepresentative_of_negativeQuarter
      K (negativeQuarterUnit K) negativeQuarter_isBinaryParameterAdmissible rfl
  have htHead : squareClass K t ∈ b.lemma66SharpHeadFactor := by
    unfold lemma66SharpHeadFactor
    rw [hgroup]
    apply (show valuationUnitSquareClassSubgroup K ≤
      valuationUnitSquareClassSubgroup K ⊔
        b.lemma66SharpCongruenceFactor from le_sup_left)
    exact htMem
  refine ⟨f, ?_, hfspinor.symm ▸ htHead⟩
  · change identify.toLinearEquiv.symm
      (modelF.toLinearEquiv (identify.toLinearEquiv b.head)) = x
    change identify.toLinearEquiv.symm (modelF.toLinearEquiv xb) = x
    rw [hmodelF]
    exact identify.toLinearEquiv.symm_apply_apply x

/-- Geometric consequence of the strengthened hyperbolic construction. -/
theorem exists_rotation_apply_head_of_firstBinary_hyperbolic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hH : b.FirstBinaryIsHyperbolic)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x := by
  rcases
      b.exists_rotation_apply_head_mem_lemma66SharpHeadFactor_of_firstBinary_hyperbolic
        hB hH x hx heq with ⟨f, hfx, _⟩
  exact ⟨f, hfx⟩

/-- Spinor-complete nonhyperbolic branch.  The exceptional residue-two
configuration is handled by the once-rescaled tail; every other
configuration uses the canonical least-rescaling setup from Lemma 6.5. -/
theorem exists_rotation_apply_head_mem_lemma66SharpHeadFactor_of_not_firstBinary_hyperbolic
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (hnotHyperbolic : ¬b.FirstBinaryIsHyperbolic)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧
        f.spinorNorm ∈ b.lemma66SharpHeadFactor := by
  by_cases hexceptional : b.Lemma65Exceptional
  · exact b.exists_exceptionalRotation_apply_head_mem_lemma66SharpHeadFactor
      hB x hx heq hexceptional hproper
  · let S := b.lemma65Setup_of_not_exceptional
      hB hnotHyperbolic hexceptional
    exact
      S.exists_rotation_apply_head_mem_lemma66SharpHeadFactor_of_setup_not_exceptional
        hB hexceptional x hx heq hproper

/-- Unconditional proof of Beli (2003), Lemma 6.6.  The first binary block
is either hyperbolic, when an Eichler transformation gives the transport, or
nonhyperbolic, when Lemma 6.5 and the exceptional-tail analysis above are
exhaustive. -/
theorem exists_rotation_apply_head_mem_lemma66SharpHeadFactor_proved
    (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧
        f.spinorNorm ∈ b.lemma66SharpHeadFactor := by
  by_cases hH : b.FirstBinaryIsHyperbolic
  · exact
      b.exists_rotation_apply_head_mem_lemma66SharpHeadFactor_of_firstBinary_hyperbolic
        hB hH x hx heq
  · exact
      b.exists_rotation_apply_head_mem_lemma66SharpHeadFactor_of_not_firstBinary_hyperbolic
        hB hH x hx heq hproper

/-- The local-law interface for Lemma 6.6 is derived from the dyadic field
axioms and no longer needs to be supplied by downstream developments. -/
noncomputable instance beliLemma66LawsProved :
    BeliLemma66Laws.{u, v} K where
  exists_rotation := by
    intro V _instAdd _instModule q L n b hB x hx heq hproper
    exact b.exists_rotation_apply_head_mem_lemma66SharpHeadFactor_proved
      hB x hx heq hproper



end BONG

end Bong
