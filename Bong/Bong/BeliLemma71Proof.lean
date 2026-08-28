/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma71
import Bong.Bong.BinaryEndpointSpinor
import Bong.Lattice.NormGenerator
import Bong.Lattice.NormGeneratorValues
import Bong.Lattice.HyperbolicDiagonalSpinor
import Bong.Lattice.HyperbolicEichlerTransport
import Bong.Lattice.HyperbolicLatticeInvariants
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.SpinorNormIsometry
import Bong.Lattice.SpinorNormMultiplicative
import Bong.Lattice.SpinorNormOrthogonalProduct

/-!
# Proof of Beli (2003), Lemma 7.1

This file gives the unconditional proof of Lemma 7.1.  The first part uses
norm-generator reflections.  For part (ii), explicit spinor-one Eichler
transformations restore the displayed hyperbolic plane; block determinant
and spinor-norm factorization then reduce the conclusion to the residual
unit bound and the parity of the two norm orders.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace Lattice

namespace NormOrderDatum

/-- A nonzero generator for the norm ideal rules out a zero-dimensional
component. -/
theorem finrank_pos (N : NormOrderDatum q L) :
    0 < Module.finrank K V := by
  letI : Module.Finite K V := L.moduleFinite
  by_contra hpos
  have hzero : Module.finrank K V = 0 := Nat.eq_zero_of_not_pos hpos
  letI : Subsingleton V := Module.finrank_zero_iff.mp hzero
  have hle : normIdeal q L ≤ (⊥ : CoefficientIdeal (K := K)) := by
    rw [normIdeal, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : (x : V) = 0 := Subsingleton.elim _ _
    simp [hx]
  have hgenerator : (N.generator : K) ∈ normIdeal q L := by
    rw [N.normIdeal_eq]
    exact generator_mem_principalIdeal _
  have hzeroGenerator : (N.generator : K) = 0 := by
    simpa only [Submodule.mem_bot] using hle hgenerator
  exact (Units.ne_zero N.generator) hzeroGenerator

/-- A represented norm generator has the order recorded by any other
generator of the same norm ideal. -/
theorem order_eq_of_isNormGenerator
    (N : NormOrderDatum q L) {x : V}
    (hx : IsNormGenerator q L x) (hanisotropic : q.IsAnisotropic x) :
    ordUnit K (Units.mk0 (q.quadratic x) hanisotropic) = N.order := by
  unfold NormOrderDatum.order
  exact (principalIdeal_eq_iff_ordUnit_eq
    (Units.mk0 (q.quadratic x) hanisotropic) N.generator).mp
      (hx.normIdeal_eq.symm.trans N.normIdeal_eq)

/-- If an integral automorphism is improper, multiplying it by a reflection
in a norm generator makes it proper.  Hence the norm-generator square class
times its spinor norm is unit-bounded whenever the proper spinor image is. -/
theorem exists_normGenerator_adjusted_spinorNorm_mem_unit
    (N : NormOrderDatum q L) (hunit : SpinorNormIsUnitBounded q L)
    (f : IntegralOrthogonalGroup q L)
    (hdet : LinearEquiv.det f.toLinearEquiv = (-1 : Kˣ)) :
    ∃ (x : V) (hx : IsNormGenerator q L x)
      (hanisotropic : q.IsAnisotropic x),
      ordUnit K (Units.mk0 (q.quadratic x) hanisotropic) = N.order ∧
      squareClass K (Units.mk0 (q.quadratic x) hanisotropic) *
          integralSpinorNorm f ∈ valuationUnitSquareClassSubgroup K := by
  letI : Module.Finite K V := L.moduleFinite
  rcases exists_isNormGenerator_of_finrank_pos q L N.finrank_pos with
    ⟨x, hx, hanisotropic⟩
  let reflection : IntegralOrthogonalGroup q L :=
    integralReflection hanisotropic
      (hx.isIntegralReflection hanisotropic)
  let rotation : IntegralRotation q L := {
    toIntegralOrthogonalGroup := reflection * f
    det_eq_one := by
      change LinearEquiv.det
          (f.toLinearEquiv.trans reflection.toLinearEquiv) = 1
      rw [LinearEquiv.det_trans, hdet]
      rw [show LinearEquiv.det reflection.toLinearEquiv = (-1 : Kˣ) by
        exact det_integralReflection hanisotropic
          (hx.isIntegralReflection hanisotropic)]
      norm_num }
  have hrotation : rotation.spinorNorm ∈
      spinorNormImageSubgroup (q := q) (L := L) := ⟨rotation, rfl⟩
  have hbounded := hunit hrotation
  have hspinor : rotation.spinorNorm =
      squareClass K (Units.mk0 (q.quadratic x) hanisotropic) *
        integralSpinorNorm f := by
    change integralSpinorNorm (reflection * f) = _
    rw [integralSpinorNorm_mul]
    change integralSpinorNorm
        (integralReflection hanisotropic
          (hx.isIntegralReflection hanisotropic)) *
        integralSpinorNorm f = _
    rw [integralSpinorNorm_integralReflection]
    rfl
  rw [hspinor] at hbounded
  exact ⟨x, hx, hanisotropic,
    N.order_eq_of_isNormGenerator hx hanisotropic, hbounded⟩

end NormOrderDatum

/-- Norm-order data for the standard lattice on a scaled hyperbolic plane. -/
noncomputable def scaledHyperbolicNormOrderDatum (s : Kˣ) :
    NormOrderDatum (QuadraticSpace.hyperbolicPlane s)
      (hyperbolicPlaneLattice (K := K)) := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let generator : Kˣ := two * s
  refine {
    generator := generator
    normIdeal_eq := ?_ }
  rw [normIdeal_hyperbolicPlaneLattice]
  congr 2

@[simp]
theorem scaledHyperbolicNormOrderDatum_uniformizerPower_order (r : Int) :
    (scaledHyperbolicNormOrderDatum
      (uniformizerPowerUnit K r)).order =
        r + ramificationIndex K := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwo : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ramificationIndex_spec]
    rfl
  change ordUnit K (two * uniformizerPowerUnit K r) =
    r + ramificationIndex K
  rw [ordUnit_mul, ordUnit_uniformizerPowerUnit, htwo]
  omega

/-- Hsia's binary hyperbolic calculation, phrased as the upper-bound
predicate used in Lemma 7.1. -/
theorem spinorNormIsUnitBounded_hyperbolicPlane (s : Kˣ) :
    SpinorNormIsUnitBounded
      (QuadraticSpace.hyperbolicPlane s)
      (hyperbolicPlaneLattice (K := K)) := by
  intro A hA
  rw [mem_spinorNormImageSubgroup_iff] at hA
  have hA' : A ∈ spinorNormImage
      (q := QuadraticSpace.hyperbolicPlane s)
      (L := hyperbolicPlaneLattice (K := K)) := hA
  rw [spinorNormImage_hyperbolicPlane_eq_valuationUnitSquareClassSubgroup
    s] at hA'
  exact hA'

private theorem squareClass_mul_self_eq_one (a : Kˣ) :
    squareClass K a * squareClass K a = 1 := by
  change squareClass K (a * a) = 1
  rw [show a * a = (1 : Kˣ) * a ^ 2 by simp [pow_two],
    squareClass_mul_square]
  rfl

namespace OrthogonalDecomposition

/-- A norm-generator reflection in one component of an orthogonal
decomposition preserves the full ambient lattice. -/
theorem component_normGenerator_isIntegralReflection
    (D : OrthogonalDecomposition q L t) (i : Fin t)
    {x : (D.component i).carrier}
    (hx : IsNormGenerator (D.component i).space
      (D.component i).lattice x)
    (hanisotropic : (D.component i).space.IsAnisotropic x) :
    IsIntegralReflection (q := q) (L := L)
      (x := (x : V)) hanisotropic := by
  let reflection : V →ₗ[IntegerRing K] V :=
    (q.reflectionLinearEquiv (x : V) hanisotropic).toLinearMap.restrictScalars
      (IntegerRing K)
  have hcomponents :
      (⨆ j, (D.component j).ambientSubmodule) ≤
        L.toSubmodule.comap reflection := by
    apply iSup_le
    intro j z hz
    rcases hz with ⟨zj, hzj, rfl⟩
    change q.reflectionLinearEquiv (x : V) hanisotropic (zj : V) ∈ L
    by_cases hji : j = i
    · subst j
      have hzreflected :
          (D.component i).space.reflectionLinearEquiv x hanisotropic zj ∈
            (D.component i).lattice :=
        hx.isIntegralReflection hanisotropic zj hzj
      apply D.component_ambientSubmodule_le i
      refine ⟨(D.component i).space.reflectionLinearEquiv
        x hanisotropic zj, hzreflected, ?_⟩
      rfl
    · have horth : q.bilin (x : V) (zj : V) = 0 :=
        D.orthogonal i j (Ne.symm hji) x zj
      rw [q.reflectionLinearEquiv_apply]
      simp [horth]
      apply D.component_ambientSubmodule_le j
      exact ⟨zj, hzj, rfl⟩
  intro y hy
  have hySum : y ∈ ⨆ j, (D.component j).ambientSubmodule := by
    rw [D.sum_eq]
    exact hy
  exact hcomponents hySum

end OrthogonalDecomposition

/-- The reflection argument proving Beli (2003), Lemma 7.1(i). -/
theorem beliLemma71_i_proved
    (D : OrthogonalDecomposition q L t)
    (N : OrthogonalComponentNormData D)
    (hunit : SpinorNormIsUnitBounded q L) (i j : Fin t) :
    Int.ModEq 2 (N i).order (N j).order := by
  let Ci := D.component i
  let Cj := D.component j
  have hiPos : 0 < Module.finrank K Ci.carrier := (N i).finrank_pos
  have hjPos : 0 < Module.finrank K Cj.carrier := (N j).finrank_pos
  rcases exists_isNormGenerator_of_finrank_pos
      Ci.space Ci.lattice hiPos with ⟨x, hx, hxAnisotropic⟩
  rcases exists_isNormGenerator_of_finrank_pos
      Cj.space Cj.lattice hjPos with ⟨y, hy, hyAnisotropic⟩
  have hxAmbient : q.IsAnisotropic (x : V) := hxAnisotropic
  have hyAmbient : q.IsAnisotropic (y : V) := hyAnisotropic
  have hxIntegral : IsIntegralReflection (q := q) (L := L)
      (x := (x : V)) hxAmbient :=
    D.component_normGenerator_isIntegralReflection i hx hxAnisotropic
  have hyIntegral : IsIntegralReflection (q := q) (L := L)
      (x := (y : V)) hyAmbient :=
    D.component_normGenerator_isIntegralReflection j hy hyAnisotropic
  let rotation : IntegralRotation q L :=
    integralReflectionProduct hxAmbient hxIntegral hyAmbient hyIntegral
  have hrotation : rotation.spinorNorm ∈
      spinorNormImageSubgroup (q := q) (L := L) := ⟨rotation, rfl⟩
  have hbounded := hunit hrotation
  have hspinor : rotation.spinorNorm =
      squareClass K
        (Units.mk0 (Ci.space.quadratic x) hxAnisotropic *
          Units.mk0 (Cj.space.quadratic y) hyAnisotropic) := by
    change integralSpinorNorm
      (integralReflection hxAmbient hxIntegral *
        integralReflection hyAmbient hyIntegral) = _
    rw [integralSpinorNorm_mul,
      integralSpinorNorm_integralReflection,
      integralSpinorNorm_integralReflection]
    rfl
  rw [hspinor,
    squareClass_mem_valuationUnitSquareClassSubgroup_iff_even] at hbounded
  have hxOrder :
      ordUnit K (Units.mk0 (Ci.space.quadratic x) hxAnisotropic) =
        (N i).order :=
    (N i).order_eq_of_isNormGenerator hx hxAnisotropic
  have hyOrder :
      ordUnit K (Units.mk0 (Cj.space.quadratic y) hyAnisotropic) =
        (N j).order :=
    (N j).order_eq_of_isNormGenerator hy hyAnisotropic
  rw [ordUnit_mul, hxOrder, hyOrder] at hbounded
  rcases hbounded with ⟨k, hk⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨-k + (N j).order, ?_⟩
  omega

/-- Every unit square class occurs in the spinor image as soon as the lattice
has a displayed scaled hyperbolic summand. -/
theorem valuationUnitSquareClassSubgroup_le_spinorNormImageSubgroup_of_hyperbolicSplitting
    (S : HyperbolicPlaneSplitting q L) :
    valuationUnitSquareClassSubgroup K ≤
      spinorNormImageSubgroup (q := q) (L := L) := by
  intro a ha
  rw [valuationUnitSquareClassSubgroup, Subgroup.mem_map] at ha
  rcases ha with ⟨u, hu, hclass⟩
  let hyperbolicIsometry := Classical.choice S.hyperbolic
  let standardOrthogonal :=
    scaledHyperbolicDiagonalLatticeIsometry
      (uniformizerPowerUnit K S.scaleOrder) u hu
  let standardRotation : IntegralRotation
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K S.scaleOrder))
      (hyperbolicPlaneLattice (K := K)) := {
    toIntegralOrthogonalGroup := standardOrthogonal
    det_eq_one := det_hyperbolicDiagonalLinearEquiv u }
  let componentRotation : IntegralRotation
      (S.decomposition.component 0).space
      (S.decomposition.component 0).lattice :=
    standardRotation.conjugateAutomorphism hyperbolicIsometry.symm
  let productOrthogonal : IntegralOrthogonalGroup
      ((S.decomposition.component 0).space.orthogonalSum
        (S.decomposition.component 1).space)
      (product (S.decomposition.component 0).lattice
        (S.decomposition.component 1).lattice) :=
    componentRotation.toIntegralOrthogonalGroup.orthogonalProductBasic
      (Isometry.refl (S.decomposition.component 1).space
        (S.decomposition.component 1).lattice)
  let productRotation : IntegralRotation
      ((S.decomposition.component 0).space.orthogonalSum
        (S.decomposition.component 1).space)
      (product (S.decomposition.component 0).lattice
        (S.decomposition.component 1).lattice) := {
    toIntegralOrthogonalGroup := productOrthogonal
    det_eq_one := by
      dsimp only [productOrthogonal]
      rw [Isometry.det_orthogonalProductBasic,
        componentRotation.det_eq_one, one_mul]
      exact LinearEquiv.det_refl }
  let ambientRotation : IntegralRotation q L :=
    productRotation.conjugateAutomorphism
      S.decomposition.pairProductLatticeIsometry
  refine ⟨ambientRotation, ?_⟩
  calc
    ambientRotation.spinorNorm = productRotation.spinorNorm :=
      productRotation.spinorNorm_conjugateAutomorphism
        S.decomposition.pairProductLatticeIsometry
    _ = componentRotation.spinorNorm := by
      exact integralSpinorNorm_orthogonalProductBasic_refl
        componentRotation.toIntegralOrthogonalGroup
    _ = standardRotation.spinorNorm :=
      standardRotation.spinorNorm_conjugateAutomorphism
        hyperbolicIsometry.symm
    _ = squareClass K u := by
      exact integralSpinorNorm_scaledHyperbolicDiagonalLatticeIsometry
        (uniformizerPowerUnit K S.scaleOrder) u hu
    _ = a := hclass

/-- The subgroup of unit square classes has index two: a subgroup containing
it is either that subgroup or the whole square-class group. -/
theorem squareClassSubgroup_eq_top_of_valuationUnit_le_of_not_le
    (H : Subgroup (SquareClass K))
    (hunit : valuationUnitSquareClassSubgroup K ≤ H)
    (hnot : ¬H ≤ valuationUnitSquareClassSubgroup K) :
    H = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro aClass
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.square Kˣ) aClass
  change ¬∀ x, x ∈ H →
    x ∈ valuationUnitSquareClassSubgroup K at hnot
  push Not at hnot
  obtain ⟨bClass, hbH, hbNotUnit⟩ := hnot
  obtain ⟨b, hbClass⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.square Kˣ) bClass
  have hbH' : squareClass K b ∈ H := by
    change (QuotientGroup.mk' (Subgroup.square Kˣ)) b ∈ H
    rw [hbClass]
    exact hbH
  have hbNotUnit' : squareClass K b ∉
      valuationUnitSquareClassSubgroup K := by
    change (QuotientGroup.mk' (Subgroup.square Kˣ)) b ∉
      valuationUnitSquareClassSubgroup K
    rw [hbClass]
    exact hbNotUnit
  have hbOdd : Odd (ordUnit K b) := by
    apply Int.not_even_iff_odd.mp
    intro hbEven
    exact hbNotUnit'
      ((squareClass_mem_valuationUnitSquareClassSubgroup_iff_even b).2
        hbEven)
  rcases Int.even_or_odd (ordUnit K a) with haEven | haOdd
  · exact hunit
      ((squareClass_mem_valuationUnitSquareClassSubgroup_iff_even a).2
        haEven)
  · have habEven : Even (ordUnit K (a / b)) := by
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
      exact haOdd.sub_odd hbOdd
    have habH : squareClass K (a / b) ∈ H :=
      hunit
        ((squareClass_mem_valuationUnitSquareClassSubgroup_iff_even
          (a / b)).2 habEven)
    have hmul := H.mul_mem habH hbH'
    change squareClass K (a / b) * squareClass K b ∈ H at hmul
    change (squareClassHom K) a ∈ H
    have hmul' : (squareClassHom K) (a / b * b) ∈ H := by
      simpa only [← squareClassHom_apply, ← map_mul] using hmul
    simpa [div_eq_mul_inv] using hmul'

namespace HyperbolicPlaneSplitting

/-- Norm-order data for the displayed hyperbolic component. -/
noncomputable def hyperbolicNorm :
    (S : HyperbolicPlaneSplitting q L) →
      NormOrderDatum (S.decomposition.component 0).space
        (S.decomposition.component 0).lattice := fun S => by
  let e := Classical.choice S.hyperbolic
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let generator : Kˣ := two * uniformizerPowerUnit K S.scaleOrder
  refine {
    generator := generator
    normIdeal_eq := ?_ }
  have hmap := normIdeal_map_isometry e.toQuadraticSpaceIsometry
    (S.decomposition.component 0).lattice
  have heq :
      map e.toQuadraticSpaceIsometry.toLinearEquiv
          (S.decomposition.component 0).lattice =
        hyperbolicPlaneLattice (K := K) := e.map_eq
  rw [heq] at hmap
  have hstandard := normIdeal_hyperbolicPlaneLattice
    (uniformizerPowerUnit K S.scaleOrder)
  calc
    normIdeal (S.decomposition.component 0).space
        (S.decomposition.component 0).lattice =
      normIdeal
        (QuadraticSpace.hyperbolicPlane
          (uniformizerPowerUnit K S.scaleOrder))
        (hyperbolicPlaneLattice (K := K)) := hmap.symm
    _ = principalIdeal (K := K)
        (2 * (uniformizerPowerUnit K S.scaleOrder : K)) := hstandard
    _ = principalIdeal (K := K) (generator : K) := by
      congr 2

@[simp]
theorem hyperbolicNorm_order (S : HyperbolicPlaneSplitting q L) :
    S.hyperbolicNorm.order = S.hyperbolicNormOrder := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwo : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ramificationIndex_spec]
    rfl
  change ordUnit K
      (two * uniformizerPowerUnit K S.scaleOrder) =
    S.scaleOrder + ramificationIndex K
  rw [ordUnit_mul, ordUnit_uniformizerPowerUnit]
  rw [htwo]
  omega

/-- Norm-order data for both components of the displayed splitting. -/
noncomputable def componentNormData (S : HyperbolicPlaneSplitting q L) :
    OrthogonalComponentNormData S.decomposition := fun i =>
  Fin.cases S.hyperbolicNorm (fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact S.remainderNorm) i

@[simp]
theorem componentNormData_zero (S : HyperbolicPlaneSplitting q L) :
    S.componentNormData 0 = S.hyperbolicNorm :=
  rfl

@[simp]
theorem componentNormData_one (S : HyperbolicPlaneSplitting q L) :
    S.componentNormData 1 = S.remainderNorm :=
  rfl

end HyperbolicPlaneSplitting

/-- Beli (2003), Lemma 7.1(ii), unequal-parity branch.  The hyperbolic
summand supplies all unit classes, while part (i) shows that the full image
cannot be unit-bounded. -/
theorem beliLemma71_ii_different_proved
    (S : HyperbolicPlaneSplitting q L)
    (hunit : S.RemainderIsUnitBounded)
    (hparity : ¬S.NormOrdersSameParity) :
    spinorNormImageSubgroup (q := q) (L := L) = ⊤ := by
  apply squareClassSubgroup_eq_top_of_valuationUnit_le_of_not_le
  · exact
      valuationUnitSquareClassSubgroup_le_spinorNormImageSubgroup_of_hyperbolicSplitting
        S
  · intro hfullUnit
    apply hparity
    unfold HyperbolicPlaneSplitting.NormOrdersSameParity
    simpa using beliLemma71_i_proved S.decomposition
      S.componentNormData hfullUnit 0 1

/-- Beli (2003), Lemma 7.1(ii), equal-parity branch.  A spinor-one product
of Eichler transformations first restores the displayed hyperbolic summand.
The resulting block automorphisms are either both proper or both improper;
in the latter case norm-generator reflections make both blocks proper, and
the parity hypothesis cancels the two remaining reflection classes. -/
theorem beliLemma71_ii_same_proved
    (S : HyperbolicPlaneSplitting q L)
    (hunit : S.RemainderIsUnitBounded)
    (hparity : S.NormOrdersSameParity) :
    spinorNormImageSubgroup (q := q) (L := L) =
      valuationUnitSquareClassSubgroup K := by
  apply le_antisymm
  · intro A hA
    rw [mem_spinorNormImageSubgroup_iff] at hA
    rcases hA with ⟨rotation, rfl⟩
    let a : Kˣ := uniformizerPowerUnit K S.scaleOrder
    let hyperbolicIsometry := Classical.choice S.hyperbolic
    let componentToModel :=
      hyperbolicIsometry.orthogonalProductBasic
        (Isometry.refl (S.decomposition.component 1).space
          (S.decomposition.component 1).lattice)
    let identify : Isometry q
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
          (S.decomposition.component 1).space)
        L
        (product (hyperbolicPlaneLattice (K := K))
          (S.decomposition.component 1).lattice) :=
      S.decomposition.pairProductLatticeIsometry.symm.trans
        componentToModel
    let modelRotation : IntegralRotation
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
          (S.decomposition.component 1).space)
        (product (hyperbolicPlaneLattice (K := K))
          (S.decomposition.component 1).lattice) :=
      rotation.conjugateAutomorphism identify
    let T := hyperbolicSummandTransport a
      modelRotation.toIntegralOrthogonalGroup
    letI : Module.Finite K (S.decomposition.component 1).carrier :=
      (S.decomposition.component 1).lattice.moduleFinite
    have hdetStabilized :
        LinearEquiv.det T.stabilized.toLinearEquiv = 1 := by
      calc
        LinearEquiv.det T.stabilized.toLinearEquiv =
            LinearEquiv.det
              modelRotation.toIntegralOrthogonalGroup.toLinearEquiv :=
          T.stabilized_det_eq
        _ = 1 := modelRotation.det_eq_one
    have hdetProduct :
        LinearEquiv.det T.leftIsometry.toLinearEquiv *
            LinearEquiv.det T.rightIsometry.toLinearEquiv = 1 := by
      rw [← T.det_left_mul_right]
      exact hdetStabilized
    have hconjugate : modelRotation.spinorNorm = rotation.spinorNorm :=
      rotation.spinorNorm_conjugateAutomorphism identify
    rcases T.leftIsometry.toQuadraticSpaceIsometry.det_eq_one_or_neg_one with
      hleft | hleft
    · change LinearEquiv.det T.leftIsometry.toLinearEquiv = 1 at hleft
      have hright :
          LinearEquiv.det T.rightIsometry.toLinearEquiv = 1 := by
        simpa [hleft] using hdetProduct
      let leftRotation : IntegralRotation
          (QuadraticSpace.hyperbolicPlane a)
          (hyperbolicPlaneLattice (K := K)) := ⟨T.leftIsometry, hleft⟩
      let rightRotation : IntegralRotation
          (S.decomposition.component 1).space
          (S.decomposition.component 1).lattice :=
        ⟨T.rightIsometry, hright⟩
      have hleftUnit : integralSpinorNorm T.leftIsometry ∈
          valuationUnitSquareClassSubgroup K := by
        apply spinorNormIsUnitBounded_hyperbolicPlane a
        exact ⟨leftRotation, rfl⟩
      have hrightUnit : integralSpinorNorm T.rightIsometry ∈
          valuationUnitSquareClassSubgroup K := by
        apply hunit
        exact ⟨rightRotation, rfl⟩
      have hmodelUnit : modelRotation.spinorNorm ∈
          valuationUnitSquareClassSubgroup K := by
        change integralSpinorNorm
            modelRotation.toIntegralOrthogonalGroup ∈
          valuationUnitSquareClassSubgroup K
        rw [← T.stabilized_spinorNorm_eq,
          T.spinorNorm_left_mul_right]
        exact (valuationUnitSquareClassSubgroup K).mul_mem
          hleftUnit hrightUnit
      rw [← hconjugate]
      exact hmodelUnit
    · change LinearEquiv.det T.leftIsometry.toLinearEquiv =
          (-1 : Kˣ) at hleft
      have hright :
          LinearEquiv.det T.rightIsometry.toLinearEquiv = (-1 : Kˣ) := by
        rw [hleft] at hdetProduct
        have h := congrArg (fun z : Kˣ => (-1 : Kˣ) * z)
          hdetProduct
        simpa [mul_assoc] using h
      obtain ⟨x, hx, hxAnisotropic, hxOrder, hxUnit⟩ :=
        (scaledHyperbolicNormOrderDatum a).exists_normGenerator_adjusted_spinorNorm_mem_unit
          (spinorNormIsUnitBounded_hyperbolicPlane a)
          T.leftIsometry hleft
      obtain ⟨y, hy, hyAnisotropic, hyOrder, hyUnit⟩ :=
        S.remainderNorm.exists_normGenerator_adjusted_spinorNorm_mem_unit
          hunit T.rightIsometry hright
      let qx : Kˣ := Units.mk0
        ((QuadraticSpace.hyperbolicPlane a).quadratic x) hxAnisotropic
      let qy : Kˣ := Units.mk0
        ((S.decomposition.component 1).space.quadratic y) hyAnisotropic
      have hxOrder' : ordUnit K qx =
          (scaledHyperbolicNormOrderDatum a).order := by
        simpa [qx] using hxOrder
      have hyOrder' : ordUnit K qy = S.remainderNorm.order := by
        simpa [qy] using hyOrder
      have hstandardOrder :
          (scaledHyperbolicNormOrderDatum a).order =
            S.hyperbolicNormOrder := by
        simp [a, HyperbolicPlaneSplitting.hyperbolicNormOrder]
      have horders : Int.ModEq 2 (ordUnit K qx) (ordUnit K qy) := by
        rw [hxOrder', hyOrder', hstandardOrder]
        exact hparity
      have heven : Even (ordUnit K (qx * qy)) := by
        rw [ordUnit_mul]
        rw [Int.modEq_iff_dvd] at horders
        rcases horders with ⟨k, hk⟩
        refine ⟨ordUnit K qx + k, ?_⟩
        omega
      have hpairUnit : squareClass K qx * squareClass K qy ∈
          valuationUnitSquareClassSubgroup K := by
        change squareClass K (qx * qy) ∈
          valuationUnitSquareClassSubgroup K
        exact
          (squareClass_mem_valuationUnitSquareClassSubgroup_iff_even
            (K := K) (qx * qy)).2 heven
      have hxUnit' : squareClass K qx *
            integralSpinorNorm T.leftIsometry ∈
          valuationUnitSquareClassSubgroup K := by
        simpa [qx] using hxUnit
      have hyUnit' : squareClass K qy *
            integralSpinorNorm T.rightIsometry ∈
          valuationUnitSquareClassSubgroup K := by
        simpa [qy] using hyUnit
      have htotal := (valuationUnitSquareClassSubgroup K).mul_mem
        ((valuationUnitSquareClassSubgroup K).mul_mem hxUnit' hyUnit')
        hpairUnit
      have hqxSq : squareClass K qx * squareClass K qx = 1 :=
        squareClass_mul_self_eq_one qx
      have hqySq : squareClass K qy * squareClass K qy = 1 :=
        squareClass_mul_self_eq_one qy
      have hrearrange :
          ((squareClass K qx * integralSpinorNorm T.leftIsometry) *
              (squareClass K qy * integralSpinorNorm T.rightIsometry)) *
              (squareClass K qx * squareClass K qy) =
            integralSpinorNorm T.leftIsometry *
              integralSpinorNorm T.rightIsometry := by
        calc
          _ = (squareClass K qx * squareClass K qx) *
                (squareClass K qy * squareClass K qy) *
                (integralSpinorNorm T.leftIsometry *
                  integralSpinorNorm T.rightIsometry) := by
              ac_rfl
          _ = _ := by rw [hqxSq, hqySq]; simp
      rw [hrearrange] at htotal
      have hmodelUnit : modelRotation.spinorNorm ∈
          valuationUnitSquareClassSubgroup K := by
        change integralSpinorNorm
            modelRotation.toIntegralOrthogonalGroup ∈
          valuationUnitSquareClassSubgroup K
        rw [← T.stabilized_spinorNorm_eq,
          T.spinorNorm_left_mul_right]
        exact htotal
      rw [← hconjugate]
      exact hmodelUnit
  · exact
      valuationUnitSquareClassSubgroup_le_spinorNormImageSubgroup_of_hyperbolicSplitting
        S

end Lattice

/-- Beli (2003), Lemma 7.1 over every dyadic local field, with no remaining
local-law hypothesis. -/
noncomputable instance beliLemma71LawsProved : BeliLemma71Laws.{u, v} K where
  component_norm_orders_modEq D N hunit i j :=
    Lattice.beliLemma71_i_proved D N hunit i j
  spinorNorm_eq_unit_of_hyperbolic_splitting S hunit hparity :=
    Lattice.beliLemma71_ii_same_proved S hunit hparity
  spinorNorm_eq_top_of_hyperbolic_splitting S hunit hparity :=
    Lattice.beliLemma71_ii_different_proved S hunit hparity

end Bong
