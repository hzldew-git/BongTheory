/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma95Jordan
import Bong.Bong.BeliLemma47Proof
import Bong.Bong.Beli2009JordanWeightOrderProof
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Bong.BinaryDiagonalModelBONG
import Bong.Bong.BinaryStrictModular
import Bong.Bong.BinaryModularInvariant
import Bong.Bong.UnaryModelBONG
import Bong.Lattice.DiagonalModular
import Bong.Lattice.JordanAmalgamation
import Bong.Lattice.ModularOrthogonalProduct
import Bong.Lattice.ModularParameter
import Bong.Lattice.ModularDecompositionSort
import Bong.Lattice.OrthogonalProductDecomposition

namespace Bong

open Dyadic
open Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The standard integral line with coefficient `a` is `a`-modular. -/
theorem unaryModel_isModular (a : Kˣ) :
    Lattice.IsModular
      (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K))
      (unaryModelLattice (K := K)) a := by
  let q := QuadraticSpace.rescaleUnit a (QuadraticSpace.line K)
  let b := Basis.singleton Unit K
  have horth : q.bilin.iIsOrtho b := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hne : ∀ i, q.quadratic (b i) ≠ 0 := by
    intro i
    have hi : i = () := Subsingleton.elim i ()
    subst i
    simp [q, b, QuadraticSpace.quadratic]
  have horder : ∀ i,
      ordUnit K (Units.mk0 (q.quadratic (b i)) (hne i)) =
        ordUnit K a := by
    intro i
    have hi : i = () := Subsingleton.elim i ()
    subst i
    apply congrArg (ordUnit K)
    apply Units.ext
    simp [q, b, QuadraticSpace.quadratic]
  simpa [q, b, unaryModelLattice] using
    Lattice.isModular_basisLattice_of_iIsOrtho_of_orders_eq
      q b horth hne a horder

namespace UnaryBinaryJordanData

variable [BONGGoodExistenceLaws.{u, u} K]
  [Beli2009WeightIdealData.{u, u} K]
  {head first second : Kˣ}
  {hadmissible : IsBinaryParameterAdmissible (second / first)}

/-- The coefficient constraints force the binary factor to lie in the
nonpositive order-gap branch. -/
theorem binaryOrderGap_nonpos
    (D : UnaryBinaryJordanData head first second hadmissible) :
    (binaryDiagonalModelBONG first second hadmissible).binaryOrderGap ≤ 0 := by
  have hα : 0 ≤ D.alpha := D.alpha_nonnegative
  have hαdual : 0 ≤ D.alpha + 2 * D.radius :=
    D.dual_alpha_nonnegative
  rw [binaryOrderGap,
    binaryDiagonalModelBONG_order_zero,
    binaryDiagonalModelBONG_order_one,
    D.first_order, D.second_order]
  omega

/-- A canonical modular scale parameter for the binary factor. -/
noncomputable def binaryScaleGenerator
    (D : UnaryBinaryJordanData head first second hadmissible) : Kˣ :=
  Classical.choose <|
    (binaryDiagonalModelBONG first second hadmissible)
      |>.exists_isModular_of_binaryOrderGap_nonpos D.binaryOrderGap_nonpos

theorem binaryScaleGenerator_isModular
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsModular
      (binaryDiagonalModelSpace first second hadmissible)
      (binaryDiagonalModelLattice (K := K))
      D.binaryScaleGenerator :=
  Classical.choose_spec <|
    (binaryDiagonalModelBONG first second hadmissible)
      |>.exists_isModular_of_binaryOrderGap_nonpos D.binaryOrderGap_nonpos

/-- The binary modular scale has the paper's center order. -/
theorem binaryScaleGenerator_order
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K D.binaryScaleGenerator = D.center := by
  have hsum :=
    (binaryDiagonalModelBONG first second hadmissible)
      |>.two_mul_modularOrder_eq_order_add D.binaryScaleGenerator
        D.binaryScaleGenerator_isModular
  rw [binaryDiagonalModelBONG_order_zero,
    binaryDiagonalModelBONG_order_one,
    D.first_order, D.second_order] at hsum
  omega

/-- The visible unary and binary factors, before sorting by scale, form a
modular decomposition of the explicit model. -/
noncomputable def modularDecomposition
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.ModularDecomposition
      (unaryBinaryModelSpace head first second hadmissible)
      (unaryBinaryModelLattice (K := K)) 2 where
  toOrthogonalDecomposition :=
    Lattice.orthogonalProductDecomposition
      (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
      (binaryDiagonalModelSpace first second hadmissible)
      (unaryModelLattice (K := K))
      (binaryDiagonalModelLattice (K := K))
  scaleGenerator := ![head, D.binaryScaleGenerator]
  modular := by
    intro i
    fin_cases i
    · exact (unaryModel_isModular head).mapLatticeIsometry
        (Lattice.orthogonalProductLeftComponentIsometry
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (binaryDiagonalModelSpace first second hadmissible)
          (unaryModelLattice (K := K)))
    · exact D.binaryScaleGenerator_isModular.mapLatticeIsometry
        (Lattice.orthogonalProductRightComponentIsometry
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelLattice (K := K)))
  component_finrank_pos := by
    intro i
    fin_cases i
    · have h := LinearEquiv.finrank_eq
        (Lattice.orthogonalProductLeftCarrierEquiv
          (K := K) (V := K) (W := Fin 2 → K))
      change 0 < finrank K
        (Lattice.orthogonalProductLeftCarrier
          (K := K) (V := K) (W := Fin 2 → K))
      rw [← h]
      simp
    · have h := LinearEquiv.finrank_eq
        (Lattice.orthogonalProductRightCarrierEquiv
          (K := K) (V := K) (W := Fin 2 → K))
      change 0 < finrank K
        (Lattice.orthogonalProductRightCarrier
          (K := K) (V := K) (W := Fin 2 → K))
      rw [← h]
      simp

@[simp]
theorem modularDecomposition_scale_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.modularDecomposition.scaleGenerator 0 = head := rfl

@[simp]
theorem modularDecomposition_scale_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.modularDecomposition.scaleGenerator 1 = D.binaryScaleGenerator := rfl

theorem modularDecomposition_scaleOrder_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K (D.modularDecomposition.scaleGenerator 0) =
      D.center + D.radius := by
  rw [D.modularDecomposition_scale_zero, D.head_order]

theorem modularDecomposition_scaleOrder_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K (D.modularDecomposition.scaleGenerator 1) = D.center := by
  rw [D.modularDecomposition_scale_one,
    D.binaryScaleGenerator_order]

/-- The unary component norm ideal is generated by `head`. -/
theorem modularDecomposition_normIdeal_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.normIdeal
        (D.modularDecomposition.component 0).space
        (D.modularDecomposition.component 0).lattice =
      Lattice.principalIdeal (K := K) (head : K) := by
  let q₀ := QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)
  let q₁ := binaryDiagonalModelSpace first second hadmissible
  let L₀ := unaryModelLattice (K := K)
  let f := Lattice.orthogonalProductLeftComponentIsometry q₀ q₁ L₀
  have hfactor : Lattice.normIdeal q₀ L₀ =
      Lattice.principalIdeal (K := K) (head : K) := by
    have h := (unaryModelBONG head).head_isNormGenerator.normIdeal_eq
    calc
      Lattice.normIdeal q₀ L₀ =
          Lattice.principalIdeal (K := K)
            ((QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)).quadratic
              (unaryModelBONG head).head) := by
        simpa [q₀, L₀] using h
      _ = Lattice.principalIdeal (K := K) (head : K) := by
        congr 1
        rw [← (unaryModelBONG head).value_zero_eq_quadratic_head,
          unaryModelBONG_value]
  calc
    Lattice.normIdeal
        (D.modularDecomposition.component 0).space
        (D.modularDecomposition.component 0).lattice =
        Lattice.normIdeal
          (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).space
          (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).lattice := by
      rfl
    _ = Lattice.normIdeal q₀ L₀ := by
      rw [show
        (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).lattice =
          Lattice.map f.toLinearEquiv L₀ by
            exact f.map_eq.symm]
      exact Lattice.normIdeal_map_isometry
        f.toQuadraticSpaceIsometry L₀
    _ = Lattice.principalIdeal (K := K) (head : K) := hfactor

/-- The binary component norm ideal is generated by `first`. -/
theorem modularDecomposition_normIdeal_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.normIdeal
        (D.modularDecomposition.component 1).space
        (D.modularDecomposition.component 1).lattice =
      Lattice.principalIdeal (K := K) (first : K) := by
  let q₀ := QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)
  let q₁ := binaryDiagonalModelSpace first second hadmissible
  let L₁ := binaryDiagonalModelLattice (K := K)
  let f := Lattice.orthogonalProductRightComponentIsometry q₀ q₁ L₁
  have hfactor : Lattice.normIdeal q₁ L₁ =
      Lattice.principalIdeal (K := K) (first : K) := by
    have h := (binaryDiagonalModelBONG first second hadmissible)
      |>.valueUnit_zero_isNormGeneratorValue
    simpa [q₁, L₁] using h.2
  calc
    Lattice.normIdeal
        (D.modularDecomposition.component 1).space
        (D.modularDecomposition.component 1).lattice =
        Lattice.normIdeal
          (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).space
          (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).lattice := by
      rfl
    _ = Lattice.normIdeal q₁ L₁ := by
      rw [show
        (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).lattice =
          Lattice.map f.toLinearEquiv L₁ by
            exact f.map_eq.symm]
      exact Lattice.normIdeal_map_isometry
        f.toQuadraticSpaceIsometry L₁
    _ = Lattice.principalIdeal (K := K) (first : K) := hfactor

/-- The displayed unary coefficient is a scalar norm generator of the unary
component in the orthogonal-product decomposition. -/
theorem modularDecomposition_normGeneratorValue_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsNormGeneratorValue
      (D.modularDecomposition.component 0).space
      (D.modularDecomposition.component 0).lattice head := by
  let q₀ := QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)
  let q₁ := binaryDiagonalModelSpace first second hadmissible
  let L₀ := unaryModelLattice (K := K)
  let f := Lattice.orthogonalProductLeftComponentIsometry q₀ q₁ L₀
  change Lattice.IsNormGeneratorValue
    (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).space
    (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).lattice head
  have hgen := (unaryModelBONG head).head_isNormGenerator.mapLatticeIsometry f
  have hquad :
      (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).space.quadratic
          (f.toLinearEquiv (unaryModelBONG head).head) = (head : K) := by
    calc
      _ = q₀.quadratic (unaryModelBONG head).head :=
        f.map_bilin (unaryModelBONG head).head (unaryModelBONG head).head
      _ = (head : K) := by
        rw [← (unaryModelBONG head).value_zero_eq_quadratic_head,
          unaryModelBONG_value]
  have hne :
      (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).space.quadratic
          (f.toLinearEquiv (unaryModelBONG head).head) ≠ 0 := by
    rw [hquad]
    exact Units.ne_zero head
  have hvalue := hgen.isNormGeneratorValue hne
  have hunit : Units.mk0
      ((Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).space.quadratic
        (f.toLinearEquiv (unaryModelBONG head).head)) hne = head := by
    apply Units.ext
    exact hquad
  simpa only [hunit] using hvalue

/-- The first displayed binary coefficient is a scalar norm generator of the
binary component in the orthogonal-product decomposition. -/
theorem modularDecomposition_normGeneratorValue_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsNormGeneratorValue
      (D.modularDecomposition.component 1).space
      (D.modularDecomposition.component 1).lattice first := by
  let q₀ := QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)
  let q₁ := binaryDiagonalModelSpace first second hadmissible
  let L₁ := binaryDiagonalModelLattice (K := K)
  let f := Lattice.orthogonalProductRightComponentIsometry q₀ q₁ L₁
  change Lattice.IsNormGeneratorValue
    (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).space
    (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).lattice first
  have hgen :=
    (binaryDiagonalModelBONG first second hadmissible).head_isNormGenerator
      |>.mapLatticeIsometry f
  have hquad :
      (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).space.quadratic
          (f.toLinearEquiv
            (binaryDiagonalModelBONG first second hadmissible).head) =
        (first : K) := by
    calc
      _ = q₁.quadratic
          (binaryDiagonalModelBONG first second hadmissible).head :=
        f.map_bilin
          (binaryDiagonalModelBONG first second hadmissible).head
          (binaryDiagonalModelBONG first second hadmissible).head
      _ = (first : K) := by
        rw [← (binaryDiagonalModelBONG first second hadmissible)
          |>.value_zero_eq_quadratic_head,
          binaryDiagonalModelBONG_value_zero]
  have hne :
      (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).space.quadratic
          (f.toLinearEquiv
            (binaryDiagonalModelBONG first second hadmissible).head) ≠ 0 := by
    rw [hquad]
    exact Units.ne_zero first
  have hvalue := hgen.isNormGeneratorValue hne
  have hunit : Units.mk0
      ((Lattice.orthogonalProductRightComponent q₀ q₁ L₁).space.quadratic
        (f.toLinearEquiv
          (binaryDiagonalModelBONG first second hadmissible).head)) hne = first := by
    apply Units.ext
    exact hquad
  simpa only [hunit] using hvalue

/-- For nonnegative radius the unary coefficient has the smallest norm order,
so it is a scalar norm generator of the full unary--binary lattice. -/
theorem ambient_normGeneratorValue_head
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsNormGeneratorValue
      (unaryBinaryModelSpace head first second hadmissible)
      (unaryBinaryModelLattice (K := K)) head := by
  constructor
  · refine ⟨((1 : K), (0 : Fin 2 → K)), unaryBinaryModel_head_mem,
      0, Submodule.zero_mem _, ?_⟩
    simp
  · rw [D.modularDecomposition.toOrthogonalDecomposition
      |>.normIdeal_eq_iSup_component,
      Lattice.iSup_fin_two_eq_sup,
      D.modularDecomposition_normIdeal_zero,
      D.modularDecomposition_normIdeal_one,
      sup_eq_left]
    apply (Lattice.principalIdeal_le_iff_ord_ge
      (Units.ne_zero first) (Units.ne_zero head)).2
    rw [← coe_ordUnit, ← coe_ordUnit, D.head_order, D.first_order]
    norm_cast
    have hα := D.alpha_nonnegative
    omega

/-- The unary component has weight order `ord(head) + e`, independently of
the chosen good BONG used to invoke Beli (2009), Lemma 2.14 in rank one. -/
theorem modularDecomposition_weightOrder_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.weightIdealOrder
        (D.modularDecomposition.component 0).space
        (D.modularDecomposition.component 0).lattice =
      D.center + D.radius + (ramificationIndex K : Int) := by
  let bRaw := Classical.choice <| exists_good_bong
    (D.modularDecomposition.component 0).space
    (D.modularDecomposition.component 0).lattice
  have hrank : finrank K
      (D.modularDecomposition.component 0).carrier = 1 := by
    have h := LinearEquiv.finrank_eq
      (Lattice.orthogonalProductLeftCarrierEquiv
        (K := K) (V := K) (W := Fin 2 → K))
    change finrank K
        (Lattice.orthogonalProductLeftCarrier
          (K := K) (V := K) (W := Fin 2 → K)) = 1
    rw [← h]
    simp
  let b := bRaw.castLength hrank
  have hweight := b.weightIdealOrder_unary_proof
  have hvalueOrder : ordUnit K (b.toBONG.valueUnit 0) = ordUnit K head := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    calc
      Lattice.principalIdeal (K := K) (b.toBONG.valueUnit 0 : K) =
          Lattice.normIdeal
            (D.modularDecomposition.component 0).space
            (D.modularDecomposition.component 0).lattice := by
        rw [b.toBONG.coe_valueUnit,
          b.toBONG.value_zero_eq_quadratic_head]
        exact b.toBONG.head_isNormGenerator.normIdeal_eq.symm
      _ = Lattice.principalIdeal (K := K) (head : K) :=
        D.modularDecomposition_normIdeal_zero
  rw [GoodBONG.order, b.toBONG.order_eq_ordUnit,
    hvalueOrder, D.head_order] at hweight
  exact hweight

/-- Rank-one weight order expressed through any scalar norm generator. -/
theorem weightIdealOrder_rankOne_of_isNormGeneratorValue
    {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hrank : finrank K V = 1) (a : Kˣ)
    (ha : Lattice.IsNormGeneratorValue q L a) :
    Lattice.weightIdealOrder q L =
      ordUnit K a + (ramificationIndex K : Int) := by
  let bRaw := Classical.choice <| exists_good_bong q L
  let b := bRaw.castLength hrank
  have hweight := b.weightIdealOrder_unary_proof
  have hvalueOrder : ordUnit K (b.toBONG.valueUnit 0) = ordUnit K a := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    calc
      Lattice.principalIdeal (K := K) (b.toBONG.valueUnit 0 : K) =
          Lattice.normIdeal q L := by
        rw [b.toBONG.coe_valueUnit,
          b.toBONG.value_zero_eq_quadratic_head]
        exact b.toBONG.head_isNormGenerator.normIdeal_eq.symm
      _ = Lattice.principalIdeal (K := K) (a : K) := ha.2
  rw [GoodBONG.order, b.toBONG.order_eq_ordUnit, hvalueOrder] at hweight
  exact hweight

/-- When the radius is nonnegative, the binary factor has the smallest scale
and hence generates the scale ideal of the whole orthogonal product. -/
theorem scaleIdeal_eq_principal_binaryScale_of_radius_nonnegative
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 ≤ D.radius) :
    Lattice.scaleIdeal
        (unaryBinaryModelSpace head first second hadmissible)
        (unaryBinaryModelLattice (K := K)) =
      Lattice.principalIdeal (K := K) (D.binaryScaleGenerator : K) := by
  rw [D.modularDecomposition.toOrthogonalDecomposition
      |>.scaleIdeal_eq_iSup_component,
    Lattice.iSup_fin_two_eq_sup,
    (D.modularDecomposition.modular 0).scaleIdeal_eq_principal
      (D.modularDecomposition.component_finrank_pos 0),
    (D.modularDecomposition.modular 1).scaleIdeal_eq_principal
      (D.modularDecomposition.component_finrank_pos 1),
    D.modularDecomposition_scale_zero,
    D.modularDecomposition_scale_one,
    sup_eq_right]
  apply (Lattice.principalIdeal_le_iff_ord_ge
    (Units.ne_zero head) (Units.ne_zero D.binaryScaleGenerator)).2
  rw [← coe_ordUnit, ← coe_ordUnit,
    D.binaryScaleGenerator_order, D.head_order]
  norm_cast
  omega

/-- Consequently the ambient `2sL` term has order `center + e`. -/
theorem twoScaleIdeal_eq_powerIdeal_of_radius_nonnegative
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 ≤ D.radius) :
    Lattice.twoScaleIdeal
        (unaryBinaryModelSpace head first second hadmissible)
        (unaryBinaryModelLattice (K := K)) =
      Lattice.powerIdeal (K := K)
        (D.center + (ramificationIndex K : Int)) := by
  rw [Lattice.twoScaleIdeal,
    D.scaleIdeal_eq_principal_binaryScale_of_radius_nonnegative hradius,
    Lattice.twicePrincipalIdeal_eq_powerIdeal,
    D.binaryScaleGenerator_order]

/-- The chosen norm generator at the sorted position of the unary factor has
the expected order. -/
theorem sortedWeakJordan_unaryNormOrder
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K
        (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
          (D.modularDecomposition.sortedReindex.equiv.symm 0)) =
      D.center + D.radius := by
  rw [← D.head_order]
  apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    Lattice.principalIdeal (K := K)
        (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
          (D.modularDecomposition.sortedReindex.equiv.symm 0) : K) =
        Lattice.normIdeal
          (D.modularDecomposition.sortedWeakJordan.component
            (D.modularDecomposition.sortedReindex.equiv.symm 0)).space
          (D.modularDecomposition.sortedWeakJordan.component
            (D.modularDecomposition.sortedReindex.equiv.symm 0)).lattice :=
      (D.modularDecomposition.sortedWeakJordan
        |>.normIdeal_eq_normGeneratorUnit _).symm
    _ = Lattice.normIdeal
          (D.modularDecomposition.component 0).space
          (D.modularDecomposition.component 0).lattice := by
      rw [D.modularDecomposition.sortedWeakJordan_component_at_old]
    _ = Lattice.principalIdeal (K := K) (head : K) :=
      D.modularDecomposition_normIdeal_zero

/-- The chosen norm generator at the sorted position of the binary factor has
the order of `first`. -/
theorem sortedWeakJordan_binaryNormOrder
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K
        (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
          (D.modularDecomposition.sortedReindex.equiv.symm 1)) =
      D.center + D.radius + D.alpha := by
  rw [← D.first_order]
  apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    Lattice.principalIdeal (K := K)
        (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
          (D.modularDecomposition.sortedReindex.equiv.symm 1) : K) =
        Lattice.normIdeal
          (D.modularDecomposition.sortedWeakJordan.component
            (D.modularDecomposition.sortedReindex.equiv.symm 1)).space
          (D.modularDecomposition.sortedWeakJordan.component
            (D.modularDecomposition.sortedReindex.equiv.symm 1)).lattice :=
      (D.modularDecomposition.sortedWeakJordan
        |>.normIdeal_eq_normGeneratorUnit _).symm
    _ = Lattice.normIdeal
          (D.modularDecomposition.component 1).space
          (D.modularDecomposition.component 1).lattice := by
      rw [D.modularDecomposition.sortedWeakJordan_component_at_old]
    _ = Lattice.principalIdeal (K := K) (first : K) :=
      D.modularDecomposition_normIdeal_one

/-- For nonpositive radius the default scale sort keeps the unary factor
before the binary factor. -/
theorem sortedReindex_positions_of_radius_nonpositive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius ≤ 0) :
    D.modularDecomposition.sortedReindex.equiv.symm 0 = 0 ∧
      D.modularDecomposition.sortedReindex.equiv.symm 1 = 1 := by
  let M := D.modularDecomposition
  let S := M.sortedReindex
  have hkey : Lattice.ModularDecomposition.ScaleIndex.key M S.tie ⟨0⟩ <
      Lattice.ModularDecomposition.ScaleIndex.key M S.tie ⟨1⟩ := by
    rw [Lattice.ModularDecomposition.sortedReindex_tie]
    apply Prod.Lex.lt_iff'.2
    by_cases hrzero : D.radius = 0
    · constructor
      · change ordUnit K (M.scaleGenerator 0) ≤
          ordUnit K (M.scaleGenerator 1)
        rw [show M = D.modularDecomposition by rfl,
          D.modularDecomposition_scaleOrder_zero,
          D.modularDecomposition_scaleOrder_one]
        omega
      · intro _
        change (0 : Nat) < 1
        omega
    · constructor
      · change ordUnit K (M.scaleGenerator 0) ≤
          ordUnit K (M.scaleGenerator 1)
        rw [show M = D.modularDecomposition by rfl,
          D.modularDecomposition_scaleOrder_zero,
          D.modularDecomposition_scaleOrder_one]
        omega
      · intro heq
        change ordUnit K (M.scaleGenerator 0) =
          ordUnit K (M.scaleGenerator 1) at heq
        rw [show M = D.modularDecomposition by rfl,
          D.modularDecomposition_scaleOrder_zero,
          D.modularDecomposition_scaleOrder_one] at heq
        omega
  have hpos : S.equiv.symm 0 < S.equiv.symm 1 :=
    (S.oldPosition_lt_iff M 0 1).2 hkey
  generalize hx : S.equiv.symm 0 = x at hpos ⊢
  generalize hy : S.equiv.symm 1 = y at hpos ⊢
  fin_cases x <;> fin_cases y <;> simp_all

/-- For positive radius the binary factor has smaller scale and therefore
appears first after sorting. -/
theorem sortedReindex_positions_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    D.modularDecomposition.sortedReindex.equiv.symm 1 = 0 ∧
      D.modularDecomposition.sortedReindex.equiv.symm 0 = 1 := by
  let M := D.modularDecomposition
  let S := M.sortedReindex
  have hkey : Lattice.ModularDecomposition.ScaleIndex.key M S.tie ⟨1⟩ <
      Lattice.ModularDecomposition.ScaleIndex.key M S.tie ⟨0⟩ := by
    apply Prod.Lex.lt_iff'.2
    constructor
    · change ordUnit K (M.scaleGenerator 1) ≤
        ordUnit K (M.scaleGenerator 0)
      rw [show M = D.modularDecomposition by rfl,
        D.modularDecomposition_scaleOrder_one,
        D.modularDecomposition_scaleOrder_zero]
      omega
    · intro heq
      change ordUnit K (M.scaleGenerator 1) =
        ordUnit K (M.scaleGenerator 0) at heq
      rw [show M = D.modularDecomposition by rfl,
        D.modularDecomposition_scaleOrder_one,
        D.modularDecomposition_scaleOrder_zero] at heq
      omega
  have hpos : S.equiv.symm 1 < S.equiv.symm 0 :=
    (S.oldPosition_lt_iff M 1 0).2 hkey
  generalize hx : S.equiv.symm 1 = x at hpos ⊢
  generalize hy : S.equiv.symm 0 = y at hpos ⊢
  fin_cases x <;> fin_cases y <;> simp_all

theorem modularDecomposition_componentRank_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.modularDecomposition.toOrthogonalDecomposition.componentRank 0 = 1 := by
  have h := LinearEquiv.finrank_eq
    (Lattice.orthogonalProductLeftCarrierEquiv
      (K := K) (V := K) (W := Fin 2 → K))
  change finrank K
      (Lattice.orthogonalProductLeftCarrier
        (K := K) (V := K) (W := Fin 2 → K)) = 1
  rw [← h]
  simp

theorem modularDecomposition_componentRank_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.modularDecomposition.toOrthogonalDecomposition.componentRank 1 = 2 := by
  have h := LinearEquiv.finrank_eq
    (Lattice.orthogonalProductRightCarrierEquiv
      (K := K) (V := K) (W := Fin 2 → K))
  change finrank K
      (Lattice.orthogonalProductRightCarrier
        (K := K) (V := K) (W := Fin 2 → K)) = 2
  rw [← h]
  simp

theorem sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius ≤ 0) :
    ordUnit K (D.modularDecomposition.sortedWeakJordan.scaleGenerator 0) =
      D.center + D.radius := by
  have h := D.modularDecomposition.sortedWeakJordan_scaleGenerator_at_old 0
  rw [(D.sortedReindex_positions_of_radius_nonpositive hradius).1] at h
  rw [h, D.modularDecomposition_scaleOrder_zero]

theorem sortedWeakJordan_scaleOrder_one_of_radius_nonpositive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius ≤ 0) :
    ordUnit K (D.modularDecomposition.sortedWeakJordan.scaleGenerator 1) =
      D.center := by
  have h := D.modularDecomposition.sortedWeakJordan_scaleGenerator_at_old 1
  rw [(D.sortedReindex_positions_of_radius_nonpositive hradius).2] at h
  rw [h, D.modularDecomposition_scaleOrder_one]

theorem sortedWeakJordan_normOrder_zero_of_radius_nonpositive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius ≤ 0) :
    ordUnit K
        (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit 0) =
      D.center + D.radius := by
  have h := D.sortedWeakJordan_unaryNormOrder
  rwa [(D.sortedReindex_positions_of_radius_nonpositive hradius).1] at h

theorem sortedWeakJordan_normOrder_one_of_radius_nonpositive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius ≤ 0) :
    ordUnit K
        (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit 1) =
      D.center + D.radius + D.alpha := by
  have h := D.sortedWeakJordan_binaryNormOrder
  rwa [(D.sortedReindex_positions_of_radius_nonpositive hradius).2] at h

theorem sortedWeakJordan_componentRank_zero_of_radius_nonpositive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius ≤ 0) :
    (D.modularDecomposition.sortedWeakJordan.toOrthogonalDecomposition
      |>.componentRank 0) = 1 := by
  have h := D.modularDecomposition.sortedWeakJordan_component_at_old 0
  rw [(D.sortedReindex_positions_of_radius_nonpositive hradius).1] at h
  change finrank K
      (D.modularDecomposition.sortedWeakJordan.component 0).carrier = 1
  rw [h]
  exact D.modularDecomposition_componentRank_zero

theorem sortedWeakJordan_componentRank_one_of_radius_nonpositive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius ≤ 0) :
    (D.modularDecomposition.sortedWeakJordan.toOrthogonalDecomposition
      |>.componentRank 1) = 2 := by
  have h := D.modularDecomposition.sortedWeakJordan_component_at_old 1
  rw [(D.sortedReindex_positions_of_radius_nonpositive hradius).2] at h
  change finrank K
      (D.modularDecomposition.sortedWeakJordan.component 1).carrier = 2
  rw [h]
  exact D.modularDecomposition_componentRank_one

theorem sortedWeakJordan_scaleOrder_zero_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    ordUnit K (D.modularDecomposition.sortedWeakJordan.scaleGenerator 0) =
      D.center := by
  have h := D.modularDecomposition.sortedWeakJordan_scaleGenerator_at_old 1
  rw [(D.sortedReindex_positions_of_radius_positive hradius).1] at h
  rw [h, D.modularDecomposition_scaleOrder_one]

theorem sortedWeakJordan_scaleOrder_one_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    ordUnit K (D.modularDecomposition.sortedWeakJordan.scaleGenerator 1) =
      D.center + D.radius := by
  have h := D.modularDecomposition.sortedWeakJordan_scaleGenerator_at_old 0
  rw [(D.sortedReindex_positions_of_radius_positive hradius).2] at h
  rw [h, D.modularDecomposition_scaleOrder_zero]

theorem sortedWeakJordan_normOrder_zero_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    ordUnit K
        (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit 0) =
      D.center + D.radius + D.alpha := by
  have h := D.sortedWeakJordan_binaryNormOrder
  rwa [(D.sortedReindex_positions_of_radius_positive hradius).1] at h

theorem sortedWeakJordan_normOrder_one_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    ordUnit K
        (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit 1) =
      D.center + D.radius := by
  have h := D.sortedWeakJordan_unaryNormOrder
  rwa [(D.sortedReindex_positions_of_radius_positive hradius).2] at h

theorem sortedWeakJordan_componentRank_zero_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    (D.modularDecomposition.sortedWeakJordan.toOrthogonalDecomposition
      |>.componentRank 0) = 2 := by
  have h := D.modularDecomposition.sortedWeakJordan_component_at_old 1
  rw [(D.sortedReindex_positions_of_radius_positive hradius).1] at h
  change finrank K
      (D.modularDecomposition.sortedWeakJordan.component 0).carrier = 2
  rw [h]
  exact D.modularDecomposition_componentRank_one

theorem sortedWeakJordan_componentRank_one_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    (D.modularDecomposition.sortedWeakJordan.toOrthogonalDecomposition
      |>.componentRank 1) = 1 := by
  have h := D.modularDecomposition.sortedWeakJordan_component_at_old 0
  rw [(D.sortedReindex_positions_of_radius_positive hradius).2] at h
  change finrank K
      (D.modularDecomposition.sortedWeakJordan.component 1).carrier = 1
  rw [h]
  exact D.modularDecomposition_componentRank_zero

theorem sortedWeakJordan_scaleOrder_strict_of_radius_negative
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0) :
    StrictMono (fun i ↦ ordUnit K
      (D.modularDecomposition.sortedWeakJordan.scaleGenerator i)) := by
  apply (Fin.strictMono_iff_lt_succ).2
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  change ordUnit K
      (D.modularDecomposition.sortedWeakJordan.scaleGenerator (0 : Fin 2)) <
    ordUnit K
      (D.modularDecomposition.sortedWeakJordan.scaleGenerator (1 : Fin 2))
  rw [D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le,
    D.sortedWeakJordan_scaleOrder_one_of_radius_nonpositive hradius.le]
  omega

theorem sortedWeakJordan_scaleOrder_strict_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    StrictMono (fun i ↦ ordUnit K
      (D.modularDecomposition.sortedWeakJordan.scaleGenerator i)) := by
  apply (Fin.strictMono_iff_lt_succ).2
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  change ordUnit K
      (D.modularDecomposition.sortedWeakJordan.scaleGenerator (0 : Fin 2)) <
    ordUnit K
      (D.modularDecomposition.sortedWeakJordan.scaleGenerator (1 : Fin 2))
  rw [D.sortedWeakJordan_scaleOrder_zero_of_radius_positive hradius,
    D.sortedWeakJordan_scaleOrder_one_of_radius_positive hradius]
  omega

theorem sortedWeakJordan_effective_zero_of_radius_negative
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0) :
    D.modularDecomposition.sortedWeakJordan.effectiveNormOrderAt 0
        (ordUnit K
          (D.modularDecomposition.sortedWeakJordan.scaleGenerator 0)) =
      D.center + D.radius := by
  rw [D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le]
  let W := D.modularDecomposition.sortedWeakJordan
  apply le_antisymm
  · have h := W.effectiveNormOrderAt_scale_le_normOrder (0 : Fin 2)
    rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
      D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le,
      D.sortedWeakJordan_normOrder_zero_of_radius_nonpositive hradius.le] at h
    exact h
  · have h := W.targetScale_le_effectiveNormOrderAt (0 : Fin 2)
      (D.center + D.radius)
    exact h

theorem sortedWeakJordan_effective_one_of_radius_negative
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0) :
    D.modularDecomposition.sortedWeakJordan.effectiveNormOrderAt 1
        (ordUnit K
          (D.modularDecomposition.sortedWeakJordan.scaleGenerator 1)) =
      D.center - D.radius := by
  rw [D.sortedWeakJordan_scaleOrder_one_of_radius_nonpositive hradius.le]
  let W := D.modularDecomposition.sortedWeakJordan
  change JordanProfileOrder.effectiveAt W.scaleOrderFamily W.normOrderFamily
      1 D.center = D.center - D.radius
  apply le_antisymm
  · have h := JordanProfileOrder.effectiveAt_le W.scaleOrderFamily
      W.normOrderFamily (1 : Fin 2) (0 : Fin 2)
      D.center
    simp only [Lattice.WeakJordanDecomposition.scaleOrderFamily,
      Lattice.WeakJordanDecomposition.normOrderFamily,
      JordanProfileOrder.adjustedAt] at h
    rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
      D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le,
      D.sortedWeakJordan_normOrder_zero_of_radius_nonpositive hradius.le] at h
    simp only [if_pos (by omega : D.center + D.radius < D.center)] at h
    have h' : JordanProfileOrder.effectiveAt
        D.modularDecomposition.sortedWeakJordan.scaleOrderFamily
        D.modularDecomposition.sortedWeakJordan.normOrderFamily 1 D.center ≤
      D.center - D.radius := by omega
    simpa only [W] using h'
  · apply JordanProfileOrder.le_effectiveAt
    intro j
    simp only [Lattice.WeakJordanDecomposition.scaleOrderFamily,
      Lattice.WeakJordanDecomposition.normOrderFamily,
      JordanProfileOrder.adjustedAt]
    fin_cases j
    · change D.center - D.radius ≤
        if ordUnit K
            (D.modularDecomposition.sortedWeakJordan.scaleGenerator
              (0 : Fin 2)) < D.center then
          ordUnit K
              (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
                (0 : Fin 2)) +
            2 * (D.center - ordUnit K
              (D.modularDecomposition.sortedWeakJordan.scaleGenerator
                (0 : Fin 2)))
        else ordUnit K
          (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
            (0 : Fin 2))
      rw [D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le,
        D.sortedWeakJordan_normOrder_zero_of_radius_nonpositive hradius.le]
      simp only [if_pos (by omega : D.center + D.radius < D.center)]
      omega
    · change D.center - D.radius ≤
        if ordUnit K
            (D.modularDecomposition.sortedWeakJordan.scaleGenerator
              (1 : Fin 2)) < D.center then
          ordUnit K
              (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
                (1 : Fin 2)) +
            2 * (D.center - ordUnit K
              (D.modularDecomposition.sortedWeakJordan.scaleGenerator
                (1 : Fin 2)))
        else ordUnit K
          (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
            (1 : Fin 2))
      rw [D.sortedWeakJordan_scaleOrder_one_of_radius_nonpositive hradius.le,
        D.sortedWeakJordan_normOrder_one_of_radius_nonpositive hradius.le]
      simp
      have hdual := D.dual_alpha_nonnegative
      omega

theorem sortedWeakJordan_effective_zero_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    D.modularDecomposition.sortedWeakJordan.effectiveNormOrderAt 0
        (ordUnit K
          (D.modularDecomposition.sortedWeakJordan.scaleGenerator 0)) =
      D.center + D.radius := by
  rw [D.sortedWeakJordan_scaleOrder_zero_of_radius_positive hradius]
  let W := D.modularDecomposition.sortedWeakJordan
  change JordanProfileOrder.effectiveAt W.scaleOrderFamily W.normOrderFamily
      0 D.center = D.center + D.radius
  apply le_antisymm
  · have h := JordanProfileOrder.effectiveAt_le W.scaleOrderFamily
      W.normOrderFamily (0 : Fin 2) (1 : Fin 2)
      D.center
    simp only [Lattice.WeakJordanDecomposition.scaleOrderFamily,
      Lattice.WeakJordanDecomposition.normOrderFamily,
      JordanProfileOrder.adjustedAt] at h
    rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
      D.sortedWeakJordan_scaleOrder_one_of_radius_positive hradius,
      D.sortedWeakJordan_normOrder_one_of_radius_positive hradius] at h
    simp only [if_neg (by omega : ¬D.center + D.radius < D.center)] at h
    simpa only [W] using h
  · apply JordanProfileOrder.le_effectiveAt
    intro j
    simp only [Lattice.WeakJordanDecomposition.scaleOrderFamily,
      Lattice.WeakJordanDecomposition.normOrderFamily,
      JordanProfileOrder.adjustedAt]
    fin_cases j
    · change D.center + D.radius ≤
        if ordUnit K
            (D.modularDecomposition.sortedWeakJordan.scaleGenerator
              (0 : Fin 2)) < D.center then
          ordUnit K
              (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
                (0 : Fin 2)) +
            2 * (D.center - ordUnit K
              (D.modularDecomposition.sortedWeakJordan.scaleGenerator
                (0 : Fin 2)))
        else ordUnit K
          (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
            (0 : Fin 2))
      rw [D.sortedWeakJordan_scaleOrder_zero_of_radius_positive hradius,
        D.sortedWeakJordan_normOrder_zero_of_radius_positive hradius]
      simp
      have hα := D.alpha_nonnegative
      omega
    · change D.center + D.radius ≤
        if ordUnit K
            (D.modularDecomposition.sortedWeakJordan.scaleGenerator
              (1 : Fin 2)) < D.center then
          ordUnit K
              (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
                (1 : Fin 2)) +
            2 * (D.center - ordUnit K
              (D.modularDecomposition.sortedWeakJordan.scaleGenerator
                (1 : Fin 2)))
        else ordUnit K
          (D.modularDecomposition.sortedWeakJordan.normGeneratorUnit
            (1 : Fin 2))
      rw [D.sortedWeakJordan_scaleOrder_one_of_radius_positive hradius,
        D.sortedWeakJordan_normOrder_one_of_radius_positive hradius]
      simp only [if_neg (by omega : ¬D.center + D.radius < D.center)]
      exact le_rfl

theorem sortedWeakJordan_effective_one_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    D.modularDecomposition.sortedWeakJordan.effectiveNormOrderAt 1
        (ordUnit K
          (D.modularDecomposition.sortedWeakJordan.scaleGenerator 1)) =
      D.center + D.radius := by
  rw [D.sortedWeakJordan_scaleOrder_one_of_radius_positive hradius]
  let W := D.modularDecomposition.sortedWeakJordan
  apply le_antisymm
  · have h := W.effectiveNormOrderAt_scale_le_normOrder (1 : Fin 2)
    rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
      D.sortedWeakJordan_scaleOrder_one_of_radius_positive hradius,
      D.sortedWeakJordan_normOrder_one_of_radius_positive hradius] at h
    exact h
  · have h := W.targetScale_le_effectiveNormOrderAt (1 : Fin 2)
      (D.center + D.radius)
    exact h

/-- At zero radius, the common scale already occurs as the unary norm, so the
effective norm of the weak decomposition at that scale is the common scale. -/
theorem sortedWeakJordan_effective_zero_of_radius_zero
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius = 0) :
    D.modularDecomposition.sortedWeakJordan.effectiveNormOrderAt 0
        (ordUnit K
          (D.modularDecomposition.sortedWeakJordan.scaleGenerator 0)) =
      D.center := by
  rw [D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le]
  simp only [hradius, add_zero]
  let W := D.modularDecomposition.sortedWeakJordan
  apply le_antisymm
  · have h := W.effectiveNormOrderAt_scale_le_normOrder (0 : Fin 2)
    rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
      D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le,
      D.sortedWeakJordan_normOrder_zero_of_radius_nonpositive hradius.le,
      hradius, add_zero] at h
    exact h
  · exact W.targetScale_le_effectiveNormOrderAt (0 : Fin 2) D.center

/-- The Jordan profile in the negative-radius branch. -/
theorem order_profile_of_radius_negative
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0) :
    ∀ i, D.goodBONG.order i =
      ![D.center + D.radius, D.center - D.radius,
        D.center + D.radius] i := by
  let W := D.modularDecomposition.sortedWeakJordan
  let hstrict := D.sortedWeakJordan_scaleOrder_strict_of_radius_negative hradius
  let J := W.toJordan hstrict
  rcases D.goodBONG.toBONG.beliLemma47_profile D.goodBONG.good J with ⟨w⟩
  intro i
  fin_cases i
  · change D.goodBONG.order (0 : Fin 3) = D.center + D.radius
    let j : Fin (J.toOrthogonalDecomposition.componentRank 0) :=
      ⟨0, by
        change 0 < W.toOrthogonalDecomposition.componentRank 0
        rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
          D.sortedWeakJordan_componentRank_zero_of_radius_nonpositive
            hradius.le]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(0 : Fin 2), j⟩ = (0 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      simp [j]
    have horder := w.order_inverse_indexEquiv (0 : Fin 2) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (0 : Fin 3) =
        BONG.jordanExpectedOrder J 0 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder (W.toJordan hstrict) 0 j = _
    rw [W.jordanExpectedOrder_toJordan hstrict]
    have hscale : ordUnit K (W.scaleGenerator 0) =
        D.center + D.radius := by
      simpa [W] using
        D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le
    have heffective : W.effectiveNormOrderAt 0
        (ordUnit K (W.scaleGenerator 0)) = D.center + D.radius := by
      simpa [W] using D.sortedWeakJordan_effective_zero_of_radius_negative hradius
    rw [heffective, hscale]
    simp [JordanProfileOrder.localOrder, j]
  · change D.goodBONG.order (1 : Fin 3) = D.center - D.radius
    let j : Fin (J.toOrthogonalDecomposition.componentRank 1) :=
      ⟨0, by
        change 0 < W.toOrthogonalDecomposition.componentRank 1
        rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
          D.sortedWeakJordan_componentRank_one_of_radius_nonpositive
            hradius.le]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(1 : Fin 2), j⟩ = (1 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      have hIio : Finset.Iio (1 : Fin 2) = {(0 : Fin 2)} := by
        ext x
        fin_cases x <;> simp
      rw [hIio]
      simp only [Finset.sum_singleton, Fin.val_one, j]
      change W.toOrthogonalDecomposition.componentRank 0 = 1
      simpa [W] using
        D.sortedWeakJordan_componentRank_zero_of_radius_nonpositive hradius.le
    have horder := w.order_inverse_indexEquiv (1 : Fin 2) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (1 : Fin 3) =
        BONG.jordanExpectedOrder J 1 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder (W.toJordan hstrict) 1 j = _
    rw [W.jordanExpectedOrder_toJordan hstrict]
    have hscale : ordUnit K (W.scaleGenerator 1) = D.center := by
      simpa [W] using
        D.sortedWeakJordan_scaleOrder_one_of_radius_nonpositive hradius.le
    have heffective : W.effectiveNormOrderAt 1
        (ordUnit K (W.scaleGenerator 1)) = D.center - D.radius := by
      simpa [W] using D.sortedWeakJordan_effective_one_of_radius_negative hradius
    rw [heffective, hscale]
    simp [JordanProfileOrder.localOrder, j]
  · change D.goodBONG.order (2 : Fin 3) = D.center + D.radius
    let j : Fin (J.toOrthogonalDecomposition.componentRank 1) :=
      ⟨1, by
        change 1 < W.toOrthogonalDecomposition.componentRank 1
        rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
          D.sortedWeakJordan_componentRank_one_of_radius_nonpositive
            hradius.le]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(1 : Fin 2), j⟩ = (2 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      have hIio : Finset.Iio (1 : Fin 2) = {(0 : Fin 2)} := by
        ext x
        fin_cases x <;> simp
      rw [hIio]
      simp only [Finset.sum_singleton, Fin.val_one, j]
      change W.toOrthogonalDecomposition.componentRank 0 + 1 = 2
      have hrank : W.toOrthogonalDecomposition.componentRank 0 = 1 := by
        simpa [W] using
          D.sortedWeakJordan_componentRank_zero_of_radius_nonpositive hradius.le
      omega
    have horder := w.order_inverse_indexEquiv (1 : Fin 2) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (2 : Fin 3) =
        BONG.jordanExpectedOrder J 1 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder (W.toJordan hstrict) 1 j = _
    rw [W.jordanExpectedOrder_toJordan hstrict]
    have hscale : ordUnit K (W.scaleGenerator 1) = D.center := by
      simpa [W] using
        D.sortedWeakJordan_scaleOrder_one_of_radius_nonpositive hradius.le
    have heffective : W.effectiveNormOrderAt 1
        (ordUnit K (W.scaleGenerator 1)) = D.center - D.radius := by
      simpa [W] using D.sortedWeakJordan_effective_one_of_radius_negative hradius
    rw [heffective, hscale]
    simp [JordanProfileOrder.localOrder, j]
    omega

/-- The Jordan profile in the positive-radius branch. -/
theorem order_profile_of_radius_positive
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 < D.radius) :
    ∀ i, D.goodBONG.order i =
      ![D.center + D.radius, D.center - D.radius,
        D.center + D.radius] i := by
  let W := D.modularDecomposition.sortedWeakJordan
  let hstrict := D.sortedWeakJordan_scaleOrder_strict_of_radius_positive hradius
  let J := W.toJordan hstrict
  rcases D.goodBONG.toBONG.beliLemma47_profile D.goodBONG.good J with ⟨w⟩
  intro i
  fin_cases i
  · change D.goodBONG.order (0 : Fin 3) = D.center + D.radius
    let j : Fin (J.toOrthogonalDecomposition.componentRank 0) :=
      ⟨0, by
        change 0 < W.toOrthogonalDecomposition.componentRank 0
        rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
          D.sortedWeakJordan_componentRank_zero_of_radius_positive hradius]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(0 : Fin 2), j⟩ = (0 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      simp [j]
    have horder := w.order_inverse_indexEquiv (0 : Fin 2) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (0 : Fin 3) =
        BONG.jordanExpectedOrder J 0 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder (W.toJordan hstrict) 0 j = _
    rw [W.jordanExpectedOrder_toJordan hstrict]
    have hscale : ordUnit K (W.scaleGenerator 0) = D.center := by
      simpa [W] using D.sortedWeakJordan_scaleOrder_zero_of_radius_positive hradius
    have heffective : W.effectiveNormOrderAt 0
        (ordUnit K (W.scaleGenerator 0)) = D.center + D.radius := by
      simpa [W] using D.sortedWeakJordan_effective_zero_of_radius_positive hradius
    rw [heffective, hscale]
    simp [JordanProfileOrder.localOrder, j]
  · change D.goodBONG.order (1 : Fin 3) = D.center - D.radius
    let j : Fin (J.toOrthogonalDecomposition.componentRank 0) :=
      ⟨1, by
        change 1 < W.toOrthogonalDecomposition.componentRank 0
        rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
          D.sortedWeakJordan_componentRank_zero_of_radius_positive hradius]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(0 : Fin 2), j⟩ = (1 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      simp [j]
    have horder := w.order_inverse_indexEquiv (0 : Fin 2) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (1 : Fin 3) =
        BONG.jordanExpectedOrder J 0 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder (W.toJordan hstrict) 0 j = _
    rw [W.jordanExpectedOrder_toJordan hstrict]
    have hscale : ordUnit K (W.scaleGenerator 0) = D.center := by
      simpa [W] using D.sortedWeakJordan_scaleOrder_zero_of_radius_positive hradius
    have heffective : W.effectiveNormOrderAt 0
        (ordUnit K (W.scaleGenerator 0)) = D.center + D.radius := by
      simpa [W] using D.sortedWeakJordan_effective_zero_of_radius_positive hradius
    rw [heffective, hscale]
    simp [JordanProfileOrder.localOrder, j]
    omega
  · change D.goodBONG.order (2 : Fin 3) = D.center + D.radius
    let j : Fin (J.toOrthogonalDecomposition.componentRank 1) :=
      ⟨0, by
        change 0 < W.toOrthogonalDecomposition.componentRank 1
        rw [show W = D.modularDecomposition.sortedWeakJordan by rfl,
          D.sortedWeakJordan_componentRank_one_of_radius_positive hradius]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(1 : Fin 2), j⟩ = (2 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      have hIio : Finset.Iio (1 : Fin 2) = {(0 : Fin 2)} := by
        ext x
        fin_cases x <;> simp
      rw [hIio]
      simp only [Finset.sum_singleton, Fin.val_one, j]
      change W.toOrthogonalDecomposition.componentRank 0 = 2
      simpa [W] using
        D.sortedWeakJordan_componentRank_zero_of_radius_positive hradius
    have horder := w.order_inverse_indexEquiv (1 : Fin 2) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (2 : Fin 3) =
        BONG.jordanExpectedOrder J 1 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder (W.toJordan hstrict) 1 j = _
    rw [W.jordanExpectedOrder_toJordan hstrict]
    have hscale : ordUnit K (W.scaleGenerator 1) =
        D.center + D.radius := by
      simpa [W] using D.sortedWeakJordan_scaleOrder_one_of_radius_positive hradius
    have heffective : W.effectiveNormOrderAt 1
        (ordUnit K (W.scaleGenerator 1)) = D.center + D.radius := by
      simpa [W] using D.sortedWeakJordan_effective_one_of_radius_positive hradius
    rw [heffective, hscale]
    simp [JordanProfileOrder.localOrder, j]

/-- The zero-radius branch is the equal-scale collision: the unary and binary
weak components amalgamate to one proper modular component of rank three. -/
theorem order_profile_of_radius_zero
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius = 0) :
    ∀ i, D.goodBONG.order i =
      ![D.center + D.radius, D.center - D.radius,
        D.center + D.radius] i := by
  let W := D.modularDecomposition.sortedWeakJordan
  let k : Fin 1 := 0
  have hscaleZero : ordUnit K (W.scaleGenerator (0 : Fin 2)) = D.center := by
    simpa [W, hradius] using
      D.sortedWeakJordan_scaleOrder_zero_of_radius_nonpositive hradius.le
  have hscaleOne : ordUnit K (W.scaleGenerator (1 : Fin 2)) = D.center := by
    simpa [W] using
      D.sortedWeakJordan_scaleOrder_one_of_radius_nonpositive hradius.le
  have heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ) := by
    simpa [k] using hscaleZero.trans hscaleOne.symm
  let M := W.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun i ↦ ordUnit K (M.scaleGenerator i)) := by
    intro i j hij
    have hij' : i = j := Subsingleton.elim i j
    subst j
    exact False.elim ((lt_irrefl i) hij)
  let J := M.toJordan hstrict
  have hrankZero : finrank K (W.component (0 : Fin 2)).carrier = 1 := by
    change W.toOrthogonalDecomposition.componentRank 0 = 1
    simpa [W] using
      D.sortedWeakJordan_componentRank_zero_of_radius_nonpositive hradius.le
  have hrankOne : finrank K (W.component (1 : Fin 2)).carrier = 2 := by
    change W.toOrthogonalDecomposition.componentRank 1 = 2
    simpa [W] using
      D.sortedWeakJordan_componentRank_one_of_radius_nonpositive hradius.le
  have hmergedRank : finrank K (M.component k).carrier = 3 := by
    change finrank K ((W.mergeAdjacentAt k heq).component k).carrier = 3
    rw [W.mergeAdjacentAt_componentRank_self k heq]
    change finrank K (W.component (0 : Fin 2)).carrier +
      finrank K (W.component (1 : Fin 2)).carrier = 3
    omega
  have heffective : W.effectiveNormOrderAt (0 : Fin 2)
      (ordUnit K (W.scaleGenerator 0)) = D.center := by
    simpa [W] using D.sortedWeakJordan_effective_zero_of_radius_zero hradius
  have hscaleCast : ordUnit K (W.scaleGenerator k.castSucc) = D.center := by
    simpa [k] using hscaleZero
  have heffectiveCast : W.effectiveNormOrderAt (0 : Fin 2)
      (ordUnit K (W.scaleGenerator k.castSucc)) = D.center := by
    simpa [k] using heffective
  rcases D.goodBONG.toBONG.beliLemma47_profile D.goodBONG.good J with ⟨w⟩
  intro i
  fin_cases i
  · simp [hradius]
    change D.goodBONG.order (0 : Fin 3) = D.center
    let j : Fin (J.toOrthogonalDecomposition.componentRank 0) :=
      ⟨0, by
        change 0 < finrank K (M.component k).carrier
        rw [hmergedRank]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(0 : Fin 1), j⟩ = (0 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      simp [j]
    have horder := w.order_inverse_indexEquiv (0 : Fin 1) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (0 : Fin 3) =
        BONG.jordanExpectedOrder J 0 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder
        ((W.mergeAdjacentAt k heq).toJordan hstrict) k j = D.center
    rw [W.jordanExpectedOrder_mergeAdjacentAt k heq hstrict (0 : Fin 2) j]
    rw [heffectiveCast, hscaleCast]
    simp [JordanProfileOrder.localOrder]
  · simp [hradius]
    change D.goodBONG.order (1 : Fin 3) = D.center
    let j : Fin (J.toOrthogonalDecomposition.componentRank 0) :=
      ⟨1, by
        change 1 < finrank K (M.component k).carrier
        rw [hmergedRank]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(0 : Fin 1), j⟩ = (1 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      simp [j]
    have horder := w.order_inverse_indexEquiv (0 : Fin 1) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (1 : Fin 3) =
        BONG.jordanExpectedOrder J 0 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder
        ((W.mergeAdjacentAt k heq).toJordan hstrict) k j = D.center
    rw [W.jordanExpectedOrder_mergeAdjacentAt k heq hstrict (0 : Fin 2) j]
    rw [heffectiveCast, hscaleCast]
    simp [JordanProfileOrder.localOrder]
  · simp [hradius]
    change D.goodBONG.order (2 : Fin 3) = D.center
    let j : Fin (J.toOrthogonalDecomposition.componentRank 0) :=
      ⟨2, by
        change 2 < finrank K (M.component k).carrier
        rw [hmergedRank]
        omega⟩
    have hindex : w.indexEquiv.symm ⟨(0 : Fin 1), j⟩ = (2 : Fin 3) := by
      apply Fin.ext
      rw [w.inverse_index_val]
      simp [j]
    have horder := w.order_inverse_indexEquiv (0 : Fin 1) j
    rw [hindex] at horder
    have horder' : D.goodBONG.order (2 : Fin 3) =
        BONG.jordanExpectedOrder J 0 j := by
      simpa only [GoodBONG.order] using horder
    rw [horder']
    change BONG.jordanExpectedOrder
        ((W.mergeAdjacentAt k heq).toJordan hstrict) k j = D.center
    rw [W.jordanExpectedOrder_mergeAdjacentAt k heq hstrict (0 : Fin 2) j]
    rw [heffectiveCast, hscaleCast]
    simp [JordanProfileOrder.localOrder]

/-- The three radius branches together give the advertised good-BONG order
profile of the explicit unary--binary model. -/
theorem order_profile_proof
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ∀ i, D.goodBONG.order i =
      ![D.center + D.radius, D.center - D.radius,
        D.center + D.radius] i := by
  rcases lt_trichotomy D.radius 0 with hnegative | hzero | hpositive
  · exact D.order_profile_of_radius_negative hnegative
  · exact D.order_profile_of_radius_zero hzero
  · exact D.order_profile_of_radius_positive hpositive

/-- The cross-defect contribution cannot be larger than the power ideal at
the order of the first binary coefficient. -/
theorem scaledCrossDefect_le_firstPower
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.scalarIdeal ((head⁻¹ : Kˣ) : K)
        (Lattice.quadraticDefectIdeal (head * first)) ≤
      Lattice.powerIdeal (K := K)
        (D.center + D.radius + D.alpha) := by
  by_cases htop : quadraticDefect K (head * first) = ⊤
  · rw [Lattice.scaledQuadraticDefectIdeal_eq_bot_of_eq_top
      head first htop]
    exact bot_le
  · rw [Lattice.scaledQuadraticDefectIdeal_eq_powerIdeal_of_ne_top
      head first htop, D.first_order]
    apply (Lattice.powerIdeal_le_iff _ _).2
    omega

/-- If the displayed alpha is odd, the cross product has odd valuation and
therefore zero quadratic defect; the cross-defect term is exactly the first
coefficient power ideal. -/
theorem scaledCrossDefect_eq_firstPower_of_alpha_odd
    (D : UnaryBinaryJordanData head first second hadmissible)
    (halpha : Odd D.alpha) :
    Lattice.scalarIdeal ((head⁻¹ : Kˣ) : K)
        (Lattice.quadraticDefectIdeal (head * first)) =
      Lattice.powerIdeal (K := K)
        (D.center + D.radius + D.alpha) := by
  have hproductOdd : Odd (ordUnit K (head * first)) := by
    rcases halpha with ⟨m, hm⟩
    refine ⟨D.center + D.radius + m, ?_⟩
    rw [ordUnit_mul, D.head_order, D.first_order, hm]
    ring
  have hdefect : quadraticDefect K (head * first) = 0 :=
    quadraticDefect_eq_zero_of_odd_ordUnit (K := K) (head * first)
      hproductOdd
  have hfinite : quadraticDefect K (head * first) ≠ ⊤ := by
    rw [hdefect]
    exact ENat.zero_ne_top
  rw [Lattice.scaledQuadraticDefectIdeal_eq_powerIdeal_of_ne_top
    head first hfinite, hdefect, D.first_order]
  simp

/-- The weight order of the unary--binary model in the nonnegative-radius
branch, proved from Beli (2009), Lemma 2.11 and the two alternatives in the
definition of the normal-form alpha. -/
theorem weight_order_of_radius_nonnegative_proof
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : 0 ≤ D.radius) :
    Lattice.weightIdealOrder
        (unaryBinaryModelSpace head first second hadmissible)
        (unaryBinaryModelLattice (K := K)) =
      D.center + D.radius + D.alpha := by
  let E := D.modularDecomposition.toOrthogonalDecomposition
  let targetOrder := D.center + D.radius + D.alpha
  let targetIdeal := Lattice.powerIdeal (K := K) targetOrder
  have hweight := E.weightIdeal_eq_sup_components_defect_fin_two
    head first D.ambient_normGeneratorValue_head
    D.modularDecomposition_normGeneratorValue_zero
    D.modularDecomposition_normGeneratorValue_one
  have hzeroLe : Lattice.weightIdeal (E.component 0).space
      (E.component 0).lattice ≤ targetIdeal := by
    rw [Lattice.weightIdeal_eq_powerIdeal]
    apply (Lattice.powerIdeal_le_iff _ _).2
    change targetOrder ≤ Lattice.weightIdealOrder
      (D.modularDecomposition.component 0).space
      (D.modularDecomposition.component 0).lattice
    rw [D.modularDecomposition_weightOrder_zero]
    dsimp only [targetOrder]
    have hbound := D.alpha_le_halfGap
    omega
  have honeLe : Lattice.weightIdeal (E.component 1).space
      (E.component 1).lattice ≤ targetIdeal := by
    rw [Lattice.weightIdeal_eq_powerIdeal]
    apply (Lattice.powerIdeal_le_iff _ _).2
    have h := Lattice.normGeneratorOrder_le_weightIdealOrder first
      D.modularDecomposition_normGeneratorValue_one
    rw [D.first_order] at h
    simpa only [E, targetOrder] using h
  have hdefectLe : Lattice.scalarIdeal ((head⁻¹ : Kˣ) : K)
      (Lattice.quadraticDefectIdeal (head * first)) ≤ targetIdeal := by
    simpa only [targetIdeal, targetOrder] using D.scaledCrossDefect_le_firstPower
  have htwoLe : Lattice.twoScaleIdeal
      (unaryBinaryModelSpace head first second hadmissible)
      (unaryBinaryModelLattice (K := K)) ≤ targetIdeal := by
    rw [D.twoScaleIdeal_eq_powerIdeal_of_radius_nonnegative hradius]
    apply (Lattice.powerIdeal_le_iff _ _).2
    dsimp only [targetIdeal, targetOrder]
    have hbound := D.alpha_le_halfGap
    omega
  have hallLe :
      Lattice.weightIdeal (E.component 0).space (E.component 0).lattice ⊔
          Lattice.weightIdeal (E.component 1).space (E.component 1).lattice ⊔
          Lattice.scalarIdeal ((head⁻¹ : Kˣ) : K)
            (Lattice.quadraticDefectIdeal (head * first)) ⊔
          Lattice.twoScaleIdeal
            (unaryBinaryModelSpace head first second hadmissible)
            (unaryBinaryModelLattice (K := K)) ≤ targetIdeal := by
    exact sup_le (sup_le (sup_le hzeroLe honeLe) hdefectLe) htwoLe
  have hsup :
      Lattice.weightIdeal (E.component 0).space (E.component 0).lattice ⊔
          Lattice.weightIdeal (E.component 1).space (E.component 1).lattice ⊔
          Lattice.scalarIdeal ((head⁻¹ : Kˣ) : K)
            (Lattice.quadraticDefectIdeal (head * first)) ⊔
          Lattice.twoScaleIdeal
            (unaryBinaryModelSpace head first second hadmissible)
            (unaryBinaryModelLattice (K := K)) = targetIdeal := by
    apply le_antisymm hallLe
    rcases D.alpha_half_or_odd with hhalf | hodd
    · have htwoEq : Lattice.twoScaleIdeal
          (unaryBinaryModelSpace head first second hadmissible)
          (unaryBinaryModelLattice (K := K)) = targetIdeal := by
        rw [D.twoScaleIdeal_eq_powerIdeal_of_radius_nonnegative hradius]
        apply congrArg (Lattice.powerIdeal (K := K))
        dsimp only [targetIdeal, targetOrder]
        omega
      rw [← htwoEq]
      exact _root_.le_sup_right
    · have hdefectEq : Lattice.scalarIdeal ((head⁻¹ : Kˣ) : K)
          (Lattice.quadraticDefectIdeal (head * first)) = targetIdeal := by
        simpa only [targetIdeal, targetOrder] using
          D.scaledCrossDefect_eq_firstPower_of_alpha_odd hodd
      rw [← hdefectEq]
      exact _root_.le_sup_right.trans _root_.le_sup_left
  apply Lattice.powerIdeal_order_eq_of_eq (K := K)
  calc
    Lattice.powerIdeal (K := K)
        (Lattice.weightIdealOrder
          (unaryBinaryModelSpace head first second hadmissible)
          (unaryBinaryModelLattice (K := K))) =
        Lattice.weightIdeal
          (unaryBinaryModelSpace head first second hadmissible)
          (unaryBinaryModelLattice (K := K)) :=
      (Lattice.weightIdeal_eq_powerIdeal _ _).symm
    _ = Lattice.weightIdeal (E.component 0).space (E.component 0).lattice ⊔
          Lattice.weightIdeal (E.component 1).space (E.component 1).lattice ⊔
          Lattice.scalarIdeal ((head⁻¹ : Kˣ) : K)
            (Lattice.quadraticDefectIdeal (head * first)) ⊔
          Lattice.twoScaleIdeal
            (unaryBinaryModelSpace head first second hadmissible)
            (unaryBinaryModelLattice (K := K)) := hweight
    _ = targetIdeal := hsup

/-! ## Reverse-dual unary--binary calculation -/

/-- The norm generator of the dual unary factor. -/
noncomputable def dualUnaryNormGenerator
    (D : UnaryBinaryJordanData head first second hadmissible) : Kˣ :=
  head⁻¹

/-- The norm generator obtained by scaling the binary head by the inverse
square of the modular parameter. -/
noncomputable def dualBinaryNormGenerator
    (D : UnaryBinaryJordanData head first second hadmissible) : Kˣ :=
  D.binaryScaleGenerator⁻¹ ^ 2 * first

theorem dualUnaryNormGenerator_order
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K D.dualUnaryNormGenerator = -D.center - D.radius := by
  rw [dualUnaryNormGenerator, ordUnit_inv, D.head_order]
  omega

theorem dualBinaryNormGenerator_order
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K D.dualBinaryNormGenerator =
      -D.center + D.radius + D.alpha := by
  rw [dualBinaryNormGenerator, ordUnit_mul, ordUnit_pow, ordUnit_inv,
    D.binaryScaleGenerator_order, D.first_order]
  omega

/-- The componentwise duals of the unary and binary factors form a modular
decomposition of the product dual lattice. -/
noncomputable def dualModularDecomposition
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.ModularDecomposition
      (unaryBinaryModelSpace head first second hadmissible)
      (Lattice.product
        (Lattice.dualLattice
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (unaryModelLattice (K := K)))
        (Lattice.dualLattice
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelLattice (K := K)))) 2 where
  toOrthogonalDecomposition :=
    Lattice.orthogonalProductDecomposition
      (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
      (binaryDiagonalModelSpace first second hadmissible)
      (Lattice.dualLattice
        (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
        (unaryModelLattice (K := K)))
      (Lattice.dualLattice
        (binaryDiagonalModelSpace first second hadmissible)
        (binaryDiagonalModelLattice (K := K)))
  scaleGenerator := ![head⁻¹, D.binaryScaleGenerator⁻¹]
  modular := by
    intro i
    fin_cases i
    · exact (unaryModel_isModular head).dual.mapLatticeIsometry
        (Lattice.orthogonalProductLeftComponentIsometry
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (binaryDiagonalModelSpace first second hadmissible)
          (Lattice.dualLattice
            (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
            (unaryModelLattice (K := K))))
    · exact D.binaryScaleGenerator_isModular.dual.mapLatticeIsometry
        (Lattice.orthogonalProductRightComponentIsometry
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (binaryDiagonalModelSpace first second hadmissible)
          (Lattice.dualLattice
            (binaryDiagonalModelSpace first second hadmissible)
            (binaryDiagonalModelLattice (K := K))))
  component_finrank_pos := by
    intro i
    fin_cases i
    · have h := LinearEquiv.finrank_eq
        (Lattice.orthogonalProductLeftCarrierEquiv
          (K := K) (V := K) (W := Fin 2 → K))
      change 0 < finrank K
        (Lattice.orthogonalProductLeftCarrier
          (K := K) (V := K) (W := Fin 2 → K))
      rw [← h]
      simp
    · have h := LinearEquiv.finrank_eq
        (Lattice.orthogonalProductRightCarrierEquiv
          (K := K) (V := K) (W := Fin 2 → K))
      change 0 < finrank K
        (Lattice.orthogonalProductRightCarrier
          (K := K) (V := K) (W := Fin 2 → K))
      rw [← h]
      simp

@[simp]
theorem dualModularDecomposition_scale_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.dualModularDecomposition.scaleGenerator 0 = head⁻¹ := rfl

@[simp]
theorem dualModularDecomposition_scale_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.dualModularDecomposition.scaleGenerator 1 =
      D.binaryScaleGenerator⁻¹ := rfl

theorem dualModularDecomposition_scaleOrder_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K (D.dualModularDecomposition.scaleGenerator 0) =
      -D.center - D.radius := by
  rw [D.dualModularDecomposition_scale_zero, ordUnit_inv, D.head_order]
  omega

theorem dualModularDecomposition_scaleOrder_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    ordUnit K (D.dualModularDecomposition.scaleGenerator 1) =
      -D.center := by
  rw [D.dualModularDecomposition_scale_one, ordUnit_inv,
    D.binaryScaleGenerator_order]

/-- An actual norm generator with prescribed nonzero quadratic value supplies
the corresponding scalar norm generator. -/
theorem isNormGeneratorValue_of_quadratic_eq
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {x : V} {a : Kˣ}
    (hx : Lattice.IsNormGenerator q L x)
    (hvalue : q.quadratic x = (a : K)) :
    Lattice.IsNormGeneratorValue q L a := by
  constructor
  · refine ⟨x, hx.mem, 0, Submodule.zero_mem _, ?_⟩
    simpa [hvalue]
  · calc
      Lattice.normIdeal q L =
          Lattice.principalIdeal (K := K) (q.quadratic x) := hx.normIdeal_eq
      _ = Lattice.principalIdeal (K := K) (a : K) := by rw [hvalue]

/-- Scalar norm generator of the dual unary factor. -/
theorem dualUnaryNormGeneratorValue_factor
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsNormGeneratorValue
      (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
      (Lattice.dualLattice
        (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
        (unaryModelLattice (K := K)))
      D.dualUnaryNormGenerator := by
  have hgen := (unaryModel_isModular head).normGenerator_dual
    (unaryModelBONG head).head_isNormGenerator
  apply isNormGeneratorValue_of_quadratic_eq hgen
  change (QuadraticSpace.rescaleUnit head
      (QuadraticSpace.line K)).quadratic
        (((head⁻¹ : Kˣ) : K) • (unaryModelBONG head).head) = _
  rw [(QuadraticSpace.rescaleUnit head
      (QuadraticSpace.line K)).quadratic_smul,
    ← (unaryModelBONG head).value_zero_eq_quadratic_head,
    unaryModelBONG_value]
  change ((head⁻¹ : Kˣ) : K) ^ 2 * (head : K) =
    (D.dualUnaryNormGenerator : K)
  rw [dualUnaryNormGenerator]
  simp
  field_simp [Units.ne_zero head]

/-- Scalar norm generator of the dual binary factor. -/
theorem dualBinaryNormGeneratorValue_factor
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsNormGeneratorValue
      (binaryDiagonalModelSpace first second hadmissible)
      (Lattice.dualLattice
        (binaryDiagonalModelSpace first second hadmissible)
        (binaryDiagonalModelLattice (K := K)))
      D.dualBinaryNormGenerator := by
  have hgen := D.binaryScaleGenerator_isModular.normGenerator_dual
    (binaryDiagonalModelBONG first second hadmissible).head_isNormGenerator
  apply isNormGeneratorValue_of_quadratic_eq hgen
  change (binaryDiagonalModelSpace first second hadmissible).quadratic
    (((D.binaryScaleGenerator⁻¹ : Kˣ) : K) •
      (binaryDiagonalModelBONG first second hadmissible).head) = _
  rw [(binaryDiagonalModelSpace first second hadmissible).quadratic_smul,
    ← (binaryDiagonalModelBONG first second hadmissible)
      |>.value_zero_eq_quadratic_head,
    binaryDiagonalModelBONG_value_zero]
  rfl

/-- The dual unary scalar is also a norm generator of the corresponding
embedded component. -/
theorem dualModularDecomposition_normGeneratorValue_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsNormGeneratorValue
      (D.dualModularDecomposition.component 0).space
      (D.dualModularDecomposition.component 0).lattice
      D.dualUnaryNormGenerator := by
  let q₀ := QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)
  let q₁ := binaryDiagonalModelSpace first second hadmissible
  let L₀ := Lattice.dualLattice q₀ (unaryModelLattice (K := K))
  let f := Lattice.orthogonalProductLeftComponentIsometry q₀ q₁ L₀
  change Lattice.IsNormGeneratorValue
    (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).space
    (Lattice.orthogonalProductLeftComponent q₀ q₁ L₀).lattice
    D.dualUnaryNormGenerator
  have hfactor := (unaryModel_isModular head).normGenerator_dual
    (unaryModelBONG head).head_isNormGenerator
  have hgen := hfactor.mapLatticeIsometry f
  apply isNormGeneratorValue_of_quadratic_eq hgen
  calc
    _ = q₀.quadratic
        (((head⁻¹ : Kˣ) : K) • (unaryModelBONG head).head) :=
      f.map_bilin _ _
    _ = (D.dualUnaryNormGenerator : K) := by
      rw [q₀.quadratic_smul,
        ← (unaryModelBONG head).value_zero_eq_quadratic_head,
        unaryModelBONG_value]
      change ((head⁻¹ : Kˣ) : K) ^ 2 * (head : K) =
        (D.dualUnaryNormGenerator : K)
      rw [dualUnaryNormGenerator]
      simp
      field_simp [Units.ne_zero head]

/-- The dual binary scalar is also a norm generator of the corresponding
embedded component. -/
theorem dualModularDecomposition_normGeneratorValue_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsNormGeneratorValue
      (D.dualModularDecomposition.component 1).space
      (D.dualModularDecomposition.component 1).lattice
      D.dualBinaryNormGenerator := by
  let q₀ := QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)
  let q₁ := binaryDiagonalModelSpace first second hadmissible
  let L₁ := Lattice.dualLattice q₁ (binaryDiagonalModelLattice (K := K))
  let f := Lattice.orthogonalProductRightComponentIsometry q₀ q₁ L₁
  change Lattice.IsNormGeneratorValue
    (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).space
    (Lattice.orthogonalProductRightComponent q₀ q₁ L₁).lattice
    D.dualBinaryNormGenerator
  have hfactor := D.binaryScaleGenerator_isModular.normGenerator_dual
    (binaryDiagonalModelBONG first second hadmissible).head_isNormGenerator
  have hgen := hfactor.mapLatticeIsometry f
  apply isNormGeneratorValue_of_quadratic_eq hgen
  calc
    _ = q₁.quadratic
        (((D.binaryScaleGenerator⁻¹ : Kˣ) : K) •
          (binaryDiagonalModelBONG first second hadmissible).head) :=
      f.map_bilin _ _
    _ = (D.dualBinaryNormGenerator : K) := by
      rw [q₁.quadratic_smul,
        ← (binaryDiagonalModelBONG first second hadmissible)
          |>.value_zero_eq_quadratic_head,
        binaryDiagonalModelBONG_value_zero]
      rfl

theorem dualModularDecomposition_componentRank_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.dualModularDecomposition.toOrthogonalDecomposition.componentRank 0 = 1 := by
  have h := LinearEquiv.finrank_eq
    (Lattice.orthogonalProductLeftCarrierEquiv
      (K := K) (V := K) (W := Fin 2 → K))
  change finrank K
      (Lattice.orthogonalProductLeftCarrier
        (K := K) (V := K) (W := Fin 2 → K)) = 1
  rw [← h]
  simp

theorem dualModularDecomposition_componentRank_one
    (D : UnaryBinaryJordanData head first second hadmissible) :
    D.dualModularDecomposition.toOrthogonalDecomposition.componentRank 1 = 2 := by
  have h := LinearEquiv.finrank_eq
    (Lattice.orthogonalProductRightCarrierEquiv
      (K := K) (V := K) (W := Fin 2 → K))
  change finrank K
      (Lattice.orthogonalProductRightCarrier
        (K := K) (V := K) (W := Fin 2 → K)) = 2
  rw [← h]
  simp

/-- The unary dual component has its rank-one weight order. -/
theorem dualModularDecomposition_weightOrder_zero
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.weightIdealOrder
        (D.dualModularDecomposition.component 0).space
        (D.dualModularDecomposition.component 0).lattice =
      -D.center - D.radius + (ramificationIndex K : Int) := by
  have h := weightIdealOrder_rankOne_of_isNormGeneratorValue
    (D.dualModularDecomposition.component 0).space
    (D.dualModularDecomposition.component 0).lattice
    D.dualModularDecomposition_componentRank_zero
    D.dualUnaryNormGenerator
    D.dualModularDecomposition_normGeneratorValue_zero
  rw [D.dualUnaryNormGenerator_order] at h
  exact h

/-- The dual unary scalar has the smallest norm order in the product dual and
is therefore an ambient scalar norm generator. -/
theorem dualAmbient_normGeneratorValue
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.IsNormGeneratorValue
      (unaryBinaryModelSpace head first second hadmissible)
      (Lattice.product
        (Lattice.dualLattice
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (unaryModelLattice (K := K)))
        (Lattice.dualLattice
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelLattice (K := K))))
      D.dualUnaryNormGenerator := by
  let q₀ := QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)
  let q₁ := binaryDiagonalModelSpace first second hadmissible
  let L₀ := Lattice.dualLattice q₀ (unaryModelLattice (K := K))
  let L₁ := Lattice.dualLattice q₁ (binaryDiagonalModelLattice (K := K))
  let x₀ : K := ((head⁻¹ : Kˣ) : K) • (unaryModelBONG head).head
  have hx₀gen : Lattice.IsNormGenerator q₀ L₀ x₀ := by
    exact (unaryModel_isModular head).normGenerator_dual
      (unaryModelBONG head).head_isNormGenerator
  have hxmem : (x₀, (0 : Fin 2 → K)) ∈ Lattice.product L₀ L₁ := by
    exact Lattice.inl_mem_product_iff.mpr hx₀gen.mem
  have hquadZero : q₀.quadratic x₀ =
      (D.dualUnaryNormGenerator : K) := by
    dsimp only [x₀]
    rw [q₀.quadratic_smul,
      ← (unaryModelBONG head).value_zero_eq_quadratic_head,
      unaryModelBONG_value]
    change ((head⁻¹ : Kˣ) : K) ^ 2 * (head : K) =
      (D.dualUnaryNormGenerator : K)
    rw [dualUnaryNormGenerator]
    simp
    field_simp [Units.ne_zero head]
  have hquad : (q₀.orthogonalSum q₁).quadratic
      (x₀, (0 : Fin 2 → K)) = (D.dualUnaryNormGenerator : K) := by
    rw [QuadraticSpace.orthogonalSum_quadratic_apply, hquadZero]
    simp
  have hnorm : Lattice.normIdeal (q₀.orthogonalSum q₁)
      (Lattice.product L₀ L₁) =
        Lattice.principalIdeal (K := K) (D.dualUnaryNormGenerator : K) := by
    let E := D.dualModularDecomposition.toOrthogonalDecomposition
    change Lattice.normIdeal
      (unaryBinaryModelSpace head first second hadmissible)
      (Lattice.product
        (Lattice.dualLattice
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (unaryModelLattice (K := K)))
        (Lattice.dualLattice
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelLattice (K := K)))) =
      Lattice.principalIdeal (K := K) (D.dualUnaryNormGenerator : K)
    rw [E.normIdeal_eq_iSup_component,
      Lattice.iSup_fin_two_eq_sup,
      D.dualModularDecomposition_normGeneratorValue_zero.2,
      D.dualModularDecomposition_normGeneratorValue_one.2,
      sup_eq_left]
    apply (Lattice.principalIdeal_le_iff_ord_ge
      (Units.ne_zero D.dualBinaryNormGenerator)
      (Units.ne_zero D.dualUnaryNormGenerator)).2
    rw [← coe_ordUnit, ← coe_ordUnit,
      D.dualUnaryNormGenerator_order,
      D.dualBinaryNormGenerator_order]
    norm_cast
    have hdual := D.dual_alpha_nonnegative
    omega
  apply isNormGeneratorValue_of_quadratic_eq
    (q := q₀.orthogonalSum q₁)
    (L := Lattice.product L₀ L₁)
    (x := (x₀, (0 : Fin 2 → K)))
  · exact ⟨hxmem, hnorm.trans (by rw [hquad])⟩
  · exact hquad

/-- In the negative-radius branch the binary dual parameter generates the
ambient dual scale ideal. -/
theorem dualScaleIdeal_eq_principal_binaryScale
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0) :
    Lattice.scaleIdeal
      (unaryBinaryModelSpace head first second hadmissible)
      (Lattice.product
        (Lattice.dualLattice
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (unaryModelLattice (K := K)))
      (Lattice.dualLattice
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelLattice (K := K)))) =
      Lattice.principalIdeal (K := K)
        ((D.binaryScaleGenerator⁻¹ : Kˣ) : K) := by
  rw [D.dualModularDecomposition.toOrthogonalDecomposition
      |>.scaleIdeal_eq_iSup_component,
    Lattice.iSup_fin_two_eq_sup,
    (D.dualModularDecomposition.modular 0).scaleIdeal_eq_principal
      (D.dualModularDecomposition.component_finrank_pos 0),
    (D.dualModularDecomposition.modular 1).scaleIdeal_eq_principal
      (D.dualModularDecomposition.component_finrank_pos 1),
    D.dualModularDecomposition_scale_zero,
    D.dualModularDecomposition_scale_one,
    sup_eq_right]
  apply (Lattice.principalIdeal_le_iff_ord_ge
    (Units.ne_zero head⁻¹) (Units.ne_zero D.binaryScaleGenerator⁻¹)).2
  rw [← coe_ordUnit, ← coe_ordUnit, ordUnit_inv, ordUnit_inv,
    D.binaryScaleGenerator_order, D.head_order]
  norm_cast
  omega

/-- The `2s` term of the product dual has order `-center + e`. -/
theorem dualTwoScaleIdeal_eq_powerIdeal
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0) :
    Lattice.twoScaleIdeal
      (unaryBinaryModelSpace head first second hadmissible)
      (Lattice.product
        (Lattice.dualLattice
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (unaryModelLattice (K := K)))
        (Lattice.dualLattice
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelLattice (K := K)))) =
      Lattice.powerIdeal (K := K)
        (-D.center + (ramificationIndex K : Int)) := by
  rw [Lattice.twoScaleIdeal,
    D.dualScaleIdeal_eq_principal_binaryScale hradius,
    Lattice.twicePrincipalIdeal_eq_powerIdeal,
    ordUnit_inv, D.binaryScaleGenerator_order]

/-- Upper bound for the cross-defect term in the product dual. -/
theorem scaledDualCrossDefect_le_firstPower
    (D : UnaryBinaryJordanData head first second hadmissible) :
    Lattice.scalarIdeal ((D.dualUnaryNormGenerator⁻¹ : Kˣ) : K)
        (Lattice.quadraticDefectIdeal
          (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator)) ≤
      Lattice.powerIdeal (K := K)
        (-D.center - D.radius + (D.alpha + 2 * D.radius)) := by
  by_cases htop : quadraticDefect K
      (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator) = ⊤
  · rw [Lattice.scaledQuadraticDefectIdeal_eq_bot_of_eq_top
      D.dualUnaryNormGenerator D.dualBinaryNormGenerator htop]
    exact bot_le
  · rw [Lattice.scaledQuadraticDefectIdeal_eq_powerIdeal_of_ne_top
      D.dualUnaryNormGenerator D.dualBinaryNormGenerator htop,
      D.dualBinaryNormGenerator_order]
    apply (Lattice.powerIdeal_le_iff _ _).2
    omega

/-- In the odd-alpha branch the dual cross defect vanishes. -/
theorem scaledDualCrossDefect_eq_firstPower_of_alpha_odd
    (D : UnaryBinaryJordanData head first second hadmissible)
    (halpha : Odd D.alpha) :
    Lattice.scalarIdeal ((D.dualUnaryNormGenerator⁻¹ : Kˣ) : K)
        (Lattice.quadraticDefectIdeal
          (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator)) =
      Lattice.powerIdeal (K := K)
        (-D.center - D.radius + (D.alpha + 2 * D.radius)) := by
  have hproductOdd : Odd (ordUnit K
      (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator)) := by
    rcases halpha with ⟨m, hm⟩
    refine ⟨-D.center + m, ?_⟩
    rw [ordUnit_mul, D.dualUnaryNormGenerator_order,
      D.dualBinaryNormGenerator_order, hm]
    ring
  have hdefect : quadraticDefect K
      (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator) = 0 :=
    quadraticDefect_eq_zero_of_odd_ordUnit (K := K)
      (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator) hproductOdd
  have hfinite : quadraticDefect K
      (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator) ≠ ⊤ := by
    rw [hdefect]
    exact ENat.zero_ne_top
  rw [Lattice.scaledQuadraticDefectIdeal_eq_powerIdeal_of_ne_top
    D.dualUnaryNormGenerator D.dualBinaryNormGenerator hfinite,
    hdefect, D.dualBinaryNormGenerator_order]
  simp
  congr 1
  omega

/-- Direct product-dual weight calculation in the negative-radius branch. -/
theorem dualProduct_weight_order_of_radius_negative
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0) :
    Lattice.weightIdealOrder
      (unaryBinaryModelSpace head first second hadmissible)
      (Lattice.product
        (Lattice.dualLattice
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (unaryModelLattice (K := K)))
        (Lattice.dualLattice
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelLattice (K := K)))) =
      -D.center - D.radius + (D.alpha + 2 * D.radius) := by
  let E := D.dualModularDecomposition.toOrthogonalDecomposition
  let targetOrder := -D.center - D.radius + (D.alpha + 2 * D.radius)
  let targetIdeal := Lattice.powerIdeal (K := K) targetOrder
  have hweight := E.weightIdeal_eq_sup_components_defect_fin_two
    D.dualUnaryNormGenerator D.dualBinaryNormGenerator
    D.dualAmbient_normGeneratorValue
    D.dualModularDecomposition_normGeneratorValue_zero
    D.dualModularDecomposition_normGeneratorValue_one
  have hzeroLe : Lattice.weightIdeal (E.component 0).space
      (E.component 0).lattice ≤ targetIdeal := by
    rw [Lattice.weightIdeal_eq_powerIdeal]
    apply (Lattice.powerIdeal_le_iff _ _).2
    change targetOrder ≤ Lattice.weightIdealOrder
      (D.dualModularDecomposition.component 0).space
      (D.dualModularDecomposition.component 0).lattice
    rw [D.dualModularDecomposition_weightOrder_zero]
    dsimp only [targetOrder]
    have hbound := D.alpha_le_halfGap
    omega
  have honeLe : Lattice.weightIdeal (E.component 1).space
      (E.component 1).lattice ≤ targetIdeal := by
    rw [Lattice.weightIdeal_eq_powerIdeal]
    apply (Lattice.powerIdeal_le_iff _ _).2
    change targetOrder ≤ Lattice.weightIdealOrder
      (D.dualModularDecomposition.component 1).space
      (D.dualModularDecomposition.component 1).lattice
    have h := Lattice.normGeneratorOrder_le_weightIdealOrder
      D.dualBinaryNormGenerator
      D.dualModularDecomposition_normGeneratorValue_one
    rw [D.dualBinaryNormGenerator_order] at h
    dsimp only [targetIdeal, targetOrder]
    omega
  have hdefectLe :
      Lattice.scalarIdeal ((D.dualUnaryNormGenerator⁻¹ : Kˣ) : K)
        (Lattice.quadraticDefectIdeal
          (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator)) ≤
        targetIdeal := by
    simpa only [targetIdeal, targetOrder] using
      D.scaledDualCrossDefect_le_firstPower
  have htwoLe : Lattice.twoScaleIdeal
      (unaryBinaryModelSpace head first second hadmissible)
      (Lattice.product
        (Lattice.dualLattice
          (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
          (unaryModelLattice (K := K)))
        (Lattice.dualLattice
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelLattice (K := K)))) ≤ targetIdeal := by
    rw [D.dualTwoScaleIdeal_eq_powerIdeal hradius]
    apply (Lattice.powerIdeal_le_iff _ _).2
    dsimp only [targetIdeal, targetOrder]
    have hbound := D.alpha_le_halfGap
    omega
  have hallLe :
      Lattice.weightIdeal (E.component 0).space (E.component 0).lattice ⊔
          Lattice.weightIdeal (E.component 1).space (E.component 1).lattice ⊔
          Lattice.scalarIdeal
            ((D.dualUnaryNormGenerator⁻¹ : Kˣ) : K)
            (Lattice.quadraticDefectIdeal
              (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator)) ⊔
          Lattice.twoScaleIdeal
            (unaryBinaryModelSpace head first second hadmissible)
            (Lattice.product
              (Lattice.dualLattice
                (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
                (unaryModelLattice (K := K)))
              (Lattice.dualLattice
                (binaryDiagonalModelSpace first second hadmissible)
                (binaryDiagonalModelLattice (K := K)))) ≤ targetIdeal := by
    exact sup_le (sup_le (sup_le hzeroLe honeLe) hdefectLe) htwoLe
  have hsup :
      Lattice.weightIdeal (E.component 0).space (E.component 0).lattice ⊔
          Lattice.weightIdeal (E.component 1).space (E.component 1).lattice ⊔
          Lattice.scalarIdeal
            ((D.dualUnaryNormGenerator⁻¹ : Kˣ) : K)
            (Lattice.quadraticDefectIdeal
              (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator)) ⊔
          Lattice.twoScaleIdeal
            (unaryBinaryModelSpace head first second hadmissible)
            (Lattice.product
              (Lattice.dualLattice
                (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
                (unaryModelLattice (K := K)))
              (Lattice.dualLattice
                (binaryDiagonalModelSpace first second hadmissible)
                (binaryDiagonalModelLattice (K := K)))) = targetIdeal := by
    apply le_antisymm hallLe
    rcases D.alpha_half_or_odd with hhalf | hodd
    · have htwoEq : Lattice.twoScaleIdeal
          (unaryBinaryModelSpace head first second hadmissible)
          (Lattice.product
            (Lattice.dualLattice
              (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
              (unaryModelLattice (K := K)))
            (Lattice.dualLattice
              (binaryDiagonalModelSpace first second hadmissible)
              (binaryDiagonalModelLattice (K := K)))) = targetIdeal := by
        rw [D.dualTwoScaleIdeal_eq_powerIdeal hradius]
        apply congrArg (Lattice.powerIdeal (K := K))
        dsimp only [targetIdeal, targetOrder]
        omega
      rw [← htwoEq]
      exact _root_.le_sup_right
    · have hdefectEq :
          Lattice.scalarIdeal
            ((D.dualUnaryNormGenerator⁻¹ : Kˣ) : K)
            (Lattice.quadraticDefectIdeal
              (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator)) =
            targetIdeal := by
        simpa only [targetIdeal, targetOrder] using
          D.scaledDualCrossDefect_eq_firstPower_of_alpha_odd hodd
      rw [← hdefectEq]
      exact _root_.le_sup_right.trans _root_.le_sup_left
  apply Lattice.powerIdeal_order_eq_of_eq (K := K)
  calc
    Lattice.powerIdeal (K := K)
        (Lattice.weightIdealOrder
          (unaryBinaryModelSpace head first second hadmissible)
          (Lattice.product
            (Lattice.dualLattice
              (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
              (unaryModelLattice (K := K)))
            (Lattice.dualLattice
              (binaryDiagonalModelSpace first second hadmissible)
              (binaryDiagonalModelLattice (K := K))))) =
        Lattice.weightIdeal
          (unaryBinaryModelSpace head first second hadmissible)
          (Lattice.product
            (Lattice.dualLattice
              (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
              (unaryModelLattice (K := K)))
            (Lattice.dualLattice
              (binaryDiagonalModelSpace first second hadmissible)
              (binaryDiagonalModelLattice (K := K)))) :=
      (Lattice.weightIdeal_eq_powerIdeal _ _).symm
    _ = Lattice.weightIdeal (E.component 0).space (E.component 0).lattice ⊔
          Lattice.weightIdeal (E.component 1).space (E.component 1).lattice ⊔
          Lattice.scalarIdeal
            ((D.dualUnaryNormGenerator⁻¹ : Kˣ) : K)
            (Lattice.quadraticDefectIdeal
              (D.dualUnaryNormGenerator * D.dualBinaryNormGenerator)) ⊔
          Lattice.twoScaleIdeal
            (unaryBinaryModelSpace head first second hadmissible)
            (Lattice.product
              (Lattice.dualLattice
                (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K))
                (unaryModelLattice (K := K)))
              (Lattice.dualLattice
                (binaryDiagonalModelSpace first second hadmissible)
                (binaryDiagonalModelLattice (K := K)))) := hweight
    _ = targetIdeal := hsup

/-- The product-dual calculation is the actual integral dual of the original
unary--binary lattice.  The reverse-good-BONG witness is not needed once the
weight ideal is computed directly. -/
theorem dual_weight_order_of_radius_negative_proof
    (D : UnaryBinaryJordanData head first second hadmissible)
    (hradius : D.radius < 0)
    (c : GoodBONG
      (unaryBinaryModelSpace head first second hadmissible)
      (Lattice.dualLattice
        (unaryBinaryModelSpace head first second hadmissible)
        (unaryBinaryModelLattice (K := K))) 3)
    (_hdual : D.goodBONG.IsReverseDualGoodBONG c) :
    Lattice.weightIdealOrder
        (unaryBinaryModelSpace head first second hadmissible)
        (Lattice.dualLattice
          (unaryBinaryModelSpace head first second hadmissible)
          (unaryBinaryModelLattice (K := K))) =
      -D.center - D.radius + (D.alpha + 2 * D.radius) := by
  rw [unaryBinaryModelSpace, unaryBinaryModelLattice,
    Lattice.dualLattice_orthogonalProduct_basic]
  exact D.dualProduct_weight_order_of_radius_negative hradius

end UnaryBinaryJordanData

end BONG

/-- Unconditional closure of the unary--binary Jordan/weight interface used
in Beli (2019), Lemma 9.5(ii). -/
noncomputable instance beli2019UnaryBinaryJordanLawsProved
    [BONGGoodExistenceLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K] :
    Beli2019UnaryBinaryJordanLaws.{u} K where
  order_profile :=
    BONG.UnaryBinaryJordanData.order_profile_proof
  weight_order_of_radius_nonnegative :=
    BONG.UnaryBinaryJordanData.weight_order_of_radius_nonnegative_proof
  dual_weight_order_of_radius_negative :=
    BONG.UnaryBinaryJordanData.dual_weight_order_of_radius_negative_proof

end Bong
