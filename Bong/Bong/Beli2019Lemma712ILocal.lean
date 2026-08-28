/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma712I
import Bong.Bong.UnaryModelBONG
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Beli (2019), Lemma 7.12(i): the local binary--unary replacement

This module transports Lemma 7.12(i) from its standard model to the literal
orthogonal product of an arbitrary binary BONG in the negative-quarter
endpoint class and an arbitrary unary BONG.  It is the local geometric step
iterated in Corollary 7.13.
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
  {J : Lattice K V} {A : Lattice K W}

theorem standardNegativeQuarterEndpoint_isIsometric_lemma712IBinary
    (p : Kˣ) :
    Lattice.IsIsometric
      (QuadraticSpace.rescaleUnit p
        (QuadraticSpace.binaryModel
          (negativeQuarterUnit K) (standardEndpointShear (K := K))))
      (binaryDiagonalModelSpace p (p * negativeQuarterUnit K)
        (lemma712I_sourceBinaryAdmissible p))
      (binaryModelLattice (K := K))
      (binaryDiagonalModelLattice (K := K)) := by
  let d := negativeQuarterUnit K
  let hAdmissible := lemma712I_sourceBinaryAdmissible p
  have hratio : (p * d) / p = d := by simp
  have hchosenTwo :
      (2 : K) * admissibleBinaryShear ((p * d) / p) hAdmissible ∈
        IntegerRing K :=
    two_mul_admissibleBinaryShear_mem ((p * d) / p) hAdmissible
  have hchosenDiag :
      admissibleBinaryShear ((p * d) / p) hAdmissible ^ 2 + (d : K) ∈
        IntegerRing K := by
    simpa only [hratio] using
      admissibleBinaryShear_sq_add_mem ((p * d) / p) hAdmissible
  have hshear :
      standardEndpointShear (K := K) -
          admissibleBinaryShear ((p * d) / p) hAdmissible ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing d
      (standardEndpointShear (K := K))
      (admissibleBinaryShear ((p * d) / p) hAdmissible)
      standardEndpointShear_two_integral
      negativeQuarter_standardEndpointShear_diagonal_integral
      hchosenTwo hchosenDiag
  have hmodel := rescaledBinaryModel_isIsometric_of_shear_sub_integral
    p d (standardEndpointShear (K := K))
      (admissibleBinaryShear ((p * d) / p) hAdmissible) hshear
  simpa only [d, hAdmissible, binaryDiagonalModelSpace,
    binaryDiagonalModelLattice, hratio] using hmodel

theorem isIsometric_lemma712IBinary_of_negativeQuarterEndpoint
    (j : GoodBONG q J 2)
    (hclass : j.toBONG.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K)) :
    Lattice.IsIsometric q
      (binaryDiagonalModelSpace (j.valueUnit 0)
        (j.valueUnit 0 * negativeQuarterUnit K)
        (lemma712I_sourceBinaryAdmissible (j.valueUnit 0)))
      J (binaryDiagonalModelLattice (K := K)) := by
  rcases j.toBONG.isIsometric_standardEndpointModel
      (negativeQuarterUnit K) hclass
      standardEndpointShear_two_integral
      negativeQuarter_standardEndpointShear_diagonal_integral with ⟨f⟩
  rcases standardNegativeQuarterEndpoint_isIsometric_lemma712IBinary
      (j.valueUnit 0) with ⟨g⟩
  exact ⟨f.trans g⟩

theorem exists_lemma712I_localGoodBONG
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [PerfectResidueFieldLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [BeliLemma43ConstructionLaws.{u, u} K]
    [Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    (j : GoodBONG q J 2) (x : GoodBONG r A 1)
    (hp : j.order 0 = x.order 0 + 1)
    (hclass : j.toBONG.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K))
    (ε : Kˣ) (hεUnit : IsValuationUnit K (ε : K)) :
    ∃ b : GoodBONG (q.orthogonalSum r) (Lattice.product J A) 3,
      ∀ i, b.valueUnit i = lemma712ITargetValues (x.valueUnit 0) ε i := by
  let p := j.valueUnit 0
  let a := x.valueUnit 0
  have hp' : ordUnit K p = ordUnit K a + 1 := by
    dsimp only [p, a, GoodBONG.valueUnit]
    rw [← j.toBONG.order_eq_ordUnit, ← x.toBONG.order_eq_ordUnit]
    exact hp
  rcases exists_beli2019Lemma712_i_goodBONG a p ε hp' hεUnit with
    ⟨model, hmodelValues⟩
  rcases j.isIsometric_lemma712IBinary_of_negativeQuarterEndpoint hclass with
    ⟨fb⟩
  let fu := x.toBONG.unaryModelLatticeIsometry
  let productToModels := fb.orthogonalProductBasic fu
  let swapModels := Lattice.orthogonalProductSwap
    (q := binaryDiagonalModelSpace p (p * negativeQuarterUnit K)
      (lemma712I_sourceBinaryAdmissible p))
    (r := QuadraticSpace.rescaleUnit a (QuadraticSpace.line K))
    (L := binaryDiagonalModelLattice (K := K))
    (M := unaryModelLattice (K := K))
  let toModel : Lattice.Isometry (q.orthogonalSum r)
      (unaryBinaryModelSpace a p (p * negativeQuarterUnit K)
        (lemma712I_sourceBinaryAdmissible p))
      (Lattice.product J A) (unaryBinaryModelLattice (K := K)) := by
    simpa only [unaryBinaryModelSpace, unaryBinaryModelLattice] using
      productToModels.trans swapModels
  let result := model.mapLatticeIsometry toModel.symm
  refine ⟨result, ?_⟩
  intro i
  apply Units.ext
  change (model.toBONG.mapLatticeIsometry toModel.symm).value i =
    ((lemma712ITargetValues a ε i : Kˣ) : K)
  rw [BONG.value_mapLatticeIsometry]
  exact congrArg Units.val (hmodelValues i)

end BONG.GoodBONG

end Bong
