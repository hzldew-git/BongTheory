/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9310GeneralWeightCoordinates
import Bong.Lattice.Omeara9318RankFourCongruence
import Bong.Lattice.OmearaBinaryModularSplitting
import Bong.Lattice.OrthogonalDecompositionDeterminant
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Dyadic.UnitsCongruentModuloAlgebra

/-!
# The parity-free rank-four determinant congruence in O'Meara 93:10

The determinant calculation used at the start of the necessity proof of
O'Meara 93:28 does not require the odd-order hypothesis of 93:18(iii).
For a quaternary unimodular lattice with norm generator `a`, split the
lattice into two binary unimodular planes and put each plane in the general
93:10 form `A(a_i, beta_i)`.  Both products `a_i beta_i` lie in
`a w(L)`, so the determinant representative

`(1 - a_0 beta_0) (1 - a_1 beta_1)`

is congruent to one modulo `a w(L)`.  This file records that calculation
without any parity or classification-law input.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private theorem mem_product_principalIdeal_of_mem_factors_9310
    {a b x y : K}
    (hx : x ∈ principalIdeal (K := K) a)
    (hy : y ∈ principalIdeal (K := K) b) :
    x * y ∈ principalIdeal (K := K) (a * b) := by
  rw [principalIdeal, Submodule.mem_span_singleton] at hx hy ⊢
  rcases hx with ⟨c, hc⟩
  rcases hy with ⟨d, hd⟩
  refine ⟨c * d, ?_⟩
  have hcx : algebraMap (IntegerRing K) K c * a = x := by
    simpa only [Algebra.smul_def] using hc
  have hdy : algebraMap (IntegerRing K) K d * b = y := by
    simpa only [Algebra.smul_def] using hd
  change
    (algebraMap (IntegerRing K) K c *
        algebraMap (IntegerRing K) K d) * (a * b) = x * y
  rw [← hcx, ← hdy]
  ring

private theorem one_sub_products_sub_one_mem_9310
    {g t₀ t₁ : K} (hg : g ∈ IntegerRing K)
    (ht₀ : t₀ ∈ principalIdeal (K := K) g)
    (ht₁ : t₁ ∈ principalIdeal (K := K) g) :
    (1 - t₀) * (1 - t₁) - 1 ∈ principalIdeal (K := K) g := by
  rw [principalIdeal, Submodule.mem_span_singleton] at ht₀ ht₁ ⊢
  rcases ht₀ with ⟨c₀, hc₀⟩
  rcases ht₁ with ⟨c₁, hc₁⟩
  let gO : IntegerRing K := ⟨g, hg⟩
  refine ⟨-c₀ - c₁ + c₀ * c₁ * gO, ?_⟩
  have h₀ : algebraMap (IntegerRing K) K c₀ * g = t₀ := by
    simpa only [Algebra.smul_def] using hc₀
  have h₁ : algebraMap (IntegerRing K) K c₁ * g = t₁ := by
    simpa only [Algebra.smul_def] using hc₁
  have h₀' : (c₀ : K) * g = t₀ := h₀
  have h₁' : (c₁ : K) * g = t₁ := h₁
  change
    ((-(c₀ : K) - (c₁ : K)) + (c₀ : K) * (c₁ : K) * g) * g =
      (1 - t₀) * (1 - t₁) - 1
  rw [← h₀', ← h₁']
  ring

/-- Witness-level output of the parity-free rank-four determinant
calculation. -/
structure Omeara9310RankFourDeterminantCongruenceData
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  representative : Kˣ
  determinantClass_eq_representative :
    determinantClass q L = unitSquareClass K representative
  representative_sub_one_mem :
    (representative : K) - 1 ∈
      scalarIdeal (a : K) (weightIdeal q L)

set_option maxHeartbeats 3000000 in

/-- O'Meara 93:10, in the quaternary unimodular form used by the necessity
proof of 93:28. -/
noncomputable def omeara9310RankFourDeterminantCongruenceData
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 4)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a) :
    Omeara9310RankFourDeterminantCongruenceData q L a := by
  letI : Module.Finite K V := L.moduleFinite
  let W : Int := weightIdealOrder q L
  let b : Kˣ := uniformizerPowerUnit K W
  have hbOrder : ordUnit K b = W := ordUnit_uniformizerPowerUnit W
  have hpos : 0 < finrank K V := by omega
  have haNonneg : 0 ≤ ordUnit K a := by
    have hnormScale := normIdeal_le_scaleIdeal q L
    rw [ha.2, hmodular.scaleIdeal_eq_principal hpos] at hnormScale
    have hord : ord K (1 : K) ≤ ord K (a : K) :=
      (principalIdeal_le_iff_ord_ge
        (Units.ne_zero a) (one_ne_zero : (1 : K) ≠ 0)).1 hnormScale
    rw [ord_one, ← coe_ordUnit K a] at hord
    exact WithTop.coe_le_coe.mp hord
  have haLeW : ordUnit K a ≤ W :=
    normGeneratorOrder_le_weightIdealOrder a ha
  have hWNonneg : 0 ≤ W := haNonneg.trans haLeW
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit]
    exact WithTop.coe_nonneg.mpr haNonneg
  have hbIntegral : (b : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit, hbOrder]
    exact WithTop.coe_nonneg.mpr hWNonneg
  have hbIdeal : principalIdeal (K := K) (b : K) =
      weightIdeal q L := by
    calc
      principalIdeal (K := K) (b : K) =
          powerIdeal (K := K) (ordUnit K b) :=
        principalIdeal_eq_powerIdeal b
      _ = powerIdeal (K := K) W := by rw [hbOrder]
      _ = weightIdeal q L := (weightIdeal_eq_powerIdeal q L).symm
  let D := binaryModularSplittingData q L (1 : Kˣ)
    hmodular (by omega)
  have hcomponentRank (i : Fin 2) :
      finrank K (D.decomposition.component i).carrier = 2 := by
    fin_cases i
    · exact D.first_rank
    · have htotal :=
        D.decomposition.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
      have hsum :
          finrank K (D.decomposition.component 0).carrier +
              finrank K (D.decomposition.component 1).carrier = 4 := by
        change finrank K
            ((D.decomposition.component 0).carrier ×
              (D.decomposition.component 1).carrier) = finrank K V at htotal
        simpa only [Module.finrank_prod, hrank] using htotal
      change finrank K (D.decomposition.component (1 : Fin 2)).carrier = 2
      have hfirst :
          finrank K (D.decomposition.component (0 : Fin 2)).carrier = 2 :=
        D.first_rank
      omega
  have hcomponentPos (i : Fin 2) :
      0 < finrank K (D.decomposition.component i).carrier := by
    rw [hcomponentRank i]
    omega
  let hxExists (i : Fin 2) := exists_isNormGenerator_of_finrank_pos
    (D.decomposition.component i).space
    (D.decomposition.component i).lattice (hcomponentPos i)
  let x (i : Fin 2) := Classical.choose (hxExists i)
  have hx (i : Fin 2) : IsNormGenerator
      (D.decomposition.component i).space
      (D.decomposition.component i).lattice (x i) :=
    (Classical.choose_spec (hxExists i)).1
  have hxne (i : Fin 2) :
      (D.decomposition.component i).space.quadratic (x i) ≠ 0 :=
    (Classical.choose_spec (hxExists i)).2
  let ak (i : Fin 2) : Kˣ := Units.mk0
    ((D.decomposition.component i).space.quadratic (x i)) (hxne i)
  have hak (i : Fin 2) : IsNormGeneratorValue
      (D.decomposition.component i).space
      (D.decomposition.component i).lattice (ak i) :=
    (hx i).isNormGeneratorValue (hxne i)
  let C (i : Fin 2) := omeara9310GeneralWeightCoordinatesData
    (D.decomposition.component_modular_of_ambient hmodular i)
    (hcomponentRank i) (x i) (hx i) (hxne i)
  have hcomponentNormLe (i : Fin 2) :
      normIdeal (D.decomposition.component i).space
          (D.decomposition.component i).lattice ≤ normIdeal q L := by
    rw [D.decomposition.normIdeal_eq_iSup_component]
    exact le_iSup (fun j ↦
      normIdeal (D.decomposition.component j).space
        (D.decomposition.component j).lattice) i
  have hakMemA (i : Fin 2) :
      (ak i : K) ∈ principalIdeal (K := K) (a : K) := by
    rw [← ha.2]
    apply hcomponentNormLe i
    rw [hak i |>.2]
    exact generator_mem_principalIdeal (K := K) (ak i : K)
  have hweightFormula :=
    D.decomposition.weightIdeal_eq_weightIdealExpression a ha ak hak
  have hcomponentWeightLe (i : Fin 2) :
      weightIdeal (D.decomposition.component i).space
          (D.decomposition.component i).lattice ≤ weightIdeal q L := by
    rw [hweightFormula]
    exact D.decomposition.componentWeight_le_weightIdealExpression a ak i
  have hbetaMemB (i : Fin 2) :
      (C i).beta ∈ principalIdeal (K := K) (b : K) := by
    rw [hbIdeal]
    exact hcomponentWeightLe i (C i).beta_mem_weight
  let t (i : Fin 2) : K := (ak i : K) * (C i).beta
  have htMem (i : Fin 2) :
      t i ∈ principalIdeal (K := K) ((a : K) * (b : K)) := by
    exact mem_product_principalIdeal_of_mem_factors_9310
      (hakMemA i) (hbetaMemB i)
  have habIntegral : (a : K) * (b : K) ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem haIntegral hbIntegral
  have halphaMem : (1 - t 0) * (1 - t 1) - 1 ∈
      principalIdeal (K := K) ((a : K) * (b : K)) :=
    one_sub_products_sub_one_mem_9310 habIntegral (htMem 0) (htMem 1)
  let d : Kˣ := Units.mk0 ((t 0 - 1) * (t 1 - 1))
    (mul_ne_zero
      (sub_ne_zero.mpr (C 0).nondegenerate)
      (sub_ne_zero.mpr (C 1).nondegenerate))
  have hcomponentDet (i : Fin 2) :
      determinantClass (D.decomposition.component i).space
          (D.decomposition.component i).lattice =
        unitSquareClass K
          (Units.mk0 (t i - 1)
            (sub_ne_zero.mpr (C i).nondegenerate)) := by
    calc
      determinantClass (D.decomposition.component i).space
          (D.decomposition.component i).lattice =
          determinantClass
            (QuadraticSpace.omearaGeneralPlane
              ((D.decomposition.component i).space.quadratic (x i))
              (C i).beta (C i).nondegenerate)
            (hyperbolicPlaneLattice (K := K)) :=
        determinantClass_eq_of_isometry (C i).isometry
      _ = unitSquareClass K
          (Units.mk0
            (((D.decomposition.component i).space.quadratic (x i)) *
              (C i).beta - 1) (sub_ne_zero.mpr (C i).nondegenerate)) :=
        determinantClass_omearaGeneralPlane _ _ _
      _ = unitSquareClass K
          (Units.mk0 (t i - 1)
            (sub_ne_zero.mpr (C i).nondegenerate)) := by
        congr 2
  have hdetClass : determinantClass q L = unitSquareClass K d := by
    let u₀ : Kˣ := Units.mk0 (t 0 - 1)
      (sub_ne_zero.mpr (C 0).nondegenerate)
    let u₁ : Kˣ := Units.mk0 (t 1 - 1)
      (sub_ne_zero.mpr (C 1).nondegenerate)
    calc
      determinantClass q L =
          determinantClass (D.decomposition.component 0).space
              (D.decomposition.component 0).lattice *
            determinantClass (D.decomposition.component 1).space
              (D.decomposition.component 1).lattice :=
        D.decomposition.determinantClass_eq_mul_components
      _ = unitSquareClass K u₀ * unitSquareClass K u₁ := by
        rw [hcomponentDet 0, hcomponentDet 1]
      _ = unitSquareClass K (u₀ * u₁) :=
        (unitSquareClass_mul K u₀ u₁).symm
      _ = unitSquareClass K d := by
        apply congrArg (unitSquareClass K)
        apply Units.ext
        rfl
  have habIdeal : scalarIdeal (a : K) (weightIdeal q L) =
      principalIdeal (K := K) ((a * b : Kˣ) : K) := by
    rw [← hbIdeal]
    exact scalarIdeal_principalIdeal_units a b
  exact
    { representative := d
      determinantClass_eq_representative := hdetClass
      representative_sub_one_mem := by
        rw [habIdeal]
        change (t 0 - 1) * (t 1 - 1) - 1 ∈
          principalIdeal (K := K) ((a : K) * (b : K))
        convert halphaMem using 1 <;> ring }

/-- Public congruence form of the parity-free rank-four 93:10
calculation. -/
theorem determinantUnit_congruent_one_mod_norm_mul_weight
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 4)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a) :
    BONG.GoodBONG.UnitsCongruentModulo
      (determinantUnit q L) (1 : Kˣ)
      (scalarIdeal (a : K) (weightIdeal q L)) := by
  let D := omeara9310RankFourDeterminantCongruenceData
    hmodular hrank a ha
  have hrepresentative : BONG.GoodBONG.UnitsCongruentModulo
      D.representative (1 : Kˣ)
      (scalarIdeal (a : K) (weightIdeal q L)) :=
    BONG.GoodBONG.unitsCongruentModulo_one_of_sub_one_mem
      D.representative _ D.representative_sub_one_mem
  apply BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    D.representative (determinantUnit q L) (1 : Kˣ) (1 : Kˣ)
      (scalarIdeal (a : K) (weightIdeal q L))
  · change unitSquareClass K D.representative = determinantClass q L
    exact D.determinantClass_eq_representative.symm
  · rfl
  · exact hrepresentative

end Lattice

end Bong
