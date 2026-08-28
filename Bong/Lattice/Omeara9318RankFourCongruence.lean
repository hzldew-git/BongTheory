/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9310GeneralWeightCoordinates
import Bong.Lattice.Omeara9318RankFourParameterProof
import Bong.Lattice.OmearaBinaryModularSplitting
import Bong.Lattice.OrthogonalDecompositionDeterminant

/-!
# The discriminant congruence in O'Meara 93:18(iii)

This file proves the arithmetic assertion abbreviated in O'Meara's text by
"it follows from Example 93:10 that alpha lies in `ab O`".  A quaternary
unimodular lattice is split into two binary unimodular lattices.  The
branch-independent form of 93:10 writes their Gram matrices as
`A(a_i, beta_i)`, with `a_i` in the ambient norm ideal and `beta_i` in the
ambient weight ideal.  Therefore both products `a_i beta_i` lie in `ab O`,
and

`(1 - a_0 beta_0) (1 - a_1 beta_1) = 1 + alpha`

with `alpha` in `ab O`.  The left side represents the actual determinant
class.  No classification law or new local arithmetic interface is used.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private theorem mem_product_principalIdeal_of_mem_factors
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

private theorem one_sub_products_sub_one_mem
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

/-- The determinant class of a standard general O'Meara plane is represented
by its two-by-two Gram determinant `alpha * beta - 1`. -/
theorem determinantClass_omearaGeneralPlane
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1) :
    determinantClass
        (QuadraticSpace.omearaGeneralPlane
          alpha beta hnondegenerate)
        (hyperbolicPlaneLattice (K := K)) =
      unitSquareClass K
        (Units.mk0 (alpha * beta - 1)
          (sub_ne_zero.mpr hnondegenerate)) := by
  let p := QuadraticSpace.omearaGeneralPlane
    alpha beta hnondegenerate
  change determinantClass p
      (basisLattice (Pi.basisFun K (Fin 2))) = _
  rw [← unitSquareClass_gramUnitOfBasis_eq_determinantClass
    p (Pi.basisFun K (Fin 2))]
  apply congrArg (unitSquareClass K)
  apply Units.ext
  let A := LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin 2)) p.bilin
  have hA : A = !![alpha, 1; 1, beta] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, p, LinearMap.BilinForm.toMatrix_apply,
        QuadraticSpace.omearaGeneralPlane_bilin_apply,
        Pi.basisFun_apply]
  change A.det = alpha * beta - 1
  rw [hA]
  simp [Matrix.det_fin_two_of]

/-- Complete output of the determinant-congruence step of 93:18(iii). -/
structure Omeara9318RankFourCongruenceData
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  parameters : Omeara9318RankFourModelParameters K
  parameters_a : parameters.a = a
  parameters_b : parameters.b =
    uniformizerPowerUnit K (weightIdealOrder q L)
  normGroupSet_eq_common :
    normGroupSet q L =
      integralSquareCoset (a : K)
        (principalIdeal (K := K) (parameters.b : K))
  determinantClass_eq_d :
    determinantClass q L = unitSquareClass K parameters.d

set_option maxHeartbeats 3000000 in

/-- O'Meara 93:18(iii), up to the final field-Hasse choice between the two
explicit models: construct `b`, `alpha`, prove `alpha ∈ ab O`, and identify
both the norm group and determinant class of the actual lattice. -/
noncomputable def omeara9318RankFourCongruenceData
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 4)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L)) :
    Omeara9318RankFourCongruenceData q L a := by
  letI : Module.Finite K V := L.moduleFinite
  let W : Int := weightIdealOrder q L
  let b : Kˣ := uniformizerPowerUnit K W
  have hbOrder : ordUnit K b = W := by
    exact ordUnit_uniformizerPowerUnit W
  have hpos : 0 < finrank K V := by omega
  have haNonneg : 0 ≤ ordUnit K a := by
    have hnormScale := normIdeal_le_scaleIdeal q L
    rw [ha.2, hmodular.scaleIdeal_eq_principal hpos] at hnormScale
    have hord : ord K (1 : K) ≤ ord K (a : K) :=
      (principalIdeal_le_iff_ord_ge
        (Units.ne_zero a) (one_ne_zero : (1 : K) ≠ 0)).1 hnormScale
    rw [ord_one, ← coe_ordUnit K a] at hord
    exact WithTop.coe_le_coe.mp hord
  have haLeW : ordUnit K a ≤ W := by
    exact normGeneratorOrder_le_weightIdealOrder a ha
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
  have hbLeA : principalIdeal (K := K) (b : K) ≤
      principalIdeal (K := K) (a : K) := by
    apply (principalIdeal_le_iff_ord_ge
      (Units.ne_zero b) (Units.ne_zero a)).2
    rw [← coe_ordUnit, ← coe_ordUnit, hbOrder]
    exact WithTop.coe_le_coe.mpr haLeW
  have hTwoLeB : principalIdeal (K := K) (2 : K) ≤
      principalIdeal (K := K) (b : K) := by
    rw [← twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      hmodular hpos, hbIdeal]
    exact twoScaleIdeal_le_weightIdeal q L
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
    exact mem_product_principalIdeal_of_mem_factors
      (hakMemA i) (hbetaMemB i)
  have habIntegral : (a : K) * (b : K) ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem haIntegral hbIntegral
  let alpha : K := (1 - t 0) * (1 - t 1) - 1
  have halphaMem : alpha ∈
      principalIdeal (K := K) ((a : K) * (b : K)) := by
    exact one_sub_products_sub_one_mem habIntegral (htMem 0) (htMem 1)
  have habNonneg : 0 ≤ ordUnit K a + ordUnit K b := by
    rw [hbOrder]
    omega
  have habNe : ordUnit K a + ordUnit K b ≠ 0 := by
    intro hz
    have hsum : ordUnit K a + W = 0 := by
      simpa only [hbOrder] using hz
    have hzeroOdd : Odd (0 : Int) := by
      rw [← hsum]
      exact hodd
    exact Int.not_odd_zero hzeroOdd
  have habPos : 0 < ordUnit K a + ordUnit K b :=
    lt_of_le_of_ne habNonneg (Ne.symm habNe)
  have halphaMax : IsInMaximalIdeal K alpha := by
    rw [IsInMaximalIdeal]
    have hlower := ord_le_of_mem_principalIdeal
      (mul_ne_zero (Units.ne_zero a) (Units.ne_zero b)) halphaMem
    have habOrder : ord K ((a : K) * (b : K)) =
        ((ordUnit K a + ordUnit K b : Int) : WithTop Int) := by
      rw [ord_mul, ← coe_ordUnit, ← coe_ordUnit]
      norm_cast
    rw [habOrder] at hlower
    exact (show (0 : WithTop Int) <
      ((ordUnit K a + ordUnit K b : Int) : WithTop Int) by
        exact_mod_cast habPos) |>.trans_le hlower
  have hoddAB : Odd (ordUnit K a + ordUnit K b) := by
    simpa only [hbOrder, W] using hodd
  let P := omeara9318RankFourModelParametersOfAlphaIdeal
    a b alpha halphaMax haIntegral hbIntegral hbLeA hTwoLeB
      (by
        rw [principalIdeal, Submodule.span_le, Set.singleton_subset_iff]
        exact halphaMem)
      hoddAB
  have hnormGroup : normGroupSet q L =
      integralSquareCoset (a : K)
        (principalIdeal (K := K) (b : K)) := by
    rw [hbIdeal]
    exact normGroupSet_eq_integralSquareCoset_weightIdeal a ha
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
  have hdetClass : determinantClass q L = unitSquareClass K P.d := by
    let u₀ : Kˣ := Units.mk0 (t 0 - 1)
      (sub_ne_zero.mpr (C 0).nondegenerate)
    let u₁ : Kˣ := Units.mk0 (t 1 - 1)
      (sub_ne_zero.mpr (C 1).nondegenerate)
    have hdValue : (P.d : K) = (1 - t 0) * (1 - t 1) := by
      change 1 + P.alpha = (1 - t 0) * (1 - t 1)
      rw [show P.alpha = alpha by rfl]
      dsimp only [alpha]
      ring
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
      _ = unitSquareClass K P.d := by
        apply congrArg (unitSquareClass K)
        apply Units.ext
        change (t 0 - 1) * (t 1 - 1) = (P.d : K)
        rw [hdValue]
        ring
  exact
    { parameters := P
      parameters_a := rfl
      parameters_b := rfl
      normGroupSet_eq_common := hnormGroup
      determinantClass_eq_d := hdetClass }

end Lattice

end Bong
