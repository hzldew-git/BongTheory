/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanBoundaryOdd
import Bong.Bong.Beli2009OrthogonalIdealProof

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The four candidates in the even-boundary order formula: parity,
quadratic defect, right weight, and left weight. -/
noncomputable def evenBoundaryCandidateMinimum
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ) : WithTop ℚ :=
  let s := J.fundamentalScaleOrder (boundaryLeftIndex i)
  let u := ordUnit K a
  let v := ordUnit K b
  let parity := (u + v) / 2 - s + ramificationIndex K
  let defectBase := u + v - 2 * s
  let rightWeight := u - 2 * s +
    J.fundamentalWeightOrder (boundaryRightIndex i)
  let leftWeight := v - 2 * s +
    J.fundamentalWeightOrder (boundaryLeftIndex i)
  min (((parity : Int) : ℚ) : WithTop ℚ)
    (min ((((defectBase : Int) : ℚ) : WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K) (a * b))
      (min (((rightWeight : Int) : ℚ) : WithTop ℚ)
        (((leftWeight : Int) : ℚ) : WithTop ℚ)))

/-- The right cross term in O'Meara 93:26 may be computed with any
norm generator of the two fundamental layers. -/
theorem rightCrossIdeal_le_productDefect_sup_parity_of_even_of_generators
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryLeftIndex i)) a)
    (hb : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryRightIndex i)) b)
    (heven : Even (J.boundaryNormOrderSum i)) :
    scalarIdeal (a : K)
        (J.fundamentalWeightIdeal (boundaryRightIndex i)) ≤
      J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i := by
  let li : Fin (t + 1) := boundaryLeftIndex i
  let ri : Fin (t + 1) := boundaryRightIndex i
  have haOrder : ordUnit K a =
      ordUnit K (J.fundamentalNormGenerator li) := by
    apply (principalIdeal_eq_iff_ordUnit_eq a
      (J.fundamentalNormGenerator li)).mp
    exact ha.2.symm.trans (J.fundamentalNormGenerator_spec li).2
  have hbOrder : ordUnit K b =
      ordUnit K (J.fundamentalNormGenerator ri) := by
    apply (principalIdeal_eq_iff_ordUnit_eq b
      (J.fundamentalNormGenerator ri)).mp
    exact hb.2.symm.trans (J.fundamentalNormGenerator_spec ri).2
  rcases weightIdeal_eq_twoScale_or_odd b hb with htwo | hodd
  · have hdual := J.fundamentalNormGenerator_order_sub_two_scale_anti
        (i := li) (j := ri) (boundaryLeftIndex_le_rightIndex i)
    change scalarIdeal (a : K)
      (weightIdeal q (J.fundamentalLattice ri)) ≤ _
    rw [htwo, J.fundamentalTwoScaleIdeal_eq_powerIdeal,
      scalarIdeal_powerIdeal_units]
    apply le_trans ?_ _root_.le_sup_right
    unfold boundaryParityIdeal
    rw [twiceIdeal_powerIdeal, powerIdeal_le_iff]
    dsimp only [li, ri] at hdual haOrder hbOrder ⊢
    unfold boundaryNormOrderSum at heven ⊢
    unfold fundamentalScaleOrder at hdual ⊢
    rcases heven with ⟨m, hm⟩
    omega
  · let g : Kˣ := uniformizerPowerUnit K
      (weightIdealOrder q (J.fundamentalLattice ri))
    change Odd (ordUnit K b +
      weightIdealOrder q (J.fundamentalLattice ri)) at hodd
    have hw : J.fundamentalWeightIdeal ri =
        principalIdeal (K := K) (g : K) := by
      change weightIdeal q (J.fundamentalLattice ri) = _
      rw [weightIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
        ordUnit_uniformizerPowerUnit]
    have hgWeight : (g : K) ∈ J.fundamentalWeightIdeal ri := by
      rw [hw]
      exact generator_mem_principalIdeal _
    have hgGroup : (g : K) ∈ J.fundamentalNormGroup ri := by
      change (g : K) ∈ weightIdeal q (J.fundamentalLattice ri) at hgWeight
      change (g : K) ∈ normGroupSet q (J.fundamentalLattice ri)
      exact weightIdeal_subset_normGroupSet b hb hgWeight
    have hproductOdd : Odd (ordUnit K a + ordUnit K g) := by
      dsimp only [g]
      rw [ordUnit_uniformizerPowerUnit]
      rcases heven with ⟨m, hm⟩
      rcases hodd with ⟨k, hk⟩
      refine ⟨m + k - ordUnit K b, ?_⟩
      dsimp only [li, ri] at haOrder hbOrder
      unfold boundaryNormOrderSum at hm
      omega
    have hle : scalarIdeal (a : K)
        (principalIdeal (K := K) (g : K)) ≤
        productDefectSum
          (J.fundamentalNormGroup li) (J.fundamentalNormGroup ri) := by
      exact scalarIdeal_le_productDefectSum_of_odd
        a g ha.1 hgGroup hproductOdd
    rw [← hw] at hle
    unfold boundaryProductDefectSum
    exact hle.trans _root_.le_sup_left

/-- Symmetric left cross term with arbitrary norm generators. -/
theorem leftCrossIdeal_le_productDefect_sup_parity_of_even_of_generators
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryLeftIndex i)) a)
    (hb : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryRightIndex i)) b)
    (heven : Even (J.boundaryNormOrderSum i)) :
    scalarIdeal (b : K)
        (J.fundamentalWeightIdeal (boundaryLeftIndex i)) ≤
      J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i := by
  let li : Fin (t + 1) := boundaryLeftIndex i
  let ri : Fin (t + 1) := boundaryRightIndex i
  have haOrder : ordUnit K a =
      ordUnit K (J.fundamentalNormGenerator li) := by
    apply (principalIdeal_eq_iff_ordUnit_eq a
      (J.fundamentalNormGenerator li)).mp
    exact ha.2.symm.trans (J.fundamentalNormGenerator_spec li).2
  have hbOrder : ordUnit K b =
      ordUnit K (J.fundamentalNormGenerator ri) := by
    apply (principalIdeal_eq_iff_ordUnit_eq b
      (J.fundamentalNormGenerator ri)).mp
    exact hb.2.symm.trans (J.fundamentalNormGenerator_spec ri).2
  rcases weightIdeal_eq_twoScale_or_odd a ha with htwo | hodd
  · have hmono := J.fundamentalNormGenerator_order_mono
        (i := li) (j := ri) (boundaryLeftIndex_le_rightIndex i)
    change scalarIdeal (b : K)
      (weightIdeal q (J.fundamentalLattice li)) ≤ _
    rw [htwo, J.fundamentalTwoScaleIdeal_eq_powerIdeal,
      scalarIdeal_powerIdeal_units]
    apply le_trans ?_ _root_.le_sup_right
    unfold boundaryParityIdeal
    rw [twiceIdeal_powerIdeal, powerIdeal_le_iff]
    dsimp only [li, ri] at hmono haOrder hbOrder ⊢
    unfold boundaryNormOrderSum at heven ⊢
    rcases heven with ⟨m, hm⟩
    omega
  · let g : Kˣ := uniformizerPowerUnit K
      (weightIdealOrder q (J.fundamentalLattice li))
    change Odd (ordUnit K a +
      weightIdealOrder q (J.fundamentalLattice li)) at hodd
    have hw : J.fundamentalWeightIdeal li =
        principalIdeal (K := K) (g : K) := by
      change weightIdeal q (J.fundamentalLattice li) = _
      rw [weightIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
        ordUnit_uniformizerPowerUnit]
    have hgWeight : (g : K) ∈ J.fundamentalWeightIdeal li := by
      rw [hw]
      exact generator_mem_principalIdeal _
    have hgGroup : (g : K) ∈ J.fundamentalNormGroup li := by
      change (g : K) ∈ weightIdeal q (J.fundamentalLattice li) at hgWeight
      change (g : K) ∈ normGroupSet q (J.fundamentalLattice li)
      exact weightIdeal_subset_normGroupSet a ha hgWeight
    have hproductOdd : Odd (ordUnit K b + ordUnit K g) := by
      dsimp only [g]
      rw [ordUnit_uniformizerPowerUnit]
      rcases heven with ⟨m, hm⟩
      rcases hodd with ⟨k, hk⟩
      refine ⟨m + k - ordUnit K a, ?_⟩
      dsimp only [li, ri] at haOrder hbOrder
      unfold boundaryNormOrderSum at hm
      omega
    have hle : scalarIdeal (b : K)
        (principalIdeal (K := K) (g : K)) ≤
        productDefectSum
          (J.fundamentalNormGroup ri) (J.fundamentalNormGroup li) := by
      exact scalarIdeal_le_productDefectSum_of_odd
        b g hb.1 hgGroup hproductOdd
    rw [← hw] at hle
    rw [productDefectSum_comm] at hle
    unfold boundaryProductDefectSum
    dsimp only [li, ri] at hle ⊢
    exact hle.trans _root_.le_sup_left

/-- O'Meara 93:26 with arbitrary chosen norm generators of the two
fundamental layers. -/
theorem scaledFundamentalIdeal_eq_even_formula_of_generators
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryLeftIndex i)) a)
    (hb : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryRightIndex i)) b)
    (heven : Even (J.boundaryNormOrderSum i)) :
    J.scaledFundamentalIdeal i =
      (((quadraticDefectIdeal (a * b) ⊔
          scalarIdeal (a : K)
            (J.fundamentalWeightIdeal (boundaryRightIndex i))) ⊔
        scalarIdeal (b : K)
          (J.fundamentalWeightIdeal (boundaryLeftIndex i))) ⊔
        J.boundaryParityIdeal i) := by
  let li : Fin (t + 1) := boundaryLeftIndex i
  let ri : Fin (t + 1) := boundaryRightIndex i
  have hA : J.fundamentalWeightIdeal li ≤
      principalIdeal (K := K) (a : K) := by
    change weightIdeal q (J.fundamentalLattice li) ≤ _
    exact weightIdeal_le_principalIdeal a ha
  have hB : J.fundamentalWeightIdeal ri ≤
      principalIdeal (K := K) (b : K) := by
    change weightIdeal q (J.fundamentalLattice ri) ≤ _
    exact weightIdeal_le_principalIdeal b hb
  have hprodUpper : J.boundaryProductDefectSum i ≤
      (quadraticDefectIdeal (a * b) ⊔
        scalarIdeal (a : K) (J.fundamentalWeightIdeal ri)) ⊔
        scalarIdeal (b : K) (J.fundamentalWeightIdeal li) := by
    unfold boundaryProductDefectSum fundamentalNormGroup
    change productDefectSum
        (normGroupSet q (J.fundamentalLattice li))
        (normGroupSet q (J.fundamentalLattice ri)) ≤ _
    rw [normGroupSet_eq_integralSquareCoset_weightIdeal a ha,
      normGroupSet_eq_integralSquareCoset_weightIdeal b hb]
    exact productDefectSum_integralSquareCoset_le a b
      (J.fundamentalWeightIdeal li) (J.fundamentalWeightIdeal ri) hA hB
  have hdefectLower : quadraticDefectIdeal (a * b) ≤
      J.boundaryProductDefectSum i := by
    unfold boundaryProductDefectSum
    exact quadraticDefectIdeal_product_le_productDefectSum
      a b ha.1 hb.1
  have hrightCross : scalarIdeal (a : K)
      (J.fundamentalWeightIdeal ri) ≤
        J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i :=
    J.rightCrossIdeal_le_productDefect_sup_parity_of_even_of_generators
      i a b ha hb heven
  have hleftCross : scalarIdeal (b : K)
      (J.fundamentalWeightIdeal li) ≤
        J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i :=
    J.leftCrossIdeal_le_productDefect_sup_parity_of_even_of_generators
      i a b ha hb heven
  rw [scaledFundamentalIdeal, if_pos heven]
  change J.boundaryProductDefectSum i ⊔ J.boundaryParityIdeal i =
    (((quadraticDefectIdeal (a * b) ⊔
        scalarIdeal (a : K) (J.fundamentalWeightIdeal ri)) ⊔
      scalarIdeal (b : K) (J.fundamentalWeightIdeal li)) ⊔
      J.boundaryParityIdeal i)
  apply le_antisymm
  · exact _root_.sup_le (hprodUpper.trans _root_.le_sup_left)
      _root_.le_sup_right
  · apply _root_.sup_le
    · apply _root_.sup_le
      · apply _root_.sup_le
        · exact hdefectLower.trans _root_.le_sup_left
        · exact hrightCross
      · exact hleftCross
    · exact _root_.le_sup_right

/-- Integral order of the even O'Meara boundary ideal, expressed using an
arbitrary pair of norm generators of the adjacent fundamental layers. -/
noncomputable def evenBoundaryFundamentalOrderOfGenerators
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ) : Int :=
  let li := boundaryLeftIndex i
  let ri := boundaryRightIndex i
  let s := J.fundamentalScaleOrder li
  let u := ordUnit K a
  let v := ordUnit K b
  let parity := (u + v) / 2 - s + ramificationIndex K
  let rightWeight := u - 2 * s + J.fundamentalWeightOrder ri
  let leftWeight := v - 2 * s + J.fundamentalWeightOrder li
  if htop : quadraticDefect K (a * b) = ⊤ then
    min parity (min rightWeight leftWeight)
  else
    min parity (min
      (u + v + Int.ofNat (quadraticDefect K (a * b)).toNat - 2 * s)
      (min rightWeight leftWeight))

theorem fundamentalIdeal_eq_powerIdeal_evenBoundaryFundamentalOrderOfGenerators
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryLeftIndex i)) a)
    (hb : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryRightIndex i)) b)
    (heven : Even (J.boundaryNormOrderSum i)) :
    J.fundamentalIdeal i = powerIdeal (K := K)
      (J.evenBoundaryFundamentalOrderOfGenerators i a b) := by
  let li : Fin (t + 1) := boundaryLeftIndex i
  let ri : Fin (t + 1) := boundaryRightIndex i
  let s : Int := J.fundamentalScaleOrder li
  let d := quadraticDefect K (a * b)
  have haOrder : ordUnit K a =
      ordUnit K (J.fundamentalNormGenerator li) := by
    apply (principalIdeal_eq_iff_ordUnit_eq a
      (J.fundamentalNormGenerator li)).mp
    exact ha.2.symm.trans (J.fundamentalNormGenerator_spec li).2
  have hbOrder : ordUnit K b =
      ordUnit K (J.fundamentalNormGenerator ri) := by
    apply (principalIdeal_eq_iff_ordUnit_eq b
      (J.fundamentalNormGenerator ri)).mp
    exact hb.2.symm.trans (J.fundamentalNormGenerator_spec ri).2
  rw [fundamentalIdeal,
    J.scaledFundamentalIdeal_eq_even_formula_of_generators
      i a b ha hb heven]
  unfold fundamentalWeightIdeal boundaryParityIdeal
  rw [weightIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
    scalarIdeal_powerIdeal_units, scalarIdeal_powerIdeal_units,
    twiceIdeal_powerIdeal]
  change scalarIdeal (((J.scaleGenerator li)⁻¹ ^ 2 : Kˣ) : K)
      (((quadraticDefectIdeal (a * b) ⊔
          powerIdeal (K := K)
            (ordUnit K a + Lattice.weightIdealOrder q
              (J.fundamentalLattice ri))) ⊔
        powerIdeal (K := K)
          (ordUnit K b + Lattice.weightIdealOrder q
            (J.fundamentalLattice li))) ⊔
        powerIdeal (K := K)
          (J.boundaryNormOrderSum i / 2 + s + ramificationIndex K)) = _
  by_cases htop : d = ⊤
  · rw [quadraticDefectIdeal, if_pos htop]
    simp only [bot_sup_eq]
    rw [sup_powerIdeal, sup_powerIdeal, scalarIdeal_powerIdeal_units]
    unfold evenBoundaryFundamentalOrderOfGenerators
    simp only [li, ri, s, d, htop, dite_true]
    apply congrArg (powerIdeal (K := K))
    rw [ordUnit_pow, ordUnit_inv]
    unfold boundaryNormOrderSum at heven ⊢
    unfold fundamentalScaleOrder fundamentalWeightOrder
    rcases heven with ⟨z, hz⟩
    dsimp only [li, ri] at haOrder hbOrder
    omega
  · rw [quadraticDefectIdeal, if_neg htop]
    rw [sup_powerIdeal, sup_powerIdeal, sup_powerIdeal,
      scalarIdeal_powerIdeal_units]
    unfold evenBoundaryFundamentalOrderOfGenerators
    simp only [li, ri, s, d, htop, dite_false]
    apply congrArg (powerIdeal (K := K))
    rw [ordUnit_pow, ordUnit_inv, ordUnit_mul]
    unfold boundaryNormOrderSum at heven ⊢
    unfold fundamentalScaleOrder fundamentalWeightOrder
    rcases heven with ⟨z, hz⟩
    dsimp only [li, ri] at haOrder hbOrder
    omega

noncomputable def evenBoundaryFundamentalOrder
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) : Int :=
  let li := boundaryLeftIndex i
  let ri := boundaryRightIndex i
  let s := J.fundamentalScaleOrder li
  let u := ordUnit K (J.fundamentalNormGenerator li)
  let v := ordUnit K (J.fundamentalNormGenerator ri)
  let parity := (u + v) / 2 - s + ramificationIndex K
  let rightWeight := u - 2 * s + J.fundamentalWeightOrder ri
  let leftWeight := v - 2 * s + J.fundamentalWeightOrder li
  if htop : quadraticDefect K
      (J.fundamentalNormGenerator li * J.fundamentalNormGenerator ri) = ⊤ then
    min parity (min rightWeight leftWeight)
  else
    min parity (min
      (u + v + Int.ofNat (quadraticDefect K
        (J.fundamentalNormGenerator li *
          J.fundamentalNormGenerator ri)).toNat - 2 * s)
      (min rightWeight leftWeight))

theorem fundamentalIdeal_eq_powerIdeal_evenBoundaryFundamentalOrder
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (heven : Even (J.boundaryNormOrderSum i)) :
    J.fundamentalIdeal i =
      powerIdeal (K := K) (J.evenBoundaryFundamentalOrder i) := by
  let li : Fin (t + 1) := boundaryLeftIndex i
  let ri : Fin (t + 1) := boundaryRightIndex i
  let s : Int := J.fundamentalScaleOrder li
  let a : Kˣ := J.fundamentalNormGenerator li
  let b : Kˣ := J.fundamentalNormGenerator ri
  let d := quadraticDefect K (a * b)
  rw [fundamentalIdeal, J.scaledFundamentalIdeal_eq_even_formula i heven]
  unfold fundamentalWeightIdeal boundaryParityIdeal
  rw [weightIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
    scalarIdeal_powerIdeal_units, scalarIdeal_powerIdeal_units,
    twiceIdeal_powerIdeal]
  change scalarIdeal (((J.scaleGenerator li)⁻¹ ^ 2 : Kˣ) : K)
      (((quadraticDefectIdeal (a * b) ⊔
          powerIdeal (K := K)
            (ordUnit K a + Lattice.weightIdealOrder q
              (J.fundamentalLattice ri))) ⊔
        powerIdeal (K := K)
          (ordUnit K b + Lattice.weightIdealOrder q
            (J.fundamentalLattice li))) ⊔
        powerIdeal (K := K)
          (J.boundaryNormOrderSum i / 2 + s + ramificationIndex K)) = _
  by_cases htop : d = ⊤
  · rw [quadraticDefectIdeal, if_pos htop]
    simp only [bot_sup_eq]
    rw [sup_powerIdeal, sup_powerIdeal,
      scalarIdeal_powerIdeal_units]
    unfold evenBoundaryFundamentalOrder
    simp only [li, ri, s, a, b, d, htop, dite_true]
    apply congrArg (powerIdeal (K := K))
    rw [ordUnit_pow, ordUnit_inv]
    unfold boundaryNormOrderSum at heven ⊢
    unfold fundamentalScaleOrder fundamentalWeightOrder
    rcases heven with ⟨z, hz⟩
    omega
  · rw [quadraticDefectIdeal, if_neg htop]
    rw [sup_powerIdeal, sup_powerIdeal, sup_powerIdeal,
      scalarIdeal_powerIdeal_units]
    unfold evenBoundaryFundamentalOrder
    simp only [li, ri, s, a, b, d, htop, dite_false]
    apply congrArg (powerIdeal (K := K))
    rw [ordUnit_pow, ordUnit_inv, ordUnit_mul]
    unfold boundaryNormOrderSum at heven ⊢
    unfold fundamentalScaleOrder fundamentalWeightOrder
    rcases heven with ⟨z, hz⟩
    omega

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m t : Nat}
  {a : GoodBONG q L (m + 1)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

/-- The signed terminal norm generator on the left of a Jordan boundary. -/
noncomputable def boundaryLeftValue
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) : Kˣ :=
  -(P.terminalValue (Lattice.JordanDecomposition.boundaryLeftIndex i))

/-- The first profile value on the right of a Jordan boundary. -/
noncomputable def boundaryRightValue
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) : Kˣ :=
  let ri := Lattice.JordanDecomposition.boundaryRightIndex i
  let first : Fin (J.toOrthogonalDecomposition.componentRank ri) :=
    ⟨0, J.component_finrank_pos ri⟩
  a.valueUnit (P.indexEquiv.symm ⟨ri, first⟩)

theorem boundaryRightValue_eq_valueUnit_succ
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) :
    P.boundaryRightValue i = a.valueUnit (P.boundaryIndex i).succ := by
  let li : Fin (t + 1) := Lattice.JordanDecomposition.boundaryLeftIndex i
  let ri : Fin (t + 1) := Lattice.JordanDecomposition.boundaryRightIndex i
  let last : Fin (J.toOrthogonalDecomposition.componentRank li) :=
    ⟨J.toOrthogonalDecomposition.componentRank li - 1, by
      exact Nat.sub_lt (J.component_finrank_pos li) Nat.zero_lt_one⟩
  let first : Fin (J.toOrthogonalDecomposition.componentRank ri) :=
    ⟨0, J.component_finrank_pos ri⟩
  let leftGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨li, last⟩
  let rightGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨ri, first⟩
  have hnext : rightGlobal.val = leftGlobal.val + 1 := by
    apply P.inverse_index_val_next_component li ri
    · rfl
    · dsimp only [last]
      exact Nat.sub_add_cancel (J.component_finrank_pos li)
  have hglobal : (P.boundaryIndex i).succ = rightGlobal := by
    apply Fin.ext
    simp only [Fin.val_succ]
    exact hnext.symm
  rw [hglobal]
  rfl

/-- The product of the actual signed endpoint generators is Beli's
adjacent product times a square. -/
theorem boundaryLeftValue_mul_boundaryRightValue
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) :
    P.boundaryLeftValue i * P.boundaryRightValue i =
      a.adjacentProduct (P.boundaryIndex i) *
        uniformizerPowerUnit K
          (ordUnit K (J.normGenerator
              (Lattice.JordanDecomposition.boundaryLeftIndex i)) -
            ordUnit K (J.scaleGenerator
              (Lattice.JordanDecomposition.boundaryLeftIndex i))) ^ 2 := by
  let li : Fin (t + 1) := Lattice.JordanDecomposition.boundaryLeftIndex i
  let last : Fin (J.toOrthogonalDecomposition.componentRank li) :=
    ⟨J.toOrthogonalDecomposition.componentRank li - 1, by
      exact Nat.sub_lt (J.component_finrank_pos li) Nat.zero_lt_one⟩
  let leftGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨li, last⟩
  have hleft : (P.boundaryIndex i).castSucc = leftGlobal := by
    apply Fin.ext
    rfl
  rw [P.boundaryRightValue_eq_valueUnit_succ]
  unfold boundaryLeftValue terminalValue GoodBONG.adjacentProduct
  rw [hleft]
  change -(uniformizerPowerUnit K
      (2 * ordUnit K (J.normGenerator li) -
        2 * ordUnit K (J.scaleGenerator li)) *
      a.valueUnit leftGlobal) *
      a.valueUnit (P.boundaryIndex i).succ =
    (-(a.valueUnit leftGlobal *
      a.valueUnit (P.boundaryIndex i).succ)) *
      uniformizerPowerUnit K
        (ordUnit K (J.normGenerator li) -
          ordUnit K (J.scaleGenerator li)) ^ 2
  have hpower : uniformizerPowerUnit K
      (2 * ordUnit K (J.normGenerator li) -
        2 * ordUnit K (J.scaleGenerator li)) =
      uniformizerPowerUnit K
        (ordUnit K (J.normGenerator li) -
          ordUnit K (J.scaleGenerator li)) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [show 2 * ordUnit K (J.normGenerator li) -
        2 * ordUnit K (J.scaleGenerator li) =
        (ordUnit K (J.normGenerator li) -
          ordUnit K (J.scaleGenerator li)) * 2 by ring,
      zpow_mul]
    rfl
  rw [hpower]
  apply Units.ext
  change -((((uniformizerPowerUnit K
      (ordUnit K (J.normGenerator li) -
        ordUnit K (J.scaleGenerator li))) : K) ^ 2) *
      (a.valueUnit leftGlobal : K)) *
      (a.valueUnit (P.boundaryIndex i).succ : K) =
    (-((a.valueUnit leftGlobal : K) *
      (a.valueUnit (P.boundaryIndex i).succ : K))) *
      ((uniformizerPowerUnit K
        (ordUnit K (J.normGenerator li) -
          ordUnit K (J.scaleGenerator li)) : K) ^ 2)
  ring

theorem quadraticDefect_boundaryValues
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) :
    quadraticDefect K (P.boundaryLeftValue i * P.boundaryRightValue i) =
      quadraticDefect K (a.adjacentProduct (P.boundaryIndex i)) := by
  rw [P.boundaryLeftValue_mul_boundaryRightValue i,
    quadraticDefect_mul_square]

end BONG.JordanOrderProfileWitness

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

theorem castComponentCount_fundamentalLattice
    {c d : Nat} (J : JordanDecomposition q L c) (h : c = d)
    (i : Fin d) :
    (J.castComponentCount h).fundamentalLattice i =
      J.fundamentalLattice (Fin.cast h.symm i) := by
  subst d
  rfl

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m c : Nat}
  {a : GoodBONG q L (m + 1)}
  {J : Lattice.JordanDecomposition q L c}

noncomputable def componentFirstValue
    (P : JordanOrderProfileWitness a.toBONG J) (k : Fin c) : Kˣ :=
  let first : Fin (J.toOrthogonalDecomposition.componentRank k) :=
    ⟨0, J.component_finrank_pos k⟩
  a.valueUnit (P.indexEquiv.symm ⟨k, first⟩)

theorem boundaryRightValue_eq_componentFirstValue
    {t : Nat} {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) :
    P.boundaryRightValue i =
      P.componentFirstValue
        (Lattice.JordanDecomposition.boundaryRightIndex i) := by
  rfl

theorem castComponentCount_componentFirstValue
    {d : Nat} (P : JordanOrderProfileWitness a.toBONG J)
    (h : c = d) (k : Fin d) :
    (P.castComponentCount h).componentFirstValue k =
      P.componentFirstValue (Fin.cast h.symm k) := by
  subst d
  rfl

end BONG.JordanOrderProfileWitness

namespace BONG.StrictJordanAdaptedAlignment

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}
  {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (m + 1)}

theorem sourceProfile_componentFirstValue_eq_endpointFirstValue
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.sourceProfile.componentFirstValue k =
      S.weakAlignment.endpoint.sourceEndpoints.profile.endpointFirstValue k := by
  unfold JordanOrderProfileWitness.componentFirstValue
    WeakJordanOrderProfileWitness.endpointFirstValue
    Lattice.WeakJordanDecomposition.endpointFirstIndex
    sourceProfile WeakJordanOrderProfileWitness.toJordanOfStrict
    GoodBONG.valueUnit
  apply congrArg a.toBONG.valueUnit
  apply Fin.ext
  rfl

theorem targetProfile_componentFirstValue_eq_endpointFirstValue
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.targetProfile.componentFirstValue k =
      S.weakAlignment.endpoint.targetEndpoints.profile.endpointFirstValue k := by
  unfold JordanOrderProfileWitness.componentFirstValue
    WeakJordanOrderProfileWitness.endpointFirstValue
    Lattice.WeakJordanDecomposition.endpointFirstIndex
    targetProfile WeakJordanOrderProfileWitness.toJordanOfStrict
    GoodBONG.valueUnit
  apply congrArg b.toBONG.valueUnit
  apply Fin.ext
  rfl

theorem sourceBoundaryLeftValue_isNormGeneratorValue
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    Lattice.IsNormGeneratorValue q
      ((S.sourceJordanSucc h).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      ((S.sourceProfileSucc h).boundaryLeftValue i) := by
  unfold JordanOrderProfileWitness.boundaryLeftValue
  exact (S.sourceTerminalValue_isNormGeneratorValue h _).neg

theorem sourceBoundaryRightValue_isNormGeneratorValue
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    Lattice.IsNormGeneratorValue q
      ((S.sourceJordanSucc h).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex i))
      ((S.sourceProfileSucc h).boundaryRightValue i) := by
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex i
  let k : Fin S.componentCount := Fin.cast h.symm ri
  have hfirst :=
    S.toStrictJordanEndpointAlignment.sourceFirstGenerator_fundamentalLattice k
  unfold sourceJordanSucc sourceProfileSucc
  rw [Lattice.JordanDecomposition.castComponentCount_fundamentalLattice]
  rw [JordanOrderProfileWitness.boundaryRightValue_eq_componentFirstValue,
    JordanOrderProfileWitness.castComponentCount_componentFirstValue]
  rw [show Fin.cast h.symm
      (Lattice.JordanDecomposition.boundaryRightIndex i) = k by rfl,
    S.sourceProfile_componentFirstValue_eq_endpointFirstValue k]
  simpa [sourceJordan, toStrictJordanEndpointAlignment] using hfirst

theorem targetBoundaryLeftValue_isNormGeneratorValue
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    Lattice.IsNormGeneratorValue r
      ((S.targetJordanSucc h).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      ((S.targetProfileSucc h).boundaryLeftValue i) := by
  unfold JordanOrderProfileWitness.boundaryLeftValue
  exact (S.targetTerminalValue_isNormGeneratorValue h _).neg

theorem targetBoundaryRightValue_isNormGeneratorValue
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    Lattice.IsNormGeneratorValue r
      ((S.targetJordanSucc h).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex i))
      ((S.targetProfileSucc h).boundaryRightValue i) := by
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex i
  let k : Fin S.componentCount := Fin.cast h.symm ri
  have hfirst :=
    S.toStrictJordanEndpointAlignment.targetFirstGenerator_fundamentalLattice k
  unfold targetJordanSucc targetProfileSucc
  rw [Lattice.JordanDecomposition.castComponentCount_fundamentalLattice]
  rw [JordanOrderProfileWitness.boundaryRightValue_eq_componentFirstValue,
    JordanOrderProfileWitness.castComponentCount_componentFirstValue]
  rw [show Fin.cast h.symm
      (Lattice.JordanDecomposition.boundaryRightIndex i) = k by rfl,
    S.targetProfile_componentFirstValue_eq_endpointFirstValue k]
  simpa [targetJordan, toStrictJordanEndpointAlignment] using hfirst

end BONG.StrictJordanAdaptedAlignment

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The integer order extracted from the even O'Meara boundary formula,
embedded into `WithTop ℚ`.  This is the four-term minimum in the exact
shape needed to compare with Beli's alpha candidates. -/
theorem coe_evenBoundaryFundamentalOrderOfGenerators
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ) :
    ((((J.evenBoundaryFundamentalOrderOfGenerators i a b : Int) : ℚ) :
        WithTop ℚ)) =
      J.evenBoundaryCandidateMinimum i a b := by
  unfold evenBoundaryCandidateMinimum
  cases hq : quadraticDefect K (a * b) with
  | top =>
      have hdorder : BONG.GoodBONG.defectOrder (K := K) (a * b) = ⊤ := by
        unfold BONG.GoodBONG.defectOrder
        rw [hq]
        rfl
      rw [hdorder]
      unfold evenBoundaryFundamentalOrderOfGenerators
      simp [hq]
  | coe d =>
      have hdorder : BONG.GoodBONG.defectOrder (K := K) (a * b) =
          ((d : ℚ) : WithTop ℚ) := by
        unfold BONG.GoodBONG.defectOrder
        rw [hq]
        rfl
      rw [hdorder]
      unfold evenBoundaryFundamentalOrderOfGenerators
      simp [hq]
      congr 2
      apply congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
      push_cast
      ring

/-- The actual O'Meara fundamental ideal, packaged with the explicit
integer order supplied by the even-boundary formula. -/
noncomputable def evenOrderedFundamentalIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryLeftIndex i)) a)
    (hb : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryRightIndex i)) b)
    (heven : Even (J.boundaryNormOrderSum i)) :
    OrderedFractionalIdeal K where
  carrier := J.fundamentalIdeal i
  order := J.evenBoundaryFundamentalOrderOfGenerators i a b
  carrier_eq_powerIdeal :=
    J.fundamentalIdeal_eq_powerIdeal_evenBoundaryFundamentalOrderOfGenerators
      i a b ha hb heven

/-- Once the four concrete candidates have been identified with Beli's
alpha minimum, the order of the packaged even fundamental ideal is alpha. -/
theorem evenOrderedFundamentalIdeal_order_eq_alpha_of_candidateMinimum
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryLeftIndex i)) a)
    (hb : IsNormGeneratorValue q
      (J.fundamentalLattice (boundaryRightIndex i)) b)
    (heven : Even (J.boundaryNormOrderSum i)) (alpha : ℚ)
    (hminimum : J.evenBoundaryCandidateMinimum i a b =
      (alpha : WithTop ℚ)) :
    (((J.evenOrderedFundamentalIdeal i a b ha hb heven).order : Int) : ℚ) =
      alpha := by
  have horder := J.coe_evenBoundaryFundamentalOrderOfGenerators i a b
  rw [hminimum] at horder
  exact WithTop.coe_eq_coe.mp horder

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}

/-- The first coordinate after a Jordan boundary is the sum of all
component ranks up to and including the component on its left. -/
theorem boundaryIndex_succ_val_eq_componentRankPrefix
    {t : Nat} {a : GoodBONG q L (m + 1)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) :
    (P.boundaryIndex i).val + 1 =
      ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex i),
        J.toOrthogonalDecomposition.componentRank k := by
  let li : Fin (t + 1) := Lattice.JordanDecomposition.boundaryLeftIndex i
  let ri : Fin (t + 1) := Lattice.JordanDecomposition.boundaryRightIndex i
  let last : Fin (J.toOrthogonalDecomposition.componentRank li) :=
    ⟨J.toOrthogonalDecomposition.componentRank li - 1, by
      exact Nat.sub_lt (J.component_finrank_pos li) Nat.zero_lt_one⟩
  let first : Fin (J.toOrthogonalDecomposition.componentRank ri) :=
    ⟨0, J.component_finrank_pos ri⟩
  let leftGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨li, last⟩
  let rightGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨ri, first⟩
  have hnext : rightGlobal.val = leftGlobal.val + 1 := by
    apply P.inverse_index_val_next_component li ri
    · rfl
    · dsimp only [last]
      exact Nat.sub_add_cancel (J.component_finrank_pos li)
  have hleft : (P.boundaryIndex i).val = leftGlobal.val := rfl
  have hright : rightGlobal.val =
      ∑ k ∈ Finset.Iio ri, J.toOrthogonalDecomposition.componentRank k := by
    simpa only [rightGlobal, first, Nat.add_zero] using
      P.inverse_index_val ri first
  calc
    (P.boundaryIndex i).val + 1 = leftGlobal.val + 1 := by rw [hleft]
    _ = rightGlobal.val := hnext.symm
    _ = ∑ k ∈ Finset.Iio ri,
        J.toOrthogonalDecomposition.componentRank k := hright

end BONG.JordanOrderProfileWitness

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Component-rank prefix sums are invariant under a cast of the number
of Jordan components. -/
theorem castComponentCount_componentRankPrefix
    {c d : Nat} (J : JordanDecomposition q L c) (h : c = d)
    (i : Fin d) :
    (∑ k ∈ Finset.Iio i, (J.castComponentCount h).componentRank k) =
      ∑ k ∈ Finset.Iio (Fin.cast h.symm i), J.componentRank k := by
  subst d
  rfl

end Lattice.JordanDecomposition

namespace BONG.StrictJordanAdaptedAlignment

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}
  {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (m + 1)}

/-- In an actual strict Jordan-adapted alignment, the BONG coordinate
immediately to the right of a boundary is the start of that Jordan
component. -/
theorem sourceBoundaryIndex_succ_val_eq_componentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    ((S.sourceProfileSucc h).boundaryIndex i).val + 1 =
      S.componentStart (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex i)) := by
  have hsum :=
    (S.sourceProfileSucc h).boundaryIndex_succ_val_eq_componentRankPrefix i
  have hprefix :=
    Lattice.JordanDecomposition.castComponentCount_componentRankPrefix
      S.sourceJordan h
        (Lattice.JordanDecomposition.boundaryRightIndex i)
  calc
    ((S.sourceProfileSucc h).boundaryIndex i).val + 1 =
        ∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex i),
          (S.sourceJordanSucc h).componentRank k := hsum
    _ = ∑ k ∈ Finset.Iio (Fin.cast h.symm
          (Lattice.JordanDecomposition.boundaryRightIndex i)),
        S.sourceJordan.componentRank k := by
      simpa only [sourceJordanSucc] using hprefix
    _ = S.componentStart (Fin.cast h.symm
          (Lattice.JordanDecomposition.boundaryRightIndex i)) := rfl

end BONG.StrictJordanAdaptedAlignment

namespace BONG.JordanOrderProfileWitness

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m t : Nat}
  {a : GoodBONG q L (m + 1)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

/-- At an actual profiled Jordan boundary, the parity and defect terms in
the even O'Meara formula are precisely Beli's half-gap and self-defect
candidates.  The two weight terms are left explicit for the component-rank
analysis of Lemmas 2.15--2.16. -/
theorem evenBoundaryCandidateMinimum_eq_profileMinimum
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t)
    (hleft : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      (P.boundaryLeftValue i))
    (hright : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex i))
      (P.boundaryRightValue i))
    (hterminal : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      (P.terminalValue
        (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (hnorm : ordUnit K
        (J.normGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i)) =
      ordUnit K
        (J.fundamentalNormGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (heven : Even (J.boundaryNormOrderSum i)) :
    let rightTerm : WithTop ℚ :=
      (((ordUnit K (P.boundaryLeftValue i) -
          2 * J.fundamentalScaleOrder
            (Lattice.JordanDecomposition.boundaryLeftIndex i) +
          J.fundamentalWeightOrder
            (Lattice.JordanDecomposition.boundaryRightIndex i) : Int) : ℚ) :
        WithTop ℚ)
    let leftTerm : WithTop ℚ :=
      (((ordUnit K (P.boundaryRightValue i) -
          2 * J.fundamentalScaleOrder
            (Lattice.JordanDecomposition.boundaryLeftIndex i) +
          J.fundamentalWeightOrder
            (Lattice.JordanDecomposition.boundaryLeftIndex i) : Int) : ℚ) :
        WithTop ℚ)
    J.evenBoundaryCandidateMinimum i
        (P.boundaryLeftValue i) (P.boundaryRightValue i) =
      min (a.halfGapCandidate (P.boundaryIndex i))
        (min (a.leftDefectCandidate (P.boundaryIndex i)
            (P.boundaryIndex i))
          (min rightTerm leftTerm)) := by
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex i
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex i
  let j : Fin m := P.boundaryIndex i
  let s : Int := J.fundamentalScaleOrder li
  let u : Int := ordUnit K (P.boundaryLeftValue i)
  let v : Int := ordUnit K (P.boundaryRightValue i)
  have hu : u = ordUnit K (J.fundamentalNormGenerator li) := by
    dsimp only [u]
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hleft.2.symm.trans (J.fundamentalNormGenerator_spec li).2
  have hv : v = ordUnit K (J.fundamentalNormGenerator ri) := by
    dsimp only [v]
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hright.2.symm.trans (J.fundamentalNormGenerator_spec ri).2
  have horderLeft : a.order j.castSucc = 2 * s - u := by
    dsimp only [j, s]
    rw [P.order_boundaryIndex i hterminal hnorm, hu]
  have horderRight : a.order j.succ = v := by
    dsimp only [j]
    rw [P.order_boundaryIndex_succ i, hv]
  have hevenUV : Even (u + v) := by
    rw [hu, hv]
    exact heven
  have hparity :
      (((((u + v) / 2 - s + ramificationIndex K : Int) : ℚ) :
          WithTop ℚ)) = a.halfGapCandidate j := by
    unfold GoodBONG.halfGapCandidate
    rw [horderLeft, horderRight]
    rcases hevenUV with ⟨z, hz⟩
    apply congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
    have hhalf : (u + v) / 2 = z := by omega
    have hgap : v - (2 * s - u) = 2 * (z - s) := by omega
    rw [hhalf, hgap]
    push_cast
    ring
  have hdefect :
      (((((u + v - 2 * s : Int) : ℚ) : WithTop ℚ) +
          GoodBONG.defectOrder (K := K)
            (P.boundaryLeftValue i * P.boundaryRightValue i))) =
        a.leftDefectCandidate j j := by
    unfold GoodBONG.leftDefectCandidate GoodBONG.adjacentDefect
    rw [horderLeft, horderRight]
    unfold GoodBONG.defectOrder
    rw [P.quadraticDefect_boundaryValues i]
    congr 2
    norm_cast
    ring
  unfold Lattice.JordanDecomposition.evenBoundaryCandidateMinimum
  dsimp only [li, ri, j, s, u, v] at hparity hdefect ⊢
  rw [hparity, hdefect]

end BONG.JordanOrderProfileWitness

end Bong
