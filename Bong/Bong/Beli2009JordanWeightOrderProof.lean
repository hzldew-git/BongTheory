/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2009JordanWeightOrderBase
import Bong.Bong.AlphaValueExt

/-!
# Beli (2009), Lemma 2.14 in arbitrary rank

This module proves the complete weight-order formula from the binary
calculation, O'Meara's orthogonal-sum weight formula, and Beli's first-block
splittings.  Both the nondecreasing unary cut and the strictly decreasing
binary cut are propagated by strong induction on the rank.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

theorem lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
    {n : Nat} (b : BONG V q L (n + 1)) :
    Lattice.IsNormGeneratorValue q L (b.valueUnit 0) := by
  have h := b.head_isNormGenerator.isNormGeneratorValue
    b.head_isAnisotropic
  let a : Kˣ := Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  have ha : a = b.valueUnit 0 := by
    apply Units.ext
    change q.quadratic b.head = (b.valueUnit 0 : K)
    rw [← b.value_zero_eq_quadratic_head, b.coe_valueUnit]
  simpa [a, ha] using h

end BONG

namespace BONG.GoodBONG

variable [Beli2009WeightIdealData.{u, v} K]

-- General Lemma 2.14 is assembled below from these transport lemmas.

@[simp] theorem lemma214_valueUnit_castLength
    {m n : Nat} (b : GoodBONG q L m) (h : m = n) (i : Fin n) :
    (b.castLength h).valueUnit i = b.valueUnit ⟨i.val, by omega⟩ := by
  subst n
  rfl

theorem lemma214_twoScale_le_firstWeight_of_scale_eq
    (D : Lattice.OrthogonalDecomposition q L 2)
    (hscale : Lattice.scaleIdeal q L =
      Lattice.scaleIdeal (D.component 0).space (D.component 0).lattice) :
    Lattice.twoScaleIdeal q L ≤
      Lattice.weightIdeal (D.component 0).space (D.component 0).lattice := by
  unfold Lattice.twoScaleIdeal
  rw [hscale]
  exact Lattice.twoScaleIdeal_le_weightIdeal
    (D.component 0).space (D.component 0).lattice

theorem lemma214_scaleIdeal_eq_component_of_doubled_order
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {doubled : Int}
    (hambient : Lattice.HasDoubledScaleOrder q L doubled)
    (c : Kˣ)
    (hcomponent : Lattice.scaleIdeal r M =
      Lattice.principalIdeal (K := K) (c : K))
    (hc : 2 * ordUnit K c = doubled) :
    Lattice.scaleIdeal q L = Lattice.scaleIdeal r M := by
  rcases hambient with ⟨s, hs, hsOrder⟩
  rw [hs, hcomponent]
  apply (Lattice.principalIdeal_eq_iff_ordUnit_eq s c).2
  omega

theorem lemma214_add_min (a x y : ℚ) :
    a + min x y = min (a + x) (a + y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
  · rw [min_eq_right h, min_eq_right (by linarith)]

theorem lemma214_withTop_add_min (a x y : WithTop ℚ) :
    a + min x y = min (a + x) (a + y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (by
      simpa [add_comm] using add_le_add_left h a)]
  · rw [min_eq_right h, min_eq_right (by
      simpa [add_comm] using add_le_add_left h a)]

theorem lemma214_ambientSubmodule_eq_bot_of_length_zero
    {n start : Nat} {b : BONG V q L n} {bound : start ≤ n}
    (w : BONG.SegmentWitness b start 0 (by omega)) :
    w.toQuadraticSublattice.ambientSubmodule = ⊥ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyzero : (y : V) = 0 := by
      have hymem : (y : V) ∈ b.segmentCarrier start 0 (by omega) := by
        rw [← w.carrier_eq_segmentCarrier]
        exact y.property
      simpa [BONG.segmentCarrier] using hymem
    change (y : V) ∈ (⊥ : Submodule (IntegerRing K) V)
    rw [hyzero]
    exact Submodule.zero_mem _
  · intro hx
    have hxzero : x = 0 := by simpa using hx
    subst x
    exact ⟨0, w.lattice.zero_mem, rfl⟩

theorem lemma214_promote_component_normGeneratorValue
    (D : Lattice.OrthogonalDecomposition q L 2) (i : Fin 2)
    (ambientValue componentValue : Kˣ)
    (hambient : Lattice.IsNormGeneratorValue q L ambientValue)
    (hcomponent : Lattice.IsNormGeneratorValue
      (D.component i).space (D.component i).lattice componentValue)
    (horder : ordUnit K ambientValue = ordUnit K componentValue) :
    Lattice.IsNormGeneratorValue q L componentValue := by
  constructor
  · exact D.component_normGroupSet_subset i hcomponent.1
  · calc
      Lattice.normIdeal q L =
          Lattice.principalIdeal (K := K) (ambientValue : K) := hambient.2
      _ = Lattice.principalIdeal (K := K) (componentValue : K) :=
        (Lattice.principalIdeal_eq_iff_ordUnit_eq
          ambientValue componentValue).2 horder

/-- The right block at the first Corollary 4.4 cut carries the same first
alpha as the canonical suffix used in Corollary 2.5(ii). -/
theorem lemma214_twoBlockRight_alphaValue_zero_eq_suffix
    {n : Nat} (b : GoodBONG q L (n + 3))
    (S : b.toBONG.TwoBlockSplitWitness 1 (by omega)) :
    ((S.right.toGoodBONG b.good).castLength
        (by omega : n + 3 - 1 = n + 2)).alphaValue 0 =
      ((b.suffixAlphaSegmentWitness (n := n + 1)
        (0 : Fin (n + 2)) (by
          show 1 < n + 2
          omega)).toGoodBONG b.good).alphaValue (0 : Fin (n + 1)) := by
  let right := (S.right.toGoodBONG b.good).castLength
    (by omega : n + 3 - 1 = n + 2)
  let suffix := (b.suffixAlphaSegmentWitness (n := n + 1)
    (0 : Fin (n + 2)) (by
      show 1 < n + 2
      omega)).toGoodBONG b.good
  have hvalues : ∀ i, right.valueUnit i = suffix.valueUnit i := by
    intro i
    rw [show right = (S.right.toGoodBONG b.good).castLength
        (by omega : n + 3 - 1 = n + 2) by rfl,
      lemma214_valueUnit_castLength]
    change S.right.bong.valueUnit ⟨i.val, by omega⟩ = suffix.valueUnit i
    rw [S.right.valueUnit_eq]
    change b.toBONG.valueUnit _ =
      (b.suffixAlphaSegmentWitness (n := n + 1)
        (0 : Fin (n + 2)) (by
          show 1 < n + 2
          omega)).bong.valueUnit i
    rw [(b.suffixAlphaSegmentWitness (n := n + 1)
      (0 : Fin (n + 2)) (by
        show 1 < n + 2
        omega)).valueUnit_eq]
    congr 1
  have halpha := right.alphaValue_eq_of_valueUnits_eq suffix hvalues
    (0 : Fin (n + 1))
  change right.alphaValue 0 = suffix.alphaValue (0 : Fin (n + 1))
  exact halpha

theorem lemma214_suffixAlphaValue_zero_eq_tail
    {n : Nat} (b : GoodBONG q L (n + 3)) :
    ((b.suffixAlphaSegmentWitness (n := n + 1)
      (0 : Fin (n + 2)) (by
        show 1 < n + 2
        omega)).toGoodBONG b.good).alphaValue (0 : Fin (n + 1)) =
      b.tail.alphaValue (0 : Fin (n + 1)) := by
  let suffix := (b.suffixAlphaSegmentWitness (n := n + 1)
    (0 : Fin (n + 2)) (by
      show 1 < n + 2
      omega)).toGoodBONG b.good
  have hvalues : ∀ i, suffix.valueUnit i = b.tail.valueUnit i := by
    intro i
    change (b.suffixAlphaSegmentWitness (n := n + 1)
      (0 : Fin (n + 2)) (by
        show 1 < n + 2
        omega)).bong.valueUnit i = b.tail.valueUnit i
    rw [(b.suffixAlphaSegmentWitness (n := n + 1)
      (0 : Fin (n + 2)) (by
        show 1 < n + 2
        omega)).valueUnit_eq]
    have hindex :
        (b.suffixAlphaSegmentWitness (n := n + 1)
          (0 : Fin (n + 2)) (by
            show 1 < n + 2
            omega)).sourceIndex i = i.succ := by
      apply Fin.ext
      change 1 + i.val = i.val + 1
      omega
    calc
      b.toBONG.valueUnit _ = b.valueUnit i.succ := by
        rw [hindex]
        rfl
      _ = b.tail.valueUnit i := by
        apply Units.ext
        change b.toBONG.value i.succ = b.toBONG.tail.value i
        exact (b.toBONG.value_tail i).symm
  have halpha := suffix.alphaValue_eq_of_valueUnits_eq b.tail hvalues
    (0 : Fin (n + 1))
  change suffix.alphaValue (0 : Fin (n + 1)) =
    b.tail.alphaValue (0 : Fin (n + 1))
  exact halpha

/-- Corollary 2.5(ii) at the first endpoint, grouped as the initial binary
alpha followed by the projected tail alpha. -/
theorem lemma214_alphaValue_zero_eq_min_initialBinary_orderGap_add_tailAlpha
    {n : Nat} (b : GoodBONG q L (n + 3)) :
    (b.alphaValue 0 : WithTop ℚ) =
      min (min (b.halfGapCandidate 0) (b.leftDefectCandidate 0 0))
        (((((b.order 1 - b.order 0 : Int) : ℚ) +
          b.tail.alphaValue (0 : Fin (n + 1)) : ℚ) : WithTop ℚ)) := by
  have h := b.alphaValue_zero_eq_min_binaryCandidates_suffix
  have hsuffix := b.lemma214_suffixAlphaValue_zero_eq_tail
  have hlocal :
      (suffixAlphaLocalizationIndex (n := n + 1)
        (0 : Fin (n + 2)) (by
          show 1 < n + 2
          omega)).localPivot = (0 : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [hlocal, hsuffix] at h
  simpa only [min_assoc] using h

theorem lemma214_pairBlock_alphaValue_eq_initialBinary
    {n : Nat} (b : GoodBONG q L (n + 3))
    (S : b.toBONG.ThreeBlockSplitWitness (0 : Fin (n + 3)) (by simp)) :
    ((S.pairBlock.toGoodBONG b.good).alphaValue 0 : WithTop ℚ) =
      min (b.halfGapCandidate 0) (b.leftDefectCandidate 0 0) := by
  let pair := S.pairBlock.toGoodBONG b.good
  have hvalue0 : pair.valueUnit 0 = b.valueUnit 0 := by
    change S.pairBlock.bong.valueUnit 0 = b.toBONG.valueUnit 0
    rw [S.pairBlock.valueUnit_eq]
    congr 1
  have hvalue1 : pair.valueUnit 1 = b.valueUnit 1 := by
    change S.pairBlock.bong.valueUnit 1 = b.toBONG.valueUnit 1
    rw [S.pairBlock.valueUnit_eq]
    congr 1
  have horder0 : pair.order 0 = b.order 0 := by
    change S.pairBlock.bong.order 0 = b.toBONG.order 0
    rw [S.pairBlock.order_eq]
    congr 1
  have horder1 : pair.order 1 = b.order 1 := by
    change S.pairBlock.bong.order 1 = b.toBONG.order 1
    rw [S.pairBlock.order_eq]
    congr 1
  have hhalf : pair.halfGapCandidate 0 = b.halfGapCandidate 0 := by
    unfold halfGapCandidate
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    rw [horder0, horder1]
  have hproduct : pair.adjacentProduct 0 = b.adjacentProduct 0 := by
    unfold adjacentProduct
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    rw [hvalue0, hvalue1]
  have hdefect : pair.leftDefectCandidate 0 0 =
      b.leftDefectCandidate 0 0 := by
    unfold leftDefectCandidate adjacentDefect
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    rw [horder0, horder1, hproduct]
  change (pair.alphaValue 0 : WithTop ℚ) = _
  rw [pair.binary_alpha_eq_min_candidates, hhalf, hdefect]

theorem lemma214_rightBlock_valueUnits_eq_tail_tail
    {n : Nat} (b : GoodBONG q L (n + 3))
    (S : b.toBONG.ThreeBlockSplitWitness (0 : Fin (n + 3)) (by simp))
    (right : GoodBONG
      (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
      S.rightBlock.lattice (n + 1))
    (hrightDef : right = (S.rightBlock.toGoodBONG b.good).castLength
      (by omega : n + 3 - (0 + 2) = n + 1)) :
    ∀ i, right.valueUnit i = b.tail.tail.valueUnit i := by
  intro i
  rw [hrightDef, lemma214_valueUnit_castLength]
  let j : Fin (n + 3 - (0 + 2)) := Fin.cast (by omega) i
  change S.rightBlock.bong.valueUnit j = b.tail.tail.valueUnit i
  rw [S.rightBlock.valueUnit_eq]
  have hindex : S.rightBlock.sourceIndex j = i.succ.succ := by
    apply Fin.ext
    change 0 + 2 + j.val = i.val + 1 + 1
    simp only [j, Fin.coe_cast]
    omega
  rw [hindex]
  apply Units.ext
  change b.toBONG.value i.succ.succ = b.toBONG.tail.tail.value i
  calc
    b.toBONG.value i.succ.succ = b.toBONG.tail.value i.succ :=
      (b.toBONG.value_tail i.succ).symm
    _ = b.toBONG.tail.tail.value i :=
      (b.toBONG.tail.value_tail i).symm

theorem lemma214_weightIdealOrder_binary_nondecreasing
    (b : GoodBONG q L 2) (hnondecreasing : b.order 0 ≤ b.order 1) :
    (Lattice.weightIdealOrder q L : ℚ) =
      min ((b.order 0 : ℚ) + b.alphaValue 0)
        ((b.order 0 : ℚ) + (ramificationIndex K : ℚ)) := by
  rcases b.toBONG.beliCorollary44_i_unconditional b.good
      (0 : Fin 2) (by simp) hnondecreasing with ⟨S⟩
  let left := S.left.toGoodBONG b.good
  let rightRaw := S.right.toGoodBONG b.good
  let right := rightRaw.castLength (by omega : 2 - 1 = 1)
  let a : Kˣ := b.toBONG.valueUnit 0
  let c : Kˣ := -b.toBONG.valueUnit 1
  have ha : Lattice.IsNormGeneratorValue q L a := by
    change Lattice.IsNormGeneratorValue q L (b.toBONG.valueUnit 0)
    exact b.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have hleftValue : left.valueUnit 0 = b.toBONG.valueUnit 0 := by
    change S.left.bong.valueUnit 0 = b.toBONG.valueUnit 0
    calc
      S.left.bong.valueUnit 0 =
          b.toBONG.valueUnit (S.left.sourceIndex 0) :=
        S.left.valueUnit_eq (0 : Fin 1)
      _ = b.toBONG.valueUnit 0 := by
        congr 1
  have hrightValue : right.valueUnit 0 = b.toBONG.valueUnit 1 := by
    rw [show right = rightRaw.castLength (by omega : 2 - 1 = 1) by rfl,
      lemma214_valueUnit_castLength]
    change S.right.bong.valueUnit ⟨0, by omega⟩ = b.toBONG.valueUnit 1
    rw [S.right.valueUnit_eq]
    rfl
  have hzero : Lattice.IsNormGeneratorValue
      (S.decomposition.component 0).space
      (S.decomposition.component 0).lattice a := by
    rw [S.component_zero]
    change Lattice.IsNormGeneratorValue
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice a
    have h := left.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
    change Lattice.IsNormGeneratorValue
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice
        (left.valueUnit 0) at h
    rw [hleftValue] at h
    simpa only [a] using h
  have hone : Lattice.IsNormGeneratorValue
      (S.decomposition.component 1).space
      (S.decomposition.component 1).lattice c := by
    rw [S.component_one]
    change Lattice.IsNormGeneratorValue
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice c
    have h := right.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
    have hneg := h.neg
    change Lattice.IsNormGeneratorValue
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice
        (-right.valueUnit 0) at hneg
    rw [hrightValue] at hneg
    simpa only [c] using hneg
  have hcomponentScale : Lattice.scaleIdeal
      (S.decomposition.component 0).space
      (S.decomposition.component 0).lattice =
        Lattice.principalIdeal (K := K) (a : K) := by
    rw [S.component_zero]
    change Lattice.scaleIdeal
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice = _
    calc
      _ = Lattice.principalIdeal (K := K) (left.valueUnit 0 : K) :=
        left.toBONG.scaleIdeal_eq_principal_valueUnit_zero_unary
      _ = Lattice.principalIdeal (K := K) (a : K) := by
        rw [hleftValue]
  have haDoubled : 2 * ordUnit K a =
      min (2 * b.order 0) (b.order 0 + b.order 1) := by
    have haOrder : ordUnit K a = b.order 0 := by
      change ordUnit K (b.toBONG.valueUnit 0) = b.toBONG.order 0
      exact (b.toBONG.order_eq_ordUnit 0).symm
    rw [haOrder, min_eq_left]
    omega
  have hscale : Lattice.scaleIdeal q L =
      Lattice.scaleIdeal (S.decomposition.component 0).space
        (S.decomposition.component 0).lattice :=
    lemma214_scaleIdeal_eq_component_of_doubled_order
      (b.toBONG.beliCorollary44_iv_unconditional b.good) a
      hcomponentScale haDoubled
  have htwo : Lattice.twoScaleIdeal q L ≤
      Lattice.weightIdeal (S.decomposition.component 0).space
        (S.decomposition.component 0).lattice :=
    lemma214_twoScale_le_firstWeight_of_scale_eq S.decomposition hscale
  have hleftOrder : Lattice.weightIdealOrder
      (S.decomposition.component 0).space
      (S.decomposition.component 0).lattice =
        b.order 0 + (ramificationIndex K : Int) := by
    rw [S.component_zero]
    change Lattice.weightIdealOrder
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice = _
    rw [left.weightIdealOrder_unary_proof]
    congr 1
    change S.left.bong.order 0 = b.toBONG.order 0
    calc
      S.left.bong.order 0 = b.toBONG.order (S.left.sourceIndex 0) :=
        S.left.order_eq (0 : Fin 1)
      _ = b.toBONG.order 0 := by
        congr 1
  have hrightOrder : Lattice.weightIdealOrder
      (S.decomposition.component 1).space
      (S.decomposition.component 1).lattice =
        b.order 1 + (ramificationIndex K : Int) := by
    rw [S.component_one]
    change Lattice.weightIdealOrder
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice = _
    rw [right.weightIdealOrder_unary_proof]
    congr 1
    exact S.right.order_toGoodBONG_castLength b.good
      (by omega : 2 - 1 = 1) (0 : Fin 1)
  by_cases htop : quadraticDefect K (a * c) = ⊤
  · have horder :=
      S.decomposition.weightIdealOrder_eq_min_components_of_defect_eq_top_fin_two
        a c ha hzero hone htwo htop
    rw [hleftOrder, hrightOrder, min_eq_left] at horder
    · have hdefectTop : b.adjacentDefect 0 = ⊤ := by
        have hadjProduct : b.adjacentProduct 0 = a * c := by
          unfold adjacentProduct
          simp [a, c, GoodBONG.valueUnit]
        unfold adjacentDefect
        rw [hadjProduct]
        unfold defectOrder
        rw [htop]
        rfl
      have halphaTop := b.binary_alpha_eq_min_candidates
      unfold leftDefectCandidate at halphaTop
      rw [hdefectTop, add_top, min_eq_left (le_top)] at halphaTop
      unfold halfGapCandidate at halphaTop
      norm_cast at halphaTop
      push_cast at horder
      rw [horder, halphaTop]
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      norm_cast
      rw [Rat.divInt_eq_div]
      push_cast
      have hcast : (b.order 0 : ℚ) ≤ b.order 1 := by
        exact_mod_cast hnondecreasing
      rw [min_eq_right]
      linarith
    · omega
  · have horder :=
      S.decomposition.weightIdealOrder_eq_min_components_defect_fin_two
        a c ha hzero hone htwo htop
    rw [hleftOrder, hrightOrder] at horder
    have hcOrder : ordUnit K c = b.order 1 := by
      dsimp only [c]
      rw [ordUnit_neg]
      exact (b.toBONG.order_eq_ordUnit 1).symm
    rw [hcOrder] at horder
    have hdefect : b.adjacentDefect 0 =
        ((((quadraticDefect K (a * c)).toNat : Nat) : ℚ) : WithTop ℚ) := by
      have hadjProduct : b.adjacentProduct 0 = a * c := by
        unfold adjacentProduct
        simp [a, c, GoodBONG.valueUnit]
      unfold adjacentDefect
      rw [hadjProduct]
      unfold defectOrder
      rw [← ENat.coe_toNat htop]
      rfl
    have halphaTop := b.binary_alpha_eq_min_candidates
    unfold leftDefectCandidate at halphaTop
    rw [hdefect] at halphaTop
    unfold halfGapCandidate at halphaTop
    norm_cast at halphaTop
    rw [Rat.divInt_eq_div] at halphaTop
    have hcomponent : b.order 0 + (ramificationIndex K : Int) ≤
        b.order 1 + (ramificationIndex K : Int) := by omega
    rw [min_eq_left hcomponent] at horder
    push_cast at horder
    rw [horder, halphaTop]
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    norm_cast
    push_cast
    rw [Rat.divInt_eq_div]
    push_cast
    have hcast : (b.order 0 : ℚ) ≤ b.order 1 := by
      exact_mod_cast hnondecreasing
    by_cases hdefectLe :
        (b.order 1 : ℚ) - b.order 0 +
            ((quadraticDefect K (a * c)).toNat : ℚ) ≤
          ((b.order 1 : ℚ) - b.order 0) / 2 +
            (ramificationIndex K : ℚ)
    · rw [min_eq_right hdefectLe]
      have heq : (b.order 0 : ℚ) +
          ((b.order 1 : ℚ) - b.order 0 +
            ((quadraticDefect K (a * c)).toNat : ℚ)) =
          (b.order 1 : ℚ) +
            ((quadraticDefect K (a * c)).toNat : ℚ) := by ring
      rw [heq, min_comm]
    · have hhalfLe :
          ((b.order 1 : ℚ) - b.order 0) / 2 +
              (ramificationIndex K : ℚ) ≤
            (b.order 1 : ℚ) - b.order 0 +
              ((quadraticDefect K (a * c)).toNat : ℚ) :=
        le_of_not_ge hdefectLe
      rw [min_eq_left hhalfLe]
      have hterminalLe : (b.order 0 : ℚ) +
            (ramificationIndex K : ℚ) ≤
          (b.order 0 : ℚ) +
            (((b.order 1 : ℚ) - b.order 0) / 2 +
              (ramificationIndex K : ℚ)) := by linarith
      rw [min_eq_right hterminalLe]
      apply min_eq_left
      linarith

/-- The unary-first induction step in Beli (2009), Lemma 2.14. -/
theorem lemma214_weightIdealOrder_nondecreasing_step
    {n : Nat} (b : GoodBONG q L (n + 3))
    (hnondecreasing : b.order 0 ≤ b.order 1)
    (S : b.toBONG.TwoBlockSplitWitness 1 (by omega))
    (right : GoodBONG
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice (n + 2))
    (hrightDef : right = (S.right.toGoodBONG b.good).castLength
      (by omega : n + 3 - 1 = n + 2))
    (ih : (Lattice.weightIdealOrder
          (q.restrict S.right.carrier S.right.nondegenerate)
          S.right.lattice : ℚ) =
        min ((right.order 0 : ℚ) + right.alphaValue 0)
          ((right.order 0 : ℚ) + (ramificationIndex K : ℚ))) :
    (Lattice.weightIdealOrder q L : ℚ) =
      min ((b.order 0 : ℚ) + b.alphaValue 0)
        ((b.order 0 : ℚ) + (ramificationIndex K : ℚ)) := by
  let left := S.left.toGoodBONG b.good
  let a : Kˣ := b.toBONG.valueUnit 0
  let c : Kˣ := -b.toBONG.valueUnit 1
  have ha : Lattice.IsNormGeneratorValue q L a := by
    change Lattice.IsNormGeneratorValue q L (b.toBONG.valueUnit 0)
    exact b.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have hleftValue : left.valueUnit 0 = b.toBONG.valueUnit 0 := by
    change S.left.bong.valueUnit 0 = b.toBONG.valueUnit 0
    calc
      S.left.bong.valueUnit 0 =
          b.toBONG.valueUnit (S.left.sourceIndex 0) :=
        S.left.valueUnit_eq (0 : Fin 1)
      _ = b.toBONG.valueUnit 0 := by congr 1
  have hrightValue : right.valueUnit 0 = b.toBONG.valueUnit 1 := by
    rw [hrightDef, lemma214_valueUnit_castLength]
    change S.right.bong.valueUnit ⟨0, by omega⟩ = b.toBONG.valueUnit 1
    rw [S.right.valueUnit_eq]
    rfl
  have hzero : Lattice.IsNormGeneratorValue
      (S.decomposition.component 0).space
      (S.decomposition.component 0).lattice a := by
    rw [S.component_zero]
    change Lattice.IsNormGeneratorValue
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice a
    have h := left.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
    change Lattice.IsNormGeneratorValue
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice
        (left.valueUnit 0) at h
    rw [hleftValue] at h
    simpa only [a] using h
  have hone : Lattice.IsNormGeneratorValue
      (S.decomposition.component 1).space
      (S.decomposition.component 1).lattice c := by
    rw [S.component_one]
    change Lattice.IsNormGeneratorValue
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice c
    have h := right.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
    have hneg := h.neg
    change Lattice.IsNormGeneratorValue
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice
        (-right.valueUnit 0) at hneg
    rw [hrightValue] at hneg
    simpa only [c] using hneg
  have hcomponentScale : Lattice.scaleIdeal
      (S.decomposition.component 0).space
      (S.decomposition.component 0).lattice =
        Lattice.principalIdeal (K := K) (a : K) := by
    rw [S.component_zero]
    change Lattice.scaleIdeal
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice = _
    calc
      _ = Lattice.principalIdeal (K := K) (left.valueUnit 0 : K) :=
        left.toBONG.scaleIdeal_eq_principal_valueUnit_zero_unary
      _ = Lattice.principalIdeal (K := K) (a : K) := by
        rw [hleftValue]
  have haDoubled : 2 * ordUnit K a =
      min (2 * b.order 0) (b.order 0 + b.order 1) := by
    have haOrder : ordUnit K a = b.order 0 := by
      change ordUnit K (b.toBONG.valueUnit 0) = b.toBONG.order 0
      exact (b.toBONG.order_eq_ordUnit 0).symm
    rw [haOrder, min_eq_left]
    omega
  have hscale : Lattice.scaleIdeal q L =
      Lattice.scaleIdeal (S.decomposition.component 0).space
        (S.decomposition.component 0).lattice :=
    lemma214_scaleIdeal_eq_component_of_doubled_order
      (b.toBONG.beliCorollary44_iv_unconditional b.good) a
      hcomponentScale haDoubled
  have htwo : Lattice.twoScaleIdeal q L ≤
      Lattice.weightIdeal (S.decomposition.component 0).space
        (S.decomposition.component 0).lattice :=
    lemma214_twoScale_le_firstWeight_of_scale_eq S.decomposition hscale
  have hleftOrder : Lattice.weightIdealOrder
      (S.decomposition.component 0).space
      (S.decomposition.component 0).lattice =
        b.order 0 + (ramificationIndex K : Int) := by
    rw [S.component_zero]
    change Lattice.weightIdealOrder
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice = _
    rw [left.weightIdealOrder_unary_proof]
    congr 1
    change S.left.bong.order 0 = b.toBONG.order 0
    calc
      S.left.bong.order 0 = b.toBONG.order (S.left.sourceIndex 0) :=
        S.left.order_eq (0 : Fin 1)
      _ = b.toBONG.order 0 := by congr 1
  have hrightOrderZero : right.order 0 = b.order 1 := by
    rw [hrightDef]
    calc
      ((S.right.toGoodBONG b.good).castLength
          (by omega : n + 3 - 1 = n + 2)).order 0 =
          b.toBONG.order (S.right.sourceIndex (0 : Fin (n + 2))) :=
        S.right.order_toGoodBONG_castLength b.good
          (by omega : n + 3 - 1 = n + 2) (0 : Fin (n + 2))
      _ = b.toBONG.order 1 := by congr 1
  have hrightAlpha : right.alphaValue 0 =
      ((b.suffixAlphaSegmentWitness (n := n + 1)
        (0 : Fin (n + 2)) (by
          show 1 < n + 2
          omega)).toGoodBONG b.good).alphaValue (0 : Fin (n + 1)) := by
    rw [hrightDef]
    exact b.lemma214_twoBlockRight_alphaValue_zero_eq_suffix S
  have hrightOrder :
      (Lattice.weightIdealOrder
        (S.decomposition.component 1).space
        (S.decomposition.component 1).lattice : ℚ) =
        min ((b.order 1 : ℚ) + right.alphaValue 0)
          ((b.order 1 : ℚ) + (ramificationIndex K : ℚ)) := by
    rw [S.component_one]
    change (Lattice.weightIdealOrder
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice : ℚ) = _
    simpa only [hrightOrderZero] using ih
  have hcOrder : ordUnit K c = b.order 1 := by
    dsimp only [c]
    rw [ordUnit_neg]
    exact (b.toBONG.order_eq_ordUnit 1).symm
  have halpha := b.alphaValue_zero_eq_min_binaryCandidates_suffix
  unfold halfGapCandidate leftDefectCandidate at halpha
  have hadjProduct : b.adjacentProduct 0 = a * c := by
    unfold adjacentProduct
    simp [a, c, GoodBONG.valueUnit]
  have hlocal :
      (suffixAlphaLocalizationIndex (n := n + 1)
        (0 : Fin (n + 2)) (by
          show 1 < n + 2
          omega)).localPivot = (0 : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [hlocal] at halpha
  by_cases htop : quadraticDefect K (a * c) = ⊤
  · have horder :=
      S.decomposition.weightIdealOrder_eq_min_components_of_defect_eq_top_fin_two
        a c ha hzero hone htwo htop
    have horderQ : (Lattice.weightIdealOrder q L : ℚ) =
        min
          (Lattice.weightIdealOrder (S.decomposition.component 0).space
            (S.decomposition.component 0).lattice : ℚ)
          (Lattice.weightIdealOrder (S.decomposition.component 1).space
            (S.decomposition.component 1).lattice : ℚ) := by
      exact_mod_cast horder
    rw [hleftOrder] at horderQ
    push_cast at horderQ
    rw [hrightOrder] at horderQ
    have hdefectTop : b.adjacentDefect 0 = ⊤ := by
      unfold adjacentDefect defectOrder
      rw [hadjProduct, htop]
      rfl
    rw [hdefectTop, add_top, min_eq_right (le_top)] at halpha
    norm_cast at halpha
    rw [← hrightAlpha] at halpha
    rw [horderQ, halpha]
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    norm_cast
    push_cast
    rw [Rat.divInt_eq_div]
    push_cast
    let r0 : ℚ := b.order 0
    let r1 : ℚ := b.order 1
    let e : ℚ := ramificationIndex K
    let A : ℚ := right.alphaValue 0
    change min (r0 + e) (min (r1 + A) (r1 + e)) =
      min (r0 + min ((r1 - r0) / 2 + e) (r1 - r0 + A))
        (r0 + e)
    have hgap : (0 : ℚ) ≤ r1 - r0 := by
      dsimp only [r0, r1]
      exact_mod_cast (sub_nonneg.mpr hnondecreasing)
    have hterminal : r0 + e ≤ r1 + e := by linarith
    have hhalf : r0 + e ≤ r0 + ((r1 - r0) / 2 + e) := by
      linarith
    have hshift : r0 + (r1 - r0 + A) = r1 + A := by ring
    calc
      min (r0 + e) (min (r1 + A) (r1 + e)) =
          min (r0 + e) (r1 + A) := by
        rw [min_comm (r1 + A) (r1 + e), ← min_assoc,
          min_eq_left hterminal]
      _ = min (r0 + min ((r1 - r0) / 2 + e) (r1 - r0 + A))
          (r0 + e) := by
        rw [lemma214_add_min, hshift]
        symm
        calc
          min
              (min (r0 + ((r1 - r0) / 2 + e)) (r1 + A))
              (r0 + e) =
              min (r0 + e)
                (min (r0 + ((r1 - r0) / 2 + e)) (r1 + A)) :=
            min_comm _ _
          _ = min (min (r0 + e)
                (r0 + ((r1 - r0) / 2 + e))) (r1 + A) := by
            rw [min_assoc]
          _ = min (r0 + e) (r1 + A) := by
            rw [min_eq_left hhalf]
  · have horder :=
      S.decomposition.weightIdealOrder_eq_min_components_defect_fin_two
        a c ha hzero hone htwo htop
    have horderQ : (Lattice.weightIdealOrder q L : ℚ) =
        min
          (min
            (Lattice.weightIdealOrder (S.decomposition.component 0).space
              (S.decomposition.component 0).lattice : ℚ)
            (Lattice.weightIdealOrder (S.decomposition.component 1).space
              (S.decomposition.component 1).lattice : ℚ))
          ((ordUnit K c + (quadraticDefect K (a * c)).toNat : Int) : ℚ) := by
      exact_mod_cast horder
    rw [hleftOrder, hcOrder] at horderQ
    push_cast at horderQ
    rw [hrightOrder] at horderQ
    have hdefect : b.adjacentDefect 0 =
        ((((quadraticDefect K (a * c)).toNat : Nat) : ℚ) : WithTop ℚ) := by
      unfold adjacentDefect
      rw [hadjProduct]
      unfold defectOrder
      rw [← ENat.coe_toNat htop]
      rfl
    rw [hdefect] at halpha
    norm_cast at halpha
    rw [← hrightAlpha] at halpha
    rw [horderQ, halpha]
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    norm_cast
    rw [Rat.divInt_eq_div]
    push_cast
    let r0 : ℚ := b.order 0
    let r1 : ℚ := b.order 1
    let e : ℚ := ramificationIndex K
    let A : ℚ := right.alphaValue 0
    let d : ℚ := (quadraticDefect K (a * c)).toNat
    change min (min (r0 + e) (min (r1 + A) (r1 + e)))
        (r1 + d) =
      min
        (r0 + min ((r1 - r0) / 2 + e)
          (min (r1 - r0 + d) (r1 - r0 + A)))
        (r0 + e)
    have hgap : (0 : ℚ) ≤ r1 - r0 := by
      dsimp only [r0, r1]
      exact_mod_cast (sub_nonneg.mpr hnondecreasing)
    have hterminal : r0 + e ≤ r1 + e := by linarith
    have hhalf : r0 + e ≤ r0 + ((r1 - r0) / 2 + e) := by
      linarith
    have hdefectShift : r0 + (r1 - r0 + d) = r1 + d := by ring
    have halphaShift : r0 + (r1 - r0 + A) = r1 + A := by ring
    calc
      min (min (r0 + e) (min (r1 + A) (r1 + e)))
          (r1 + d) = min (min (r0 + e) (r1 + A)) (r1 + d) := by
        rw [min_comm (r1 + A) (r1 + e), ← min_assoc,
          min_eq_left hterminal]
      _ = min
          (r0 + min ((r1 - r0) / 2 + e)
            (min (r1 - r0 + d) (r1 - r0 + A)))
          (r0 + e) := by
        rw [lemma214_add_min, lemma214_add_min, hdefectShift, halphaShift]
        symm
        calc
          min
              (min (r0 + ((r1 - r0) / 2 + e))
                (min (r1 + d) (r1 + A)))
              (r0 + e) =
              min (r0 + e)
                (min (r0 + ((r1 - r0) / 2 + e))
                  (min (r1 + d) (r1 + A))) := min_comm _ _
          _ = min
              (min (r0 + e) (r0 + ((r1 - r0) / 2 + e)))
              (min (r1 + d) (r1 + A)) := by rw [min_assoc]
          _ = min (r0 + e) (min (r1 + d) (r1 + A)) := by
            rw [min_eq_left hhalf]
          _ = min (min (r0 + e) (r1 + A)) (r1 + d) := by
            ac_rfl

/-- The binary-first rank-three step in Beli (2009), Lemma 2.14. -/
theorem lemma214_weightIdealOrder_ternary_strict
    (b : GoodBONG q L 3) (hstrict : b.order 1 < b.order 0) :
    (Lattice.weightIdealOrder q L : ℚ) =
      (b.order 0 : ℚ) + b.alphaValue 0 := by
  rcases b.toBONG.beliCorollary44_ii_unconditional b.good
      (0 : Fin 3) (by simp) hstrict with ⟨S⟩
  have hzero : (S.decomposition.component 0).ambientSubmodule = ⊥ := by
    rw [S.component_zero]
    exact lemma214_ambientSubmodule_eq_bot_of_length_zero S.leftBlock
  let D := S.decomposition.dropFirstZeroFinThree hzero
  let pair := S.pairBlock.toGoodBONG b.good
  let rightRaw := S.rightBlock.toGoodBONG b.good
  let right := rightRaw.castLength (by omega : 3 - (0 + 2) = 1)
  have hpairOrder0 : pair.order 0 = b.order 0 := by
    change S.pairBlock.bong.order 0 = b.toBONG.order 0
    rw [S.pairBlock.order_eq]
    congr 1
  have hpairOrder1 : pair.order 1 = b.order 1 := by
    change S.pairBlock.bong.order 1 = b.toBONG.order 1
    rw [S.pairBlock.order_eq]
    congr 1
  have hpairStrict : pair.order 1 < pair.order 0 := by
    rw [hpairOrder1, hpairOrder0]
    exact hstrict
  have hpairValue1 : pair.valueUnit 1 = b.valueUnit 1 := by
    change S.pairBlock.bong.valueUnit 1 = b.toBONG.valueUnit 1
    rw [S.pairBlock.valueUnit_eq]
    congr 1
  have hrightValue0 : right.valueUnit 0 = b.valueUnit 2 := by
    rw [show right = rightRaw.castLength
        (by omega : 3 - (0 + 2) = 1) by rfl,
      lemma214_valueUnit_castLength]
    change S.rightBlock.bong.valueUnit ⟨0, by omega⟩ = b.toBONG.valueUnit 2
    rw [S.rightBlock.valueUnit_eq]
    congr 1
  have hrightOrder0 : right.order 0 = b.order 2 := by
    change ((S.rightBlock.toGoodBONG b.good).castLength
      (by omega : 3 - (0 + 2) = 1)).order 0 = b.toBONG.order 2
    simpa using S.rightBlock.order_toGoodBONG_castLength b.good
      (by omega : 3 - (0 + 2) = 1) (0 : Fin 1)
  let a : Kˣ := pair.toBONG.terminalMultiplierUnit hpairStrict ^ 2 *
    pair.valueUnit 1
  let c : Kˣ := -right.valueUnit 0
  have hpairGenerator : Lattice.IsNormGeneratorValue
      (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate)
      S.pairBlock.lattice a := by
    have hgen := pair.toBONG.terminalNormVector_isNormGenerator hpairStrict
    have hne : (q.restrict S.pairBlock.carrier
        S.pairBlock.nondegenerate).quadratic
          (pair.toBONG.terminalNormVector hpairStrict) ≠ 0 := by
      rw [pair.toBONG.quadratic_terminalNormVector hpairStrict]
      exact Units.ne_zero _
    have hvalue := hgen.isNormGeneratorValue hne
    convert hvalue using 1
    apply Units.ext
    change (a : K) =
      (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate).quadratic
        (pair.toBONG.terminalNormVector hpairStrict)
    exact (pair.toBONG.quadratic_terminalNormVector hpairStrict).symm
  have hcomponentZero : Lattice.IsNormGeneratorValue
      (D.component 0).space (D.component 0).lattice a := by
    change Lattice.IsNormGeneratorValue
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).lattice a
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_zero,
      S.component_one]
    exact hpairGenerator
  have hambientHead : Lattice.IsNormGeneratorValue q L (b.valueUnit 0) := by
    change Lattice.IsNormGeneratorValue q L (b.toBONG.valueUnit 0)
    exact b.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have haOrder : ordUnit K a = b.order 0 := by
    change ordUnit K
      (pair.toBONG.terminalMultiplierUnit hpairStrict ^ 2 *
        pair.toBONG.valueUnit 1) = b.order 0
    rw [pair.toBONG.ordUnit_terminalValue_eq_order_zero hpairStrict]
    exact hpairOrder0
  have ha : Lattice.IsNormGeneratorValue q L a :=
    lemma214_promote_component_normGeneratorValue D 0 (b.valueUnit 0) a
      hambientHead hcomponentZero (by
        calc
          ordUnit K (b.valueUnit 0) = b.order 0 := by
            change ordUnit K (b.toBONG.valueUnit 0) = b.toBONG.order 0
            exact (b.toBONG.order_eq_ordUnit 0).symm
          _ = ordUnit K a := haOrder.symm)
  have hcomponentOne : Lattice.IsNormGeneratorValue
      (D.component 1).space (D.component 1).lattice c := by
    change Lattice.IsNormGeneratorValue
      ((S.decomposition.dropFirstZeroFinThree hzero).component 1).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 1).lattice c
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_one,
      S.component_two]
    change Lattice.IsNormGeneratorValue
      (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
      S.rightBlock.lattice c
    have h := right.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
    have hneg := h.neg
    change Lattice.IsNormGeneratorValue
      (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
      S.rightBlock.lattice (-right.valueUnit 0) at hneg
    simpa only [c] using hneg
  let m : Kˣ := pair.toBONG.binaryMixedPairingUnit hpairStrict
  have hcomponentScale : Lattice.scaleIdeal
      (D.component 0).space (D.component 0).lattice =
        Lattice.principalIdeal (K := K) (m : K) := by
    change Lattice.scaleIdeal
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).lattice = _
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_zero,
      S.component_one]
    change Lattice.scaleIdeal
      (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate)
      S.pairBlock.lattice = Lattice.principalIdeal (K := K) (m : K)
    simpa only [m, pair.toBONG.coe_binaryMixedPairingUnit hpairStrict] using
      pair.toBONG.scaleIdeal_eq_principal_binaryMixedPairing hpairStrict
  have hmDoubled : 2 * ordUnit K m =
      min (2 * b.order 0) (b.order 0 + b.order 1) := by
    change 2 * ordUnit K
      (pair.toBONG.binaryMixedPairingUnit hpairStrict) = _
    rw [pair.toBONG.two_mul_ordUnit_binaryMixedPairing_eq_order_add]
    change pair.order 0 + pair.order 1 = _
    rw [hpairOrder0, hpairOrder1, min_eq_right]
    omega
  have hscale : Lattice.scaleIdeal q L =
      Lattice.scaleIdeal (D.component 0).space (D.component 0).lattice :=
    lemma214_scaleIdeal_eq_component_of_doubled_order
      (b.toBONG.beliCorollary44_iv_unconditional b.good) m
      hcomponentScale hmDoubled
  have htwo : Lattice.twoScaleIdeal q L ≤
      Lattice.weightIdeal (D.component 0).space (D.component 0).lattice :=
    lemma214_twoScale_le_firstWeight_of_scale_eq D hscale
  have hpairWeight : (Lattice.weightIdealOrder
      (D.component 0).space (D.component 0).lattice : ℚ) =
        (b.order 0 : ℚ) + pair.alphaValue 0 := by
    change (Lattice.weightIdealOrder
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).lattice : ℚ) = _
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_zero,
      S.component_one]
    change (Lattice.weightIdealOrder
      (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate)
      S.pairBlock.lattice : ℚ) = _
    simpa only [hpairOrder0] using
      BONG.weightIdealOrder_binary_strict pair hpairStrict
  have hrightWeight : Lattice.weightIdealOrder
      (D.component 1).space (D.component 1).lattice =
        b.order 2 + (ramificationIndex K : Int) := by
    change Lattice.weightIdealOrder
      ((S.decomposition.dropFirstZeroFinThree hzero).component 1).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 1).lattice = _
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_one,
      S.component_two]
    change Lattice.weightIdealOrder
      (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
      S.rightBlock.lattice = _
    rw [right.weightIdealOrder_unary_proof, hrightOrder0]
  have hcOrder : ordUnit K c = b.order 2 := by
    dsimp only [c]
    rw [ordUnit_neg]
    change ordUnit K (right.toBONG.valueUnit 0) = b.order 2
    rw [← right.toBONG.order_eq_ordUnit]
    exact hrightOrder0
  have hcross : quadraticDefect K (a * c) =
      quadraticDefect K (-(b.valueUnit 1 * b.valueUnit 2)) := by
    have hfactor : a * c =
        (-(b.valueUnit 1 * b.valueUnit 2)) *
          pair.toBONG.terminalMultiplierUnit hpairStrict ^ 2 := by
      dsimp only [a, c]
      rw [hpairValue1, hrightValue0]
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [hfactor, quadraticDefect_mul_square]
  have htailValue0 : b.tail.valueUnit (0 : Fin 2) = b.valueUnit 1 := by
    change b.toBONG.tail.valueUnit 0 = b.toBONG.valueUnit 1
    apply Units.ext
    simpa using b.toBONG.value_tail (0 : Fin 2)
  have htailValue1 : b.tail.valueUnit (1 : Fin 2) = b.valueUnit 2 := by
    change b.toBONG.tail.valueUnit 1 = b.toBONG.valueUnit 2
    apply Units.ext
    simpa using b.toBONG.value_tail (1 : Fin 2)
  have htailProduct : b.tail.adjacentProduct 0 =
      -(b.valueUnit 1 * b.valueUnit 2) := by
    unfold adjacentProduct
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one,
      htailValue0, htailValue1]
  have hpairAlpha := b.lemma214_pairBlock_alphaValue_eq_initialBinary S
  have hglobal :=
    b.lemma214_alphaValue_zero_eq_min_initialBinary_orderGap_add_tailAlpha
  rw [← hpairAlpha] at hglobal
  have htail := b.tail.binary_alpha_eq_min_candidates
  push_cast at hglobal
  rw [htail] at hglobal
  have htailOrder0 : b.tail.order 0 = b.order 1 := by
    change b.toBONG.tail.order 0 = b.toBONG.order 1
    exact b.toBONG.order_tail 0
  have htailOrder1 : b.tail.order 1 = b.order 2 := by
    change b.toBONG.tail.order 1 = b.toBONG.order 2
    exact b.toBONG.order_tail 1
  have hpairLeHalf := pair.alphaValue_le_halfGapValue 0
  unfold halfGapValue orderGap at hpairLeHalf
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hpairLeHalf
  rw [hpairOrder0, hpairOrder1] at hpairLeHalf
  have hgood02 : b.order 0 ≤ b.order 2 := b.good 0 (by simp)
  have hstrictQ : (b.order 1 : ℚ) < b.order 0 := by
    exact_mod_cast hstrict
  have hdomQ : pair.alphaValue 0 ≤
      ((b.order 1 - b.order 0 : Int) : ℚ) +
        b.tail.halfGapValue 0 := by
    unfold halfGapValue orderGap
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    rw [htailOrder0, htailOrder1]
    push_cast
    push_cast at hpairLeHalf
    have hgood02Q : (b.order 0 : ℚ) ≤ b.order 2 := by
      exact_mod_cast hgood02
    linarith
  have hdom : (pair.alphaValue 0 : WithTop ℚ) ≤
      (((b.order 1 - b.order 0 : Int) : ℚ) : WithTop ℚ) +
        b.tail.halfGapCandidate 0 := by
    rw [← b.tail.coe_halfGapValue]
    norm_cast
  push_cast at hdom
  have hdom' :
      (((S.pairBlock.toGoodBONG b.good).alphaValue 0 : ℚ) : WithTop ℚ) ≤
        (((b.order 1 : ℚ) : WithTop ℚ) -
          ((b.order 0 : ℚ) : WithTop ℚ)) +
            b.tail.halfGapCandidate 0 := by
    simpa only [pair] using hdom
  rw [lemma214_withTop_add_min] at hglobal
  rw [← min_assoc, min_eq_left hdom'] at hglobal
  by_cases htop : quadraticDefect K (a * c) = ⊤
  · have horder :=
      D.weightIdealOrder_eq_min_components_of_defect_eq_top_fin_two
        a c ha hcomponentZero hcomponentOne htwo htop
    have hcrossTop : b.tail.adjacentDefect 0 = ⊤ := by
      unfold adjacentDefect
      rw [htailProduct]
      unfold defectOrder
      rw [← hcross, htop]
      rfl
    unfold leftDefectCandidate at hglobal
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hglobal
    rw [hcrossTop] at hglobal
    simp at hglobal
    have hglobalQ : pair.alphaValue 0 = b.alphaValue 0 := by
      apply WithTop.coe_injective
      rw [pair.coe_alphaValue, b.coe_alphaValue]
      exact hglobal.symm
    have hrightQ : (b.order 0 : ℚ) + pair.alphaValue 0 ≤
        (b.order 2 : ℚ) + (ramificationIndex K : ℚ) := by
      push_cast at hpairLeHalf
      have hgood02Q : (b.order 0 : ℚ) ≤ b.order 2 := by
        exact_mod_cast hgood02
      linarith
    have horderQ : (Lattice.weightIdealOrder q L : ℚ) =
        min
          (Lattice.weightIdealOrder (D.component 0).space
            (D.component 0).lattice : ℚ)
          (Lattice.weightIdealOrder (D.component 1).space
            (D.component 1).lattice : ℚ) := by exact_mod_cast horder
    rw [hpairWeight, hrightWeight] at horderQ
    push_cast at horderQ
    rw [min_eq_left hrightQ] at horderQ
    rw [horderQ, hglobalQ]
  · have horder :=
      D.weightIdealOrder_eq_min_components_defect_fin_two
        a c ha hcomponentZero hcomponentOne htwo htop
    have hcrossFinite : b.tail.adjacentDefect 0 =
        ((((quadraticDefect K (a * c)).toNat : Nat) : ℚ) : WithTop ℚ) := by
      unfold adjacentDefect
      rw [htailProduct]
      unfold defectOrder
      rw [← hcross]
      rw [← ENat.coe_toNat htop]
      rfl
    unfold leftDefectCandidate at hglobal
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hglobal
    rw [hcrossFinite, htailOrder0, htailOrder1] at hglobal
    norm_cast at hglobal
    push_cast at hglobal
    have hrightQ : (b.order 0 : ℚ) + pair.alphaValue 0 ≤
        (b.order 2 : ℚ) + (ramificationIndex K : ℚ) := by
      push_cast at hpairLeHalf
      have hgood02Q : (b.order 0 : ℚ) ≤ b.order 2 := by
        exact_mod_cast hgood02
      linarith
    have horderQ : (Lattice.weightIdealOrder q L : ℚ) =
        min
          (min
            (Lattice.weightIdealOrder (D.component 0).space
              (D.component 0).lattice : ℚ)
            (Lattice.weightIdealOrder (D.component 1).space
              (D.component 1).lattice : ℚ))
          ((ordUnit K c + (quadraticDefect K (a * c)).toNat : Int) : ℚ) := by
      exact_mod_cast horder
    rw [hpairWeight, hrightWeight, hcOrder] at horderQ
    push_cast at horderQ
    rw [min_eq_left hrightQ] at horderQ
    rw [horderQ, hglobal]
    rw [lemma214_add_min]
    congr 1
    ring

/-- The binary-first induction step in the strictly decreasing branch of
Beli (2009), Lemma 2.14. -/
theorem lemma214_weightIdealOrder_strict_step
    {n : Nat} (b : GoodBONG q L (n + 4))
    (hstrict : b.order 1 < b.order 0)
    (S : b.toBONG.ThreeBlockSplitWitness
      (0 : Fin (n + 4)) (by simp))
    (right : GoodBONG
      (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
      S.rightBlock.lattice (n + 2))
    (hrightDef : right =
      (S.rightBlock.toGoodBONG b.good).castLength
        (by omega : n + 4 - (0 + 2) = n + 2))
    (ih : (Lattice.weightIdealOrder
          (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
          S.rightBlock.lattice : ℚ) =
        min ((right.order 0 : ℚ) + right.alphaValue 0)
          ((right.order 0 : ℚ) + (ramificationIndex K : ℚ))) :
    (Lattice.weightIdealOrder q L : ℚ) =
      (b.order 0 : ℚ) + b.alphaValue 0 := by
  have hzero : (S.decomposition.component 0).ambientSubmodule = ⊥ := by
    rw [S.component_zero]
    exact lemma214_ambientSubmodule_eq_bot_of_length_zero S.leftBlock
  let D := S.decomposition.dropFirstZeroFinThree hzero
  let pair := S.pairBlock.toGoodBONG b.good
  have hpairOrder0 : pair.order 0 = b.order 0 := by
    change S.pairBlock.bong.order 0 = b.toBONG.order 0
    rw [S.pairBlock.order_eq]
    congr 1
  have hpairOrder1 : pair.order 1 = b.order 1 := by
    change S.pairBlock.bong.order 1 = b.toBONG.order 1
    rw [S.pairBlock.order_eq]
    congr 1
  have hpairStrict : pair.order 1 < pair.order 0 := by
    rw [hpairOrder1, hpairOrder0]
    exact hstrict
  have hpairValue1 : pair.valueUnit 1 = b.valueUnit 1 := by
    change S.pairBlock.bong.valueUnit 1 = b.toBONG.valueUnit 1
    rw [S.pairBlock.valueUnit_eq]
    congr 1
  have hrightValue0 : right.valueUnit 0 = b.valueUnit 2 := by
    rw [hrightDef, lemma214_valueUnit_castLength]
    change S.rightBlock.bong.valueUnit _ = b.toBONG.valueUnit 2
    rw [S.rightBlock.valueUnit_eq]
    apply congrArg b.toBONG.valueUnit
    apply Fin.ext
    simp only [SegmentWitness.sourceIndex_val, Fin.coe_cast]
    change 2 = 2 % (n + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hrightOrder0 : right.order 0 = b.order 2 := by
    rw [hrightDef]
    calc
      ((S.rightBlock.toGoodBONG b.good).castLength
          (by omega : n + 4 - (0 + 2) = n + 2)).order 0 =
          b.toBONG.order
            (S.rightBlock.sourceIndex (Fin.cast (by simp) (0 : Fin (n + 2)))) :=
        S.rightBlock.order_toGoodBONG_castLength b.good
          (by simp : n + 4 - (0 + 2) = n + 2) (0 : Fin (n + 2))
      _ = b.toBONG.order 2 := by
        apply congrArg b.toBONG.order
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val, Fin.coe_cast]
        change 2 = 2 % (n + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
  let a : Kˣ := pair.toBONG.terminalMultiplierUnit hpairStrict ^ 2 *
    pair.valueUnit 1
  let c : Kˣ := -right.valueUnit 0
  have hpairGenerator : Lattice.IsNormGeneratorValue
      (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate)
      S.pairBlock.lattice a := by
    have hgen := pair.toBONG.terminalNormVector_isNormGenerator hpairStrict
    have hne : (q.restrict S.pairBlock.carrier
        S.pairBlock.nondegenerate).quadratic
          (pair.toBONG.terminalNormVector hpairStrict) ≠ 0 := by
      rw [pair.toBONG.quadratic_terminalNormVector hpairStrict]
      exact Units.ne_zero _
    have hvalue := hgen.isNormGeneratorValue hne
    convert hvalue using 1
    apply Units.ext
    change (a : K) =
      (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate).quadratic
        (pair.toBONG.terminalNormVector hpairStrict)
    exact (pair.toBONG.quadratic_terminalNormVector hpairStrict).symm
  have hcomponentZero : Lattice.IsNormGeneratorValue
      (D.component 0).space (D.component 0).lattice a := by
    change Lattice.IsNormGeneratorValue
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).lattice a
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_zero,
      S.component_one]
    exact hpairGenerator
  have hambientHead : Lattice.IsNormGeneratorValue q L (b.valueUnit 0) := by
    change Lattice.IsNormGeneratorValue q L (b.toBONG.valueUnit 0)
    exact b.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have haOrder : ordUnit K a = b.order 0 := by
    change ordUnit K
      (pair.toBONG.terminalMultiplierUnit hpairStrict ^ 2 *
        pair.toBONG.valueUnit 1) = b.order 0
    rw [pair.toBONG.ordUnit_terminalValue_eq_order_zero hpairStrict]
    exact hpairOrder0
  have ha : Lattice.IsNormGeneratorValue q L a :=
    lemma214_promote_component_normGeneratorValue D 0 (b.valueUnit 0) a
      hambientHead hcomponentZero (by
        calc
          ordUnit K (b.valueUnit 0) = b.order 0 := by
            change ordUnit K (b.toBONG.valueUnit 0) = b.toBONG.order 0
            exact (b.toBONG.order_eq_ordUnit 0).symm
          _ = ordUnit K a := haOrder.symm)
  have hcomponentOne : Lattice.IsNormGeneratorValue
      (D.component 1).space (D.component 1).lattice c := by
    change Lattice.IsNormGeneratorValue
      ((S.decomposition.dropFirstZeroFinThree hzero).component 1).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 1).lattice c
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_one,
      S.component_two]
    change Lattice.IsNormGeneratorValue
      (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
      S.rightBlock.lattice c
    have h := right.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
    have hneg := h.neg
    change Lattice.IsNormGeneratorValue
      (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
      S.rightBlock.lattice (-right.valueUnit 0) at hneg
    simpa only [c] using hneg
  let m : Kˣ := pair.toBONG.binaryMixedPairingUnit hpairStrict
  have hcomponentScale : Lattice.scaleIdeal
      (D.component 0).space (D.component 0).lattice =
        Lattice.principalIdeal (K := K) (m : K) := by
    change Lattice.scaleIdeal
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).lattice = _
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_zero,
      S.component_one]
    change Lattice.scaleIdeal
      (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate)
      S.pairBlock.lattice = Lattice.principalIdeal (K := K) (m : K)
    simpa only [m, pair.toBONG.coe_binaryMixedPairingUnit hpairStrict] using
      pair.toBONG.scaleIdeal_eq_principal_binaryMixedPairing hpairStrict
  have hmDoubled : 2 * ordUnit K m =
      min (2 * b.order 0) (b.order 0 + b.order 1) := by
    change 2 * ordUnit K
      (pair.toBONG.binaryMixedPairingUnit hpairStrict) = _
    rw [pair.toBONG.two_mul_ordUnit_binaryMixedPairing_eq_order_add]
    change pair.order 0 + pair.order 1 = _
    rw [hpairOrder0, hpairOrder1, min_eq_right]
    omega
  have hscale : Lattice.scaleIdeal q L =
      Lattice.scaleIdeal (D.component 0).space (D.component 0).lattice :=
    lemma214_scaleIdeal_eq_component_of_doubled_order
      (b.toBONG.beliCorollary44_iv_unconditional b.good) m
      hcomponentScale hmDoubled
  have htwo : Lattice.twoScaleIdeal q L ≤
      Lattice.weightIdeal (D.component 0).space (D.component 0).lattice :=
    lemma214_twoScale_le_firstWeight_of_scale_eq D hscale
  have hpairWeight : (Lattice.weightIdealOrder
      (D.component 0).space (D.component 0).lattice : ℚ) =
        (b.order 0 : ℚ) + pair.alphaValue 0 := by
    change (Lattice.weightIdealOrder
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 0).lattice : ℚ) = _
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_zero,
      S.component_one]
    change (Lattice.weightIdealOrder
      (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate)
      S.pairBlock.lattice : ℚ) = _
    simpa only [hpairOrder0] using
      BONG.weightIdealOrder_binary_strict pair hpairStrict
  have hrightWeight : (Lattice.weightIdealOrder
      (D.component 1).space (D.component 1).lattice : ℚ) =
        min ((b.order 2 : ℚ) + right.alphaValue 0)
          ((b.order 2 : ℚ) + (ramificationIndex K : ℚ)) := by
    change (Lattice.weightIdealOrder
      ((S.decomposition.dropFirstZeroFinThree hzero).component 1).space
      ((S.decomposition.dropFirstZeroFinThree hzero).component 1).lattice : ℚ) = _
    rw [Lattice.OrthogonalDecomposition.dropFirstZeroFinThree_component_one,
      S.component_two]
    change (Lattice.weightIdealOrder
      (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
      S.rightBlock.lattice : ℚ) = _
    simpa only [hrightOrder0] using ih
  have hcOrder : ordUnit K c = b.order 2 := by
    dsimp only [c]
    rw [ordUnit_neg]
    change ordUnit K (right.toBONG.valueUnit 0) = b.order 2
    rw [← right.toBONG.order_eq_ordUnit]
    exact hrightOrder0
  have hcross : quadraticDefect K (a * c) =
      quadraticDefect K (-(b.valueUnit 1 * b.valueUnit 2)) := by
    have hfactor : a * c =
        (-(b.valueUnit 1 * b.valueUnit 2)) *
          pair.toBONG.terminalMultiplierUnit hpairStrict ^ 2 := by
      dsimp only [a, c]
      rw [hpairValue1, hrightValue0]
      rw [mul_neg, neg_mul]
      congr 1
      ac_rfl
    rw [hfactor, quadraticDefect_mul_square]
  have hrightValues : ∀ i,
      right.valueUnit i = b.tail.tail.valueUnit i :=
    b.lemma214_rightBlock_valueUnits_eq_tail_tail S right hrightDef
  have hrightAlpha : right.alphaValue 0 =
      b.tail.tail.alphaValue 0 :=
    right.alphaValue_eq_of_valueUnits_eq b.tail.tail hrightValues 0
  have htailValue0 : b.tail.valueUnit 0 = b.valueUnit 1 := by
    change b.toBONG.tail.valueUnit 0 = b.toBONG.valueUnit 1
    apply Units.ext
    simpa using b.toBONG.value_tail (0 : Fin (n + 3))
  have htailValue1 : b.tail.valueUnit 1 = b.valueUnit 2 := by
    change b.toBONG.tail.valueUnit 1 = b.toBONG.valueUnit 2
    apply Units.ext
    simpa using b.toBONG.value_tail (1 : Fin (n + 3))
  have htailProduct : b.tail.adjacentProduct 0 =
      -(b.valueUnit 1 * b.valueUnit 2) := by
    unfold adjacentProduct
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one,
      htailValue0, htailValue1]
  have hpairAlpha := b.lemma214_pairBlock_alphaValue_eq_initialBinary S
  have hglobal :=
    b.lemma214_alphaValue_zero_eq_min_initialBinary_orderGap_add_tailAlpha
  rw [← hpairAlpha] at hglobal
  have htail :=
    b.tail.lemma214_alphaValue_zero_eq_min_initialBinary_orderGap_add_tailAlpha
  rw [← hrightAlpha] at htail
  push_cast at hglobal
  rw [htail] at hglobal
  have htailOrder0 : b.tail.order 0 = b.order 1 := by
    change b.toBONG.tail.order 0 = b.toBONG.order 1
    exact b.toBONG.order_tail 0
  have htailOrder1 : b.tail.order 1 = b.order 2 := by
    change b.toBONG.tail.order 1 = b.toBONG.order 2
    exact b.toBONG.order_tail 1
  have hpairLeHalf := pair.alphaValue_le_halfGapValue 0
  unfold halfGapValue orderGap at hpairLeHalf
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hpairLeHalf
  rw [hpairOrder0, hpairOrder1] at hpairLeHalf
  have hgood02 : b.order 0 ≤ b.order 2 := b.good 0 (by simp)
  have hstrictQ : (b.order 1 : ℚ) < b.order 0 := by
    exact_mod_cast hstrict
  have hdomQ : pair.alphaValue 0 ≤
      ((b.order 1 - b.order 0 : Int) : ℚ) +
        b.tail.halfGapValue 0 := by
    unfold halfGapValue orderGap
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    rw [htailOrder0, htailOrder1]
    push_cast
    push_cast at hpairLeHalf
    have hgood02Q : (b.order 0 : ℚ) ≤ b.order 2 := by
      exact_mod_cast hgood02
    linarith
  have hdom : (pair.alphaValue 0 : WithTop ℚ) ≤
      (((b.order 1 - b.order 0 : Int) : ℚ) : WithTop ℚ) +
        b.tail.halfGapCandidate 0 := by
    rw [← b.tail.coe_halfGapValue]
    norm_cast
  push_cast at hdom
  have hdom' :
      (((S.pairBlock.toGoodBONG b.good).alphaValue 0 : ℚ) : WithTop ℚ) ≤
        (((b.order 1 : ℚ) : WithTop ℚ) -
          ((b.order 0 : ℚ) : WithTop ℚ)) +
            b.tail.halfGapCandidate 0 := by
    simpa only [pair] using hdom
  rw [lemma214_withTop_add_min, lemma214_withTop_add_min] at hglobal
  rw [min_assoc, ← min_assoc, min_eq_left hdom'] at hglobal
  have hrightTerminal : (b.order 0 : ℚ) + pair.alphaValue 0 ≤
      (b.order 2 : ℚ) + (ramificationIndex K : ℚ) := by
    push_cast at hpairLeHalf
    have hgood02Q : (b.order 0 : ℚ) ≤ b.order 2 := by
      exact_mod_cast hgood02
    linarith
  by_cases htop : quadraticDefect K (a * c) = ⊤
  · have horder :=
      D.weightIdealOrder_eq_min_components_of_defect_eq_top_fin_two
        a c ha hcomponentZero hcomponentOne htwo htop
    have hcrossTop : b.tail.adjacentDefect 0 = ⊤ := by
      unfold adjacentDefect
      rw [htailProduct]
      unfold defectOrder
      rw [← hcross, htop]
      rfl
    unfold leftDefectCandidate at hglobal
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hglobal
    rw [hcrossTop, htailOrder0, htailOrder1] at hglobal
    simp at hglobal
    have hglobalPair : b.alphaValue 0 =
        min (pair.alphaValue 0)
          ((b.order 1 : ℚ) - b.order 0 +
            ((b.order 2 : ℚ) - b.order 1 + right.alphaValue 0)) := by
      apply WithTop.coe_injective
      push_cast
      rw [b.coe_alphaValue, pair.coe_alphaValue, right.coe_alphaValue]
      convert hglobal using 1 <;> simp only [pair]
      congr 1
    have horderQ : (Lattice.weightIdealOrder q L : ℚ) =
        min
          (Lattice.weightIdealOrder (D.component 0).space
            (D.component 0).lattice : ℚ)
          (Lattice.weightIdealOrder (D.component 1).space
            (D.component 1).lattice : ℚ) := by
      exact_mod_cast horder
    rw [hpairWeight, hrightWeight] at horderQ
    rw [min_comm ((b.order 2 : ℚ) + right.alphaValue 0)
          ((b.order 2 : ℚ) + (ramificationIndex K : ℚ)),
        ← min_assoc, min_eq_left hrightTerminal] at horderQ
    rw [horderQ, hglobalPair, lemma214_add_min]
    congr 1
    ring
  · have horder :=
      D.weightIdealOrder_eq_min_components_defect_fin_two
        a c ha hcomponentZero hcomponentOne htwo htop
    have hcrossFinite : b.tail.adjacentDefect 0 =
        ((((quadraticDefect K (a * c)).toNat : Nat) : ℚ) : WithTop ℚ) := by
      unfold adjacentDefect
      rw [htailProduct]
      unfold defectOrder
      rw [← hcross, ← ENat.coe_toNat htop]
      rfl
    unfold leftDefectCandidate at hglobal
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hglobal
    rw [hcrossFinite, htailOrder0, htailOrder1] at hglobal
    norm_cast at hglobal
    push_cast at hglobal
    have hglobalPair : b.alphaValue 0 =
        min (pair.alphaValue 0)
          (min
            ((b.order 1 : ℚ) - b.order 0 +
              ((b.order 2 : ℚ) - b.order 1 +
                ((quadraticDefect K (a * c)).toNat : ℚ)))
            ((b.order 1 : ℚ) - b.order 0 +
              ((b.order 2 : ℚ) - b.order 1 + right.alphaValue 0))) := by
      simpa only [pair] using hglobal
    have horderQ : (Lattice.weightIdealOrder q L : ℚ) =
        min
          (min
            (Lattice.weightIdealOrder (D.component 0).space
              (D.component 0).lattice : ℚ)
            (Lattice.weightIdealOrder (D.component 1).space
              (D.component 1).lattice : ℚ))
          ((ordUnit K c + (quadraticDefect K (a * c)).toNat : Int) : ℚ) := by
      exact_mod_cast horder
    rw [hpairWeight, hrightWeight, hcOrder] at horderQ
    push_cast at horderQ
    rw [min_comm ((b.order 2 : ℚ) + right.alphaValue 0)
          ((b.order 2 : ℚ) + (ramificationIndex K : ℚ)),
        ← min_assoc, min_eq_left hrightTerminal] at horderQ
    rw [horderQ, hglobalPair, lemma214_add_min, lemma214_add_min]
    have hdShift : (b.order 0 : ℚ) +
        ((b.order 1 : ℚ) - b.order 0 +
          ((b.order 2 : ℚ) - b.order 1 +
            ((quadraticDefect K (a * c)).toNat : ℚ))) =
          (b.order 2 : ℚ) +
            ((quadraticDefect K (a * c)).toNat : ℚ) := by
      ring
    have halphaShift : (b.order 0 : ℚ) +
        ((b.order 1 : ℚ) - b.order 0 +
          ((b.order 2 : ℚ) - b.order 1 + right.alphaValue 0)) =
          (b.order 2 : ℚ) + right.alphaValue 0 := by
      ring
    rw [hdShift, halphaShift]
    rw [min_assoc, min_comm ((b.order 2 : ℚ) + right.alphaValue 0)
      ((b.order 2 : ℚ) +
        ((quadraticDefect K (a * c)).toNat : ℚ))]

theorem lemma214_weightIdealOrder_formula_of_strict
    {n : Nat} (b : GoodBONG q L (n + 2))
    (hstrict : b.order 1 < b.order 0)
    (hweight : (Lattice.weightIdealOrder q L : ℚ) =
      (b.order 0 : ℚ) + b.alphaValue 0) :
    (Lattice.weightIdealOrder q L : ℚ) =
      min ((b.order 0 : ℚ) + b.alphaValue 0)
        ((b.order 0 : ℚ) + (ramificationIndex K : ℚ)) := by
  calc
    (Lattice.weightIdealOrder q L : ℚ) =
        (b.order 0 : ℚ) + b.alphaValue 0 := hweight
    _ = min ((b.order 0 : ℚ) + b.alphaValue 0)
        ((b.order 0 : ℚ) + (ramificationIndex K : ℚ)) := by
      symm
      apply min_eq_left
      have halpha := b.alphaValue_le_halfGapValue 0
      unfold halfGapValue orderGap at halpha
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at halpha
      push_cast at halpha
      have hstrictQ : (b.order 1 : ℚ) < b.order 0 := by
        exact_mod_cast hstrict
      linarith

/-- Beli (2009), Lemma 2.14 in every rank at least two. -/
theorem lemma214_weightIdealOrder_all
    {n : Nat} (b : GoodBONG q L (n + 2)) :
    (Lattice.weightIdealOrder q L : ℚ) =
      min ((b.order 0 : ℚ) + b.alphaValue 0)
        ((b.order 0 : ℚ) + (ramificationIndex K : ℚ)) := by
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      cases n with
      | zero =>
          by_cases hnondecreasing : b.order 0 ≤ b.order 1
          · exact b.lemma214_weightIdealOrder_binary_nondecreasing hnondecreasing
          · have hstrict : b.order 1 < b.order 0 :=
              lt_of_not_ge hnondecreasing
            exact b.lemma214_weightIdealOrder_formula_of_strict hstrict
              (BONG.weightIdealOrder_binary_strict b hstrict)
      | succ n =>
          cases n with
          | zero =>
              by_cases hnondecreasing : b.order 0 ≤ b.order 1
              · rcases b.toBONG.beliCorollary44_i_unconditional b.good
                    (0 : Fin 3) (by simp) hnondecreasing with ⟨S⟩
                let right := (S.right.toGoodBONG b.good).castLength
                  (by omega : 3 - 1 = 2)
                have hright :
                    (Lattice.weightIdealOrder
                      (q.restrict S.right.carrier S.right.nondegenerate)
                      S.right.lattice : ℚ) =
                      min ((right.order 0 : ℚ) + right.alphaValue 0)
                        ((right.order 0 : ℚ) +
                          (ramificationIndex K : ℚ)) :=
                  ih 0 (by omega) right
                exact b.lemma214_weightIdealOrder_nondecreasing_step
                  hnondecreasing S right rfl hright
              · have hstrict : b.order 1 < b.order 0 :=
                    lt_of_not_ge hnondecreasing
                exact b.lemma214_weightIdealOrder_formula_of_strict hstrict
                  (b.lemma214_weightIdealOrder_ternary_strict hstrict)
          | succ n =>
              by_cases hnondecreasing : b.order 0 ≤ b.order 1
              · rcases b.toBONG.beliCorollary44_i_unconditional b.good
                    (0 : Fin (n + 4)) (by simp)
                    hnondecreasing with ⟨S⟩
                let right := (S.right.toGoodBONG b.good).castLength
                  (by omega : n + 4 - 1 = n + 3)
                have hright :
                    (Lattice.weightIdealOrder
                      (q.restrict S.right.carrier S.right.nondegenerate)
                      S.right.lattice : ℚ) =
                      min ((right.order 0 : ℚ) + right.alphaValue 0)
                        ((right.order 0 : ℚ) +
                          (ramificationIndex K : ℚ)) :=
                  ih (n + 1) (by omega) right
                exact b.lemma214_weightIdealOrder_nondecreasing_step
                  hnondecreasing S right rfl hright
              · have hstrict : b.order 1 < b.order 0 :=
                    lt_of_not_ge hnondecreasing
                rcases b.toBONG.beliCorollary44_ii_unconditional b.good
                    (0 : Fin (n + 4)) (by simp) hstrict with ⟨S⟩
                let right := (S.rightBlock.toGoodBONG b.good).castLength
                  (by omega : n + 4 - (0 + 2) = n + 2)
                have hright :
                    (Lattice.weightIdealOrder
                      (q.restrict S.rightBlock.carrier
                        S.rightBlock.nondegenerate)
                      S.rightBlock.lattice : ℚ) =
                      min ((right.order 0 : ℚ) + right.alphaValue 0)
                        ((right.order 0 : ℚ) +
                          (ramificationIndex K : ℚ)) :=
                  ih n (by omega) right
                exact b.lemma214_weightIdealOrder_formula_of_strict hstrict
                  (b.lemma214_weightIdealOrder_strict_step hstrict S right rfl
                    hright)

end BONG.GoodBONG

noncomputable instance beli2009JordanWeightOrderLawsProved :
    Beli2009JordanWeightOrderLaws.{u, v} K where
  lemma214_unary := fun b => b.weightIdealOrder_unary_proof
  lemma214 := fun b => b.lemma214_weightIdealOrder_all

end Bong
