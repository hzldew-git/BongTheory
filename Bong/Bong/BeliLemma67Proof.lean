/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma67
import Bong.Bong.BeliDiscriminantNormGenerator

/-!
# Beli (2003), Lemma 6.7: local norm-group proof

This file discharges the local-law interface in Lemma 6.7.  The odd-gap
branch uses the distinguished discriminant class, including the endpoint
`R = 2e + 1`.  The even-gap branch identifies the adjacent parameter with
`-epsilon_i epsilon_(i+1)` modulo squares and applies Hilbert duality.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem squareClass_mem_units_iff_even (a : Kˣ) :
    squareClass K a ∈ valuationUnitSquareClassSubgroup K ↔
      Even (ordUnit K a) := by
  constructor
  · rintro ⟨u, hu, hclass⟩
    change QuotientGroup.mk' (Subgroup.square Kˣ) u =
      QuotientGroup.mk' (Subgroup.square Kˣ) a at hclass
    rw [QuotientGroup.mk'_eq_mk'] at hclass
    rcases hclass with ⟨s, hs, husa⟩
    change IsSquare s at hs
    rcases hs with ⟨t, rfl⟩
    have huOrder :=
      (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
    have hord := congrArg (ordUnit K) husa
    rw [ordUnit_mul, ordUnit_mul, huOrder] at hord
    exact ⟨ordUnit K t, by omega⟩
  · rintro ⟨k, hk⟩
    let t : Kˣ := uniformizerPowerUnit K (-k)
    let u : Kˣ := a * t ^ 2
    have huOrder : ordUnit K u = 0 := by
      simp only [u, t, ordUnit_mul, ordUnit_pow,
        ordUnit_uniformizerPowerUnit]
      omega
    have hu : IsValuationUnit K (u : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder
    refine ⟨u, hu, ?_⟩
    exact squareClass_mul_square K a t

private theorem cyclic_sup_units_inf_eq_of_odd
    (a : Kˣ) (H : Subgroup (SquareClass K))
    (ha : squareClass K a ∈ H) (hodd : Odd (ordUnit K a)) :
    cyclicSquareClassSubgroup K a ⊔
        (valuationUnitSquareClassSubgroup K ⊓ H) = H := by
  apply le_antisymm
  · apply sup_le
    · exact (Subgroup.zpowers_le).2 ha
    · exact inf_le_right
  · intro z hz
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    change squareClass K x ∈ H at hz
    change squareClass K x ∈
      cyclicSquareClassSubgroup K a ⊔
        (valuationUnitSquareClassSubgroup K ⊓ H)
    rcases Int.even_or_odd (ordUnit K x) with hxEven | hxOdd
    · exact Subgroup.mem_sup.mpr ⟨1,
        (cyclicSquareClassSubgroup K a).one_mem,
        squareClass K x,
        ⟨(squareClass_mem_units_iff_even x).2 hxEven, hz⟩,
        by simp⟩
    · have hratioEven : Even (ordUnit K (x / a)) := by
        rcases hxOdd with ⟨r, hr⟩
        rcases hodd with ⟨s, hs⟩
        refine ⟨r - s, ?_⟩
        simp only [ordUnit_mul, ordUnit_inv, div_eq_mul_inv]
        omega
      have hratioH : squareClass K (x / a) ∈ H := by
        have haInv := H.inv_mem ha
        change squareClass K (x * a⁻¹) ∈ H
        exact H.mul_mem hz haInv
      exact Subgroup.mem_sup.mpr ⟨squareClass K a,
        Subgroup.mem_zpowers _, squareClass K (x / a),
        ⟨(squareClass_mem_units_iff_even (x / a)).2 hratioEven,
          hratioH⟩, by
        change squareClass K (a * (x / a)) = squareClass K x
        congr 1
        simp [div_eq_mul_inv]⟩

theorem beliSpinorGroupRepresentative_eq_norm_of_odd_trigger
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hodd : Odd (ordUnit K a))
    (hupper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) + 1) :
    beliSpinorGroupRepresentative K a =
      quadraticNormSquareClassSubgroup K (-a) := by
  have hnonneg : 0 ≤ ordUnit K a :=
    ha.ordUnit_nonneg_of_odd hodd
  have hoddNeg : Odd (ordUnit K (-a)) := by simpa using hodd
  have hdefect : beliParameterDefect K a = 0 := by
    exact quadraticDefect_eq_zero_of_odd_ordUnit (-a) hoddNeg
  have hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K) := by
    intro hclass
    have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
    rw [ordUnit_negativeQuarterUnit] at hord
    have he : 0 < (ramificationIndex K : Int) := by
      exact_mod_cast ramificationIndex_pos (K := K)
    omega
  by_cases hR : ordUnit K a ≤ 2 * (ramificationIndex K : Int)
  · have hd : 2 * beliParameterDefect K a ≤
        (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
      rw [hdefect]
      simp
    exact beliSpinorGroupRepresentative_caseIII_low K a ha
      hquarter hR hd
  · have hRlow : 2 * (ramificationIndex K : Int) < ordUnit K a :=
      lt_of_not_ge hR
    have horder : ordUnit K a =
        2 * (ramificationIndex K : Int) + 1 := by omega
    have hRhigh : ordUnit K a ≤
        4 * (ramificationIndex K : Int) := by
      have he : 0 < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos (K := K)
      omega
    have hd : 2 * beliParameterDefect K a ≤
        (beliSpinorCaseIICutoff K a : ℕ∞) := by
      rw [hdefect]
      simp
    rw [beliSpinorGroupRepresentative_caseII_low K a ha hquarter
      hRlow hRhigh hd]
    have hexponent : beliSpinorCaseIILowExponent K a = 1 := by
      unfold beliSpinorCaseIILowExponent beliParameterDefectNat
      rw [horder, hdefect]
      simp
    rw [hexponent, ← principalUnitSquareClassSubgroup_zero_eq_one,
      principalUnitSquareClassSubgroup_zero]
    apply cyclic_sup_units_inf_eq_of_odd (K := K) a
      (quadraticNormSquareClassSubgroup K (-a))
    · refine ⟨a, ?_, rfl⟩
      refine ⟨0, 1, ?_⟩
      simp
    · exact hodd

theorem beliSpinorGroupRepresentative_eq_norm_of_low_defect
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hR : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hd : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (hfinite : beliParameterDefect K a ≠ ⊤) :
    beliSpinorGroupRepresentative K a =
      quadraticNormSquareClassSubgroup K (-a) := by
  have hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K) := by
    intro hclass
    rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
      K hclass with ⟨s, hs, has⟩
    have hdefect := beliParameterDefect_mul_valuationUnit_square K a s hs
    rw [has, beliParameterDefect_negativeQuarterUnit] at hdefect
    exact hfinite hdefect.symm
  exact beliSpinorGroupRepresentative_caseIII_low K a ha
    hquarter hR hd

private theorem adjacentParameter_eq_uniformizerPower_mul_normalized
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (i : Fin n) (hi : i.1 + 1 < n) :
    b.adjacentParameter i hi =
      uniformizerPowerUnit K
          (b.order ⟨i.1 + 1, hi⟩ - b.order i) *
        (b.normalizedValue ⟨i.1 + 1, hi⟩ / b.normalizedValue i) := by
  unfold BONG.adjacentParameter
  rw [← b.uniformizer_zpow_mul_normalizedValue ⟨i.1 + 1, hi⟩,
    ← b.uniformizer_zpow_mul_normalizedValue i]
  unfold uniformizerPowerUnit
  simp only [div_eq_mul_inv, mul_inv_rev, zpow_sub]
  let A : Kˣ := uniformizerUnit K ^ b.order ⟨i.1 + 1, hi⟩
  let B : Kˣ := b.normalizedValue ⟨i.1 + 1, hi⟩
  let C : Kˣ := uniformizerUnit K ^ b.order i
  let D : Kˣ := b.normalizedValue i
  change A * B * (D⁻¹ * C⁻¹) = A * C⁻¹ * (B * D⁻¹)
  calc
    A * B * (D⁻¹ * C⁻¹) = A * (B * (C⁻¹ * D⁻¹)) := by
      rw [mul_comm D⁻¹ C⁻¹, mul_assoc]
    _ = A * (C⁻¹ * (B * D⁻¹)) := by
      rw [mul_left_comm B C⁻¹ D⁻¹]
    _ = A * C⁻¹ * (B * D⁻¹) := by rw [mul_assoc]

private theorem negative_adjacentParameter_eq_normalizedProduct_mul_square_of_even
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 1)) (i : Fin n)
    (heven : Even (b.order i.succ - b.order i.castSucc)) :
    ∃ s : Kˣ,
      -(b.adjacentParameter i.castSucc (by simpa using i.isLt)) =
        b.normalizedAdjacentProduct i * s ^ 2 := by
  rcases heven with ⟨r, hr⟩
  let εi : Kˣ := b.normalizedValue i.castSucc
  let εj : Kˣ := b.normalizedValue i.succ
  let s : Kˣ := uniformizerPowerUnit K r * εi⁻¹
  refine ⟨s, ?_⟩
  rw [adjacentParameter_eq_uniformizerPower_mul_normalized]
  have hindex : (⟨i.castSucc.1 + 1, by simpa using i.isLt⟩ : Fin (n + 1)) =
      i.succ := by ext; simp
  rw [hindex]
  have hpower : uniformizerPowerUnit K
        (b.order i.succ - b.order i.castSucc) =
      uniformizerPowerUnit K r ^ 2 := by
    rw [hr]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
  rw [hpower]
  unfold BONG.normalizedAdjacentProduct
  change -(uniformizerPowerUnit K r ^ 2 * (εj / εi)) =
    -(εi * εj) * s ^ 2
  dsimp only [s]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero εi]

theorem adjacentParameterDefect_eq_normalizedDefect_of_even
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 1)) (i : Fin n)
    (heven : Even (b.order i.succ - b.order i.castSucc)) :
    beliParameterDefect K
        (b.adjacentParameter i.castSucc (by simpa using i.isLt)) =
      quadraticDefect K (b.normalizedAdjacentProduct i) := by
  rcases negative_adjacentParameter_eq_normalizedProduct_mul_square_of_even
    (K := K) b i heven with ⟨s, hs⟩
  unfold beliParameterDefect
  rw [hs, quadraticDefect_mul_square]

theorem normalizedDefect_bounds_of_even_trigger
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 1)) (i : Fin n)
    (heven : Even (b.order i.succ - b.order i.castSucc))
    (hbound : b.normalizedAdjacentDefectOrder i ≤
      ((((ramificationIndex K : ℚ) -
        ((b.order i.succ - b.order i.castSucc : Int) : ℚ) / 2) : ℚ) :
          WithTop ℚ)) :
    ∃ d : Nat,
      quadraticDefect K (b.normalizedAdjacentProduct i) = (d : ℕ∞) ∧
        2 * (d : Int) ≤
          2 * (ramificationIndex K : Int) -
            (b.order i.succ - b.order i.castSucc) := by
  cases hdefect : quadraticDefect K (b.normalizedAdjacentProduct i) with
  | top =>
      unfold BONG.normalizedAdjacentDefectOrder at hbound
      rw [hdefect] at hbound
      change (⊤ : WithTop ℚ) ≤
        ((((ramificationIndex K : ℚ) -
          ((b.order i.succ - b.order i.castSucc : Int) : ℚ) / 2) : ℚ) :
            WithTop ℚ) at hbound
      simpa using hbound
  | coe d =>
      refine ⟨d, rfl, ?_⟩
      unfold BONG.normalizedAdjacentDefectOrder at hbound
      rw [hdefect] at hbound
      change ((d : ℚ) : WithTop ℚ) ≤
        ((((ramificationIndex K : ℚ) -
          ((b.order i.succ - b.order i.castSucc : Int) : ℚ) / 2) : ℚ) :
            WithTop ℚ) at hbound
      have hq : (d : ℚ) ≤
          (ramificationIndex K : ℚ) -
            ((b.order i.succ - b.order i.castSucc : Int) : ℚ) / 2 := by
        exact_mod_cast hbound
      rcases heven with ⟨r, hr⟩
      rw [hr] at hq ⊢
      have hq' : (d : ℚ) ≤ (ramificationIndex K : ℚ) - r := by
        norm_num at hq ⊢
        exact hq
      have hz : (d : Int) ≤ (ramificationIndex K : Int) - r := by
        exact_mod_cast hq'
      omega

private theorem theoremOneAlpha_le_twoE_of_neighborFailure
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (i : Fin (n + 2))
    (hR : b.order i.succ - b.order i.castSucc ≤
      2 * (ramificationIndex K : Int) + 1)
    (hneighbor :
      (∃ j : Fin (n + 3), j.1 + 1 = i.1 ∧
        b.order i.castSucc - b.order j <
          2 * (ramificationIndex K : Int) + 1) ∨
      (∃ k : Fin (n + 3), i.1 + 2 = k.1 ∧
        b.order k - b.order i.succ <
          2 * (ramificationIndex K : Int) + 1)) :
    b.theoremOneAlpha ≤ 2 * ramificationIndex K := by
  rcases hneighbor with ⟨j, hj, hjgap⟩ | ⟨k, hk, hkgap⟩
  · let p : Fin (n + 1) := ⟨j.1, by omega⟩
    have halpha := b.theoremOneAlpha_le_twoStepDepth p
    dsimp only [BONG.theoremOneTwoStepDepth, p] at halpha
    have hstart : (⟨j.1, by omega⟩ : Fin (n + 3)) = j := by
      ext
      rfl
    have hend : (⟨j.1 + 2, by omega⟩ : Fin (n + 3)) = i.succ := by
      ext
      simp only [Fin.val_mk, Fin.val_succ]
      omega
    rw [hstart, hend] at halpha
    have hdepth : Int.toNat ((b.order i.succ - b.order j) / 2) ≤
        2 * ramificationIndex K := by
      have he : 0 < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos (K := K)
      omega
    exact halpha.trans hdepth
  · let p : Fin (n + 1) := ⟨i.1, by omega⟩
    have halpha := b.theoremOneAlpha_le_twoStepDepth p
    dsimp only [BONG.theoremOneTwoStepDepth, p] at halpha
    have hstart : (⟨i.1, by omega⟩ : Fin (n + 3)) = i.castSucc := by
      ext
      rfl
    have hend : (⟨i.1 + 2, by omega⟩ : Fin (n + 3)) = k := by
      ext
      simpa using hk
    rw [hstart, hend] at halpha
    have hdepth : Int.toNat ((b.order k - b.order i.castSucc) / 2) ≤
        2 * ramificationIndex K := by
      have he : 0 < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos (K := K)
      omega
    exact halpha.trans hdepth

private theorem theoremOneAlpha_add_defect_le_twoE_of_neighborFailure
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (i : Fin (n + 2)) (d : Nat)
    (hA : b.HasPropertyA)
    (hRd : 2 * (d : Int) ≤
      2 * (ramificationIndex K : Int) -
        (b.order i.succ - b.order i.castSucc))
    (hneighbor :
      (∃ j : Fin (n + 3), j.1 + 1 = i.1 ∧
        b.order i.castSucc - b.order j <
          2 * (ramificationIndex K : Int) + 1) ∨
      (∃ k : Fin (n + 3), i.1 + 2 = k.1 ∧
        b.order k - b.order i.succ <
          2 * (ramificationIndex K : Int) + 1)) :
    b.theoremOneAlpha + d ≤ 2 * ramificationIndex K := by
  rcases hneighbor with ⟨j, hj, hjgap⟩ | ⟨k, hk, hkgap⟩
  · let p : Fin (n + 1) := ⟨j.1, by omega⟩
    have halpha := b.theoremOneAlpha_le_twoStepDepth p
    dsimp only [BONG.theoremOneTwoStepDepth, p] at halpha
    have hstart : (⟨j.1, by omega⟩ : Fin (n + 3)) = j := by
      ext
      rfl
    have hend : (⟨j.1 + 2, by omega⟩ : Fin (n + 3)) = i.succ := by
      ext
      simp only [Fin.val_succ]
      omega
    rw [hstart, hend] at halpha
    have hpos : b.order j < b.order i.succ := by
      have h := hA j (by omega)
      have htarget : (⟨j.1 + 2, by omega⟩ : Fin (n + 3)) = i.succ := by
        ext
        simp only [Fin.val_succ]
        omega
      simpa only [htarget] using h
    have hdepth :
        Int.toNat ((b.order i.succ - b.order j) / 2) + d ≤
          2 * ramificationIndex K := by
      have he : 0 < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos (K := K)
      omega
    omega
  · let p : Fin (n + 1) := ⟨i.1, by omega⟩
    have halpha := b.theoremOneAlpha_le_twoStepDepth p
    dsimp only [BONG.theoremOneTwoStepDepth, p] at halpha
    have hstart : (⟨i.1, by omega⟩ : Fin (n + 3)) = i.castSucc := by
      ext
      rfl
    have hend : (⟨i.1 + 2, by omega⟩ : Fin (n + 3)) = k := by
      ext
      simpa using hk
    rw [hstart, hend] at halpha
    have hpos : b.order i.castSucc < b.order k := by
      have hi2 : i.castSucc.1 + 2 < n + 3 := by
        change i.1 + 2 < n + 3
        rw [hk]
        exact k.isLt
      have h := hA i.castSucc hi2
      have htarget : (⟨i.castSucc.1 + 2, by omega⟩ : Fin (n + 3)) = k := by
        ext
        simpa using hk
      simpa only [htarget] using h
    have hdepth :
        Int.toNat ((b.order k - b.order i.castSucc) / 2) + d ≤
          2 * ramificationIndex K := by
      have he : 0 < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos (K := K)
      omega
    omega

private theorem quadraticNorm_sup_beliCongruence_eq_top_of_defect_add_le
    (a : Kˣ) (alpha d : Nat)
    (hdefect : quadraticDefect K a = (d : ℕ∞))
    (hbound : alpha + d ≤ 2 * ramificationIndex K) :
    quadraticNormSquareClassSubgroup K a ⊔
        beliCongruenceSquareClassSubgroup K alpha = ⊤ := by
  by_cases halpha : alpha = 0
  · subst alpha
    simp
  · have halphaPos : 0 < alpha := Nat.pos_of_ne_zero halpha
    rw [beliCongruenceSquareClassSubgroup_of_pos K halphaPos]
    have hnot : ¬principalUnitSquareClassSubgroup K alpha ≤
        quadraticNormSquareClassSubgroup K a := by
      rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff
        K a alpha halphaPos, hdefect]
      norm_cast
      omega
    rw [quadraticNormSquareClassSubgroup_eq_ker] at hnot ⊢
    simpa using inf_ker_sup_eq_of_le_of_not_le
      (squareClassHilbertCharacter K a) ⊤
      (principalUnitSquareClassSubgroup K alpha) le_top hnot

noncomputable instance beliLemma67LawsProved :
    BONG.BeliLemma67Laws.{u, v} K where
  local_factor_eq_top_of_violation := by
    intro V _instAdd _instModule q L n b hA w
    let i : Fin (n + 2) := w.index
    have hi : i.castSucc.1 + 1 < n + 3 := by
      simpa [i, Nat.succ_eq_add_one, Nat.add_assoc] using
        Nat.succ_lt_succ w.index.isLt
    let a : Kˣ := b.adjacentParameter i.castSucc hi
    have ha : BONG.IsBinaryParameterAdmissible a :=
      b.adjacentParameter_isBinaryParameterAdmissible i.castSucc hi
    have horder : ordUnit K a =
        b.order i.succ - b.order i.castSucc := by
      dsimp only [a]
      rw [b.ordUnit_adjacentParameter]
      congr 2
    change beliSpinorGroup K (unitSquareClass K a) ⊔
        beliCongruenceSquareClassSubgroup K b.theoremOneAlpha = ⊤
    rw [beliSpinorGroup_unitSquareClass]
    have htrigger := w.trigger
    change
      (b.order i.succ - b.order i.castSucc ≤
          2 * (ramificationIndex K : Int) + 1 ∧
        Odd (b.order i.succ - b.order i.castSucc)) ∨
      (Even (b.order i.succ - b.order i.castSucc) ∧
        b.normalizedAdjacentDefectOrder i ≤
          ((((ramificationIndex K : ℚ) -
            ((b.order i.succ - b.order i.castSucc : Int) : ℚ) / 2) : ℚ) :
              WithTop ℚ)) at htrigger
    rcases htrigger with ⟨hRupper, hodd⟩ | ⟨heven, hdefectBound⟩
    · have hoddA : Odd (ordUnit K a) := by rwa [horder]
      have hG := beliSpinorGroupRepresentative_eq_norm_of_odd_trigger
        (K := K) a ha hoddA (by rwa [horder])
      rw [hG]
      have hoddNeg : Odd (ordUnit K (-a)) := by simpa using hoddA
      have hdefect : quadraticDefect K (-a) = (0 : ℕ∞) :=
        quadraticDefect_eq_zero_of_odd_ordUnit (-a) hoddNeg
      have halpha := theoremOneAlpha_le_twoE_of_neighborFailure
        (K := K) b i hRupper w.neighborFailure
      exact quadraticNorm_sup_beliCongruence_eq_top_of_defect_add_le
        (K := K) (-a) b.theoremOneAlpha 0 hdefect (by simpa using halpha)
    · rcases normalizedDefect_bounds_of_even_trigger
          (K := K) b i heven hdefectBound with ⟨d, hd, hRd⟩
      have hparameterDefect : beliParameterDefect K a = (d : ℕ∞) := by
        rw [adjacentParameterDefect_eq_normalizedDefect_of_even
          (K := K) b i heven, hd]
      have hRupper : ordUnit K a ≤
          2 * (ramificationIndex K : Int) := by
        rw [horder]
        omega
      have hlow : 2 * beliParameterDefect K a ≤
          (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
        rw [hparameterDefect]
        norm_cast
        unfold beliSpinorCaseIIILowerCutoff
        rw [horder]
        have hnonneg : 0 ≤
            2 * (ramificationIndex K : Int) -
              (b.order i.succ - b.order i.castSucc) := by omega
        have hcutCast :
            (Int.toNat
                (2 * (ramificationIndex K : Int) -
                  (b.order i.succ - b.order i.castSucc)) : Int) =
              2 * (ramificationIndex K : Int) -
                (b.order i.succ - b.order i.castSucc) :=
          Int.toNat_of_nonneg hnonneg
        omega
      have hfinite : beliParameterDefect K a ≠ ⊤ := by
        rw [hparameterDefect]
        exact ENat.coe_ne_top d
      have hG := beliSpinorGroupRepresentative_eq_norm_of_low_defect
        (K := K) a ha hRupper hlow hfinite
      rw [hG]
      have halpha :=
        theoremOneAlpha_add_defect_le_twoE_of_neighborFailure
          (K := K) b i d hA hRd w.neighborFailure
      exact quadraticNorm_sup_beliCongruence_eq_top_of_defect_add_le
        (K := K) (-a) b.theoremOneAlpha d hparameterDefect halpha

end Bong
