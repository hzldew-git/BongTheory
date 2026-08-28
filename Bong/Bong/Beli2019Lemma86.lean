/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma85
import Bong.Bong.Beli2006SectionTwo
import Bong.Bong.Beli2009ClassificationPropagation
import Bong.Bong.Beli2009TwoAdic
import Bong.Bong.BinaryDefectCriterion
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Lemma 8.6

This file formalizes the comparison-sequence construction in Lemma 8.6.
An orthogonal basis with the same order sequence as a fixed good BONG is
equipped with its literal prefix products and adjacent defects.  Prefix-defect
bounds and the square full product force every adjacent binary parameter to be
admissible, hence the prescribed basis realizes a good BONG.  The remaining
parts compare the alpha invariants of the source and the realization.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

/-- The order-theoretic inequality `ord(a) + d(a) ≥ 0`, expressed with the
rationally embedded defect order, implies integral absolute quadratic defect.
This is the bridge used in the binary-admissibility step of Lemma 8.6(i). -/
theorem hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
    [QuadraticDefectLaws K] (a : Kˣ)
    (h : (0 : WithTop ℚ) ≤
      ((ordUnit K a : ℚ) : WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K) a) :
    HasNonnegativeAbsoluteQuadraticDefect a := by
  rw [hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le]
  by_cases htop : quadraticDefect K a = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    have hdefect : BONG.GoodBONG.defectOrder (K := K) a =
        (d : WithTop ℚ) := by
      unfold BONG.GoodBONG.defectOrder
      rw [← hd]
      rfl
    rw [hdefect] at h
    norm_cast at h
    by_cases horder : 0 ≤ ordUnit K a
    · rw [absoluteDefectThreshold_eq_zero_of_nonneg horder]
      exact bot_le
    · have horderNeg : ordUnit K a < 0 := lt_of_not_ge horder
      have hboundInt : -ordUnit K a ≤ (d : Int) :=
        (neg_le_iff_add_nonneg).2 (by simpa [add_comm] using h)
      have hboundNat : Int.toNat (-ordUnit K a) ≤ d := by
        omega
      rw [absoluteDefectThreshold, ← hd]
      exact WithTop.coe_le_coe.mpr hboundNat

end Dyadic

namespace BONG.OrthogonalBasisData

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {N : Nat}

/-- Product of the first `m` values of a prescribed orthogonal basis. -/
noncomputable def prefixProduct (X : OrthogonalBasisData r N) (m : Nat) : Kˣ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin N => j.1 < m), X.valueUnit j

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
  @[simp]
  theorem prefixProduct_zero (X : OrthogonalBasisData r N) :
      X.prefixProduct 0 = 1 := by
    simp [prefixProduct]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
  /-- Recurrence for prescribed-basis prefix products. -/
  theorem prefixProduct_succ (X : OrthogonalBasisData r N)
      (m : Nat) (hm : m < N) :
      X.prefixProduct (m + 1) =
        X.prefixProduct m * X.valueUnit ⟨m, hm⟩ := by
    classical
    have hset :
        Finset.univ.filter (fun j : Fin N => j.1 < m + 1) =
          insert ⟨m, hm⟩
            (Finset.univ.filter (fun j : Fin N => j.1 < m)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · intro hj
        by_cases hjm : j.1 = m
        · exact Or.inl (Fin.ext hjm)
        · exact Or.inr (by omega)
      · rintro (rfl | hj)
        · exact Nat.lt_succ_self m
        · omega
    rw [prefixProduct, prefixProduct, hset, Finset.prod_insert]
    · ac_rfl
    · simp

/-- The unit `-b_j b_{j+1}` attached to a prescribed orthogonal basis. -/
noncomputable def adjacentProduct (X : OrthogonalBasisData r (N + 1))
    (j : Fin N) : Kˣ :=
  -(X.valueUnit j.castSucc * X.valueUnit j.succ)

/-- The rationally embedded relative defect of a prescribed adjacent pair. -/
noncomputable def adjacentDefect (X : OrthogonalBasisData r (N + 1))
    (j : Fin N) : WithTop ℚ :=
  GoodBONG.defectOrder (K := K) (X.adjacentProduct j)

/-- Mixed prefix product between a good BONG and a prescribed orthogonal
basis. -/
noncomputable def comparisonPrefixUnit
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (m : Nat) : Kˣ :=
  a.prefixProduct m * X.prefixProduct m

/-- Defect of the mixed prefix product. -/
noncomputable def comparisonPrefixDefect
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (m : Nat) : WithTop ℚ :=
  GoodBONG.defectOrder (K := K) (X.comparisonPrefixUnit a m)

/-- Adding an adjacent pair multiplies the mixed prefix by the two adjacent
products. -/
theorem comparisonPrefixUnit_add_two
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (m : Nat) (hm : m + 1 < N + 1) :
    X.comparisonPrefixUnit a (m + 2) =
      X.comparisonPrefixUnit a m *
        a.adjacentProduct ⟨m, by omega⟩ *
          X.adjacentProduct ⟨m, by omega⟩ := by
  unfold comparisonPrefixUnit GoodBONG.prefixProduct adjacentProduct
    GoodBONG.adjacentProduct GoodBONG.valueUnit
  rw [a.toBONG.prefixProduct_succ (m + 1) hm,
    a.toBONG.prefixProduct_succ m (by omega),
    X.prefixProduct_succ (m + 1) hm,
    X.prefixProduct_succ m (by omega)]
  have hzero :
      (⟨m, by omega⟩ : Fin (N + 1)) =
        (⟨m, by omega⟩ : Fin N).castSucc := by
    apply Fin.ext
    rfl
  have hone :
      (⟨m + 1, hm⟩ : Fin (N + 1)) =
        (⟨m, by omega⟩ : Fin N).succ := by
    apply Fin.ext
    rfl
  rw [hzero, hone]
  apply Units.ext
  simp only [Units.val_mul, Units.val_neg]
  ring

@[simp]
theorem comparisonPrefixDefect_zero
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1)) :
    X.comparisonPrefixDefect a 0 = ⊤ := by
  unfold comparisonPrefixDefect comparisonPrefixUnit GoodBONG.prefixProduct
  rw [BONG.prefixProduct_zero, prefixProduct_zero]
  simpa using GoodBONG.defectOrder_one (K := K)

/-- A square full comparison product has infinite defect. -/
theorem comparisonPrefixDefect_full_eq_top
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (hfull : IsSquare (X.comparisonPrefixUnit a (N + 1))) :
    X.comparisonPrefixDefect a (N + 1) = ⊤ := by
  unfold comparisonPrefixDefect
  exact GoodBONG.defectOrder_eq_top_of_isSquare hfull

/-- The domination identity used in Lemma 8.6(i): the target adjacent defect
is bounded below by the preceding comparison defect, the following comparison
defect, and the source adjacent defect. -/
theorem min_comparison_adjacentDefect_le
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (m : Nat) (hm : m + 1 < N + 1) :
    min (X.comparisonPrefixDefect a m)
        (min (X.comparisonPrefixDefect a (m + 2))
          (a.adjacentDefect ⟨m, by omega⟩)) ≤
      X.adjacentDefect ⟨m, by omega⟩ := by
  let x := X.comparisonPrefixUnit a m
  let y := a.adjacentProduct ⟨m, by omega⟩
  let z := X.adjacentProduct ⟨m, by omega⟩
  have hafter : X.comparisonPrefixUnit a (m + 2) = x * y * z := by
    simpa only [x, y, z] using X.comparisonPrefixUnit_add_two a m hm
  have hfirst := GoodBONG.defectOrder_mul_ge_min (K := K)
    x (X.comparisonPrefixUnit a (m + 2))
  have hsecond := GoodBONG.defectOrder_mul_ge_min (K := K)
    (x * X.comparisonPrefixUnit a (m + 2)) y
  have hbound :
      min (GoodBONG.defectOrder (K := K) x)
          (min (GoodBONG.defectOrder (K := K)
              (X.comparisonPrefixUnit a (m + 2)))
            (GoodBONG.defectOrder (K := K) y)) ≤
        GoodBONG.defectOrder (K := K)
          ((x * X.comparisonPrefixUnit a (m + 2)) * y) := by
    rw [← min_assoc]
    exact (min_le_min hfirst le_rfl).trans hsecond
  have hsquare :
      GoodBONG.defectOrder (K := K)
          ((x * X.comparisonPrefixUnit a (m + 2)) * y) =
        GoodBONG.defectOrder (K := K) z := by
    rw [hafter]
    rw [show (x * (x * y * z)) * y = z * (x * y) ^ 2 by
      simp only [pow_two]
      ac_rfl]
    exact GoodBONG.defectOrder_mul_square z (x * y)
  rw [hsquare] at hbound
  simpa only [comparisonPrefixDefect, adjacentDefect,
    GoodBONG.adjacentDefect, x, y, z] using hbound

/-- The prescribed adjacent parameter has the difference of the two prescribed
orders. -/
theorem ordUnit_adjacentParameter
    (X : OrthogonalBasisData r N) (i : Fin N) (hi : i.1 + 1 < N) :
    ordUnit K (X.adjacentParameter i hi) =
      X.order ⟨i.1 + 1, hi⟩ - X.order i := by
  unfold adjacentParameter order
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
  abel

/-- Relative defect is unchanged when the adjacent ratio is replaced by the
negative product of the two adjacent values. -/
theorem defectOrder_neg_adjacentParameter
    (X : OrthogonalBasisData r (N + 1))
    (i : Fin (N + 1)) (hi : i.1 + 1 < N + 1) :
    GoodBONG.defectOrder (K := K) (-X.adjacentParameter i hi) =
      X.adjacentDefect ⟨i.1, by omega⟩ := by
  let j : Fin N := ⟨i.1, by omega⟩
  have hiEq : i = j.castSucc := by
    apply Fin.ext
    rfl
  have hnext : (⟨i.1 + 1, hi⟩ : Fin (N + 1)) = j.succ := by
    apply Fin.ext
    rfl
  have hproduct :
      X.adjacentProduct j =
        (-X.adjacentParameter i hi) * (X.valueUnit i) ^ 2 := by
    unfold adjacentProduct adjacentParameter
    rw [← hiEq, ← hnext]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_div_eq_div_val,
      Units.val_pow_eq_pow_val]
    field_simp [X.value_ne_zero i]
  rw [adjacentDefect, hproduct,
    GoodBONG.defectOrder_mul_square]

/-- The prescribed basis has the same complete order sequence as the source
good BONG. -/
def SameOrders (a : GoodBONG q L (N + 1))
    (X : OrthogonalBasisData r (N + 1)) : Prop :=
  ∀ i, X.order i = a.order i

/-- The mixed prefix defect at every internal cut is at least the source
alpha invariant. -/
def PrefixDefectBounds (a : GoodBONG q L (N + 1))
    (X : OrthogonalBasisData r (N + 1)) : Prop :=
  ∀ i : Fin N,
    (a.alphaValue i : WithTop ℚ) ≤
      X.comparisonPrefixDefect a (i.1 + 1)

/-- The preceding mixed prefix, shifted by the current order gap, bounds the
current source alpha.  At the left endpoint the prefix defect is infinite. -/
theorem alpha_le_orderGap_add_previousComparison
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (hprefix : X.PrefixDefectBounds a) (j : Fin N) :
    (a.alphaValue j : WithTop ℚ) ≤
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
        X.comparisonPrefixDefect a j.1 := by
  by_cases hj0 : j.1 = 0
  · rw [hj0, X.comparisonPrefixDefect_zero a]
    simp
  · let p : Fin N := ⟨j.1 - 1, by omega⟩
    have hpnext : p.1 + 1 < N := by
      dsimp [p]
      omega
    have hP1 := (a.alpha_p1 p hpnext).2
    have hpSucc : (⟨p.1 + 1, hpnext⟩ : Fin N) = j := by
      apply Fin.ext
      dsimp [p]
      omega
    rw [hpSucc] at hP1
    have hendpoint := hP1
    unfold GoodBONG.alphaRightEndpoint at hendpoint
    have hpOrder : p.succ = j.castSucc := by
      apply Fin.ext
      dsimp [p]
      omega
    rw [hpOrder] at hendpoint
    have hrat :
        a.alphaValue j ≤ (a.orderGap j : ℚ) + a.alphaValue p := by
      unfold GoodBONG.orderGap
      push_cast at hendpoint ⊢
      linarith
    have hratTop :
        (a.alphaValue j : WithTop ℚ) ≤
          (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            (a.alphaValue p : WithTop ℚ) := by
      exact_mod_cast hrat
    have hpBound := hprefix p
    have hpIndex : p.1 + 1 = j.1 := by
      dsimp [p]
      omega
    rw [hpIndex] at hpBound
    have hadd := add_le_add_left hpBound
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ)
    exact hratTop.trans (by simpa [add_comm] using hadd)

/-- The following mixed prefix, shifted by the current order gap, bounds the
current source alpha.  At the right endpoint the full comparison defect is
infinite. -/
theorem alpha_le_orderGap_add_nextComparison
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (hprefix : X.PrefixDefectBounds a)
    (hfull : IsSquare (X.comparisonPrefixUnit a (N + 1)))
    (j : Fin N) :
    (a.alphaValue j : WithTop ℚ) ≤
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
        X.comparisonPrefixDefect a (j.1 + 2) := by
  by_cases hlast : j.1 + 1 = N
  · have hindex : j.1 + 2 = N + 1 := by omega
    rw [hindex, X.comparisonPrefixDefect_full_eq_top a hfull]
    simp
  · have hjnext : j.1 + 1 < N := by omega
    let s : Fin N := ⟨j.1 + 1, hjnext⟩
    have hP1 := (a.alpha_p1 j hjnext).1
    have hjSucc : (⟨j.1 + 1, hjnext⟩ : Fin N) = s := rfl
    rw [hjSucc] at hP1
    have hendpoint := hP1
    unfold GoodBONG.alphaLeftEndpoint at hendpoint
    have hsOrder : s.castSucc = j.succ := by
      apply Fin.ext
      rfl
    rw [hsOrder] at hendpoint
    have hrat :
        a.alphaValue j ≤ (a.orderGap j : ℚ) + a.alphaValue s := by
      unfold GoodBONG.orderGap
      push_cast at hendpoint ⊢
      linarith
    have hratTop :
        (a.alphaValue j : WithTop ℚ) ≤
          (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            (a.alphaValue s : WithTop ℚ) := by
      exact_mod_cast hrat
    have hsBound := hprefix s
    have hsIndex : s.1 + 1 = j.1 + 2 := by
      rfl
    rw [hsIndex] at hsBound
    have hadd := add_le_add_left hsBound
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ)
    exact hratTop.trans (by simpa [add_comm] using hadd)

/-- The source adjacent candidate itself gives the third shifted lower bound
used by domination. -/
theorem alpha_le_orderGap_add_sourceAdjacent
    (a : GoodBONG q L (N + 1)) (j : Fin N) :
    (a.alphaValue j : WithTop ℚ) ≤
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
        a.adjacentDefect j := by
  rw [a.coe_alphaValue]
  simpa only [GoodBONG.leftDefectCandidate, GoodBONG.orderGap] using
    (a.alpha_le_leftDefectCandidate (i := j) (j := j) le_rfl)

/-- Core inequality of Lemma 8.6(i): every prescribed adjacent pair has
`R_(j+1)-R_j+d(-b_j b_(j+1)) ≥ α_j`. -/
theorem alpha_le_orderGap_add_adjacentDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (hprefix : X.PrefixDefectBounds a)
    (hfull : IsSquare (X.comparisonPrefixUnit a (N + 1)))
    (j : Fin N) :
    (a.alphaValue j : WithTop ℚ) ≤
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ) + X.adjacentDefect j := by
  let shift : ℚ := (a.orderGap j : Int)
  have hprevious := X.alpha_le_orderGap_add_previousComparison a hprefix j
  have hnext := X.alpha_le_orderGap_add_nextComparison a hprefix hfull j
  have hsource := alpha_le_orderGap_add_sourceAdjacent (a := a) j
  have hminimum :
      (a.alphaValue j : WithTop ℚ) ≤
        (shift : WithTop ℚ) +
          min (X.comparisonPrefixDefect a j.1)
            (min (X.comparisonPrefixDefect a (j.1 + 2))
              (a.adjacentDefect j)) :=
    withTop_le_shift_add_min _ shift _ _ hprevious
      (withTop_le_shift_add_min _ shift _ _ hnext hsource)
  have hdomination := X.min_comparison_adjacentDefect_le
    a j.1 (by omega)
  have hadd := add_le_add_left hdomination (shift : WithTop ℚ)
  exact hminimum.trans (by simpa [add_comm, shift] using hadd)

/-- Under equal orders, the core adjacent-defect inequality is exactly the
binary admissibility criterion for the prescribed adjacent ratio. -/
theorem adjacentParameter_isBinaryParameterAdmissible_of_prefixBounds
    [QuadraticDefectLaws K] [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (horders : X.SameOrders a) (hprefix : X.PrefixDefectBounds a)
    (hfull : IsSquare (X.comparisonPrefixUnit a (N + 1)))
    (i : Fin (N + 1)) (hi : i.1 + 1 < N + 1) :
    IsBinaryParameterAdmissible (X.adjacentParameter i hi) := by
  let j : Fin N := ⟨i.1, by omega⟩
  have hiEq : i = j.castSucc := by
    apply Fin.ext
    rfl
  have hnext : (⟨i.1 + 1, hi⟩ : Fin (N + 1)) = j.succ := by
    apply Fin.ext
    rfl
  have hgap : ordUnit K (X.adjacentParameter i hi) = a.orderGap j := by
    calc
      ordUnit K (X.adjacentParameter i hi) =
          X.order ⟨i.1 + 1, hi⟩ - X.order i :=
        X.ordUnit_adjacentParameter i hi
      _ = a.order ⟨i.1 + 1, hi⟩ - a.order i := by
        rw [horders ⟨i.1 + 1, hi⟩, horders i]
      _ = a.order j.succ - a.order j.castSucc :=
        congrArg₂ (· - ·) (congrArg a.order hnext)
          (congrArg a.order hiEq)
      _ = a.orderGap j := rfl
  apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
    (X.adjacentParameter i hi)).2
  constructor
  · rw [hgap]
    have hlower := a.orderGap_ge_neg_two_mul_e j
    omega
  · apply
      Dyadic.hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
    have hlocal := X.alpha_le_orderGap_add_adjacentDefect
      a hprefix hfull j
    have halpha : 0 ≤ a.alphaValue j := (a.alpha_p2 j).1
    have halphaTop :
        (0 : WithTop ℚ) ≤ (a.alphaValue j : WithTop ℚ) := by
      exact_mod_cast halpha
    have hsum := halphaTop.trans hlocal
    have hneg :
        ordUnit K (-X.adjacentParameter i hi) =
          ordUnit K (X.adjacentParameter i hi) := by
      apply WithTop.coe_injective
      simp only [coe_ordUnit, Units.val_neg, ord_neg]
    rw [hneg, hgap, X.defectOrder_neg_adjacentParameter i hi]
    exact hsum

/-- Lemma 8.6(i): the prescribed orthogonal basis occurs as a good BONG of a
lattice.  This is the precise formal counterpart of `N ≅ [b₁,…,bₙ]`. -/
theorem beli2019Lemma86_i
    [QuadraticDefectLaws K] [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, w} K]
    [Beli2006SectionTwoLaws.{u, w} K]
    (a : GoodBONG q L (N + 1)) (X : OrthogonalBasisData r (N + 1))
    (horders : X.SameOrders a) (hprefix : X.PrefixDefectBounds a)
    (hfull : IsSquare (X.comparisonPrefixUnit a (N + 1))) :
    X.HasGoodRealization := by
  apply (X.hasGoodRealization_iff_beli2006Criteria).2
  constructor
  · intro i hi
    rw [horders i, horders ⟨i.1 + 2, hi⟩]
    exact a.good i hi
  · intro i hi
    exact X.adjacentParameter_isBinaryParameterAdmissible_of_prefixBounds
      a horders hprefix hfull i hi

end BONG.OrthogonalBasisData

namespace BONG.GoodBONG

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- A supplied square full comparison product gives the right-endpoint defect
used in Lemma 8.6, without requiring an ambient-isometry interface. -/
theorem comparisonPrefixDefect_full_eq_top_of_isSquare
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 1))) :
    comparisonPrefixDefect a b (N + 1) = ⊤ := by
  unfold comparisonPrefixDefect
  exact defectOrder_eq_top_of_isSquare hfull

/-- The target-adjacent version of the domination identity. -/
theorem min_comparison_adjacentDefect_le_target
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (m : Nat) (hm : m + 1 < N + 1) :
    min (comparisonPrefixDefect a b m)
        (min (comparisonPrefixDefect a b (m + 2))
          (a.adjacentDefect ⟨m, by omega⟩)) ≤
      b.adjacentDefect ⟨m, by omega⟩ := by
  let x := comparisonPrefixUnit a b m
  let y := a.adjacentProduct ⟨m, by omega⟩
  let z := b.adjacentProduct ⟨m, by omega⟩
  have hafter : comparisonPrefixUnit a b (m + 2) = x * y * z := by
    simpa only [x, y, z] using comparisonPrefixUnit_add_two a b m hm
  have hfirst := defectOrder_mul_ge_min (K := K)
    x (comparisonPrefixUnit a b (m + 2))
  have hsecond := defectOrder_mul_ge_min (K := K)
    (x * comparisonPrefixUnit a b (m + 2)) y
  have hbound :
      min (defectOrder (K := K) x)
          (min (defectOrder (K := K)
              (comparisonPrefixUnit a b (m + 2)))
            (defectOrder (K := K) y)) ≤
        defectOrder (K := K)
          ((x * comparisonPrefixUnit a b (m + 2)) * y) := by
    rw [← min_assoc]
    exact (min_le_min hfirst le_rfl).trans hsecond
  have hsquare :
      defectOrder (K := K)
          ((x * comparisonPrefixUnit a b (m + 2)) * y) =
        defectOrder (K := K) z := by
    rw [hafter]
    rw [show (x * (x * y * z)) * y = z * (x * y) ^ 2 by
      simp only [pow_two]
      ac_rfl]
    exact defectOrder_mul_square z (x * y)
  rw [hsquare] at hbound
  simpa only [comparisonPrefixDefect, adjacentDefect, x, y, z] using hbound

/-- Internal-prefix form of the hypothesis in Lemma 8.6. -/
theorem prefixDefectBounds_comparison
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (hprefix : a.PrefixDefectBounds b) (i : Fin N) :
    (a.alphaValue i : WithTop ℚ) ≤
      comparisonPrefixDefect a b (i.1 + 1) := by
  exact hprefix i

/-- The previous comparison prefix supplies the left endpoint bound in the
actual-good-BONG formulation of Lemma 8.6. -/
theorem alpha_le_orderGap_add_previousComparison_target
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (hprefix : a.PrefixDefectBounds b) (j : Fin N) :
    (a.alphaValue j : WithTop ℚ) ≤
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
        comparisonPrefixDefect a b j.1 := by
  by_cases hj0 : j.1 = 0
  · rw [hj0, comparisonPrefixDefect_zero]
    simp
  · let p : Fin N := ⟨j.1 - 1, by omega⟩
    have hpnext : p.1 + 1 < N := by
      dsimp [p]
      omega
    have hendpoint := (a.alpha_p1 p hpnext).2
    have hpAlpha : (⟨p.1 + 1, hpnext⟩ : Fin N) = j := by
      apply Fin.ext
      dsimp [p]
      omega
    rw [hpAlpha] at hendpoint
    unfold alphaRightEndpoint at hendpoint
    have hpOrder : p.succ = j.castSucc := by
      apply Fin.ext
      dsimp [p]
      omega
    rw [hpOrder] at hendpoint
    have hrat :
        a.alphaValue j ≤ (a.orderGap j : ℚ) + a.alphaValue p := by
      unfold orderGap
      push_cast at hendpoint ⊢
      linarith
    have hratTop :
        (a.alphaValue j : WithTop ℚ) ≤
          (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            (a.alphaValue p : WithTop ℚ) := by
      exact_mod_cast hrat
    have hpBound := prefixDefectBounds_comparison a b hprefix p
    have hpIndex : p.1 + 1 = j.1 := by
      dsimp [p]
      omega
    rw [hpIndex] at hpBound
    have hadd := add_le_add_left hpBound
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ)
    exact hratTop.trans (by simpa [add_comm] using hadd)

/-- The next comparison prefix supplies the right endpoint bound. -/
theorem alpha_le_orderGap_add_nextComparison_target
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (hprefix : a.PrefixDefectBounds b)
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 1)))
    (j : Fin N) :
    (a.alphaValue j : WithTop ℚ) ≤
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
        comparisonPrefixDefect a b (j.1 + 2) := by
  by_cases hlast : j.1 + 1 = N
  · have hindex : j.1 + 2 = N + 1 := by omega
    rw [hindex, comparisonPrefixDefect_full_eq_top_of_isSquare a b hfull]
    simp
  · have hjnext : j.1 + 1 < N := by omega
    let s : Fin N := ⟨j.1 + 1, hjnext⟩
    have hendpoint := (a.alpha_p1 j hjnext).1
    have hjAlpha : (⟨j.1 + 1, hjnext⟩ : Fin N) = s := rfl
    rw [hjAlpha] at hendpoint
    unfold alphaLeftEndpoint at hendpoint
    have hsOrder : s.castSucc = j.succ := by
      apply Fin.ext
      rfl
    rw [hsOrder] at hendpoint
    have hrat :
        a.alphaValue j ≤ (a.orderGap j : ℚ) + a.alphaValue s := by
      unfold orderGap
      push_cast at hendpoint ⊢
      linarith
    have hratTop :
        (a.alphaValue j : WithTop ℚ) ≤
          (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            (a.alphaValue s : WithTop ℚ) := by
      exact_mod_cast hrat
    have hsBound := prefixDefectBounds_comparison a b hprefix s
    have hsIndex : s.1 + 1 = j.1 + 2 := rfl
    rw [hsIndex] at hsBound
    have hadd := add_le_add_left hsBound
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ)
    exact hratTop.trans (by simpa [add_comm] using hadd)

/-- The target adjacent defect satisfies the same lower bound as in the
prescribed-basis construction. -/
theorem beli2019Lemma86_adjacent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (hprefix : a.PrefixDefectBounds b)
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 1)))
    (j : Fin N) :
    (a.alphaValue j : WithTop ℚ) ≤
      (((a.orderGap j : Int) : ℚ) : WithTop ℚ) + b.adjacentDefect j := by
  let shift : ℚ := (a.orderGap j : Int)
  have hprevious :=
    alpha_le_orderGap_add_previousComparison_target a b hprefix j
  have hnext :=
    alpha_le_orderGap_add_nextComparison_target a b hprefix hfull j
  have hsource :
      (a.alphaValue j : WithTop ℚ) ≤
        (shift : WithTop ℚ) + a.adjacentDefect j := by
    rw [a.coe_alphaValue]
    simpa only [leftDefectCandidate, orderGap, shift] using
      (a.alpha_le_leftDefectCandidate (i := j) (j := j) le_rfl)
  have hminimum :
      (a.alphaValue j : WithTop ℚ) ≤
        (shift : WithTop ℚ) +
          min (comparisonPrefixDefect a b j.1)
            (min (comparisonPrefixDefect a b (j.1 + 2))
              (a.adjacentDefect j)) :=
    withTop_le_shift_add_min _ shift _ _ hprevious
      (withTop_le_shift_add_min _ shift _ _ hnext hsource)
  have hdomination := min_comparison_adjacentDefect_le_target
    a b j.1 (by omega)
  have hadd := add_le_add_left hdomination (shift : WithTop ℚ)
  exact hminimum.trans (by simpa [add_comm, shift] using hadd)

/-- Every target left-defect candidate lies above the corresponding source
alpha. -/
theorem beli2019Lemma86_leftCandidate
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (b : GoodBONG r M (N + 2))
    (horders : a.SameOrders b) (hprefix : a.PrefixDefectBounds b)
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 2)))
    (i j : Fin (N + 1)) (hji : j ≤ i) :
    (a.alphaValue i : WithTop ℚ) ≤ b.leftDefectCandidate i j := by
  let coefficient : ℚ := (a.order i.succ - a.order j.succ : Int)
  have hendpoint := a.alphaRightEndpoint_antitone hji
  have hfirstRat :
      a.alphaValue i ≤ coefficient + a.alphaValue j := by
    unfold alphaRightEndpoint at hendpoint
    dsimp [coefficient]
    push_cast at hendpoint ⊢
    linarith
  have hfirst :
      (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) + (a.alphaValue j : WithTop ℚ) := by
    exact_mod_cast hfirstRat
  have hlocal := beli2019Lemma86_adjacent a b hprefix hfull j
  have hshift := add_le_add_left hlocal (coefficient : WithTop ℚ)
  have hcombined :
      (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) +
          ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            b.adjacentDefect j) := by
    exact hfirst.trans (by
      calc
        (coefficient : WithTop ℚ) + (a.alphaValue j : WithTop ℚ) =
            (a.alphaValue j : WithTop ℚ) + coefficient := add_comm _ _
        _ ≤ ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
              b.adjacentDefect j) + coefficient := hshift
        _ = (coefficient : WithTop ℚ) +
              ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
                b.adjacentDefect j) := add_comm _ _)
  calc
    (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) +
          ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            b.adjacentDefect j) := hcombined
    _ = b.leftDefectCandidate i j := by
      unfold coefficient orderGap leftDefectCandidate
      rw [← horders i.succ, ← horders j.castSucc]
      rw [← add_assoc]
      congr 1
      norm_cast
      ring

/-- Every target right-defect candidate lies above the corresponding source
alpha. -/
theorem beli2019Lemma86_rightCandidate
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (b : GoodBONG r M (N + 2))
    (horders : a.SameOrders b) (hprefix : a.PrefixDefectBounds b)
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 2)))
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    (a.alphaValue i : WithTop ℚ) ≤ b.rightDefectCandidate i j := by
  let coefficient : ℚ := (a.order j.castSucc - a.order i.castSucc : Int)
  have hendpoint := a.alphaLeftEndpoint_monotone hij
  have hfirstRat :
      a.alphaValue i ≤ coefficient + a.alphaValue j := by
    unfold alphaLeftEndpoint at hendpoint
    dsimp [coefficient]
    push_cast at hendpoint ⊢
    linarith
  have hfirst :
      (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) + (a.alphaValue j : WithTop ℚ) := by
    exact_mod_cast hfirstRat
  have hlocal := beli2019Lemma86_adjacent a b hprefix hfull j
  have hshift := add_le_add_left hlocal (coefficient : WithTop ℚ)
  have hcombined :
      (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) +
          ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            b.adjacentDefect j) := by
    exact hfirst.trans (by
      calc
        (coefficient : WithTop ℚ) + (a.alphaValue j : WithTop ℚ) =
            (a.alphaValue j : WithTop ℚ) + coefficient := add_comm _ _
        _ ≤ ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
              b.adjacentDefect j) + coefficient := hshift
        _ = (coefficient : WithTop ℚ) +
              ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
                b.adjacentDefect j) := add_comm _ _)
  calc
    (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) +
          ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            b.adjacentDefect j) := hcombined
    _ = b.rightDefectCandidate i j := by
      unfold coefficient orderGap rightDefectCandidate
      rw [← horders j.succ, ← horders i.castSucc]
      rw [← add_assoc]
      congr 1
      norm_cast
      ring

/-- Lemma 8.6(ii): under the prefix-defect hypotheses, every source alpha is
bounded above by the corresponding alpha of the prescribed good BONG. -/
theorem beli2019Lemma86_ii
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (b : GoodBONG r M (N + 2))
    (horders : a.SameOrders b) (hprefix : a.PrefixDefectBounds b)
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 2)))
    (i : Fin (N + 1)) :
    a.alphaValue i ≤ b.alphaValue i := by
  have htop :
      (a.alphaValue i : WithTop ℚ) ≤ (b.alphaValue i : WithTop ℚ) := by
    rw [b.coe_alphaValue]
    unfold alpha
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hy with rfl | (⟨j, ⟨hji, rfl⟩⟩ | ⟨j, ⟨hij, rfl⟩⟩)
    · unfold halfGapCandidate
      rw [← horders i.succ, ← horders i.castSucc]
      rw [a.coe_alphaValue]
      exact a.alpha_le_halfGapCandidate i
    · exact beli2019Lemma86_leftCandidate a b horders hprefix hfull i j hji
    · exact beli2019Lemma86_rightCandidate a b horders hprefix hfull i j hij
  exact_mod_cast htop

/-- At an index of the set `C` from Lemma 8.5, the central adjacent defect is
finite.  This follows because the central candidate is the finite alpha
value. -/
theorem adjacentDefect_ne_top_of_beli2019Lemma85C
    (a : GoodBONG q L (N + 2)) (j : Fin (N + 1))
    (hC : a.Beli2019Lemma85C j) :
    a.adjacentDefect j ≠ ⊤ := by
  intro htop
  apply (WithTop.coe_ne_top : (a.alphaValue j : WithTop ℚ) ≠ ⊤)
  calc
    (a.alphaValue j : WithTop ℚ) = a.leftDefectCandidate j j := hC.2.2
    _ = ⊤ := by simp [leftDefectCandidate, htop]

/-- Property A and the strict endpoint condition defining `C` place the
central adjacent defect strictly below the preceding comparison-prefix
defect.  At the left boundary the latter is infinite. -/
theorem adjacentDefect_lt_previousComparison_of_beli2019Lemma85C
    (a : GoodBONG q L (N + 2)) (b : GoodBONG r M (N + 2))
    (hproperty : a.toBONG.HasPropertyA)
    (hprefix : a.PrefixDefectBounds b)
    (j : Fin (N + 1)) (hC : a.Beli2019Lemma85C j) :
    a.adjacentDefect j < comparisonPrefixDefect a b j.1 := by
  by_cases hj0 : j.1 = 0
  · rw [hj0, comparisonPrefixDefect_zero]
    exact lt_top_iff_ne_top.mpr
      (adjacentDefect_ne_top_of_beli2019Lemma85C a j hC)
  · let p : Fin (N + 1) := ⟨j.1 - 1, by omega⟩
    have hpTwo : p.1 + 2 < N + 2 := by
      dsimp [p]
      omega
    have horder := hproperty p.castSucc hpTwo
    have hpMiddle : p.succ = j.castSucc := by
      apply Fin.ext
      dsimp [p]
      omega
    have hpLast :
        (⟨p.castSucc.1 + 2, hpTwo⟩ : Fin (N + 2)) = j.succ := by
      apply Fin.ext
      dsimp [p]
      omega
    rw [hpLast] at horder
    have hsum : a.adjacentOrderSum p < a.adjacentOrderSum j := by
      unfold adjacentOrderSum
      rw [hpMiddle]
      calc
        a.order p.castSucc + a.order j.castSucc =
            a.order j.castSucc + a.order p.castSucc := add_comm _ _
        _ < a.order j.castSucc + a.order j.succ :=
          add_lt_add_right horder _
    have hendpoint := hC.2.1.2 p hsum
    unfold alphaRightEndpoint at hendpoint
    rw [hpMiddle] at hendpoint
    have hrat :
        a.alphaValue j < (a.orderGap j : ℚ) + a.alphaValue p := by
      unfold orderGap
      push_cast at hendpoint ⊢
      linarith
    have hratTop :
        (a.alphaValue j : WithTop ℚ) <
          (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            (a.alphaValue p : WithTop ℚ) := by
      exact_mod_cast hrat
    have hcentral :
        (a.alphaValue j : WithTop ℚ) =
          (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            a.adjacentDefect j := by
      simpa only [leftDefectCandidate, orderGap] using hC.2.2
    rw [hcentral] at hratTop
    have hyAlpha :
        a.adjacentDefect j < (a.alphaValue p : WithTop ℚ) := by
      by_contra hnot
      have hadd := add_le_add_left (le_of_not_gt hnot)
        (((a.orderGap j : Int) : ℚ) : WithTop ℚ)
      exact (not_lt_of_ge (by simpa only [add_comm] using hadd)) hratTop
    have hpBound := prefixDefectBounds_comparison a b hprefix p
    have hpIndex : p.1 + 1 = j.1 := by
      dsimp [p]
      omega
    rw [hpIndex] at hpBound
    exact hyAlpha.trans_le hpBound

/-- Symmetrically, a central adjacent defect at an index of `C` is strictly
below the following comparison-prefix defect.  At the right boundary the
full comparison product is a square. -/
theorem adjacentDefect_lt_nextComparison_of_beli2019Lemma85C
    (a : GoodBONG q L (N + 2)) (b : GoodBONG r M (N + 2))
    (hproperty : a.toBONG.HasPropertyA)
    (hprefix : a.PrefixDefectBounds b)
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 2)))
    (j : Fin (N + 1)) (hC : a.Beli2019Lemma85C j) :
    a.adjacentDefect j < comparisonPrefixDefect a b (j.1 + 2) := by
  by_cases hlast : j.1 + 1 = N + 1
  · have hindex : j.1 + 2 = N + 2 := by omega
    rw [hindex, comparisonPrefixDefect_full_eq_top_of_isSquare a b hfull]
    exact lt_top_iff_ne_top.mpr
      (adjacentDefect_ne_top_of_beli2019Lemma85C a j hC)
  · have hjnext : j.1 + 1 < N + 1 := by omega
    let s : Fin (N + 1) := ⟨j.1 + 1, hjnext⟩
    have hjTwo : j.1 + 2 < N + 2 := by omega
    have horder := hproperty j.castSucc hjTwo
    have hjLast :
        (⟨j.castSucc.1 + 2, hjTwo⟩ : Fin (N + 2)) = s.succ := by
      apply Fin.ext
      rfl
    rw [hjLast] at horder
    have hjMiddle : s.castSucc = j.succ := by
      apply Fin.ext
      rfl
    have hsum : a.adjacentOrderSum j < a.adjacentOrderSum s := by
      unfold adjacentOrderSum
      rw [hjMiddle]
      calc
        a.order j.castSucc + a.order j.succ =
            a.order j.succ + a.order j.castSucc := add_comm _ _
        _ < a.order j.succ + a.order s.succ :=
          add_lt_add_right horder _
    have hendpoint := hC.2.1.1 s hsum
    unfold alphaLeftEndpoint at hendpoint
    rw [hjMiddle] at hendpoint
    have hrat :
        a.alphaValue j < (a.orderGap j : ℚ) + a.alphaValue s := by
      unfold orderGap
      push_cast at hendpoint ⊢
      linarith
    have hratTop :
        (a.alphaValue j : WithTop ℚ) <
          (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            (a.alphaValue s : WithTop ℚ) := by
      exact_mod_cast hrat
    have hcentral :
        (a.alphaValue j : WithTop ℚ) =
          (((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            a.adjacentDefect j := by
      simpa only [leftDefectCandidate, orderGap] using hC.2.2
    rw [hcentral] at hratTop
    have hyAlpha :
        a.adjacentDefect j < (a.alphaValue s : WithTop ℚ) := by
      by_contra hnot
      have hadd := add_le_add_left (le_of_not_gt hnot)
        (((a.orderGap j : Int) : ℚ) : WithTop ℚ)
      exact (not_lt_of_ge (by simpa only [add_comm] using hadd)) hratTop
    have hsBound := prefixDefectBounds_comparison a b hprefix s
    have hsIndex : s.1 + 1 = j.1 + 2 := rfl
    rw [hsIndex] at hsBound
    exact hyAlpha.trans_le hsBound

/-- At every index in the set `C`, the source and target adjacent quadratic
defects agree exactly.  The source defect is strictly smaller than both
neighboring comparison-prefix defects, so it dominates their product; the
remaining factor is the target adjacent product up to a square. -/
theorem adjacentDefect_eq_target_of_beli2019Lemma85C
    (a : GoodBONG q L (N + 2)) (b : GoodBONG r M (N + 2))
    (hproperty : a.toBONG.HasPropertyA)
    (hprefix : a.PrefixDefectBounds b)
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 2)))
    (j : Fin (N + 1)) (hC : a.Beli2019Lemma85C j) :
    a.adjacentDefect j = b.adjacentDefect j := by
  let x := comparisonPrefixUnit a b j.1
  let y := a.adjacentProduct j
  let z := b.adjacentProduct j
  have hafter : comparisonPrefixUnit a b (j.1 + 2) = x * y * z := by
    simpa only [x, y, z] using
      comparisonPrefixUnit_add_two a b j.1 (by omega)
  have hyPrevious :
      defectOrder (K := K) y < defectOrder (K := K) x := by
    simpa only [comparisonPrefixDefect, adjacentDefect, x, y] using
      adjacentDefect_lt_previousComparison_of_beli2019Lemma85C
        a b hproperty hprefix j hC
  have hyNext :
      defectOrder (K := K) y <
        defectOrder (K := K) (comparisonPrefixUnit a b (j.1 + 2)) := by
    simpa only [comparisonPrefixDefect, adjacentDefect, y] using
      adjacentDefect_lt_nextComparison_of_beli2019Lemma85C
        a b hproperty hprefix hfull j hC
  have hproduct := defectOrder_mul_ge_min (K := K)
    x (comparisonPrefixUnit a b (j.1 + 2))
  have hyProduct :
      defectOrder (K := K) y <
        defectOrder (K := K)
          (x * comparisonPrefixUnit a b (j.1 + 2)) :=
    (lt_min hyPrevious hyNext).trans_le hproduct
  have hsharp := defectOrder_mul_eq_right_of_lt_left (K := K)
    (a := x * comparisonPrefixUnit a b (j.1 + 2)) (b := y) hyProduct
  have htarget : defectOrder (K := K) z = defectOrder (K := K) y := by
    calc
      defectOrder (K := K) z =
          defectOrder (K := K) (z * (x * y) ^ 2) :=
        (defectOrder_mul_square z (x * y)).symm
      _ = defectOrder (K := K)
          ((x * comparisonPrefixUnit a b (j.1 + 2)) * y) := by
        apply congrArg (defectOrder (K := K))
        rw [hafter]
        simp only [pow_two]
        ac_rfl
      _ = defectOrder (K := K) y := hsharp
  simpa only [adjacentDefect, y, z] using htarget.symm

/-- Lemma 8.6(iii): if the source BONG has property A, then all inequalities
from part (ii) are equalities. -/
theorem beli2019Lemma86_iii
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (b : GoodBONG r M (N + 2))
    (hproperty : a.toBONG.HasPropertyA)
    (horders : a.SameOrders b) (hprefix : a.PrefixDefectBounds b)
    (hfull : IsSquare (comparisonPrefixUnit a b (N + 2))) :
    a.SameAlphas b := by
  intro i
  have hlower : a.alphaValue i ≤ b.alphaValue i :=
    beli2019Lemma86_ii a b horders hprefix hfull i
  by_cases hhalf : a.AttainsHalfGap i
  · have hhalfValues : b.halfGapValue i = a.halfGapValue i := by
      unfold halfGapValue orderGap
      rw [← horders i.succ, ← horders i.castSucc]
    have hupper : b.alphaValue i ≤ a.alphaValue i := by
      unfold AttainsHalfGap at hhalf
      calc
        b.alphaValue i ≤ b.halfGapValue i :=
          b.alphaValue_le_halfGapValue i
        _ = a.halfGapValue i := hhalfValues
        _ = a.alphaValue i := hhalf.symm
    exact le_antisymm hlower hupper
  · have hA : a.Beli2019Lemma85A i :=
      (a.beli2019Lemma85A_iff_not_attainsHalfGap i).2 hhalf
    rcases a.beli2019Lemma85 i hA with
      ⟨j, hC, hleft | hright, _⟩
    · rcases hleft with ⟨hji, _, hvalue⟩
      have hdefect := adjacentDefect_eq_target_of_beli2019Lemma85C
        a b hproperty hprefix hfull j hC
      have hcandidates :
          b.leftDefectCandidate i j = a.leftDefectCandidate i j := by
        unfold leftDefectCandidate
        rw [← horders i.succ, ← horders j.castSucc, ← hdefect]
      have hbCandidate :
          (b.alphaValue i : WithTop ℚ) ≤ b.leftDefectCandidate i j := by
        rw [b.coe_alphaValue]
        exact b.alpha_le_leftDefectCandidate hji
      have hupperTop :
          (b.alphaValue i : WithTop ℚ) ≤
            (a.alphaValue i : WithTop ℚ) := by
        calc
          (b.alphaValue i : WithTop ℚ) ≤ b.leftDefectCandidate i j :=
            hbCandidate
          _ = a.leftDefectCandidate i j := hcandidates
          _ = (a.alphaValue i : WithTop ℚ) := hvalue.symm
      have hupper : b.alphaValue i ≤ a.alphaValue i := by
        exact_mod_cast hupperTop
      exact le_antisymm hlower hupper
    · rcases hright with ⟨hij, _, hvalue⟩
      have hdefect := adjacentDefect_eq_target_of_beli2019Lemma85C
        a b hproperty hprefix hfull j hC
      have hcandidates :
          b.rightDefectCandidate i j = a.rightDefectCandidate i j := by
        unfold rightDefectCandidate
        rw [← horders j.succ, ← horders i.castSucc, ← hdefect]
      have hbCandidate :
          (b.alphaValue i : WithTop ℚ) ≤ b.rightDefectCandidate i j := by
        rw [b.coe_alphaValue]
        exact b.alpha_le_rightDefectCandidate hij
      have hupperTop :
          (b.alphaValue i : WithTop ℚ) ≤
            (a.alphaValue i : WithTop ℚ) := by
        calc
          (b.alphaValue i : WithTop ℚ) ≤ b.rightDefectCandidate i j :=
            hbCandidate
          _ = a.rightDefectCandidate i j := hcandidates
          _ = (a.alphaValue i : WithTop ℚ) := hvalue.symm
      have hupper : b.alphaValue i ≤ a.alphaValue i := by
        exact_mod_cast hupperTop
      exact le_antisymm hlower hupper

end BONG.GoodBONG

end Bong
