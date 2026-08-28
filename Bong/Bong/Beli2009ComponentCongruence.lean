/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009FundamentalWeightTransport

/-!
# Prefix defects and component-generator congruence

This file isolates the elementary square-class calculation used in Beli
(2009), Lemma 3.3.  The product of the two comparison prefixes adjacent to a
coordinate differs from the product of the two coordinate values by a square.
Consequently, lower bounds for the two adjacent prefix defects imply the
component congruence at that coordinate.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- One-step form of the comparison-prefix recurrence. -/
theorem comparisonPrefixUnit_succ
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : Nat) (hi : i < n + 1) :
    comparisonPrefixUnit a b (i + 1) =
      comparisonPrefixUnit a b i *
        (a.valueUnit ⟨i, hi⟩ * b.valueUnit ⟨i, hi⟩) := by
  unfold comparisonPrefixUnit GoodBONG.prefixProduct GoodBONG.valueUnit
  rw [a.toBONG.prefixProduct_succ i hi,
    b.toBONG.prefixProduct_succ i hi]
  apply Units.ext
  simp only [Units.val_mul]
  ac_rfl

/-- The coordinate product and the product of its two adjacent comparison
prefixes have the same quadratic defect. -/
theorem defectOrder_valueProduct_eq_adjacentPrefixes
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : Nat) (hi : i < n + 1) :
    defectOrder (K := K) (a.valueUnit ⟨i, hi⟩ * b.valueUnit ⟨i, hi⟩) =
      defectOrder (K := K)
        (comparisonPrefixUnit a b i * comparisonPrefixUnit a b (i + 1)) := by
  rw [comparisonPrefixUnit_succ a b i hi]
  rw [show comparisonPrefixUnit a b i *
        (comparisonPrefixUnit a b i *
          (a.valueUnit ⟨i, hi⟩ * b.valueUnit ⟨i, hi⟩)) =
      (a.valueUnit ⟨i, hi⟩ * b.valueUnit ⟨i, hi⟩) *
        comparisonPrefixUnit a b i ^ 2 by
      simp only [pow_two]
      ac_rfl]
  exact (defectOrder_mul_square
    (a.valueUnit ⟨i, hi⟩ * b.valueUnit ⟨i, hi⟩)
      (comparisonPrefixUnit a b i)).symm

/-- A common lower bound for the two adjacent comparison-prefix defects is a
lower bound for the relative defect of the coordinate values. -/
theorem le_defectOrder_valueProduct_of_adjacentPrefixes
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : Nat) (hi : i < n + 1) (d : WithTop ℚ)
    (hleft : d ≤ comparisonPrefixDefect a b i)
    (hright : d ≤ comparisonPrefixDefect a b (i + 1)) :
    d ≤ defectOrder (K := K)
      (a.valueUnit ⟨i, hi⟩ * b.valueUnit ⟨i, hi⟩) := by
  have hmul := defectOrder_mul_ge_min (K := K)
    (comparisonPrefixUnit a b i) (comparisonPrefixUnit a b (i + 1))
  rw [← a.defectOrder_valueProduct_eq_adjacentPrefixes b i hi]
    at hmul
  exact (le_min hleft hright).trans hmul

/-- Integral-power-ideal form of the preceding defect calculation. -/
theorem unitsCongruentModulo_valueUnits_of_adjacentPrefixes
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : Nat) (hi : i < n + 1) (d : Int) (hd : 0 ≤ d)
    (horder : a.order ⟨i, hi⟩ = b.order ⟨i, hi⟩)
    (hleft : ((((d : Int) : ℚ) : WithTop ℚ) ≤
      comparisonPrefixDefect a b i))
    (hright : ((((d : Int) : ℚ) : WithTop ℚ) ≤
      comparisonPrefixDefect a b (i + 1))) :
    UnitsCongruentModulo (a.valueUnit ⟨i, hi⟩) (b.valueUnit ⟨i, hi⟩)
      (Lattice.powerIdeal (K := K) d) := by
  apply (unitsCongruentModulo_powerIdeal_iff_intCast_le_defectOrder_mul
    (a.valueUnit ⟨i, hi⟩) (b.valueUnit ⟨i, hi⟩) d hd (by
      simpa only [GoodBONG.order, GoodBONG.valueUnit,
        BONG.order_eq_ordUnit] using horder)).2
  exact a.le_defectOrder_valueProduct_of_adjacentPrefixes b i hi _ hleft hright

end BONG.GoodBONG

namespace BONG.StrictJordanAdaptedAlignment

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}

/-- The retained source fundamental generator is literally the BONG value at
the first coordinate of the component. -/
theorem sourceFundamentalGenerator_eq_valueUnit
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.sourceFundamentalGenerator k =
      a.valueUnit ⟨S.componentStart k, by
        have hstart := S.componentStart_lt_componentStop k
        have hstop := S.componentStop_le k
        omega⟩ := by
  exact S.sourceEndpointFirstValue_eq_componentStart k

/-- Target analogue of `sourceFundamentalGenerator_eq_valueUnit`. -/
theorem targetFundamentalGenerator_eq_valueUnit
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.targetFundamentalGenerator k =
      b.valueUnit ⟨S.componentStart k, by
        have hstart := S.componentStart_lt_componentStop k
        have hstop := S.componentStop_le k
        omega⟩ := by
  change S.symm.sourceFundamentalGenerator k = _
  rw [S.symm.sourceFundamentalGenerator_eq_valueUnit]
  simp only [symm_componentStart]

/-- The order of the retained source generator is the BONG order at the
component start. -/
theorem sourceFundamentalGenerator_order_eq_componentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    ordUnit K (S.sourceFundamentalGenerator k) =
      a.order ⟨S.componentStart k, by
        have hstart := S.componentStart_lt_componentStop k
        have hstop := S.componentStop_le k
        omega⟩ := by
  rw [S.sourceFundamentalGenerator_eq_valueUnit]
  exact (a.toBONG.order_eq_ordUnit _).symm

/-- The exponent of Beli's normalized component weight `a_k⁻¹ w_k`. -/
noncomputable def sourceNormalizedFundamentalWeightOrder
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) : Int :=
  S.sourceJordan.fundamentalWeightOrder k -
    ordUnit K (S.sourceFundamentalGenerator k)

/-- A fundamental weight is contained in the norm-generator ideal, so its
normalized exponent is nonnegative. -/
theorem sourceNormalizedFundamentalWeightOrder_nonnegative
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    0 ≤ S.sourceNormalizedFundamentalWeightOrder k := by
  have hle : Lattice.weightIdeal q (S.sourceJordan.fundamentalLattice k) ≤
      Lattice.principalIdeal (K := K) (S.sourceFundamentalGenerator k : K) :=
    Lattice.weightIdeal_le_principalIdeal
      (S.sourceFundamentalGenerator k) (S.sourceFundamentalGenerator_spec k)
  rw [Lattice.weightIdeal_eq_powerIdeal,
    Lattice.principalIdeal_eq_powerIdeal,
    Lattice.powerIdeal_le_iff] at hle
  change ordUnit K (S.sourceFundamentalGenerator k) ≤
    S.sourceJordan.fundamentalWeightOrder k at hle
  unfold sourceNormalizedFundamentalWeightOrder
  omega

/-- On a non-unary Jordan component, the normalized fundamental-weight order
is exactly the alpha at the first coordinate of that component.  This is
Beli's Corollary 2.17(i), now specialized to the concrete aligned component. -/
theorem sourceNormalizedFundamentalWeightOrder_eq_alpha_of_rank_two
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount)
    (hrank : 2 ≤ S.sourceJordan.componentRank k) :
    (S.sourceNormalizedFundamentalWeightOrder k : ℚ) =
      a.alphaValue ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ := by
  have hstartAlpha : S.componentStart k < n + 1 := by
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    change 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
    omega
  have hnext : S.componentStart k + 1 < S.componentStop k := by
    unfold componentStop
    change 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
    omega
  have hinternal :=
    (S.source_component_internal k (S.componentStart k) le_rfl hnext).1
  unfold sourceNormalizedFundamentalWeightOrder
  rw [S.sourceFundamentalGenerator_order_eq_componentStart]
  push_cast
  dsimp only [sourceInternalAlphaData,
    GoodBONG.InternalJordanAlphaData.leftIndex,
    GoodBONG.InternalJordanAlphaData.alphaIndex,
    sourceFundamentalWeight] at hinternal
  change
    (a.order ⟨S.componentStart k, by omega⟩ : ℚ) +
        a.alphaValue ⟨S.componentStart k, hstartAlpha⟩ =
      (S.sourceJordan.fundamentalWeightOrder k : ℚ) at hinternal
  linarith

/-- Once the preceding boundary prefix is controlled, the normalized-weight
congruence of a non-unary component is equivalent to the defect bound at its
first coordinate.  This is the local non-unary step in Beli's Lemma 3.3. -/
theorem componentGenerator_congruent_iff_headPrefixDefect_of_rank_two
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b)
    (k : Fin S.componentCount)
    (hrank : 2 ≤ S.sourceJordan.componentRank k)
    (hleft :
      (a.alphaValue ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStart k)) :
    GoodBONG.UnitsCongruentModulo
        (S.sourceFundamentalGenerator k) (S.targetFundamentalGenerator k)
        (Lattice.powerIdeal (K := K)
          (S.sourceNormalizedFundamentalWeightOrder k)) ↔
      (a.alphaValue ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStart k + 1) := by
  let start := S.componentStart k
  let d := S.sourceNormalizedFundamentalWeightOrder k
  have hstartValue : start < n + 2 := by
    dsimp only [start]
    exact (S.componentStart_lt_componentStop k).trans_le (S.componentStop_le k)
  have hstartAlpha : start < n + 1 := by
    dsimp only [start]
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    change 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
    omega
  have hdNonnegative : 0 ≤ d :=
    S.sourceNormalizedFundamentalWeightOrder_nonnegative k
  have hdEq : (((d : Int) : ℚ) : WithTop ℚ) =
      (a.alphaValue ⟨start, hstartAlpha⟩ : WithTop ℚ) := by
    apply congrArg (fun z : ℚ ↦ (z : WithTop ℚ))
    exact S.sourceNormalizedFundamentalWeightOrder_eq_alpha_of_rank_two k hrank
  have hvalueOrder :
      ordUnit K (a.valueUnit ⟨start, hstartValue⟩) =
        ordUnit K (b.valueUnit ⟨start, hstartValue⟩) := by
    simpa only [GoodBONG.order, GoodBONG.valueUnit,
      BONG.order_eq_ordUnit] using horders ⟨start, hstartValue⟩
  have hleftD : (((d : Int) : ℚ) : WithTop ℚ) ≤
      GoodBONG.comparisonPrefixDefect a b start := by
    rw [hdEq]
    simpa only [start] using hleft
  constructor
  · intro hcomponent
    have hvalue : (((d : Int) : ℚ) : WithTop ℚ) ≤
        GoodBONG.defectOrder (K := K)
          (a.valueUnit ⟨start, hstartValue⟩ *
            b.valueUnit ⟨start, hstartValue⟩) := by
      apply (GoodBONG.unitsCongruentModulo_powerIdeal_iff_intCast_le_defectOrder_mul
        (a.valueUnit ⟨start, hstartValue⟩)
        (b.valueUnit ⟨start, hstartValue⟩) d hdNonnegative hvalueOrder).1
      rw [← S.sourceFundamentalGenerator_eq_valueUnit k,
          ← S.targetFundamentalGenerator_eq_valueUnit k]
      exact hcomponent
    have hmul := GoodBONG.defectOrder_mul_ge_min (K := K)
      (GoodBONG.comparisonPrefixUnit a b start)
      (a.valueUnit ⟨start, hstartValue⟩ *
        b.valueUnit ⟨start, hstartValue⟩)
    rw [← GoodBONG.comparisonPrefixUnit_succ a b start hstartValue] at hmul
    rw [← hdEq]
    exact (le_min hleftD hvalue).trans hmul
  · intro hright
    have hraw := a.unitsCongruentModulo_valueUnits_of_adjacentPrefixes
      b start hstartValue d hdNonnegative
      (horders ⟨start, hstartValue⟩)
      (by rw [hdEq]; exact hleft)
      (by rw [hdEq]; exact hright)
    rw [S.sourceFundamentalGenerator_eq_valueUnit,
      S.targetFundamentalGenerator_eq_valueUnit]
    simpa only [start, d] using hraw

/-- Two entries at distance two inside one concrete Jordan component have
the same order. -/
theorem source_order_add_two_eq
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (j : Nat)
    (hstart : S.componentStart k ≤ j)
    (hfit : j + 2 < S.componentStop k) :
    a.order ⟨j, by
      exact (by omega : j < S.componentStop k).trans_le (S.componentStop_le k)⟩ =
      a.order ⟨j + 2, hfit.trans_le (S.componentStop_le k)⟩ := by
  let C := S.sourceComponentCoordinates k
  have hjStop : j < C.stop := by
    change j < S.componentStop k
    omega
  have hj2Stop : j + 2 < C.stop := by
    change j + 2 < S.componentStop k
    exact hfit
  have hj := C.order_eq j hstart hjStop
  have hj2 := C.order_eq (j + 2) (by
      change S.componentStart k ≤ j + 2
      omega) hj2Stop
  have hparity : (j + 2 - C.start) % 2 = (j - C.start) % 2 := by
    dsimp only [C, sourceComponentCoordinates]
    omega
  rw [hj, hj2, hparity]

/-- Beli's Lemma 3.2 propagates a head prefix condition through every
interior alpha index of a non-unary concrete Jordan component. -/
theorem prefixDefectBound_inside_sourceComponent
    [Beli2006AlphaLaws.{u, v} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b) (halphas : a.SameAlphas b)
    (k : Fin S.componentCount)
    (hrank : 2 ≤ S.sourceJordan.componentRank k)
    (hleft : S.componentStart k = 0 ∨ ∃ hs : 0 < S.componentStart k,
      (a.alphaValue ⟨S.componentStart k - 1, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStart k))
    (hhead :
      (a.alphaValue ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStart k + 1)) :
    ∀ (j : Nat) (hjAlpha : j < n + 1),
      S.componentStart k ≤ j → j + 1 < S.componentStop k →
      (a.alphaValue ⟨j, hjAlpha⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (j + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjAlpha hjStart hjInternal
      by_cases hjHead : j = S.componentStart k
      · subst j
        exact hhead
      by_cases hjSecond : j = S.componentStart k + 1
      · have hfit : S.componentStart k + 2 < n + 2 := by
          exact (by omega : S.componentStart k + 2 < S.componentStop k).trans_le
            (S.componentStop_le k)
        have houter := S.source_order_add_two_eq k (S.componentStart k)
          le_rfl (by omega)
        have hprop := GoodBONG.beli2009Lemma32_forward a b horders halphas
          (S.componentStart k) hfit houter hleft
        simpa only [hjSecond] using hprop
      · have hjTwo : S.componentStart k + 2 ≤ j := by omega
        have hprevAlpha : j - 2 < n + 1 := by omega
        have hprev := ih (j - 2) (by omega) hprevAlpha (by omega) (by omega)
        have hfit : (j - 1) + 2 < n + 2 := by omega
        have houter := S.source_order_add_two_eq k (j - 1)
          (by omega) (by omega)
        have hprev' :
            (a.alphaValue ⟨(j - 1) - 1, by omega⟩ : WithTop ℚ) ≤
              GoodBONG.comparisonPrefixDefect a b (j - 1) := by
          have hindex : (⟨(j - 1) - 1, by omega⟩ : Fin (n + 1)) =
              ⟨j - 2, hprevAlpha⟩ := by
            apply Fin.ext
            change (j - 1) - 1 = j - 2
            omega
          rw [hindex, show j - 1 = (j - 2) + 1 by omega]
          exact hprev
        have hprop := GoodBONG.beli2009Lemma32_forward a b horders halphas
          (j - 1) hfit houter (Or.inr ⟨by omega, hprev'⟩)
        simpa only [show j - 1 + 1 = j by omega,
          show j - 1 + 2 = j + 1 by omega] using hprop

/-- Boundary seeds, left-end seeds, and the heads of non-unary components
cover every prefix-defect condition.  All intermediate indices are supplied
by `prefixDefectBound_inside_sourceComponent`. -/
theorem prefixDefectBounds_of_componentSeeds
    [Beli2006AlphaLaws.{u, v} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b) (halphas : a.SameAlphas b)
    (hboundary : ∀ (k : Fin S.componentCount)
      (hstop : S.componentStop k < n + 2),
      (a.alphaValue ⟨S.componentStop k - 1, by omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStop k))
    (hleft : ∀ k : Fin S.componentCount,
      S.componentStart k = 0 ∨ ∃ hs : 0 < S.componentStart k,
        (a.alphaValue ⟨S.componentStart k - 1, by
          have hstop := S.componentStop_le k
          have hstart := S.componentStart_lt_componentStop k
          omega⟩ : WithTop ℚ) ≤
          GoodBONG.comparisonPrefixDefect a b (S.componentStart k))
    (hhead : ∀ (k : Fin S.componentCount)
      (hrank : 2 ≤ S.sourceJordan.componentRank k),
      (a.alphaValue ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStart k + 1)) :
    a.PrefixDefectBounds b := by
  intro i
  let k : Fin S.componentCount := (S.sourceProfile.indexEquiv i.castSucc).1
  have hiStartRaw := S.sourceProfile.componentStart_le_index_val i.castSucc
  have hiStart : S.componentStart k ≤ i.val := by
    simpa only [k, componentStart, sourceJordan, Fin.val_castSucc] using hiStartRaw
  have hiStopRaw := S.sourceProfile.index_val_lt_componentEnd i.castSucc
  have hiStop : i.val < S.componentStop k := by
    simpa only [k, componentStop, componentStart, sourceJordan,
      Fin.val_castSucc] using hiStopRaw
  have hresult :
      (a.alphaValue i : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (i.val + 1) := by
    by_cases hiInternal : i.val + 1 < S.componentStop k
    · have hrank : 2 ≤ S.sourceJordan.componentRank k := by
        have hcomponentStop := S.componentStop_le k
        unfold componentStop at hiInternal
        change S.componentStart k +
          S.sourceJordan.toOrthogonalDecomposition.componentRank k >
            i.val + 1 at hiInternal
        change 2 ≤ S.sourceJordan.toOrthogonalDecomposition.componentRank k
        omega
      exact S.prefixDefectBound_inside_sourceComponent horders halphas k hrank
        (hleft k) (hhead k hrank) i.val i.isLt hiStart hiInternal
    · have hiBoundary : i.val + 1 = S.componentStop k := by omega
      have hstop : S.componentStop k < n + 2 := by omega
      have hb := hboundary k hstop
      have hindex : (⟨S.componentStop k - 1, by omega⟩ : Fin (n + 1)) = i := by
        apply Fin.ext
        change S.componentStop k - 1 = i.val
        omega
      rw [hindex, ← hiBoundary] at hb
      exact hb
  unfold GoodBONG.comparisonPrefixDefect GoodBONG.comparisonPrefixUnit at hresult
  simpa only [GoodBONG.comparisonPrefixProduct] using hresult

/-- At the head of a non-unary noninitial Jordan component, the preceding
alpha dominates the head alpha.  This is the endpoint-monotonicity step used
in the non-unary paragraph of Lemma 3.3. -/
theorem source_alpha_componentStart_le_predecessor_of_rank_two
    [Beli2006AlphaLaws.{u, v} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (hrank : 2 ≤ S.sourceJordan.componentRank k) :
    a.alphaValue ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ ≤
      a.alphaValue ⟨S.componentStart k - 1, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        have hstart := S.componentStart_lt_componentStop k
        have hpositive : 0 < S.componentStart k := by
          unfold componentStart
          let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
          have hp : previous ∈ Finset.Iio k := by
            simp only [Finset.mem_Iio]
            change k.val - 1 < k.val
            omega
          exact (S.sourceJordan.component_finrank_pos previous).trans_le
            (Finset.single_le_sum
              (s := Finset.Iio k)
              (f := fun z ↦ S.sourceJordan.componentRank z)
              (fun _ _ ↦ Nat.zero_le _) hp)
        have hrankPos := S.sourceJordan.component_finrank_pos k
        change 0 <
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrankPos
        omega⟩ := by
  have hstartPositive : 0 < S.componentStart k := by
    unfold componentStart
    let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hp : previous ∈ Finset.Iio k := by
      simp only [Finset.mem_Iio]
      change k.val - 1 < k.val
      omega
    exact (S.sourceJordan.component_finrank_pos previous).trans_le
      (Finset.single_le_sum
        (s := Finset.Iio k)
        (f := fun z ↦ S.sourceJordan.componentRank z)
        (fun _ _ ↦ Nat.zero_le _) hp)
  let previous : Fin (n + 1) := ⟨S.componentStart k - 1, by
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    have hrankPos := S.sourceJordan.component_finrank_pos k
    change 0 <
      S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrankPos
    omega⟩
  let current : Fin (n + 1) := ⟨S.componentStart k, by
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    change 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
    omega⟩
  have hmono := a.alphaRightEndpoint_antitone (show previous ≤ current by
      change S.componentStart k - 1 ≤ S.componentStart k
      omega)
  unfold GoodBONG.alphaRightEndpoint at hmono
  have hdescending := S.source_component_head_descending k hrank
  have hdescendingQ :
      (a.order ⟨S.componentStart k + 1, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : ℚ) ≤
      (a.order ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : ℚ) := by
    exact_mod_cast hdescending
  have hpreviousSucc : previous.succ =
      ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ := by
    apply Fin.ext
    dsimp only [previous]
    change S.componentStart k - 1 + 1 = S.componentStart k
    omega
  have hcurrentSucc : current.succ =
      ⟨S.componentStart k + 1, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ := by
    apply Fin.ext
    rfl
  have hdescendingAtEndpoints :
      (a.order current.succ : ℚ) ≤ (a.order previous.succ : ℚ) := by
    rw [hpreviousSucc, hcurrentSucc]
    exact hdescendingQ
  have hresult : a.alphaValue current ≤ a.alphaValue previous := by
    linarith
  simpa only [current, previous] using hresult

/-- The normalized fundamental weight is bounded by the alpha immediately to
the right of the component head whenever that alpha exists. -/
theorem sourceNormalizedFundamentalWeightOrder_le_rightAlpha
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount)
    (hright : S.componentStart k < n + 1) :
    (S.sourceNormalizedFundamentalWeightOrder k : ℚ) ≤
      a.alphaValue ⟨S.componentStart k, hright⟩ := by
  unfold sourceNormalizedFundamentalWeightOrder
  rw [S.sourceFundamentalGenerator_order_eq_componentStart]
  push_cast
  by_cases hkzero : k.val = 0
  · have hk : k = S.sourceFirstComponent := by
      apply Fin.ext
      exact hkzero
    subst k
    have hstartZero : S.componentStart S.sourceFirstComponent = 0 := by
      unfold componentStart
      rw [S.Iio_sourceFirstComponent_eq_empty]
      simp
    simp only [hstartZero]
    have hfirstWeight :
        S.sourceJordan.fundamentalWeightOrder S.sourceFirstComponent =
          Lattice.weightIdealOrder q L := by
      rw [show S.sourceFirstComponent =
        (⟨0, S.componentCount_pos⟩ : Fin S.componentCount) from Fin.ext rfl]
      exact S.sourceJordan.fundamentalWeightOrder_zero S.componentCount_pos
    rw [hfirstWeight]
    have hformula := a.lemma214_weightIdealOrder_all
    rw [hformula]
    have hmin := min_le_left
      ((a.order (0 : Fin (n + 2)) : ℚ) + a.alphaValue (0 : Fin (n + 1)))
      ((a.order (0 : Fin (n + 2)) : ℚ) + (ramificationIndex K : ℚ))
    simpa only [Fin.zero_eta] using
      (sub_le_iff_le_add.mpr (by simpa [add_comm, add_left_comm, add_assoc]
        using hmin))
  · have hk : 0 < k.val := Nat.pos_of_ne_zero hkzero
    rcases S.source_hasTwoBlockSplit_componentStart k hk with ⟨T⟩
    by_cases hrank : S.sourceJordan.componentRank k = 1
    · have hformula :=
        S.sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
          k hk T hrank hright
      dsimp only at hformula
      change
        (Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : ℚ) -
            (a.order ⟨S.componentStart k, by omega⟩ : ℚ) ≤
          a.alphaValue ⟨S.componentStart k, hright⟩
      have hindex :
          (⟨S.componentStart k, hright⟩ : Fin (n + 1)).castSucc =
            (⟨S.componentStart k, by omega⟩ : Fin (n + 2)) :=
        Fin.ext rfl
      rw [hindex] at hformula
      rw [hformula]
      have hmin : min
          (a.alphaValue ⟨S.componentStart k - 1, by omega⟩)
          (min (a.alphaValue ⟨S.componentStart k, hright⟩)
            (ramificationIndex K : ℚ)) ≤
          a.alphaValue ⟨S.componentStart k, hright⟩ :=
        (min_le_right _ _).trans (min_le_left _ _)
      linarith
    · have hrankTwo : 2 ≤ S.sourceJordan.componentRank k := by
        have hpos := S.sourceJordan.component_finrank_pos k
        change 0 < S.sourceJordan.componentRank k at hpos
        omega
      have hformula :=
        S.sourceFundamentalWeightOrder_eq_order_add_alpha_componentStart
          k hk T hrankTwo
      dsimp only at hformula
      change
        (Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : ℚ) -
            (a.order ⟨S.componentStart k, by omega⟩ : ℚ) ≤
          a.alphaValue ⟨S.componentStart k, hright⟩
      have hindex :
          (⟨S.componentStart k, by omega⟩ : Fin (n + 1)).castSucc =
            (⟨S.componentStart k, by omega⟩ : Fin (n + 2)) :=
        Fin.ext rfl
      rw [hindex] at hformula
      rw [hformula]
      linarith

/-- For a noninitial component, the normalized fundamental weight is also
bounded by the alpha immediately preceding its head. -/
theorem sourceNormalizedFundamentalWeightOrder_le_leftAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val) :
    (S.sourceNormalizedFundamentalWeightOrder k : ℚ) ≤
      a.alphaValue ⟨S.componentStart k - 1, by
        have hstartPositive : 0 < S.componentStart k := by
          unfold componentStart
          let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
          have hp : previous ∈ Finset.Iio k := by
            simp only [Finset.mem_Iio]
            change k.val - 1 < k.val
            omega
          exact (S.sourceJordan.component_finrank_pos previous).trans_le
            (Finset.single_le_sum
              (s := Finset.Iio k)
              (f := fun z ↦ S.sourceJordan.componentRank z)
              (fun _ _ ↦ Nat.zero_le _) hp)
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change S.componentStart k + S.sourceJordan.componentRank k ≤
          n + 2 at hstop
        have hrankPos := S.sourceJordan.component_finrank_pos k
        change 0 < S.sourceJordan.componentRank k at hrankPos
        omega⟩ := by
  unfold sourceNormalizedFundamentalWeightOrder
  rw [S.sourceFundamentalGenerator_order_eq_componentStart]
  push_cast
  rcases S.source_hasTwoBlockSplit_componentStart k hk with ⟨T⟩
  by_cases hrank : S.sourceJordan.componentRank k = 1
  · by_cases hright : S.componentStart k < n + 1
    · have hformula :=
        S.sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
          k hk T hrank hright
      dsimp only at hformula
      change
        (Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : ℚ) -
            (a.order ⟨S.componentStart k, by omega⟩ : ℚ) ≤
          a.alphaValue ⟨S.componentStart k - 1, by omega⟩
      have hindex :
          (⟨S.componentStart k, hright⟩ : Fin (n + 1)).castSucc =
            (⟨S.componentStart k, by omega⟩ : Fin (n + 2)) :=
        Fin.ext rfl
      rw [hindex] at hformula
      rw [hformula]
      have hmin : min
          (a.alphaValue ⟨S.componentStart k - 1, by omega⟩)
          (min (a.alphaValue ⟨S.componentStart k, hright⟩)
            (ramificationIndex K : ℚ)) ≤
          a.alphaValue ⟨S.componentStart k - 1, by omega⟩ :=
        min_le_left _ _
      linarith
    · have hterminal : n + 2 - S.componentStart k = 1 := by
        have hstart := S.componentStart_lt_componentStop k
        have hstop := S.componentStop_le k
        omega
      have hformula :=
        S.sourceFundamentalWeightOrder_eq_order_add_min_alpha_e_of_unary_terminal
          k hk T hrank hterminal
      dsimp only at hformula
      change
        (Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : ℚ) -
            (a.order ⟨S.componentStart k, by omega⟩ : ℚ) ≤
          a.alphaValue ⟨S.componentStart k - 1, by omega⟩
      rw [hformula]
      have hmin : min
          (a.alphaValue ⟨S.componentStart k - 1, by omega⟩)
          (ramificationIndex K : ℚ) ≤
          a.alphaValue ⟨S.componentStart k - 1, by omega⟩ :=
        min_le_left _ _
      linarith
  · have hrankTwo : 2 ≤ S.sourceJordan.componentRank k := by
      have hpos := S.sourceJordan.component_finrank_pos k
      change 0 < S.sourceJordan.componentRank k at hpos
      omega
    have hformula :=
      S.sourceFundamentalWeightOrder_eq_order_add_alpha_componentStart
        k hk T hrankTwo
    dsimp only at hformula
    have hstartAlpha : S.componentStart k < n + 1 := by
      have hstop := S.componentStop_le k
      unfold componentStop at hstop
      change S.componentStart k + S.sourceJordan.componentRank k ≤
        n + 2 at hstop
      omega
    have hstartValue : S.componentStart k < n + 2 := by omega
    have hpreviousAlpha : S.componentStart k - 1 < n + 1 := by omega
    change
      (Lattice.weightIdealOrder q
          (S.sourceJordan.fundamentalLattice k) : ℚ) -
          (a.order ⟨S.componentStart k, hstartValue⟩ : ℚ) ≤
        a.alphaValue ⟨S.componentStart k - 1, hpreviousAlpha⟩
    have hindex :
        (⟨S.componentStart k, hstartAlpha⟩ : Fin (n + 1)).castSucc =
          (⟨S.componentStart k, hstartValue⟩ : Fin (n + 2)) :=
      Fin.ext rfl
    rw [hindex] at hformula
    rw [hformula]
    have halpha :=
      S.source_alpha_componentStart_le_predecessor_of_rank_two k hk hrankTwo
    linarith

/-- All BONG prefix-defect conditions imply Beli's normalized-weight
congruence for every aligned Jordan component.  The two missing endpoint
prefixes are respectively the empty square and the ambient determinant
square class. -/
theorem componentGenerator_congruent_of_prefixDefectBounds
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AmbientDeterminantLaws.{u, v, w} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (ambient : q.IsIsometric r)
    (horders : a.SameOrders b) (hprefix : a.PrefixDefectBounds b)
    (k : Fin S.componentCount) :
    GoodBONG.UnitsCongruentModulo
      (S.sourceFundamentalGenerator k) (S.targetFundamentalGenerator k)
      (Lattice.powerIdeal (K := K)
        (S.sourceNormalizedFundamentalWeightOrder k)) := by
  let start := S.componentStart k
  have hstartValue : start < n + 2 := by
    dsimp only [start]
    exact (S.componentStart_lt_componentStop k).trans_le
      (S.componentStop_le k)
  let d := S.sourceNormalizedFundamentalWeightOrder k
  have hd : 0 ≤ d := S.sourceNormalizedFundamentalWeightOrder_nonnegative k
  have hleft : ((((d : Int) : ℚ) : WithTop ℚ) ≤
      GoodBONG.comparisonPrefixDefect a b start) := by
    by_cases hstartZero : start = 0
    · rw [hstartZero, GoodBONG.comparisonPrefixDefect_zero]
      exact le_top
    · have hstartPositive : 0 < start := Nat.pos_of_ne_zero hstartZero
      have hk : 0 < k.val := by
        by_contra hknot
        have hkzero : k.val = 0 := Nat.eq_zero_of_not_pos hknot
        have hkfirst : k = S.sourceFirstComponent := by
          apply Fin.ext
          exact hkzero
        subst k
        apply hstartZero
        dsimp only [start, componentStart]
        rw [S.Iio_sourceFirstComponent_eq_empty]
        simp
      have hnormalized :=
        S.sourceNormalizedFundamentalWeightOrder_le_leftAlpha k hk
      have hnormalizedTop : ((((d : Int) : ℚ) : WithTop ℚ) ≤
          (a.alphaValue ⟨start - 1, by omega⟩ : WithTop ℚ)) := by
        exact_mod_cast hnormalized
      have hp := hprefix (⟨start - 1, by omega⟩ : Fin (n + 1))
      unfold GoodBONG.comparisonPrefixProduct at hp
      unfold GoodBONG.comparisonPrefixDefect GoodBONG.comparisonPrefixUnit
      rw [show start - 1 + 1 = start by omega] at hp
      exact hnormalizedTop.trans hp
  have hright : ((((d : Int) : ℚ) : WithTop ℚ) ≤
      GoodBONG.comparisonPrefixDefect a b (start + 1)) := by
    by_cases hstartRight : start < n + 1
    · have hnormalized :=
        S.sourceNormalizedFundamentalWeightOrder_le_rightAlpha k (by
          simpa only [start] using hstartRight)
      have hnormalizedTop : ((((d : Int) : ℚ) : WithTop ℚ) ≤
          (a.alphaValue ⟨start, hstartRight⟩ : WithTop ℚ)) := by
        exact_mod_cast hnormalized
      have hp := hprefix (⟨start, hstartRight⟩ : Fin (n + 1))
      unfold GoodBONG.comparisonPrefixProduct at hp
      unfold GoodBONG.comparisonPrefixDefect GoodBONG.comparisonPrefixUnit
      exact hnormalizedTop.trans hp
    · have hfull : start + 1 = n + 2 := by omega
      rw [hfull, GoodBONG.comparisonPrefixDefect_full_eq_top ambient]
      exact le_top
  have hraw := a.unitsCongruentModulo_valueUnits_of_adjacentPrefixes
    b start hstartValue d hd
      (horders ⟨start, hstartValue⟩) hleft hright
  rw [S.sourceFundamentalGenerator_eq_valueUnit,
    S.targetFundamentalGenerator_eq_valueUnit]
  simpa only [start, d] using hraw

/-- Conditions 3.1(i)--(iii) construct the complete O'Meara fundamental type
of the two synchronously aligned strict Jordan decompositions. -/
noncomputable def sameFundamentalType_of_firstThreeConditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AmbientDeterminantLaws.{u, v, w} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (ambient : q.IsIsometric r)
    (horders : a.SameOrders b) (halphas : a.SameAlphas b)
    (hprefix : a.PrefixDefectBounds b) :
    Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan :=
  S.sameFundamentalType_of_normalizedWeightCongruence horders
    (S.fundamentalWeightOrder_eq_of_sameOrders_sameAlphas horders halphas)
    (S.componentGenerator_congruent_of_prefixDefectBounds
      ambient horders hprefix)

end BONG.StrictJordanAdaptedAlignment

end Bong
