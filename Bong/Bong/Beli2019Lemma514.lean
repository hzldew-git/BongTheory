/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517AlphaProfiles
import Bong.Bong.Beli2009JordanProfileGap
import Bong.Lattice.ProductDefectRescale

/-!
# Beli (2019), Lemma 5.14 and boundary monotonicity

This file isolates the ideal calculation used at a Jordan boundary in
Lemma 5.17(i).  In the even/even case, inclusions of the two fundamental
norm groups compare the product-defect terms, while the half-gap inequality
compares O'Meara's dyadic parity terms.  Equal left scales then remove the
common square rescaling from the two fundamental ideals.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- Inclusion of intrinsic lattices reverses their norm-generator orders. -/
theorem fundamentalNormGeneratorOrder_anti_of_fundamentalLattice_le
    {s t : Nat} {J : JordanDecomposition q L s}
    {H : JordanDecomposition q M t} (i : Fin s) (j : Fin t)
    (hLM : J.fundamentalLattice i ≤ H.fundamentalLattice j) :
    ordUnit K (H.fundamentalNormGenerator j) ≤
      ordUnit K (J.fundamentalNormGenerator i) := by
  have hnorm := normIdeal_mono q hLM
  rw [(J.fundamentalNormGenerator_spec i).2,
    (H.fundamentalNormGenerator_spec j).2,
    principalIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
    powerIdeal_le_iff] at hnorm
  exact hnorm

/-- Even-boundary monotonicity in the exact form used in Beli (2019),
Lemma 5.17.  The source `J` is the smaller lattice and `H` the larger one. -/
theorem fundamentalIdeal_le_of_even_normGroup_subsets
    {t : Nat} {J : JordanDecomposition q L (t + 1)}
    {H : JordanDecomposition q M (t + 1)} (z : Fin t)
    (hleftScale :
      J.fundamentalScaleOrder (boundaryLeftIndex z) =
        H.fundamentalScaleOrder (boundaryLeftIndex z))
    (hleftGroup : J.fundamentalNormGroup (boundaryLeftIndex z) ⊆
      H.fundamentalNormGroup (boundaryLeftIndex z))
    (hrightGroup : J.fundamentalNormGroup (boundaryRightIndex z) ⊆
      H.fundamentalNormGroup (boundaryRightIndex z))
    (hsum : H.boundaryNormOrderSum z ≤ J.boundaryNormOrderSum z)
    (hJeven : Even (J.boundaryNormOrderSum z))
    (hHeven : Even (H.boundaryNormOrderSum z)) :
    J.fundamentalIdeal z ≤ H.fundamentalIdeal z := by
  have hproduct : J.boundaryProductDefectSum z ≤
      H.boundaryProductDefectSum z := by
    unfold boundaryProductDefectSum
    exact productDefectSum_mono hleftGroup hrightGroup
  have hparity : J.boundaryParityIdeal z ≤ H.boundaryParityIdeal z := by
    unfold boundaryParityIdeal
    rw [twiceIdeal_powerIdeal, twiceIdeal_powerIdeal, powerIdeal_le_iff]
    rcases hJeven with ⟨j, hj⟩
    rcases hHeven with ⟨h, hh⟩
    have hjhalf : J.boundaryNormOrderSum z / 2 = j := by omega
    have hhhalf : H.boundaryNormOrderSum z / 2 = h := by omega
    rw [hjhalf, hhhalf, hleftScale]
    omega
  have hscaled : J.scaledFundamentalIdeal z ≤
      H.scaledFundamentalIdeal z := by
    rw [scaledFundamentalIdeal, if_pos hJeven,
      scaledFundamentalIdeal, if_pos hHeven]
    exact sup_le_sup hproduct hparity
  let cJ : Kˣ := (J.scaleGenerator (boundaryLeftIndex z))⁻¹ ^ 2
  let cH : Kˣ := (H.scaleGenerator (boundaryLeftIndex z))⁻¹ ^ 2
  have hc : ordUnit K cJ = ordUnit K cH := by
    dsimp only [cJ, cH]
    rw [ordUnit_pow, ordUnit_inv, ordUnit_pow, ordUnit_inv]
    unfold fundamentalScaleOrder at hleftScale
    omega
  unfold fundamentalIdeal
  change scalarIdeal (cJ : K) (J.scaledFundamentalIdeal z) ≤
    scalarIdeal (cH : K) (H.scaledFundamentalIdeal z)
  rw [scalarIdeal_units_eq_of_ordUnit_eq cJ cH
    (J.scaledFundamentalIdeal z) hc]
  exact Submodule.map_mono hscaled

/-- If the smaller-side boundary has odd norm-order sum, its scaled
fundamental ideal is exactly its product-defect sum.  Product-defect
monotonicity therefore gives the required fundamental-ideal inclusion,
regardless of the parity on the larger side. -/
theorem fundamentalIdeal_le_of_odd_normGroup_subsets
    {t : Nat} {J : JordanDecomposition q L (t + 1)}
    {H : JordanDecomposition q M (t + 1)} (z : Fin t)
    (hleftScale :
      J.fundamentalScaleOrder (boundaryLeftIndex z) =
        H.fundamentalScaleOrder (boundaryLeftIndex z))
    (hleftGroup : J.fundamentalNormGroup (boundaryLeftIndex z) ⊆
      H.fundamentalNormGroup (boundaryLeftIndex z))
    (hrightGroup : J.fundamentalNormGroup (boundaryRightIndex z) ⊆
      H.fundamentalNormGroup (boundaryRightIndex z))
    (hJodd : Odd (J.boundaryNormOrderSum z)) :
    J.fundamentalIdeal z ≤ H.fundamentalIdeal z := by
  have hproduct : J.boundaryProductDefectSum z ≤
      H.boundaryProductDefectSum z := by
    unfold boundaryProductDefectSum
    exact productDefectSum_mono hleftGroup hrightGroup
  have hproductScaled : H.boundaryProductDefectSum z ≤
      H.scaledFundamentalIdeal z := by
    by_cases hHeven : Even (H.boundaryNormOrderSum z)
    · rw [scaledFundamentalIdeal, if_pos hHeven]
      exact _root_.le_sup_left
    · rw [scaledFundamentalIdeal, if_neg hHeven]
  have hscaled : J.scaledFundamentalIdeal z ≤
      H.scaledFundamentalIdeal z := by
    have hJnotEven : ¬ Even (J.boundaryNormOrderSum z) := by
      exact Int.not_even_iff_odd.mpr hJodd
    rw [scaledFundamentalIdeal, if_neg hJnotEven]
    exact hproduct.trans hproductScaled
  let cJ : Kˣ := (J.scaleGenerator (boundaryLeftIndex z))⁻¹ ^ 2
  let cH : Kˣ := (H.scaleGenerator (boundaryLeftIndex z))⁻¹ ^ 2
  have hc : ordUnit K cJ = ordUnit K cH := by
    dsimp only [cJ, cH]
    rw [ordUnit_pow, ordUnit_inv, ordUnit_pow, ordUnit_inv]
    unfold fundamentalScaleOrder at hleftScale
    omega
  unfold fundamentalIdeal
  change scalarIdeal (cJ : K) (J.scaledFundamentalIdeal z) ≤
    scalarIdeal (cH : K) (H.scaledFundamentalIdeal z)
  rw [scalarIdeal_units_eq_of_ordUnit_eq cJ cH
    (J.scaledFundamentalIdeal z) hc]
  exact Submodule.map_mono hscaled

/-- Heterogeneous-component-count form of the even boundary ideal
comparison. -/
theorem fundamentalIdeal_le_of_even_normGroup_subsets_at
    {s t : Nat} {J : JordanDecomposition q L (s + 1)}
    {H : JordanDecomposition q M (t + 1)}
    (zJ : Fin s) (zH : Fin t)
    (hleftScale :
      J.fundamentalScaleOrder (boundaryLeftIndex zJ) =
        H.fundamentalScaleOrder (boundaryLeftIndex zH))
    (hleftGroup : J.fundamentalNormGroup (boundaryLeftIndex zJ) ⊆
      H.fundamentalNormGroup (boundaryLeftIndex zH))
    (hrightGroup : J.fundamentalNormGroup (boundaryRightIndex zJ) ⊆
      H.fundamentalNormGroup (boundaryRightIndex zH))
    (hsum : H.boundaryNormOrderSum zH ≤ J.boundaryNormOrderSum zJ)
    (hJeven : Even (J.boundaryNormOrderSum zJ))
    (hHeven : Even (H.boundaryNormOrderSum zH)) :
    J.fundamentalIdeal zJ ≤ H.fundamentalIdeal zH := by
  have hproduct : J.boundaryProductDefectSum zJ ≤
      H.boundaryProductDefectSum zH := by
    unfold boundaryProductDefectSum
    exact productDefectSum_mono hleftGroup hrightGroup
  have hparity : J.boundaryParityIdeal zJ ≤ H.boundaryParityIdeal zH := by
    unfold boundaryParityIdeal
    rw [twiceIdeal_powerIdeal, twiceIdeal_powerIdeal, powerIdeal_le_iff]
    rcases hJeven with ⟨j, hj⟩
    rcases hHeven with ⟨h, hh⟩
    have hjhalf : J.boundaryNormOrderSum zJ / 2 = j := by omega
    have hhhalf : H.boundaryNormOrderSum zH / 2 = h := by omega
    rw [hjhalf, hhhalf, hleftScale]
    omega
  have hscaled : J.scaledFundamentalIdeal zJ ≤
      H.scaledFundamentalIdeal zH := by
    rw [scaledFundamentalIdeal, if_pos hJeven,
      scaledFundamentalIdeal, if_pos hHeven]
    exact sup_le_sup hproduct hparity
  let cJ : Kˣ := (J.scaleGenerator (boundaryLeftIndex zJ))⁻¹ ^ 2
  let cH : Kˣ := (H.scaleGenerator (boundaryLeftIndex zH))⁻¹ ^ 2
  have hc : ordUnit K cJ = ordUnit K cH := by
    dsimp only [cJ, cH]
    rw [ordUnit_pow, ordUnit_inv, ordUnit_pow, ordUnit_inv]
    unfold fundamentalScaleOrder at hleftScale
    omega
  unfold fundamentalIdeal
  change scalarIdeal (cJ : K) (J.scaledFundamentalIdeal zJ) ≤
    scalarIdeal (cH : K) (H.scaledFundamentalIdeal zH)
  rw [scalarIdeal_units_eq_of_ordUnit_eq cJ cH
    (J.scaledFundamentalIdeal zJ) hc]
  exact Submodule.map_mono hscaled

/-- Heterogeneous-component-count form of the odd-source boundary ideal
comparison. -/
theorem fundamentalIdeal_le_of_odd_normGroup_subsets_at
    {s t : Nat} {J : JordanDecomposition q L (s + 1)}
    {H : JordanDecomposition q M (t + 1)}
    (zJ : Fin s) (zH : Fin t)
    (hleftScale :
      J.fundamentalScaleOrder (boundaryLeftIndex zJ) =
        H.fundamentalScaleOrder (boundaryLeftIndex zH))
    (hleftGroup : J.fundamentalNormGroup (boundaryLeftIndex zJ) ⊆
      H.fundamentalNormGroup (boundaryLeftIndex zH))
    (hrightGroup : J.fundamentalNormGroup (boundaryRightIndex zJ) ⊆
      H.fundamentalNormGroup (boundaryRightIndex zH))
    (hJodd : Odd (J.boundaryNormOrderSum zJ)) :
    J.fundamentalIdeal zJ ≤ H.fundamentalIdeal zH := by
  have hproduct : J.boundaryProductDefectSum zJ ≤
      H.boundaryProductDefectSum zH := by
    unfold boundaryProductDefectSum
    exact productDefectSum_mono hleftGroup hrightGroup
  have hproductScaled : H.boundaryProductDefectSum zH ≤
      H.scaledFundamentalIdeal zH := by
    by_cases hHeven : Even (H.boundaryNormOrderSum zH)
    · rw [scaledFundamentalIdeal, if_pos hHeven]
      exact _root_.le_sup_left
    · rw [scaledFundamentalIdeal, if_neg hHeven]
  have hscaled : J.scaledFundamentalIdeal zJ ≤
      H.scaledFundamentalIdeal zH := by
    have hJnotEven : ¬ Even (J.boundaryNormOrderSum zJ) :=
      Int.not_even_iff_odd.mpr hJodd
    rw [scaledFundamentalIdeal, if_neg hJnotEven]
    exact hproduct.trans hproductScaled
  let cJ : Kˣ := (J.scaleGenerator (boundaryLeftIndex zJ))⁻¹ ^ 2
  let cH : Kˣ := (H.scaleGenerator (boundaryLeftIndex zH))⁻¹ ^ 2
  have hc : ordUnit K cJ = ordUnit K cH := by
    dsimp only [cJ, cH]
    rw [ordUnit_pow, ordUnit_inv, ordUnit_pow, ordUnit_inv]
    unfold fundamentalScaleOrder at hleftScale
    omega
  unfold fundamentalIdeal
  change scalarIdeal (cJ : K) (J.scaledFundamentalIdeal zJ) ≤
    scalarIdeal (cH : K) (H.scaledFundamentalIdeal zH)
  rw [scalarIdeal_units_eq_of_ordUnit_eq cJ cH
    (J.scaledFundamentalIdeal zJ) hc]
  exact Submodule.map_mono hscaled

end Lattice.JordanDecomposition

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- Alpha is monotone in the order gap when the source gap is odd.  Below
`2e` the odd source alpha is the gap itself; above `2e` both alphas are the
corresponding half-gap values. -/
theorem alphaValue_le_of_orderGap_le_of_source_odd
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {n : Nat} (a : GoodBONG q M (n + 1))
    (b : GoodBONG q L (n + 1)) (i j : Fin n)
    (hgap : a.orderGap i ≤ b.orderGap j)
    (hodd : Odd (a.orderGap i)) :
    a.alphaValue i ≤ b.alphaValue j := by
  rcases le_or_gt (a.orderGap i)
      (2 * (ramificationIndex K : Int)) with haSmall | haLarge
  · have haAlpha :=
      (a.beli2009Lemma27_iii i haSmall).2.mpr (Or.inr hodd)
    rw [haAlpha]
    rcases le_or_gt (b.orderGap j)
        (2 * (ramificationIndex K : Int)) with hbSmall | hbLarge
    · have hbLower := (b.beli2009Lemma27_iii j hbSmall).1
      have hgapQ : (a.orderGap i : ℚ) ≤ (b.orderGap j : ℚ) := by
        exact_mod_cast hgap
      exact hgapQ.trans hbLower
    · rw [b.beli2009Lemma27_ii j hbLarge.le]
      unfold GoodBONG.halfGapValue
      have haCast : (a.orderGap i : ℚ) ≤
          2 * (ramificationIndex K : ℚ) := by
        exact_mod_cast haSmall
      have hbCast : 2 * (ramificationIndex K : ℚ) <
          (b.orderGap j : ℚ) := by
        exact_mod_cast hbLarge
      linarith
  · have hbLarge : 2 * (ramificationIndex K : Int) <
        b.orderGap j := lt_of_lt_of_le haLarge hgap
    rw [a.beli2009Lemma27_ii i haLarge.le,
      b.beli2009Lemma27_ii j hbLarge.le]
    unfold GoodBONG.halfGapValue
    have hgapQ : (a.orderGap i : ℚ) ≤ (b.orderGap j : ℚ) := by
      exact_mod_cast hgap
    linarith

/-- Full boundary comparison behind Beli (2019), Lemma 5.14.  The proof
uses product-defect monotonicity.  The only parity branch not yielding a
direct fundamental-ideal inclusion has odd source gap, where the preceding
arithmetic lemma applies. -/
theorem alphaValue_le_of_boundary_normGroup_subsets
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {n t : Nat} (a : GoodBONG q M (n + 2))
    (b : GoodBONG q L (n + 2))
    {J : Lattice.JordanDecomposition q L (t + 1)}
    {H : Lattice.JordanDecomposition q M (t + 1)}
    (Psmall : JordanOrderProfileWitness b.toBONG J)
    (Plarge : JordanOrderProfileWitness a.toBONG H)
    (z : Fin t)
    (hleftScale :
      J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) =
        H.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hleftGroup : J.fundamentalNormGroup
        (Lattice.JordanDecomposition.boundaryLeftIndex z) ⊆
      H.fundamentalNormGroup
        (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hrightGroup : J.fundamentalNormGroup
        (Lattice.JordanDecomposition.boundaryRightIndex z) ⊆
      H.fundamentalNormGroup
        (Lattice.JordanDecomposition.boundaryRightIndex z))
    (hsum : H.boundaryNormOrderSum z ≤ J.boundaryNormOrderSum z) :
    a.alphaValue (Plarge.boundaryIndex z) ≤
      b.alphaValue (Psmall.boundaryIndex z) := by
  have hlargeGap :=
    Plarge.orderGap_boundaryIndex_eq_boundaryNormOrderSum_sub_twoScale z
  have hsmallGap :=
    Psmall.orderGap_boundaryIndex_eq_boundaryNormOrderSum_sub_twoScale z
  have hgap : a.orderGap (Plarge.boundaryIndex z) ≤
      b.orderGap (Psmall.boundaryIndex z) := by
    rw [hlargeGap, hsmallGap, hleftScale]
    exact sub_le_sub_right hsum _
  have hhalf : a.halfGapValue (Plarge.boundaryIndex z) ≤
      b.halfGapValue (Psmall.boundaryIndex z) := by
    unfold GoodBONG.halfGapValue
    have hgapQ : (a.orderGap (Plarge.boundaryIndex z) : ℚ) ≤
        (b.orderGap (Psmall.boundaryIndex z) : ℚ) := by
      exact_mod_cast hgap
    linarith
  by_cases hJeven : Even (J.boundaryNormOrderSum z)
  · by_cases hHeven : Even (H.boundaryNormOrderSum z)
    · have hideal :=
        Lattice.JordanDecomposition.fundamentalIdeal_le_of_even_normGroup_subsets
          z hleftScale hleftGroup hrightGroup hsum hJeven hHeven
      exact alphaValue_le_of_boundary_fundamentalIdeal_le a b
        Psmall Plarge z hideal hhalf
    · have hHodd : Odd (H.boundaryNormOrderSum z) :=
        Int.not_even_iff_odd.mp hHeven
      have hsourceOdd : Odd (a.orderGap (Plarge.boundaryIndex z)) := by
        rw [hlargeGap]
        rcases hHodd with ⟨k, hk⟩
        refine ⟨k - H.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z), ?_⟩
        omega
      exact alphaValue_le_of_orderGap_le_of_source_odd a b
        (Plarge.boundaryIndex z) (Psmall.boundaryIndex z) hgap hsourceOdd
  · have hJodd : Odd (J.boundaryNormOrderSum z) :=
      Int.not_even_iff_odd.mp hJeven
    have hideal :=
      Lattice.JordanDecomposition.fundamentalIdeal_le_of_odd_normGroup_subsets
        z hleftScale hleftGroup hrightGroup hJodd
    exact alphaValue_le_of_boundary_fundamentalIdeal_le a b
      Psmall Plarge z hideal hhalf

/-- Geometric form of the preceding boundary comparison.  Inclusions of
the two intrinsic lattices imply both the norm-group inclusions and the
boundary norm-order-sum inequality. -/
theorem alphaValue_le_of_boundary_fundamentalLattices_le
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {n t : Nat} (a : GoodBONG q M (n + 2))
    (b : GoodBONG q L (n + 2))
    {J : Lattice.JordanDecomposition q L (t + 1)}
    {H : Lattice.JordanDecomposition q M (t + 1)}
    (Psmall : JordanOrderProfileWitness b.toBONG J)
    (Plarge : JordanOrderProfileWitness a.toBONG H)
    (z : Fin t)
    (hleftScale :
      J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) =
        H.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hleftLattice : J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z) ≤
      H.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hrightLattice : J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z) ≤
      H.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z)) :
    a.alphaValue (Plarge.boundaryIndex z) ≤
      b.alphaValue (Psmall.boundaryIndex z) := by
  have hleftGroup : J.fundamentalNormGroup
        (Lattice.JordanDecomposition.boundaryLeftIndex z) ⊆
      H.fundamentalNormGroup
        (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
    unfold Lattice.JordanDecomposition.fundamentalNormGroup
    exact Lattice.normGroupSet_mono hleftLattice
  have hrightGroup : J.fundamentalNormGroup
        (Lattice.JordanDecomposition.boundaryRightIndex z) ⊆
      H.fundamentalNormGroup
        (Lattice.JordanDecomposition.boundaryRightIndex z) := by
    unfold Lattice.JordanDecomposition.fundamentalNormGroup
    exact Lattice.normGroupSet_mono hrightLattice
  have hleftOrder :=
    Lattice.JordanDecomposition.fundamentalNormGeneratorOrder_anti_of_fundamentalLattice_le
      (J := J) (H := H)
      (Lattice.JordanDecomposition.boundaryLeftIndex z)
      (Lattice.JordanDecomposition.boundaryLeftIndex z) hleftLattice
  have hrightOrder :=
    Lattice.JordanDecomposition.fundamentalNormGeneratorOrder_anti_of_fundamentalLattice_le
      (J := J) (H := H)
      (Lattice.JordanDecomposition.boundaryRightIndex z)
      (Lattice.JordanDecomposition.boundaryRightIndex z) hrightLattice
  have hsum : H.boundaryNormOrderSum z ≤
      J.boundaryNormOrderSum z := by
    unfold Lattice.JordanDecomposition.boundaryNormOrderSum
    omega
  exact alphaValue_le_of_boundary_normGroup_subsets a b Psmall Plarge z
    hleftScale hleftGroup hrightGroup hsum

/-- Heterogeneous-component-count form of the full boundary comparison.
This is needed when one weak Jordan family has amalgamated its unique
equal-scale pair and the other has not. -/
theorem alphaValue_le_of_boundary_fundamentalLattices_le_at
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {n s t : Nat} (a : GoodBONG q M (n + 2))
    (b : GoodBONG q L (n + 2))
    {J : Lattice.JordanDecomposition q L (s + 1)}
    {H : Lattice.JordanDecomposition q M (t + 1)}
    (Psmall : JordanOrderProfileWitness b.toBONG J)
    (Plarge : JordanOrderProfileWitness a.toBONG H)
    (zSmall : Fin s) (zLarge : Fin t)
    (hleftScale :
      J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex zSmall) =
        H.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex zLarge))
    (hleftLattice : J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex zSmall) ≤
      H.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex zLarge))
    (hrightLattice : J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex zSmall) ≤
      H.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex zLarge)) :
    a.alphaValue (Plarge.boundaryIndex zLarge) ≤
      b.alphaValue (Psmall.boundaryIndex zSmall) := by
  let lSmall := Lattice.JordanDecomposition.boundaryLeftIndex zSmall
  let rSmall := Lattice.JordanDecomposition.boundaryRightIndex zSmall
  let lLarge := Lattice.JordanDecomposition.boundaryLeftIndex zLarge
  let rLarge := Lattice.JordanDecomposition.boundaryRightIndex zLarge
  have hleftGroup : J.fundamentalNormGroup lSmall ⊆
      H.fundamentalNormGroup lLarge := by
    unfold Lattice.JordanDecomposition.fundamentalNormGroup
    exact Lattice.normGroupSet_mono hleftLattice
  have hrightGroup : J.fundamentalNormGroup rSmall ⊆
      H.fundamentalNormGroup rLarge := by
    unfold Lattice.JordanDecomposition.fundamentalNormGroup
    exact Lattice.normGroupSet_mono hrightLattice
  have hleftOrder :=
    Lattice.JordanDecomposition.fundamentalNormGeneratorOrder_anti_of_fundamentalLattice_le
      (J := J) (H := H) lSmall lLarge hleftLattice
  have hrightOrder :=
    Lattice.JordanDecomposition.fundamentalNormGeneratorOrder_anti_of_fundamentalLattice_le
      (J := J) (H := H) rSmall rLarge hrightLattice
  have hsum : H.boundaryNormOrderSum zLarge ≤
      J.boundaryNormOrderSum zSmall := by
    unfold Lattice.JordanDecomposition.boundaryNormOrderSum
    change ordUnit K (H.fundamentalNormGenerator lLarge) +
        ordUnit K (H.fundamentalNormGenerator rLarge) ≤
      ordUnit K (J.fundamentalNormGenerator lSmall) +
        ordUnit K (J.fundamentalNormGenerator rSmall)
    omega
  have hlargeGap :=
    Plarge.orderGap_boundaryIndex_eq_boundaryNormOrderSum_sub_twoScale zLarge
  have hsmallGap :=
    Psmall.orderGap_boundaryIndex_eq_boundaryNormOrderSum_sub_twoScale zSmall
  have hgap : a.orderGap (Plarge.boundaryIndex zLarge) ≤
      b.orderGap (Psmall.boundaryIndex zSmall) := by
    rw [hlargeGap, hsmallGap]
    change J.fundamentalScaleOrder lSmall =
      H.fundamentalScaleOrder lLarge at hleftScale
    rw [hleftScale]
    exact sub_le_sub_right hsum _
  have hhalf : a.halfGapValue (Plarge.boundaryIndex zLarge) ≤
      b.halfGapValue (Psmall.boundaryIndex zSmall) := by
    unfold GoodBONG.halfGapValue
    have hgapQ : (a.orderGap (Plarge.boundaryIndex zLarge) : ℚ) ≤
        (b.orderGap (Psmall.boundaryIndex zSmall) : ℚ) := by
      exact_mod_cast hgap
    linarith
  by_cases hJeven : Even (J.boundaryNormOrderSum zSmall)
  · by_cases hHeven : Even (H.boundaryNormOrderSum zLarge)
    · have hideal :=
        Lattice.JordanDecomposition.fundamentalIdeal_le_of_even_normGroup_subsets_at
          zSmall zLarge hleftScale hleftGroup hrightGroup hsum hJeven hHeven
      exact alphaValue_le_of_boundary_fundamentalIdeal_le_at a b
        Psmall Plarge zSmall zLarge hideal hhalf
    · have hHodd : Odd (H.boundaryNormOrderSum zLarge) :=
        Int.not_even_iff_odd.mp hHeven
      have hsourceOdd : Odd (a.orderGap (Plarge.boundaryIndex zLarge)) := by
        rw [hlargeGap]
        rcases hHodd with ⟨k, hk⟩
        refine ⟨k - H.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex zLarge), ?_⟩
        omega
      exact alphaValue_le_of_orderGap_le_of_source_odd a b
        (Plarge.boundaryIndex zLarge) (Psmall.boundaryIndex zSmall)
        hgap hsourceOdd
  · have hJodd : Odd (J.boundaryNormOrderSum zSmall) :=
      Int.not_even_iff_odd.mp hJeven
    have hideal :=
      Lattice.JordanDecomposition.fundamentalIdeal_le_of_odd_normGroup_subsets_at
        zSmall zLarge hleftScale hleftGroup hrightGroup hJodd
    exact alphaValue_le_of_boundary_fundamentalIdeal_le_at a b
      Psmall Plarge zSmall zLarge hideal hhalf

end BONG

end Bong
