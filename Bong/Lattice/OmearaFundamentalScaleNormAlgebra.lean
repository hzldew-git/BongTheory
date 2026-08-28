/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328GeneratorChoice

/-!
# Fundamental invariants from scale and norm-group data

The dimensions in O'Meara's complete fundamental type are irrelevant to
the fundamental weights and boundary ideals.  This file isolates the
stronger fact actually used in rank reduction: equal ordered scale values
and equal fundamental norm groups already determine all those ideals.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}
  {J : JordanDecomposition q L t} {H : JordanDecomposition r M t}

/-- Equal fundamental norm groups identify the orders of independently
chosen norm generators, without any component-rank hypothesis. -/
theorem fundamentalNormGenerator_order_eq_of_normGroup_eq
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (i : Fin t) :
    ordUnit K (H.fundamentalNormGenerator i) =
      ordUnit K (J.fundamentalNormGenerator i) := by
  have hcommon := isNormGeneratorValue_of_normGroupSet_eq
    (J.fundamentalNormGenerator_spec i) (hnorm i).symm
    (H.exists_fundamentalNormGenerator i)
  have hown := H.fundamentalNormGenerator_spec i
  apply (principalIdeal_eq_iff_ordUnit_eq
    (H.fundamentalNormGenerator i)
    (J.fundamentalNormGenerator i)).mp
  exact hown.2.symm.trans hcommon.2

/-- Scale orders and fundamental norm groups determine the fundamental
weight ideals. -/
theorem fundamentalWeightIdeal_eq_of_scaleOrder_normGroup_eq
    (hscale : ∀ i, H.fundamentalScaleOrder i = J.fundamentalScaleOrder i)
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (i : Fin t) :
    H.fundamentalWeightIdeal i = J.fundamentalWeightIdeal i := by
  have htwo : twoScaleIdeal q (J.fundamentalLattice i) =
      twoScaleIdeal r (H.fundamentalLattice i) := by
    unfold twoScaleIdeal
    congr 1
    unfold fundamentalLattice fundamentalScaleOrder
    rw [J.scaleIdeal_scaleTruncation_at_component,
      H.scaleIdeal_scaleTruncation_at_component]
    have hs := hscale i
    change ordUnit K (H.scaleGenerator i) =
      ordUnit K (J.scaleGenerator i) at hs
    rw [hs]
  apply (weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    (J.fundamentalNormGenerator_spec i)
    (H.exists_fundamentalNormGenerator i)
    (hnorm i).symm htwo).symm

theorem fundamentalWeightOrder_eq_of_scaleOrder_normGroup_eq
    (hscale : ∀ i, H.fundamentalScaleOrder i = J.fundamentalScaleOrder i)
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (i : Fin t) :
    H.fundamentalWeightOrder i = J.fundamentalWeightOrder i := by
  unfold fundamentalWeightOrder
  apply powerIdeal_order_eq_of_eq (K := K)
  rw [← weightIdeal_eq_powerIdeal, ← weightIdeal_eq_powerIdeal]
  simpa only [fundamentalWeightIdeal] using
    fundamentalWeightIdeal_eq_of_scaleOrder_normGroup_eq hscale hnorm i

/-- The explicit threshold formed with the same scalar generator is
unchanged under scale/norm-group preserving rank reduction. -/
theorem fourNormOverWeightIdealWith_eq_of_scaleOrder_normGroup_eq
    (hscale : ∀ i, H.fundamentalScaleOrder i = J.fundamentalScaleOrder i)
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (A : FundamentalNormGeneratorChoice J)
    (B : FundamentalNormGeneratorChoice H)
    (hvalue : ∀ i, B.value i = A.value i)
    (i : Fin t) :
    H.fourNormOverWeightIdealWith B i =
      J.fourNormOverWeightIdealWith A i := by
  unfold fourNormOverWeightIdealWith
  rw [hvalue i,
    fundamentalWeightOrder_eq_of_scaleOrder_normGroup_eq hscale hnorm i]

/-- Boundary norm-order sums depend only on the fundamental norm groups. -/
theorem boundaryNormOrderSum_eq_of_normGroup_eq
    {N : Nat}
    {J : JordanDecomposition q L (N + 1)}
    {H : JordanDecomposition r M (N + 1)}
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (i : Fin N) :
    H.boundaryNormOrderSum i = J.boundaryNormOrderSum i := by
  unfold boundaryNormOrderSum
  rw [fundamentalNormGenerator_order_eq_of_normGroup_eq hnorm,
    fundamentalNormGenerator_order_eq_of_normGroup_eq hnorm]

theorem boundaryProductDefectSum_eq_of_normGroup_eq
    {N : Nat}
    {J : JordanDecomposition q L (N + 1)}
    {H : JordanDecomposition r M (N + 1)}
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (i : Fin N) :
    H.boundaryProductDefectSum i = J.boundaryProductDefectSum i := by
  unfold boundaryProductDefectSum
  rw [hnorm (boundaryLeftIndex i), hnorm (boundaryRightIndex i)]

theorem boundaryParityIdeal_eq_of_scaleOrder_normGroup_eq
    {N : Nat}
    {J : JordanDecomposition q L (N + 1)}
    {H : JordanDecomposition r M (N + 1)}
    (hscale : ∀ i, H.fundamentalScaleOrder i = J.fundamentalScaleOrder i)
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (i : Fin N) :
    H.boundaryParityIdeal i = J.boundaryParityIdeal i := by
  unfold boundaryParityIdeal
  rw [boundaryNormOrderSum_eq_of_normGroup_eq hnorm,
    hscale (boundaryLeftIndex i)]

theorem scaledFundamentalIdeal_eq_of_scaleOrder_normGroup_eq
    {N : Nat}
    {J : JordanDecomposition q L (N + 1)}
    {H : JordanDecomposition r M (N + 1)}
    (hscale : ∀ i, H.fundamentalScaleOrder i = J.fundamentalScaleOrder i)
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (i : Fin N) :
    H.scaledFundamentalIdeal i = J.scaledFundamentalIdeal i := by
  unfold scaledFundamentalIdeal
  rw [boundaryNormOrderSum_eq_of_normGroup_eq hnorm,
    boundaryProductDefectSum_eq_of_normGroup_eq hnorm,
    boundaryParityIdeal_eq_of_scaleOrder_normGroup_eq hscale hnorm]

/-- O'Meara's boundary ideals are invariant under a rank change that
preserves the ordered scale and fundamental norm-group data. -/
theorem fundamentalIdeal_eq_of_scaleOrder_normGroup_eq
    {N : Nat}
    {J : JordanDecomposition q L (N + 1)}
    {H : JordanDecomposition r M (N + 1)}
    (hscale : ∀ i, H.fundamentalScaleOrder i = J.fundamentalScaleOrder i)
    (hnorm : ∀ i, H.fundamentalNormGroup i = J.fundamentalNormGroup i)
    (i : Fin N) :
    H.fundamentalIdeal i = J.fundamentalIdeal i := by
  unfold fundamentalIdeal
  rw [scaledFundamentalIdeal_eq_of_scaleOrder_normGroup_eq hscale hnorm]
  apply scalarIdeal_units_eq_of_ordUnit_eq
  rw [ordUnit_pow, ordUnit_inv, ordUnit_pow, ordUnit_inv]
  have hs := hscale (boundaryLeftIndex i)
  change ordUnit K (H.scaleGenerator (boundaryLeftIndex i)) =
    ordUnit K (J.scaleGenerator (boundaryLeftIndex i)) at hs
  rw [hs]

/-- Equal norm groups at two possibly differently indexed Jordan scales
identify the orders of their independently chosen norm generators. -/
theorem fundamentalNormGenerator_order_eq_of_normGroup_eq_at
    {s t : Nat}
    {J : JordanDecomposition q L t} {H : JordanDecomposition r M s}
    (i : Fin t) (j : Fin s)
    (hnorm : H.fundamentalNormGroup j = J.fundamentalNormGroup i) :
    ordUnit K (H.fundamentalNormGenerator j) =
      ordUnit K (J.fundamentalNormGenerator i) := by
  have hcommon := isNormGeneratorValue_of_normGroupSet_eq
    (J.fundamentalNormGenerator_spec i) hnorm.symm
    (H.exists_fundamentalNormGenerator j)
  have hown := H.fundamentalNormGenerator_spec j
  apply (principalIdeal_eq_iff_ordUnit_eq
    (H.fundamentalNormGenerator j)
    (J.fundamentalNormGenerator i)).mp
  exact hown.2.symm.trans hcommon.2

/-- Fundamental weight orders agree at any two scales with equal scale order
and equal fundamental norm group; the surrounding Jordan chains need not
have the same length. -/
theorem fundamentalWeightOrder_eq_of_scaleOrder_normGroup_eq_at
    {s t : Nat}
    {J : JordanDecomposition q L t} {H : JordanDecomposition r M s}
    (i : Fin t) (j : Fin s)
    (hscale : H.fundamentalScaleOrder j = J.fundamentalScaleOrder i)
    (hnorm : H.fundamentalNormGroup j = J.fundamentalNormGroup i) :
    H.fundamentalWeightOrder j = J.fundamentalWeightOrder i := by
  have htwo : twoScaleIdeal q (J.fundamentalLattice i) =
      twoScaleIdeal r (H.fundamentalLattice j) := by
    rw [J.fundamentalTwoScaleIdeal_eq_powerIdeal,
      H.fundamentalTwoScaleIdeal_eq_powerIdeal, hscale]
  have hweight : H.fundamentalWeightIdeal j =
      J.fundamentalWeightIdeal i := by
    apply (weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
      (J.fundamentalNormGenerator_spec i)
      (H.exists_fundamentalNormGenerator j) hnorm.symm htwo).symm
  unfold fundamentalWeightOrder
  apply powerIdeal_order_eq_of_eq (K := K)
  rw [← weightIdeal_eq_powerIdeal, ← weightIdeal_eq_powerIdeal]
  simpa only [fundamentalWeightIdeal] using hweight

/-- Boundary ideals agree when the two endpoint scale orders and norm groups
agree, even if the boundaries lie in Jordan chains of different lengths. -/
theorem fundamentalIdeal_eq_of_boundaryData_eq
    {N P : Nat}
    {J : JordanDecomposition q L (N + 1)}
    {H : JordanDecomposition r M (P + 1)}
    (i : Fin N) (j : Fin P)
    (hscaleLeft :
      H.fundamentalScaleOrder (boundaryLeftIndex j) =
        J.fundamentalScaleOrder (boundaryLeftIndex i))
    (hnormLeft :
      H.fundamentalNormGroup (boundaryLeftIndex j) =
        J.fundamentalNormGroup (boundaryLeftIndex i))
    (hnormRight :
      H.fundamentalNormGroup (boundaryRightIndex j) =
        J.fundamentalNormGroup (boundaryRightIndex i)) :
    H.fundamentalIdeal j = J.fundamentalIdeal i := by
  have hleftOrder := fundamentalNormGenerator_order_eq_of_normGroup_eq_at
    (J := J) (H := H) (boundaryLeftIndex i) (boundaryLeftIndex j)
      hnormLeft
  have hrightOrder := fundamentalNormGenerator_order_eq_of_normGroup_eq_at
    (J := J) (H := H) (boundaryRightIndex i) (boundaryRightIndex j)
      hnormRight
  have hsum : H.boundaryNormOrderSum j = J.boundaryNormOrderSum i := by
    unfold boundaryNormOrderSum
    rw [hleftOrder, hrightOrder]
  have hproduct : H.boundaryProductDefectSum j =
      J.boundaryProductDefectSum i := by
    unfold boundaryProductDefectSum
    rw [hnormLeft, hnormRight]
  have hparity : H.boundaryParityIdeal j = J.boundaryParityIdeal i := by
    unfold boundaryParityIdeal
    rw [hsum, hscaleLeft]
  have hscaled : H.scaledFundamentalIdeal j =
      J.scaledFundamentalIdeal i := by
    unfold scaledFundamentalIdeal
    rw [hsum, hproduct, hparity]
  unfold fundamentalIdeal
  rw [hscaled]
  apply scalarIdeal_units_eq_of_ordUnit_eq
  simp only [ordUnit_pow, ordUnit_inv]
  have hs := hscaleLeft
  unfold fundamentalScaleOrder at hs
  rw [hs]

end Lattice.JordanDecomposition

end Bong
