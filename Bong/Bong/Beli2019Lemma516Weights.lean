/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma516
import Bong.Bong.Beli2009JordanProfileInternal
import Bong.Bong.Beli2009JordanProfileBoundary
import Bong.Lattice.Omeara9325FundamentalMonotonicity

/-!
# Weight-order consequence of Beli (2019), Lemma 5.16

The lattice inclusion in Lemma 5.16 is converted, using O'Meara 93:25, to
the inequality between the weights of the corresponding intrinsic lattices.
This is the ideal-theoretic step used at an internal good-BONG coordinate in
the proof of Lemma 5.17(i).
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V}

namespace Lattice.JordanDecomposition

/-- Inclusion of two intrinsic lattices reverses the order of their weight
ideals.  This is O'Meara 93:25 written in valuation-order form. -/
theorem fundamentalWeightOrder_anti_of_fundamentalLattice_le
    {s t : Nat} {J : JordanDecomposition q L s}
    {H : JordanDecomposition q M t} (i : Fin s) (j : Fin t)
    (hLM : J.fundamentalLattice i ≤ H.fundamentalLattice j) :
    H.fundamentalWeightOrder j ≤ J.fundamentalWeightOrder i := by
  have hweight :
      weightIdeal q (J.fundamentalLattice i) ≤
        weightIdeal q (H.fundamentalLattice j) :=
    weightIdeal_mono_of_lattice_le hLM
      (J.fundamentalNormGenerator i) (H.fundamentalNormGenerator j)
      (J.fundamentalNormGenerator_spec i)
      (H.fundamentalNormGenerator_spec j)
  rw [weightIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
    powerIdeal_le_iff] at hweight
  exact hweight

/-- Equal fundamental scales identify the two intrinsic lattices with the
same pair of scale truncations. -/
theorem fundamentalLattice_le_of_scaleTruncation_le
    {s t : Nat} {J : JordanDecomposition q L s}
    {H : JordanDecomposition q M t} (i : Fin s) (j : Fin t)
    (hscale : J.fundamentalScaleOrder i = H.fundamentalScaleOrder j)
    (hLM : scaleTruncation q L (J.fundamentalScaleOrder i) ≤
      scaleTruncation q M (J.fundamentalScaleOrder i)) :
    J.fundamentalLattice i ≤ H.fundamentalLattice j := by
  unfold fundamentalLattice
  rwa [← hscale]

end Lattice.JordanDecomposition

namespace Lattice.Beli2019Lemma51Data

/-- Lemma 5.16 at two possibly different truncation scales.  If the large
lattice is truncated at an earlier scale than the small lattice, the latter
first embeds into its own earlier truncation and then into the large
lattice. -/
theorem smallFundamentalLattice_le_large_of_scale_le
    (D : Beli2019Lemma51Data q M N)
    {s t : Nat} {J : Lattice.JordanDecomposition q N s}
    {H : Lattice.JordanDecomposition q M t} (i : Fin s) (j : Fin t)
    (hscale : H.fundamentalScaleOrder j ≤
      J.fundamentalScaleOrder i)
    (hbound : H.fundamentalScaleOrder j ≤
      ordUnit K D.input.block.enlargedScaleGenerator) :
    J.fundamentalLattice i ≤ H.fundamentalLattice j := by
  unfold Lattice.JordanDecomposition.fundamentalLattice
  have hanti :
      scaleTruncation q N (J.fundamentalScaleOrder i) ≤
        scaleTruncation q N (H.fundamentalScaleOrder j) :=
    Lattice.scaleTruncation_anti (q := q) (L := N) hscale
  intro x hx
  exact D.scaleTruncation_small_le_large _ hbound (hanti hx)

/-- Lemma 5.16 at a scale represented simultaneously by Jordan components
of the small and large lattices, expressed as a fundamental-weight-order
inequality. -/
theorem largeFundamentalWeightOrder_le_small
    (D : Beli2019Lemma51Data q M N)
    {s t : Nat} {J : Lattice.JordanDecomposition q N s}
    {H : Lattice.JordanDecomposition q M t} (i : Fin s) (j : Fin t)
    (hscale : J.fundamentalScaleOrder i = H.fundamentalScaleOrder j)
    (hbound : J.fundamentalScaleOrder i ≤
      ordUnit K D.input.block.enlargedScaleGenerator) :
    H.fundamentalWeightOrder j ≤ J.fundamentalWeightOrder i := by
  apply Lattice.JordanDecomposition.fundamentalWeightOrder_anti_of_fundamentalLattice_le
    (J := J) (H := H) i j
  apply Lattice.JordanDecomposition.fundamentalLattice_le_of_scaleTruncation_le
    (J := J) (H := H) i j hscale
  exact D.scaleTruncation_small_le_large _ hbound

/-- The form needed at the selected binary component: the intrinsic small
lattice may be taken at a later (larger) truncation scale.  The containment
is the chain `N^smallScale ≤ N^largeScale ≤ M^largeScale`. -/
theorem largeFundamentalWeightOrder_le_small_of_scale_le
    (D : Beli2019Lemma51Data q M N)
    {s t : Nat} {J : Lattice.JordanDecomposition q N s}
    {H : Lattice.JordanDecomposition q M t} (i : Fin s) (j : Fin t)
    (hscale : H.fundamentalScaleOrder j ≤ J.fundamentalScaleOrder i)
    (hbound : H.fundamentalScaleOrder j ≤
      ordUnit K D.input.block.enlargedScaleGenerator) :
    H.fundamentalWeightOrder j ≤ J.fundamentalWeightOrder i := by
  apply Lattice.JordanDecomposition.fundamentalWeightOrder_anti_of_fundamentalLattice_le
    (J := J) (H := H) i j
  exact D.smallFundamentalLattice_le_large_of_scale_le i j hscale hbound

/-- Internal-coordinate branch of Beli (2019), Lemma 5.17(i).  At an
internal good-BONG boundary, Beli (2009), Lemma 2.16(i), identifies
`R_i + alpha_i` with the fundamental weight order.  Lemma 5.16 and
O'Meara 93:25 compare those weight orders, so equality of `R_i` and `S_i`
leaves precisely `alpha_i ≤ beta_i`. -/
theorem alphaValue_le_of_internal_coordinates
    (D : Beli2019Lemma51Data q M N)
    {n s t : Nat} (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    {J : Lattice.JordanDecomposition q N s}
    {H : Lattice.JordanDecomposition q M t}
    (Psmall : BONG.JordanOrderProfileWitness b.toBONG J)
    (Plarge : BONG.JordanOrderProfileWitness a.toBONG H)
    (i : Fin n)
    (hsmallInternal : (Psmall.indexEquiv i.castSucc).2.val + 1 <
      J.componentRank (Psmall.indexEquiv i.castSucc).1)
    (hlargeInternal : (Plarge.indexEquiv i.castSucc).2.val + 1 <
      H.componentRank (Plarge.indexEquiv i.castSucc).1)
    (hscale :
      H.fundamentalScaleOrder (Plarge.indexEquiv i.castSucc).1 ≤
        J.fundamentalScaleOrder (Psmall.indexEquiv i.castSucc).1)
    (hbound :
      H.fundamentalScaleOrder (Plarge.indexEquiv i.castSucc).1 ≤
        ordUnit K D.input.block.enlargedScaleGenerator)
    (hcurrent : a.order i.castSucc = b.order i.castSucc) :
    a.alphaValue i ≤ b.alphaValue i := by
  have hweight := D.largeFundamentalWeightOrder_le_small_of_scale_le
    (J := J) (H := H)
    (Psmall.indexEquiv i.castSucc).1
    (Plarge.indexEquiv i.castSucc).1 hscale hbound
  have hlargeFormula :=
    Plarge.internal_weightOrder_eq_order_add_alpha i hlargeInternal
  have hsmallFormula :=
    Psmall.internal_weightOrder_eq_order_add_alpha i hsmallInternal
  have hweightQ :
      (H.fundamentalWeightOrder
          (Plarge.indexEquiv i.castSucc).1 : ℚ) ≤
        (J.fundamentalWeightOrder
          (Psmall.indexEquiv i.castSucc).1 : ℚ) := by
    exact_mod_cast hweight
  have hcurrentQ : (a.order i.castSucc : ℚ) =
      (b.order i.castSucc : ℚ) := by
    exact_mod_cast hcurrent
  linarith

end Lattice.Beli2019Lemma51Data

namespace BONG

/-- Boundary-coordinate comparison isolated from the geometric proof of
Lemma 5.17.  Beli (2009), Lemma 2.16(ii), writes both alphas as minima.
Containment of the small fundamental ideal in the large one reverses their
valuation orders, while the second hypothesis compares the half-gap terms. -/
theorem alphaValue_le_of_boundary_fundamentalIdeal_le
    {n t : Nat} (a : GoodBONG q M (n + 2))
    (b : GoodBONG q N (n + 2))
    {J : Lattice.JordanDecomposition q N (t + 1)}
    {H : Lattice.JordanDecomposition q M (t + 1)}
    (Psmall : JordanOrderProfileWitness b.toBONG J)
    (Plarge : JordanOrderProfileWitness a.toBONG H)
    (z : Fin t)
    (hideal : J.fundamentalIdeal z ≤ H.fundamentalIdeal z)
    (hhalf : a.halfGapValue (Plarge.boundaryIndex z) ≤
      b.halfGapValue (Psmall.boundaryIndex z)) :
    a.alphaValue (Plarge.boundaryIndex z) ≤
      b.alphaValue (Psmall.boundaryIndex z) := by
  obtain ⟨Ilarge, hlargeCarrier, hlargeFormula⟩ :=
    Plarge.exists_orderedFundamentalIdeal_alpha_eq_min z
  obtain ⟨Ismall, hsmallCarrier, hsmallFormula⟩ :=
    Psmall.exists_orderedFundamentalIdeal_alpha_eq_min z
  have hcarrier : Ismall.carrier ≤ Ilarge.carrier := by
    rw [hsmallCarrier, hlargeCarrier]
    exact hideal
  have horder : Ilarge.order ≤ Ismall.order := by
    rw [Ilarge.carrier_eq_powerIdeal, Ismall.carrier_eq_powerIdeal,
      Lattice.powerIdeal_le_iff] at hcarrier
    exact hcarrier
  have horderQ : (Ilarge.order : ℚ) ≤ (Ismall.order : ℚ) := by
    exact_mod_cast horder
  calc
    a.alphaValue (Plarge.boundaryIndex z) =
        min (Ilarge.order : ℚ)
          (a.halfGapValue (Plarge.boundaryIndex z)) := hlargeFormula
    _ ≤ min (Ismall.order : ℚ)
          (b.halfGapValue (Psmall.boundaryIndex z)) :=
      min_le_min horderQ hhalf
    _ = b.alphaValue (Psmall.boundaryIndex z) := hsmallFormula.symm

/-- Heterogeneous-index form of the boundary comparison.  The two strict
Jordan decompositions may have different component counts because only one
side may have amalgamated an equal-scale adjacent pair. -/
theorem alphaValue_le_of_boundary_fundamentalIdeal_le_at
    {n s t : Nat} (a : GoodBONG q M (n + 2))
    (b : GoodBONG q N (n + 2))
    {J : Lattice.JordanDecomposition q N (s + 1)}
    {H : Lattice.JordanDecomposition q M (t + 1)}
    (Psmall : JordanOrderProfileWitness b.toBONG J)
    (Plarge : JordanOrderProfileWitness a.toBONG H)
    (zSmall : Fin s) (zLarge : Fin t)
    (hideal : J.fundamentalIdeal zSmall ≤ H.fundamentalIdeal zLarge)
    (hhalf : a.halfGapValue (Plarge.boundaryIndex zLarge) ≤
      b.halfGapValue (Psmall.boundaryIndex zSmall)) :
    a.alphaValue (Plarge.boundaryIndex zLarge) ≤
      b.alphaValue (Psmall.boundaryIndex zSmall) := by
  obtain ⟨Ilarge, hlargeCarrier, hlargeFormula⟩ :=
    Plarge.exists_orderedFundamentalIdeal_alpha_eq_min zLarge
  obtain ⟨Ismall, hsmallCarrier, hsmallFormula⟩ :=
    Psmall.exists_orderedFundamentalIdeal_alpha_eq_min zSmall
  have hcarrier : Ismall.carrier ≤ Ilarge.carrier := by
    rw [hsmallCarrier, hlargeCarrier]
    exact hideal
  have horder : Ilarge.order ≤ Ismall.order := by
    rw [Ilarge.carrier_eq_powerIdeal, Ismall.carrier_eq_powerIdeal,
      Lattice.powerIdeal_le_iff] at hcarrier
    exact hcarrier
  have horderQ : (Ilarge.order : ℚ) ≤ (Ismall.order : ℚ) := by
    exact_mod_cast horder
  calc
    a.alphaValue (Plarge.boundaryIndex zLarge) =
        min (Ilarge.order : ℚ)
          (a.halfGapValue (Plarge.boundaryIndex zLarge)) := hlargeFormula
    _ ≤ min (Ismall.order : ℚ)
          (b.halfGapValue (Psmall.boundaryIndex zSmall)) :=
      min_le_min horderQ hhalf
    _ = b.alphaValue (Psmall.boundaryIndex zSmall) := hsmallFormula.symm

end BONG

end Bong
