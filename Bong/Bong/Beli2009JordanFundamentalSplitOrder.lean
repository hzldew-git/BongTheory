/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanFundamentalLayerFormula

/-!
# The unreduced order formula for a noninitial fundamental layer

This file isolates the common geometric part of Beli (2009), Lemmas 2.15
and 2.16.  At a noninitial strict Jordan component, the fundamental layer is
the orthogonal product of the exact suffix and the scale-rescaled dual of the
exact prefix.  Lemma 2.11 therefore expresses its weight order as the minimum
of the two component weights and one adjacent quadratic-defect term.

Unlike the later non-unary formula, no descending first pair is assumed.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}

namespace BONG.StrictJordanAdaptedAlignment

variable {a : GoodBONG q L (m + 1)}
  {b : GoodBONG r M (m + 1)}

private theorem splitOrder_mul_square_inv_identity (x c y : Kˣ) :
    x * c ^ 2 * y⁻¹ = y * x * (c * y⁻¹) ^ 2 := by
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

set_option maxHeartbeats 5000000 in
-- The proof expands the actual prefix/suffix isometry and applies Lemma 2.11.
/-- The unreduced weight-order formula for an arbitrary noninitial
fundamental layer.  The two component terms are the actual suffix weight and
the actual scale-rescaled dual-prefix weight; the final term is the adjacent
defect at the cut. -/
theorem sourceFundamentalWeightOrder_eq_min_split
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k))) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    let P := D.prefixQuadraticSublattice k.val
    let U := D.suffixQuadraticSublattice k.val
    let c := Lattice.scaleTruncationUnit (K := K)
      (ordUnit K (S.sourceJordan.scaleGenerator k))
    let j : Fin m := ⟨S.componentStart k - 1, by
      have hprefix : 0 < S.componentStart k := by
        unfold componentStart
        let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
        have hp : p ∈ Finset.Iio k := by
          simp only [Finset.mem_Iio]
          change k.val - 1 < k.val
          omega
        have hle := Finset.single_le_sum
          (s := Finset.Iio k)
          (f := fun z ↦
            S.sourceJordan.toOrthogonalDecomposition.componentRank z)
          (fun _ _ ↦ Nat.zero_le _) hp
        exact (S.sourceJordan.component_finrank_pos p).trans_le hle
      have hbound : S.componentStart k < m + 1 :=
        (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)
      omega⟩
    ((((Lattice.weightIdealOrder q
        (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) : WithTop ℚ)) =
      min
        (min
          ((((Lattice.weightIdealOrder U.space U.lattice : Int) : ℚ) :
            WithTop ℚ))
          ((((Lattice.weightIdealOrder P.space
              (Lattice.rescale c
                (Lattice.dualLattice P.space P.lattice)) : Int) : ℚ) :
            WithTop ℚ)))
        (((((2 * ordUnit K (S.sourceJordan.scaleGenerator k) -
              a.order j.castSucc : Int) : ℚ) : WithTop ℚ)) +
          a.adjacentDefect j) := by
  have hmpos : 0 < m := by
    have hbound : S.componentStart k < m + 1 :=
      (S.componentStart_lt_componentStop k).trans_le
        (S.componentStop_le k)
    have hstartPos : 0 < S.componentStart k := by
      unfold componentStart
      let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
      have hp : p ∈ Finset.Iio k := by
        simp only [Finset.mem_Iio]
        change k.val - 1 < k.val
        omega
      have hle := Finset.single_le_sum
        (s := Finset.Iio k)
        (f := fun z ↦
          S.sourceJordan.toOrthogonalDecomposition.componentRank z)
        (fun _ _ ↦ Nat.zero_le _) hp
      exact (S.sourceJordan.component_finrank_pos p).trans_le hle
    omega
  let D := S.sourceJordan.toOrthogonalDecomposition
  let P := D.prefixQuadraticSublattice k.val
  let U := D.suffixQuadraticSublattice k.val
  letI : Module.Finite K U.carrier := U.lattice.moduleFinite
  letI : Module.Finite K P.carrier := P.lattice.moduleFinite
  let c := Lattice.scaleTruncationUnit (K := K)
    (ordUnit K (S.sourceJordan.scaleGenerator k))
  let f := S.sourceFundamentalLayerSwappedIsometry k hk
  have hprefixStart : 0 < S.componentStart k := by
    unfold componentStart
    let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hp : p ∈ Finset.Iio k := by
      simp only [Finset.mem_Iio]
      change k.val - 1 < k.val
      omega
    have hle := Finset.single_le_sum
      (s := Finset.Iio k)
      (f := fun z ↦
        S.sourceJordan.toOrthogonalDecomposition.componentRank z)
      (fun _ _ ↦ Nat.zero_le _) hp
    exact (S.sourceJordan.component_finrank_pos p).trans_le hle
  let j : Fin m := ⟨S.componentStart k - 1, by
    have hbound : S.componentStart k < m + 1 :=
      (S.componentStart_lt_componentStop k).trans_le
        (S.componentStop_le k)
    omega⟩
  have hambient0 :=
    S.toStrictJordanEndpointAlignment.sourceFirstGenerator_fundamentalLattice k
  change Lattice.IsNormGeneratorValue q
      (S.sourceJordan.fundamentalLattice k)
      (S.weakAlignment.endpoint.sourceEndpoints.profile.endpointFirstValue k)
    at hambient0
  rw [S.sourceEndpointFirstValue_eq_componentStart k] at hambient0
  have hsuffixLengthPos : 0 < m + 1 - S.componentStart k := by
    have hbound : S.componentStart k < m + 1 :=
      (S.componentStart_lt_componentStop k).trans_le
        (S.componentStop_le k)
    omega
  obtain ⟨tail, htail⟩ : ∃ tail, tail + 1 =
      m + 1 - S.componentStart k :=
    ⟨m + 1 - S.componentStart k - 1, by omega⟩
  let suffix := (S.sourceSuffixGoodBONG k hk T).castLength htail.symm
  have hsuffixGen :=
    suffix.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have hsuffixValue : suffix.valueUnit 0 =
      a.valueUnit ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ := by
    rw [show suffix =
        (S.sourceSuffixGoodBONG k hk T).castLength htail.symm by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    simpa using S.sourceSuffixGoodBONG_valueUnit k hk T
      (⟨0, hsuffixLengthPos⟩ : Fin (m + 1 - S.componentStart k))
  change Lattice.IsNormGeneratorValue U.space U.lattice
      (suffix.valueUnit 0) at hsuffixGen
  rw [hsuffixValue] at hsuffixGen
  have hsuffixRankPos : 0 < Module.finrank K U.carrier := by
    have hlen := (S.sourceSuffixGoodBONG k hk T).toBONG.length_eq_finrank
    have hlen' : m + 1 - S.componentStart k =
        Module.finrank K U.carrier := by
      simpa only [D, U] using hlen
    have hstop := S.componentStop_le k
    have hstart := S.componentStart_lt_componentStop k
    omega
  have hprefixRankPos : 0 < Module.finrank K P.carrier := by
    have hlen := (S.sourcePrefixGoodBONG k hk T).toBONG.length_eq_finrank
    have hlen' : S.componentStart k = Module.finrank K P.carrier := by
      simpa only [D, P] using hlen
    omega
  have htwoProductFundamental :
      Lattice.twoScaleIdeal (U.space.orthogonalSum P.space)
          (Lattice.product U.lattice
            (Lattice.rescale c (Lattice.dualLattice P.space P.lattice))) =
        Lattice.twoScaleIdeal q
          (S.sourceJordan.fundamentalLattice k) := by
    unfold Lattice.twoScaleIdeal
    calc
      Lattice.twiceIdeal
          (Lattice.scaleIdeal (U.space.orthogonalSum P.space)
            (Lattice.product U.lattice
              (Lattice.rescale c
                (Lattice.dualLattice P.space P.lattice)))) =
          Lattice.twiceIdeal
            (Lattice.scaleIdeal q
              (Lattice.map f.toLinearEquiv
                (Lattice.product U.lattice
                  (Lattice.rescale c
                    (Lattice.dualLattice P.space P.lattice))))) := by
        congr 1
        exact (Lattice.scaleIdeal_map_isometry
          f.toQuadraticSpaceIsometry
          (Lattice.product U.lattice
            (Lattice.rescale c
              (Lattice.dualLattice P.space P.lattice)))).symm
      _ = Lattice.twiceIdeal
          (Lattice.scaleIdeal q
            (S.sourceJordan.fundamentalLattice k)) := by
        rw [f.map_eq]
  have htwo : Lattice.twoScaleIdeal
      (U.space.orthogonalSum P.space)
      (Lattice.product U.lattice
        (Lattice.rescale c (Lattice.dualLattice P.space P.lattice))) ≤
      Lattice.weightIdeal
        (Lattice.orthogonalProductLeftComponent
          U.space P.space U.lattice).space
        (Lattice.orthogonalProductLeftComponent
          U.space P.space U.lattice).lattice := by
    rw [htwoProductFundamental,
      S.sourceFundamentalTwoScaleIdeal_eq_suffix k]
    have hweight := Lattice.weightIdeal_eq_of_isometry
      (Lattice.orthogonalProductLeftComponentIsometry
        U.space P.space U.lattice) hsuffixRankPos
    rw [hweight]
    exact Lattice.twoScaleIdeal_le_weightIdeal U.space U.lattice
  obtain ⟨ell, hell⟩ : ∃ ell, ell + 1 = S.componentStart k :=
    ⟨S.componentStart k - 1, by omega⟩
  let prefixBong := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
  rcases prefixBong.beli2009Remark26_duality with
    ⟨dual, _hvectors, hvalues, _hdualOrders, _halphas⟩
  have hdualGen :=
    dual.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have hdualScaled := hdualGen.rescaleQuadraticUnit (c ^ 2)
  have hdualRescaled := hdualScaled.mapLatticeIsometry
    (Lattice.scalarMultiplicationRescaleLatticeIsometry
      P.space (Lattice.dualLattice P.space P.lattice) c)
  let a0 : Kˣ := -(a.valueUnit ⟨S.componentStart k, by
    have hstop := S.componentStop_le k
    have hstart := S.componentStart_lt_componentStop k
    omega⟩)
  let d0 : Kˣ := (c ^ 2) * dual.valueUnit 0
  change Lattice.IsNormGeneratorValue P.space
    (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) d0
      at hdualRescaled
  have hambient : Lattice.IsNormGeneratorValue
      (U.space.orthogonalSum P.space)
      (Lattice.product U.lattice
        (Lattice.rescale c (Lattice.dualLattice P.space P.lattice))) a0 := by
    exact hambient0.neg.mapLatticeIsometry f.symm
  have huniform := weightIdealOrder_of_orthogonalProductIsometry
    f a0 d0 hambient (by simpa only [a0] using hsuffixGen.neg)
    hdualRescaled htwo hsuffixRankPos hprefixRankPos
  have hrevZero : Fin.rev (0 : Fin (ell + 1)) = Fin.last ell := by
    apply Fin.ext
    simp [Fin.rev]
  have hprefixLastValue : prefixBong.valueUnit (Fin.last ell) =
      a.valueUnit j.castSucc := by
    rw [show prefixBong =
        (S.sourcePrefixGoodBONG k hk T).castLength hell.symm by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    have hlocal : (⟨(Fin.last ell).val, by omega⟩ :
        Fin (S.componentStart k)) = ⟨ell, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hlocal]
    have h := S.sourcePrefixGoodBONG_valueUnit k hk T
      (⟨ell, by omega⟩ : Fin (S.componentStart k))
    rw [h]
    apply congrArg a.valueUnit
    apply Fin.ext
    change ell = S.componentStart k - 1
    omega
  have hdualValueZero : dual.valueUnit 0 =
      (prefixBong.valueUnit (Fin.last ell))⁻¹ := by
    apply Units.ext
    have h := hvalues 0
    rw [hrevZero] at h
    exact h
  have hd0 : d0 = (c ^ 2) * (a.valueUnit j.castSucc)⁻¹ := by
    dsimp only [d0]
    rw [hdualValueZero, hprefixLastValue]
  have hstartIndex : j.succ =
      ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ := by
    apply Fin.ext
    change S.componentStart k - 1 + 1 = S.componentStart k
    omega
  have hcrossUnit : a0 * d0 =
      a.adjacentProduct j * (c * (a.valueUnit j.castSucc)⁻¹) ^ 2 := by
    rw [hd0]
    unfold a0 GoodBONG.adjacentProduct
    rw [hstartIndex]
    simp only [neg_mul]
    apply neg_injective
    simpa only [neg_neg, mul_assoc] using
      splitOrder_mul_square_inv_identity
        (a.valueUnit ⟨S.componentStart k, by
          have hstop := S.componentStop_le k
          have hstart := S.componentStart_lt_componentStop k
          omega⟩) c (a.valueUnit j.castSucc)
  have hcrossDefect : GoodBONG.defectOrder (K := K) (a0 * d0) =
      a.adjacentDefect j := by
    unfold GoodBONG.adjacentDefect GoodBONG.defectOrder
    rw [hcrossUnit, quadraticDefect_mul_square]
  have hcOrder : ordUnit K c =
      ordUnit K (S.sourceJordan.scaleGenerator k) := by
    dsimp only [c]
    rw [Lattice.scaleTruncationUnit, ordUnit_uniformizerPowerUnit]
  have hd0Order : ordUnit K d0 =
      2 * ordUnit K (S.sourceJordan.scaleGenerator k) -
        a.order j.castSucc := by
    rw [hd0, ordUnit_mul, ordUnit_pow]
    change 2 * ordUnit K c + ordUnit K ((a.valueUnit j.castSucc)⁻¹) = _
    rw [hcOrder, ordUnit_inv]
    change 2 * ordUnit K (S.sourceJordan.scaleGenerator k) +
      -ordUnit K (a.toBONG.valueUnit j.castSucc) = _
    rw [← a.toBONG.order_eq_ordUnit]
    change 2 * ordUnit K (S.sourceJordan.scaleGenerator k) +
      -a.order j.castSucc = _
    ring
  rw [hcrossDefect] at huniform
  have hd0OrderTop := congrArg
    (fun z : Int ↦ (((z : Int) : ℚ) : WithTop ℚ)) hd0Order
  norm_cast at hd0OrderTop
  rw [hd0OrderTop] at huniform
  simpa only [D, P, U, c, j] using huniform

end BONG.StrictJordanAdaptedAlignment

end Bong
