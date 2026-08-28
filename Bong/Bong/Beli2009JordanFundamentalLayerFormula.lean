/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanFundamentalWeight
import Bong.Bong.Beli2009AlphaParityProof
import Bong.Bong.StructuralProof
import Bong.Lattice.JordanSuffixScale

/-!
# Beli (2009), the noninitial fundamental-weight formula

This file proves the missing noninitial branch of Lemma 2.16(i) directly
from the orthogonal splitting of the fundamental lattice, Remark 2.6, and
the segment-recursive formula of Corollary 2.5(ii).  In particular, no
`Beli2009JordanAlphaLaws` parameter is used.
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

private theorem fundamentalLayer_mul_square_inv_identity (x c y : Kˣ) :
    x * c ^ 2 * y⁻¹ = y * x * (c * y⁻¹) ^ 2 := by
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

theorem weightIdealOrder_dual_goodBONG_unary
    {X : Type*} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    (c : GoodBONG s N 1) :
    Lattice.weightIdealOrder s (Lattice.dualLattice s N) =
      -c.order 0 + ramificationIndex K := by
  rcases c.beli2009Remark26_duality with ⟨d, _, _, horders, _⟩
  have h := d.weightIdealOrder_unary_proof
  rw [horders 0] at h
  simpa using h

theorem weightIdealOrder_dual_goodBONG
    {X : Type*} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    {p : Nat} (c : GoodBONG s N (p + 2)) :
    (Lattice.weightIdealOrder s (Lattice.dualLattice s N) : ℚ) =
      min
        (-(c.order ⟨p + 1, by omega⟩ : ℚ) +
          c.alphaValue ⟨p, by omega⟩)
        (-(c.order ⟨p + 1, by omega⟩ : ℚ) +
          (ramificationIndex K : ℚ)) := by
  rcases c.beli2009Remark26_duality with ⟨d, _, _, horders, halphas⟩
  have h := d.lemma214_weightIdealOrder_all
  have hrevOrder : Fin.rev (0 : Fin (p + 2)) = ⟨p + 1, by omega⟩ := by
    apply Fin.ext
    simp [Fin.rev]
  have hrevAlpha : Fin.rev (0 : Fin (p + 1)) = ⟨p, by omega⟩ := by
    apply Fin.ext
    simp [Fin.rev]
  rw [horders 0, halphas 0, hrevOrder, hrevAlpha] at h
  simpa using h

theorem alphaValue_last_eq_min_prefixCandidates
    {X : Type*} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    {p : Nat} (c : GoodBONG s N (p + 3)) :
    let i : Fin (p + 2) := ⟨p + 1, by omega⟩
    (c.alphaValue i : WithTop ℚ) =
      min (c.halfGapCandidate i)
        (min (c.leftDefectCandidate i i)
          (c.prefixSegmentAlphaCandidate i (by
            change 0 < p + 1
            omega))) := by
  let i : Fin (p + 2) := ⟨p + 1, by omega⟩
  dsimp only
  rw [c.coe_alphaValue, c.beli2009Corollary25_ii i]
  simp [GoodBONG.segmentRecursiveAlphaCandidates,
    GoodBONG.prefixSegmentAlphaCandidates,
    GoodBONG.suffixSegmentAlphaCandidates, i,
    min_assoc, min_left_comm, min_comm]

theorem prefixSegmentAlphaCandidate_last_eq_gap_add_alpha
    {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {z : QuadraticSpace K Y}
    {N : Lattice K X} {P : Lattice K Y}
    {p : Nat} (c : GoodBONG s N (p + 3))
    (d : GoodBONG z P (p + 2))
    (hvalues : ∀ j, d.valueUnit j = c.valueUnit j.castSucc) :
    let i : Fin (p + 2) := ⟨p + 1, by omega⟩
    c.prefixSegmentAlphaCandidate i (by
        change 0 < p + 1
        omega) =
      ((c.orderGap i : ℚ) + d.alphaValue ⟨p, by omega⟩ : ℚ) := by
  let i : Fin (p + 2) := ⟨p + 1, by omega⟩
  let loc := GoodBONG.prefixAlphaLocalizationIndex i (by
    change 0 < p + 1
    omega)
  let e := (c.prefixAlphaSegmentWitness i (by
    change 0 < p + 1
    omega)).toGoodBONG c.good
  have hAlphaLen : loc.stop - loc.start = p + 1 := by
    dsimp [loc, GoodBONG.prefixAlphaLocalizationIndex, i]
  let hValLen : loc.length = p + 2 :=
    congrArg (fun z : Nat ↦ z + 1) hAlphaLen
  let e' := e.castLength hValLen
  have hevalues : ∀ j, e'.valueUnit j = c.valueUnit j.castSucc := by
    intro j
    rw [show e' = e.castLength hValLen by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    change (c.prefixAlphaSegmentWitness i _).bong.valueUnit _ = _
    rw [(c.prefixAlphaSegmentWitness i _).valueUnit_eq]
    apply congrArg c.valueUnit
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex, loc,
      GoodBONG.prefixAlphaLocalizationIndex, i]
  have heqValues : ∀ j, e'.valueUnit j = d.valueUnit j := by
    intro j
    exact (hevalues j).trans (hvalues j).symm
  have halpha := e'.alphaValue_eq_of_valueUnits_eq d heqValues
    ⟨p, by omega⟩
  have hlocal : Fin.cast hAlphaLen.symm ⟨p, by omega⟩ = loc.localPivot := by
    apply Fin.ext
    dsimp [loc, GoodBONG.prefixAlphaLocalizationIndex, i,
      AlphaLocalizationIndex.localPivot]
  have hcastAlpha := GoodBONG.alphaValue_castLength_fundamental
    e hAlphaLen ⟨p, by omega⟩
  have halphaLocal : e.alphaValue loc.localPivot =
      d.alphaValue ⟨p, by omega⟩ := by
    rw [← hlocal]
    exact hcastAlpha.symm.trans halpha
  have hbase := c.prefixSegmentAlphaCandidate_eq_gap_add_alpha i (by
    change 0 < p + 1
    omega)
  dsimp only
  rw [hbase]
  norm_cast
  simpa only [i, e, loc] using
    congrArg (fun z : ℚ ↦ (c.orderGap i : ℚ) + z) halphaLocal

theorem sourceEndpointFirstValue_eq_componentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.weakAlignment.endpoint.sourceEndpoints.profile.endpointFirstValue k =
      a.valueUnit ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ := by
  unfold WeakJordanOrderProfileWitness.endpointFirstValue
    Lattice.WeakJordanDecomposition.endpointFirstIndex
  apply congrArg a.valueUnit
  apply Fin.ext
  change (S.sourceProfile.indexEquiv.symm
    ⟨k, ⟨0, S.sourceJordan.component_finrank_pos k⟩⟩).val = _
  rw [S.sourceProfile.inverse_index_val]
  rfl

@[simp]
theorem sourcePrefixGoodBONG_valueUnit
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (i : Fin (S.componentStart k)) :
    (S.sourcePrefixGoodBONG k hk T).valueUnit i =
      a.valueUnit ⟨i.val, by
        have hi := i.isLt
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ := by
  unfold sourcePrefixGoodBONG
  rw [GoodBONG.valueUnit_mapLatticeIsometry]
  change T.left.bong.valueUnit i = a.toBONG.valueUnit _
  rw [T.left.valueUnit_eq]
  apply congrArg a.toBONG.valueUnit
  apply Fin.ext
  simp [BONG.SegmentWitness.sourceIndex]

@[simp]
theorem sourceSuffixGoodBONG_valueUnit
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (i : Fin (m + 1 - S.componentStart k)) :
    (S.sourceSuffixGoodBONG k hk T).valueUnit i =
      a.valueUnit ⟨S.componentStart k + i.val, by omega⟩ := by
  unfold sourceSuffixGoodBONG
  rw [GoodBONG.valueUnit_mapLatticeIsometry]
  change T.right.bong.valueUnit i = a.toBONG.valueUnit _
  rw [T.right.valueUnit_eq]
  apply congrArg a.toBONG.valueUnit
  apply Fin.ext
  simp [BONG.SegmentWitness.sourceIndex]

/-- Lemma 2.14 on the actual Jordan suffix, without assuming that its first
component is non-unary.  The capped `e` term is essential when the first
suffix component has rank one. -/
theorem sourceSuffix_weightIdealOrder_general
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (p : Nat) (hp : p + 2 = m + 1 - S.componentStart k) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    let U := D.suffixQuadraticSublattice k.val
    let suffix := (S.sourceSuffixGoodBONG k hk T).castLength hp.symm
    (Lattice.weightIdealOrder U.space U.lattice : ℚ) =
      min
        ((a.order ⟨S.componentStart k, by
            have hstop := S.componentStop_le k
            have hstart := S.componentStart_lt_componentStop k
            omega⟩ : ℚ) + suffix.alphaValue 0)
        ((a.order ⟨S.componentStart k, by
            have hstop := S.componentStop_le k
            have hstart := S.componentStart_lt_componentStop k
            omega⟩ : ℚ) + (ramificationIndex K : ℚ)) := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let U := D.suffixQuadraticSublattice k.val
  let suffix := (S.sourceSuffixGoodBONG k hk T).castLength hp.symm
  have hformula := suffix.lemma214_weightIdealOrder_all
  have horder0 : suffix.order 0 =
      a.order ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ := by
    rw [show suffix =
        (S.sourceSuffixGoodBONG k hk T).castLength hp.symm by rfl,
      GoodBONG.order_castLength]
    change (S.sourceSuffixGoodBONG k hk T).order ⟨0, by omega⟩ =
      a.order _
    have h := S.sourceSuffixGoodBONG_order k hk T ⟨0, by omega⟩
    change (S.sourceSuffixGoodBONG k hk T).order ⟨0, by omega⟩ =
      a.order ⟨S.componentStart k + 0, by omega⟩ at h
    simpa only [Nat.add_zero] using h
  rw [horder0] at hformula
  simpa only [D, U, suffix] using hformula

theorem sourceSuffix_weightIdealOrder
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hrank : 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank k)
    (p : Nat) (hp : p + 2 = m + 1 - S.componentStart k) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    let U := D.suffixQuadraticSublattice k.val
    (Lattice.weightIdealOrder U.space U.lattice : ℚ) =
      (a.order ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ : ℚ) +
        ((S.sourceSuffixGoodBONG k hk T).castLength hp.symm).alphaValue 0 := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let U := D.suffixQuadraticSublattice k.val
  let c := S.sourceSuffixGoodBONG k hk T
  have hlen : 2 ≤ m + 1 - S.componentStart k := by
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    omega
  let c' := c.castLength hp.symm
  have hformula := c'.lemma214_weightIdealOrder_all
  have horder0 : c'.order 0 =
      a.order ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ := by
    rw [show c' = c.castLength hp.symm by rfl,
      GoodBONG.order_castLength]
    change c.order ⟨0, by omega⟩ = a.order _
    have h := S.sourceSuffixGoodBONG_order k hk T ⟨0, by omega⟩
    change c.order ⟨0, by omega⟩ =
      a.order ⟨S.componentStart k + 0, by omega⟩ at h
    calc
      c.order ⟨0, by omega⟩ =
          a.order ⟨S.componentStart k + 0, by omega⟩ := h
      _ = a.order ⟨S.componentStart k, by omega⟩ := by congr 1
  have horder1 : c'.order 1 =
      a.order ⟨S.componentStart k + 1, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        omega⟩ := by
    rw [show c' = c.castLength hp.symm by rfl,
      GoodBONG.order_castLength]
    change c.order ⟨1, by omega⟩ = a.order _
    have h := S.sourceSuffixGoodBONG_order k hk T ⟨1, by omega⟩
    change c.order ⟨1, by omega⟩ =
      a.order ⟨S.componentStart k + 1, by omega⟩ at h
    exact h
  have hdescending : c'.order 1 ≤ c'.order 0 := by
    rw [horder1, horder0]
    exact S.source_component_head_descending k hrank
  have halpha : c'.alphaValue 0 ≤ (ramificationIndex K : ℚ) := by
    have h := c'.alphaValue_le_halfGapValue 0
    unfold GoodBONG.halfGapValue GoodBONG.orderGap at h
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h
    push_cast at h
    have hdQ : (c'.order 1 : ℚ) ≤ c'.order 0 := by exact_mod_cast hdescending
    linarith
  have hmin : min
      ((c'.order 0 : ℚ) + c'.alphaValue 0)
      ((c'.order 0 : ℚ) + (ramificationIndex K : ℚ)) =
      (c'.order 0 : ℚ) + c'.alphaValue 0 := by
    apply min_eq_left
    linarith
  rw [hmin] at hformula
  simpa only [D, U, c, c', horder0] using hformula

set_option maxHeartbeats 2000000 in
theorem sourceFundamentalTwoScaleIdeal_eq_suffix
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    let U := D.suffixQuadraticSublattice k.val
    Lattice.twoScaleIdeal q (S.sourceJordan.fundamentalLattice k) =
      Lattice.twoScaleIdeal U.space U.lattice := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let U := D.suffixQuadraticSublattice k.val
  let tailCount := S.componentCount - k.val - 1
  have hcount : k.val + (tailCount + 1) = S.componentCount := by
    dsimp only [tailCount]
    omega
  rw [S.sourceJordan.fundamentalTwoScaleIdeal_eq_powerIdeal k]
  dsimp only [D, U]
  unfold Lattice.twoScaleIdeal
  rw [S.sourceJordan.scaleIdeal_suffixQuadraticSublattice hcount,
    Lattice.twiceIdeal_principalIdeal]
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let z : Kˣ := two *
    S.sourceJordan.scaleGenerator ⟨k.val, by omega⟩
  have htwo : (two : K) = 2 := rfl
  have hz : (2 : K) *
      (S.sourceJordan.scaleGenerator ⟨k.val, by omega⟩ : K) =
      (z : K) := by
    simp [z, htwo]
  rw [hz, Lattice.principalIdeal_eq_powerIdeal]
  congr 1
  have htwoOrder : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, htwo, ← ramificationIndex_spec]
  dsimp only [z]
  rw [ordUnit_mul, htwoOrder]
  unfold Lattice.JordanDecomposition.fundamentalScaleOrder
  simpa only [Int.add_comm]

private theorem orthogonalProduct_component_zero_normGenerator
    {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {z : QuadraticSpace K Y}
    {N : Lattice K X} {P0 : Lattice K Y} {x : Kˣ}
    (hx : Lattice.IsNormGeneratorValue s N x) :
    Lattice.IsNormGeneratorValue
      ((Lattice.orthogonalProductDecomposition s z N P0).component 0).space
      ((Lattice.orthogonalProductDecomposition s z N P0).component 0).lattice
      x := by
  change Lattice.IsNormGeneratorValue
    (Lattice.orthogonalProductLeftComponent s z N).space
    (Lattice.orthogonalProductLeftComponent s z N).lattice x
  exact hx.mapLatticeIsometry
    (Lattice.orthogonalProductLeftComponentIsometry s z N)

private theorem orthogonalProduct_component_one_normGenerator
    {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {z : QuadraticSpace K Y}
    {N : Lattice K X} {P0 : Lattice K Y} {x : Kˣ}
    (hx : Lattice.IsNormGeneratorValue z P0 x) :
    Lattice.IsNormGeneratorValue
      ((Lattice.orthogonalProductDecomposition s z N P0).component 1).space
      ((Lattice.orthogonalProductDecomposition s z N P0).component 1).lattice
      x := by
  change Lattice.IsNormGeneratorValue
    (Lattice.orthogonalProductRightComponent s z P0).space
    (Lattice.orthogonalProductRightComponent s z P0).lattice x
  exact hx.mapLatticeIsometry
    (Lattice.orthogonalProductRightComponentIsometry s z P0)

private theorem orthogonalProduct_component_zero_weightOrder
    {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {z : QuadraticSpace K Y}
    {N : Lattice K X} {P0 : Lattice K Y}
    (hpos : 0 < Module.finrank K X) :
    Lattice.weightIdealOrder
        ((Lattice.orthogonalProductDecomposition s z N P0).component 0).space
        ((Lattice.orthogonalProductDecomposition s z N P0).component 0).lattice =
      Lattice.weightIdealOrder s N := by
  change Lattice.weightIdealOrder
      (Lattice.orthogonalProductLeftComponent s z N).space
      (Lattice.orthogonalProductLeftComponent s z N).lattice =
    Lattice.weightIdealOrder s N
  exact Lattice.weightIdealOrder_eq_of_isometry
    (Lattice.orthogonalProductLeftComponentIsometry s z N) hpos

private theorem orthogonalProduct_component_one_weightOrder
    {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {z : QuadraticSpace K Y}
    {N : Lattice K X} {P0 : Lattice K Y}
    (hpos : 0 < Module.finrank K Y) :
    Lattice.weightIdealOrder
        ((Lattice.orthogonalProductDecomposition s z N P0).component 1).space
        ((Lattice.orthogonalProductDecomposition s z N P0).component 1).lattice =
      Lattice.weightIdealOrder z P0 := by
  change Lattice.weightIdealOrder
      (Lattice.orthogonalProductRightComponent s z P0).space
      (Lattice.orthogonalProductRightComponent s z P0).lattice =
    Lattice.weightIdealOrder z P0
  exact Lattice.weightIdealOrder_eq_of_isometry
    (Lattice.orthogonalProductRightComponentIsometry s z P0) hpos

private theorem orthogonalProduct_twoScale_le_component_zero_weight
    {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {z : QuadraticSpace K Y}
    {N : Lattice K X} {P0 : Lattice K Y}
    (h : Lattice.twoScaleIdeal (s.orthogonalSum z)
      (Lattice.product N P0) ≤
        Lattice.weightIdeal
          (Lattice.orthogonalProductLeftComponent s z N).space
          (Lattice.orthogonalProductLeftComponent s z N).lattice) :
    Lattice.twoScaleIdeal (s.orthogonalSum z) (Lattice.product N P0) ≤
      Lattice.weightIdeal
        ((Lattice.orthogonalProductDecomposition s z N P0).component 0).space
        ((Lattice.orthogonalProductDecomposition s z N P0).component 0).lattice := by
  change Lattice.twoScaleIdeal (s.orthogonalSum z) (Lattice.product N P0) ≤
    Lattice.weightIdeal
      (Lattice.orthogonalProductLeftComponent s z N).space
      (Lattice.orthogonalProductLeftComponent s z N).lattice
  exact h

set_option maxHeartbeats 3000000 in
theorem weightIdealOrder_of_orthogonalProductIsometry
    {X Y Z : Type*}
    [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z]
    {s : QuadraticSpace K X} {z : QuadraticSpace K Y}
    {t0 : QuadraticSpace K Z}
    {N : Lattice K X} {P0 : Lattice K Y} {Q0 : Lattice K Z}
    (f0 : Lattice.Isometry (s.orthogonalSum z) t0
      (Lattice.product N P0) Q0)
    (a1 d1 : Kˣ)
    (ha : Lattice.IsNormGeneratorValue (s.orthogonalSum z)
      (Lattice.product N P0) a1)
    (hzero0 : Lattice.IsNormGeneratorValue s N a1)
    (hone0 : Lattice.IsNormGeneratorValue z P0 d1)
    (htwo0 : Lattice.twoScaleIdeal (s.orthogonalSum z)
      (Lattice.product N P0) ≤
        Lattice.weightIdeal
          (Lattice.orthogonalProductLeftComponent s z N).space
          (Lattice.orthogonalProductLeftComponent s z N).lattice)
    (hX : 0 < Module.finrank K X)
    (hY : 0 < Module.finrank K Y) :
    ((((Lattice.weightIdealOrder t0 Q0 : Int) : ℚ) : WithTop ℚ)) =
      min
        (min
          ((((Lattice.weightIdealOrder s N : Int) : ℚ) : WithTop ℚ))
          ((((Lattice.weightIdealOrder z P0 : Int) : ℚ) : WithTop ℚ)))
        (((((ordUnit K d1 : Int) : ℚ) : WithTop ℚ)) +
          GoodBONG.defectOrder (K := K) (a1 * d1)) := by
  letI : Module.Finite K X := N.moduleFinite
  letI : Module.Finite K Y := P0.moduleFinite
  have hproductRank : 0 < Module.finrank K (X × Y) := by
    rw [Module.finrank_prod]
    omega
  have hzeroProduct :=
    orthogonalProduct_component_zero_normGenerator
      (s := s) (z := z) (N := N) (P0 := P0) hzero0
  have honeProduct :=
    orthogonalProduct_component_one_normGenerator
      (s := s) (z := z) (N := N) (P0 := P0) hone0
  have htwoProduct :=
    orthogonalProduct_twoScale_le_component_zero_weight
      (s := s) (z := z) (N := N) (P0 := P0) htwo0
  by_cases hdefect : quadraticDefect K (a1 * d1) = ⊤
  · have hproduct :=
      (Lattice.orthogonalProductDecomposition s z N P0).weightIdealOrder_eq_min_components_of_defect_eq_top_fin_two
        a1 d1 ha hzeroProduct honeProduct htwoProduct hdefect
    have hisometry := Lattice.weightIdealOrder_eq_of_isometry
      f0 hproductRank
    have hfundamental : Lattice.weightIdealOrder t0 Q0 =
        min (Lattice.weightIdealOrder s N)
          (Lattice.weightIdealOrder z P0) := by
      rw [hisometry, hproduct,
        orthogonalProduct_component_zero_weightOrder
          (s := s) (z := z) (N := N) (P0 := P0) hX,
        orthogonalProduct_component_one_weightOrder
          (s := s) (z := z) (N := N) (P0 := P0) hY]
    have hdefectOrder : GoodBONG.defectOrder (K := K) (a1 * d1) = ⊤ := by
      unfold GoodBONG.defectOrder
      rw [hdefect]
      rfl
    rw [hfundamental, hdefectOrder, add_top]
    simp only [min_eq_left (le_top : _ ≤ (⊤ : WithTop ℚ))]
    norm_cast
  · have hproduct :=
      (Lattice.orthogonalProductDecomposition s z N P0).weightIdealOrder_eq_min_components_defect_fin_two
        a1 d1 ha hzeroProduct honeProduct htwoProduct hdefect
    have hisometry := Lattice.weightIdealOrder_eq_of_isometry
      f0 hproductRank
    have hfundamental : Lattice.weightIdealOrder t0 Q0 =
        min
          (min (Lattice.weightIdealOrder s N)
            (Lattice.weightIdealOrder z P0))
          (ordUnit K d1 + (quadraticDefect K (a1 * d1)).toNat) := by
      rw [hisometry, hproduct,
        orthogonalProduct_component_zero_weightOrder
          (s := s) (z := z) (N := N) (P0 := P0) hX,
        orthogonalProduct_component_one_weightOrder
          (s := s) (z := z) (N := N) (P0 := P0) hY]
    have hdefectOrder : GoodBONG.defectOrder (K := K) (a1 * d1) =
        ((((quadraticDefect K (a1 * d1)).toNat : Nat) : ℚ) : WithTop ℚ) := by
      unfold GoodBONG.defectOrder
      rw [← ENat.coe_toNat hdefect]
      rfl
    rw [hfundamental, hdefectOrder]
    norm_cast

private theorem fundamentalMinimum_unary
    (A B C E alphaSuffix : ℚ) (delta : WithTop ℚ)
    (hAC : A ≤ C) (hCB : C ≤ B)
    (hSuffix : alphaSuffix ≤ (C - B) / 2 + E) :
    min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((B + C - A + E : ℚ) : WithTop ℚ)
          (((B + C - A : ℚ) : WithTop ℚ) + delta)) =
      min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ)
          (((B + C - A : ℚ) : WithTop ℚ) + delta)) := by
  have hSH : B + alphaSuffix ≤ C + (B - A) / 2 + E := by
    linarith
  have hSE : B + alphaSuffix ≤ B + C - A + E := by
    linarith
  have hSHTop : ((B + alphaSuffix : ℚ) : WithTop ℚ) ≤
      ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ) := by
    exact_mod_cast hSH
  have hSETop : ((B + alphaSuffix : ℚ) : WithTop ℚ) ≤
      ((B + C - A + E : ℚ) : WithTop ℚ) := by
    exact_mod_cast hSE
  calc
    min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((B + C - A + E : ℚ) : WithTop ℚ)
          (((B + C - A : ℚ) : WithTop ℚ) + delta)) =
        min
          (min ((B + alphaSuffix : ℚ) : WithTop ℚ)
            ((B + C - A + E : ℚ) : WithTop ℚ))
          (((B + C - A : ℚ) : WithTop ℚ) + delta) := by
      rw [← min_assoc]
    _ = min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (((B + C - A : ℚ) : WithTop ℚ) + delta) := by
      rw [show min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        ((B + C - A + E : ℚ) : WithTop ℚ) =
          ((B + alphaSuffix : ℚ) : WithTop ℚ) from
        min_eq_left hSETop]
    _ = min
          (min ((B + alphaSuffix : ℚ) : WithTop ℚ)
            ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ))
          (((B + C - A : ℚ) : WithTop ℚ) + delta) := by
      rw [show min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ) =
          ((B + alphaSuffix : ℚ) : WithTop ℚ) from
        min_eq_left hSHTop]
    _ = min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ)
          (((B + C - A : ℚ) : WithTop ℚ) + delta)) := by
      rw [min_assoc]

private theorem fundamentalMinimum_nonunary
    (A B C E alphaPrefix alphaSuffix : ℚ) (delta : WithTop ℚ)
    (hAC : A ≤ C) (hCB : C ≤ B)
    (hSuffix : alphaSuffix ≤ (C - B) / 2 + E) :
    min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min
          (min ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ)
            ((B + C - A + E : ℚ) : WithTop ℚ))
          (((B + C - A : ℚ) : WithTop ℚ) + delta)) =
      min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ)
          (min (((B + C - A : ℚ) : WithTop ℚ) + delta)
            ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ))) := by
  have hSH : B + alphaSuffix ≤ C + (B - A) / 2 + E := by
    linarith
  have hSE : B + alphaSuffix ≤ B + C - A + E := by
    linarith
  have hSHTop : ((B + alphaSuffix : ℚ) : WithTop ℚ) ≤
      ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ) := by
    exact_mod_cast hSH
  have hSETop : ((B + alphaSuffix : ℚ) : WithTop ℚ) ≤
      ((B + C - A + E : ℚ) : WithTop ℚ) := by
    exact_mod_cast hSE
  rw [show min
      ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ)
      ((B + C - A + E : ℚ) : WithTop ℚ) =
      min
        ((B + C - A + E : ℚ) : WithTop ℚ)
        ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ) by
    exact min_comm _ _]
  calc
    min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min
          (min ((B + C - A + E : ℚ) : WithTop ℚ)
            ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ))
          (((B + C - A : ℚ) : WithTop ℚ) + delta)) =
        min
          (min ((B + alphaSuffix : ℚ) : WithTop ℚ)
            ((B + C - A + E : ℚ) : WithTop ℚ))
          (min ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ)
            (((B + C - A : ℚ) : WithTop ℚ) + delta)) := by
      ac_rfl
    _ = min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ)
          (((B + C - A : ℚ) : WithTop ℚ) + delta)) := by
      rw [show min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        ((B + C - A + E : ℚ) : WithTop ℚ) =
          ((B + alphaSuffix : ℚ) : WithTop ℚ) from
        min_eq_left hSETop]
    _ = min
          (min ((B + alphaSuffix : ℚ) : WithTop ℚ)
            ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ))
          (min (((B + C - A : ℚ) : WithTop ℚ) + delta)
            ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ)) := by
      rw [show min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ) =
          ((B + alphaSuffix : ℚ) : WithTop ℚ) from
        min_eq_left hSHTop]
      ac_rfl
    _ = min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ)
          (min (((B + C - A : ℚ) : WithTop ℚ) + delta)
            ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ))) := by
      simp only [min_assoc]

private theorem globalAlphaMinimum_unary
    (A B C E alpha alphaSuffix : ℚ)
    (delta prefixCandidate : WithTop ℚ)
    (hAlpha : (alpha : WithTop ℚ) =
      min prefixCandidate (alphaSuffix : WithTop ℚ))
    (hPrefix : prefixCandidate =
      (((C - B : ℚ) : WithTop ℚ) +
        min (((B - A) / 2 + E : ℚ) : WithTop ℚ)
          (((B - A : ℚ) : WithTop ℚ) + delta))) :
    ((B + alpha : ℚ) : WithTop ℚ) =
      min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ)
          (((B + C - A : ℚ) : WithTop ℚ) + delta)) := by
  have hSuffixCast : (B : WithTop ℚ) + (alphaSuffix : WithTop ℚ) =
      ((B + alphaSuffix : ℚ) : WithTop ℚ) := by norm_cast
  have hHalf : (B : WithTop ℚ) +
      (((C - B : ℚ) : WithTop ℚ) +
        (((B - A) / 2 + E : ℚ) : WithTop ℚ)) =
      ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ) := by
    norm_cast
    ring
  have hDefect : (B : WithTop ℚ) +
      (((C - B : ℚ) : WithTop ℚ) +
        (((B - A : ℚ) : WithTop ℚ) + delta)) =
      (((B + C - A : ℚ) : WithTop ℚ) + delta) := by
    calc
      (B : WithTop ℚ) +
          (((C - B : ℚ) : WithTop ℚ) +
            (((B - A : ℚ) : WithTop ℚ) + delta)) =
          (((B : WithTop ℚ) + ((C - B : ℚ) : WithTop ℚ) +
            ((B - A : ℚ) : WithTop ℚ)) + delta) := by abel
      _ = (((B + C - A : ℚ) : WithTop ℚ) + delta) := by
        congr 1
        norm_cast
        ring
  rw [show ((B + alpha : ℚ) : WithTop ℚ) =
      (B : WithTop ℚ) + (alpha : WithTop ℚ) by norm_cast,
    hAlpha, GoodBONG.lemma214_withTop_add_min, hPrefix,
    GoodBONG.lemma214_withTop_add_min,
    GoodBONG.lemma214_withTop_add_min]
  rw [hSuffixCast, hHalf, hDefect]
  ac_rfl

private theorem globalAlphaMinimum_nonunary
    (A B C E alpha alphaPrefix alphaSuffix : ℚ)
    (delta prefixCandidate : WithTop ℚ)
    (hAlpha : (alpha : WithTop ℚ) =
      min prefixCandidate (alphaSuffix : WithTop ℚ))
    (hPrefix : prefixCandidate =
      (((C - B : ℚ) : WithTop ℚ) +
        min (((B - A) / 2 + E : ℚ) : WithTop ℚ)
          (min (((B - A : ℚ) : WithTop ℚ) + delta)
            ((B - A + alphaPrefix : ℚ) : WithTop ℚ)))) :
    ((B + alpha : ℚ) : WithTop ℚ) =
      min ((B + alphaSuffix : ℚ) : WithTop ℚ)
        (min ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ)
          (min (((B + C - A : ℚ) : WithTop ℚ) + delta)
            ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ))) := by
  have hSuffixCast : (B : WithTop ℚ) + (alphaSuffix : WithTop ℚ) =
      ((B + alphaSuffix : ℚ) : WithTop ℚ) := by norm_cast
  have hHalf : (B : WithTop ℚ) +
      (((C - B : ℚ) : WithTop ℚ) +
        (((B - A) / 2 + E : ℚ) : WithTop ℚ)) =
      ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ) := by
    norm_cast
    ring
  have hDefect : (B : WithTop ℚ) +
      (((C - B : ℚ) : WithTop ℚ) +
        (((B - A : ℚ) : WithTop ℚ) + delta)) =
      (((B + C - A : ℚ) : WithTop ℚ) + delta) := by
    calc
      (B : WithTop ℚ) +
          (((C - B : ℚ) : WithTop ℚ) +
            (((B - A : ℚ) : WithTop ℚ) + delta)) =
          (((B : WithTop ℚ) + ((C - B : ℚ) : WithTop ℚ) +
            ((B - A : ℚ) : WithTop ℚ)) + delta) := by abel
      _ = (((B + C - A : ℚ) : WithTop ℚ) + delta) := by
        congr 1
        norm_cast
        ring
  have hPrefixTerm : (B : WithTop ℚ) +
      (((C - B : ℚ) : WithTop ℚ) +
        ((B - A + alphaPrefix : ℚ) : WithTop ℚ)) =
      ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ) := by
    norm_cast
    ring
  rw [show ((B + alpha : ℚ) : WithTop ℚ) =
      (B : WithTop ℚ) + (alpha : WithTop ℚ) by norm_cast,
    hAlpha, GoodBONG.lemma214_withTop_add_min, hPrefix,
    GoodBONG.lemma214_withTop_add_min,
    GoodBONG.lemma214_withTop_add_min,
    GoodBONG.lemma214_withTop_add_min,
    GoodBONG.lemma214_withTop_add_min]
  rw [hSuffixCast, hHalf, hDefect, hPrefixTerm]
  ac_rfl

set_option maxHeartbeats 8000000 in
theorem sourceFundamentalWeightOrder_eq_order_add_alpha_componentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hrank : 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank k) :
    let i : Fin m := ⟨S.componentStart k, by
      have hstop := S.componentStop_le k
      unfold componentStop at hstop
      omega⟩
    (Lattice.weightIdealOrder q (S.sourceJordan.fundamentalLattice k) : ℚ) =
      (a.order i.castSucc : ℚ) + a.alphaValue i := by
  have hmpos : 0 < m := by
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  let D := S.sourceJordan.toOrthogonalDecomposition
  let P := D.prefixQuadraticSublattice k.val
  let U := D.suffixQuadraticSublattice k.val
  letI : Module.Finite K U.carrier := U.lattice.moduleFinite
  letI : Module.Finite K P.carrier := P.lattice.moduleFinite
  let c := Lattice.scaleTruncationUnit (K := K)
    (ordUnit K (S.sourceJordan.scaleGenerator k))
  let F := Lattice.orthogonalProductDecomposition
    U.space P.space U.lattice
      (Lattice.rescale c (Lattice.dualLattice P.space P.lattice))
  let f := S.sourceFundamentalLayerSwappedIsometry k hk
  have hambient0 :=
    S.toStrictJordanEndpointAlignment.sourceFirstGenerator_fundamentalLattice k
  change Lattice.IsNormGeneratorValue q
      (S.sourceJordan.fundamentalLattice k)
      (S.weakAlignment.endpoint.sourceEndpoints.profile.endpointFirstValue k)
    at hambient0
  rw [S.sourceEndpointFirstValue_eq_componentStart k] at hambient0
  have hambient : Lattice.IsNormGeneratorValue
      (U.space.orthogonalSum P.space)
      (Lattice.product U.lattice
        (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)))
      (a.valueUnit ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩) := by
    exact hambient0.mapLatticeIsometry f.symm
  have hsuffixLen : 2 ≤ n.succ + 1 - S.componentStart k := by
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    omega
  obtain ⟨p, hp⟩ : ∃ p, p + 2 = n.succ + 1 - S.componentStart k :=
    ⟨n.succ + 1 - S.componentStart k - 2, by omega⟩
  let suffix := (S.sourceSuffixGoodBONG k hk T).castLength hp.symm
  have hsuffixGen0 := suffix.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have hsuffixValue : suffix.valueUnit 0 =
      a.valueUnit ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ := by
    rw [show suffix = (S.sourceSuffixGoodBONG k hk T).castLength hp.symm by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    simpa using S.sourceSuffixGoodBONG_valueUnit k hk T
      (⟨0, by omega⟩ : Fin (n.succ + 1 - S.componentStart k))
  change Lattice.IsNormGeneratorValue U.space U.lattice
      (suffix.valueUnit 0) at hsuffixGen0
  rw [hsuffixValue] at hsuffixGen0
  have hzero : Lattice.IsNormGeneratorValue
      (Lattice.orthogonalProductLeftComponent
        U.space P.space U.lattice).space
      (Lattice.orthogonalProductLeftComponent
        U.space P.space U.lattice).lattice
      (a.valueUnit ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩) := by
    have h := hsuffixGen0.mapLatticeIsometry
      (Lattice.orthogonalProductLeftComponentIsometry
        U.space P.space U.lattice)
    exact h
  have hsuffixRankPos : 0 < Module.finrank K U.carrier := by
    have hlen :=
      (S.sourceSuffixGoodBONG k hk T).toBONG.length_eq_finrank
    have hlen' : n.succ + 1 - S.componentStart k =
        Module.finrank K U.carrier := by
      simpa only [D, U] using hlen
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
  have hprefixLen : 0 < S.componentStart k := by
    unfold componentStart
    let j : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hj : j ∈ Finset.Iio k := by
      simp only [Finset.mem_Iio]
      change k.val - 1 < k.val
      omega
    have hle := Finset.single_le_sum
      (s := Finset.Iio k)
      (f := fun z ↦
        S.sourceJordan.toOrthogonalDecomposition.componentRank z)
      (fun _ _ ↦ Nat.zero_le _) hj
    have hjpos := S.sourceJordan.component_finrank_pos j
    exact hjpos.trans_le hle
  obtain ⟨ell, hell⟩ : ∃ ell, ell + 1 = S.componentStart k :=
    ⟨S.componentStart k - 1, by omega⟩
  let prefixBong := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
  rcases prefixBong.beli2009Remark26_duality with
    ⟨dual, _hvectors, hvalues, hdualOrders, _halphas⟩
  have hdualGen0 := dual.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have hdualScaled := hdualGen0.rescaleQuadraticUnit (c ^ 2)
  have hdualRescaled := hdualScaled.mapLatticeIsometry
    (Lattice.scalarMultiplicationRescaleLatticeIsometry
      P.space (Lattice.dualLattice P.space P.lattice) c)
  have hone : Lattice.IsNormGeneratorValue
      (Lattice.orthogonalProductRightComponent
        U.space P.space
          (Lattice.rescale c
            (Lattice.dualLattice P.space P.lattice))).space
      (Lattice.orthogonalProductRightComponent
        U.space P.space
          (Lattice.rescale c
            (Lattice.dualLattice P.space P.lattice))).lattice
      ((c ^ 2) * dual.valueUnit 0) := by
    have h := hdualRescaled.mapLatticeIsometry
      (Lattice.orthogonalProductRightComponentIsometry
        U.space P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)))
    exact h
  let a0 : Kˣ := -(a.valueUnit ⟨S.componentStart k, by
    have hstop := S.componentStop_le k
    have hstart := S.componentStart_lt_componentStop k
    omega⟩)
  let d0 : Kˣ := (c ^ 2) * dual.valueUnit 0
  have hprefixRankPos : 0 < Module.finrank K P.carrier := by
    have hlen := prefixBong.toBONG.length_eq_finrank
    have hlen' : ell + 1 = Module.finrank K P.carrier := by
      simpa only [D, P, prefixBong] using hlen
    omega
  change Lattice.IsNormGeneratorValue P.space
    (Lattice.rescale c (Lattice.dualLattice P.space P.lattice))
    ((c ^ 2) * dual.valueUnit 0) at hdualRescaled
  have huniform := weightIdealOrder_of_orthogonalProductIsometry
    f a0 d0 (by simpa only [a0] using hambient.neg)
    (by simpa only [a0] using hsuffixGen0.neg)
    (by simpa only [d0] using hdualRescaled) htwo
    hsuffixRankPos hprefixRankPos
  have hstartAlphaBound : S.componentStart k < n.succ := by
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    omega
  let i : Fin n.succ := ⟨S.componentStart k, hstartAlphaBound⟩
  let j : Fin n.succ := ⟨S.componentStart k - 1, by omega⟩
  let A : ℚ := a.order j.castSucc
  let B : ℚ := a.order i.castSucc
  let C : ℚ := a.order i.succ
  let E : ℚ := ramificationIndex K
  let alphaSuffix : ℚ := suffix.alphaValue 0
  let delta : WithTop ℚ := a.adjacentDefect j
  have hACInt : a.order j.castSucc ≤ a.order i.succ := by
    have hjbound : j.castSucc.val + 2 < n.succ + 1 := by
      change S.componentStart k - 1 + 2 < n.succ + 1
      omega
    have hgood := a.good j.castSucc hjbound
    have hidx : (⟨j.castSucc.val + 2, hjbound⟩ : Fin (n.succ + 1)) =
        i.succ := by
      apply Fin.ext
      change S.componentStart k - 1 + 2 = S.componentStart k + 1
      omega
    rw [hidx] at hgood
    exact hgood
  have hAC : A ≤ C := by
    dsimp only [A, C]
    exact_mod_cast hACInt
  have hCBInt : a.order i.succ ≤ a.order i.castSucc := by
    have h := S.source_component_head_descending k hrank
    have hleft : (⟨S.componentStart k + 1, by
          have hstop := S.componentStop_le k
          unfold componentStop at hstop
          omega⟩ : Fin (n.succ + 1)) = i.succ := by
      apply Fin.ext
      rfl
    have hright : (⟨S.componentStart k, by
          have hstop := S.componentStop_le k
          unfold componentStop at hstop
          omega⟩ : Fin (n.succ + 1)) = i.castSucc := by
      apply Fin.ext
      rfl
    rw [hleft, hright] at h
    exact h
  have hCB : C ≤ B := by
    dsimp only [B, C]
    exact_mod_cast hCBInt
  let coordinates := S.sourceComponentCoordinates k
  have hinside : S.componentStart k + 1 < S.componentStop k := by
    unfold componentStop
    omega
  have hcoordStart : coordinates.start = S.componentStart k := rfl
  have hcoordStop : coordinates.stop = S.componentStop k := rfl
  have hstartInside : S.componentStart k < coordinates.stop := by
    rw [hcoordStop]
    exact S.componentStart_lt_componentStop k
  have hsum0 := coordinates.adjacent_order_sum
    (S.componentStart k) (by rw [hcoordStart]) (by simpa only [hcoordStop] using hinside)
  have hindexLeft : coordinates.index (S.componentStart k) hstartInside =
      i.castSucc := by
    apply Fin.ext
    rfl
  have hindexRight : coordinates.index (S.componentStart k + 1) hinside =
      i.succ := by
    apply Fin.ext
    rfl
  rw [hindexLeft, hindexRight] at hsum0
  have hscaleOrder : coordinates.scaleOrder =
      ordUnit K (S.sourceJordan.scaleGenerator k) := rfl
  have hsum : B + C =
      2 * (ordUnit K (S.sourceJordan.scaleGenerator k) : ℚ) := by
    have hsumQ := congrArg (fun z : Int => (z : ℚ)) hsum0
    push_cast at hsumQ
    rw [hscaleOrder] at hsumQ
    simpa only [B, C] using hsumQ
  have hsuffixOrder (z : Fin (p + 2)) : suffix.order z =
      a.order ⟨S.componentStart k + z.val, by omega⟩ := by
    rw [show suffix =
        (S.sourceSuffixGoodBONG k hk T).castLength hp.symm by rfl,
      GoodBONG.order_castLength]
    exact S.sourceSuffixGoodBONG_order k hk T ⟨z.val, by omega⟩
  have hsuffixOrderZero : suffix.order 0 = a.order i.castSucc := by
    have h := hsuffixOrder 0
    have hidx : (⟨S.componentStart k + (0 : Fin (p + 2)).val, by omega⟩ :
        Fin (n.succ + 1)) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_zero, Nat.add_zero]
      rfl
    rw [hidx] at h
    exact h
  have hsuffixOrderOne : suffix.order 1 = a.order i.succ := by
    have h := hsuffixOrder 1
    have hidx : (⟨S.componentStart k + (1 : Fin (p + 2)).val, by omega⟩ :
        Fin (n.succ + 1)) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_one]
      rfl
    rw [hidx] at h
    exact h
  have hsuffixAlphaBound : alphaSuffix ≤ (C - B) / 2 + E := by
    have h := suffix.alphaValue_le_halfGapValue (0 : Fin (p + 1))
    unfold GoodBONG.halfGapValue GoodBONG.orderGap at h
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h
    rw [hsuffixOrderZero, hsuffixOrderOne] at h
    push_cast at h
    simpa only [A, B, C, E, alphaSuffix] using h
  have hsuffixWeight :
      (Lattice.weightIdealOrder U.space U.lattice : ℚ) =
        B + alphaSuffix := by
    have h := S.sourceSuffix_weightIdealOrder
      k hk T hrank p hp
    have hidx : (⟨S.componentStart k, by
          have hstop := S.componentStop_le k
          have hstart := S.componentStart_lt_componentStop k
          omega⟩ : Fin (n.succ + 1)) = i.castSucc := by
      apply Fin.ext
      rfl
    rw [hidx] at h
    simpa only [D, U, suffix, B, alphaSuffix] using h
  have hrevZero : Fin.rev (0 : Fin (ell + 1)) = Fin.last ell := by
    apply Fin.ext
    simp [Fin.rev]
  have hprefixLastOrder : prefixBong.order (Fin.last ell) =
      a.order j.castSucc := by
    rw [show prefixBong =
        (S.sourcePrefixGoodBONG k hk T).castLength hell.symm by rfl,
      GoodBONG.order_castLength]
    have hlocal : (⟨(Fin.last ell).val, by omega⟩ :
        Fin (S.componentStart k)) = ⟨ell, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hlocal]
    have h := S.sourcePrefixGoodBONG_order k hk T
      (⟨ell, by omega⟩ : Fin (S.componentStart k))
    rw [h]
    apply congrArg a.order
    apply Fin.ext
    change ell = S.componentStart k - 1
    omega
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
  have hjSucc : j.succ = i.castSucc := by
    apply Fin.ext
    change S.componentStart k - 1 + 1 = S.componentStart k
    omega
  have hcrossUnit : a0 * d0 =
      a.adjacentProduct j * (c * (a.valueUnit j.castSucc)⁻¹) ^ 2 := by
    rw [hd0]
    unfold a0 GoodBONG.adjacentProduct
    change -(a.valueUnit i.castSucc) * (c ^ 2 * (a.valueUnit j.castSucc)⁻¹) = _
    rw [hjSucc]
    simp only [neg_mul]
    apply neg_injective
    simpa only [neg_neg, mul_assoc] using
      fundamentalLayer_mul_square_inv_identity
        (a.valueUnit i.castSucc) c (a.valueUnit j.castSucc)
  have hcrossDefect : GoodBONG.defectOrder (K := K) (a0 * d0) =
      delta := by
    dsimp only [delta]
    unfold GoodBONG.adjacentDefect GoodBONG.defectOrder
    rw [hcrossUnit, quadraticDefect_mul_square]
  have hcOrder : ordUnit K c =
      ordUnit K (S.sourceJordan.scaleGenerator k) := by
    dsimp only [c]
    rw [Lattice.scaleTruncationUnit, ordUnit_uniformizerPowerUnit]
  have hd0OrderInt : ordUnit K d0 =
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
  have hd0Order : (ordUnit K d0 : ℚ) = B + C - A := by
    calc
      (ordUnit K d0 : ℚ) =
          2 * (ordUnit K (S.sourceJordan.scaleGenerator k) : ℚ) -
            (a.order j.castSucc : ℚ) := by
        exact_mod_cast hd0OrderInt
      _ = B + C - A := by
        dsimp only [A, B, C] at hsum ⊢
        linarith
  have hrescaleWeight := Lattice.weightIdealOrder_rescaleLattice
    P.space (Lattice.dualLattice P.space P.lattice) c hprefixRankPos
  let loc := GoodBONG.prefixAlphaLocalizationIndex i hprefixLen
  let rawSegment :=
    (a.prefixAlphaSegmentWitness i hprefixLen).toGoodBONG a.good
  have hsegmentAlphaLength : loc.stop - loc.start = ell + 1 := by
    dsimp [loc, GoodBONG.prefixAlphaLocalizationIndex, i]
    omega
  let hsegmentLength := congrArg (fun z : Nat => z + 1) hsegmentAlphaLength
  let segment := rawSegment.castLength hsegmentLength
  have hsegmentValues (z : Fin (ell + 2)) :
      segment.valueUnit z = a.valueUnit ⟨z.val, by
        have hz := z.isLt
        omega⟩ := by
    rw [show segment = rawSegment.castLength hsegmentLength by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    change (a.prefixAlphaSegmentWitness i hprefixLen).bong.valueUnit _ = _
    rw [(a.prefixAlphaSegmentWitness i hprefixLen).valueUnit_eq]
    apply congrArg a.valueUnit
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex, loc,
      GoodBONG.prefixAlphaLocalizationIndex]
  have hsegmentOrders (z : Fin (ell + 2)) :
      segment.order z = a.order ⟨z.val, by
        have hz := z.isLt
        omega⟩ := by
    change segment.toBONG.order z = a.toBONG.order _
    rw [segment.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit]
    change ordUnit K (segment.valueUnit z) = ordUnit K (a.valueUnit _)
    rw [hsegmentValues]
  have hsegmentLocalPivot :
      Fin.cast hsegmentAlphaLength.symm ⟨ell, by omega⟩ = loc.localPivot := by
    apply Fin.ext
    dsimp [loc, GoodBONG.prefixAlphaLocalizationIndex,
      AlphaLocalizationIndex.localPivot, i]
    omega
  have hsegmentAlphaLast : segment.alphaValue ⟨ell, by omega⟩ =
      rawSegment.alphaValue loc.localPivot := by
    have hcast := GoodBONG.alphaValue_castLength_fundamental
      rawSegment hsegmentAlphaLength ⟨ell, by omega⟩
    rw [hsegmentLocalPivot] at hcast
    simpa only [segment, hsegmentLength] using hcast
  have hprefixSegmentValues (z : Fin (ell + 1)) :
      prefixBong.valueUnit z = segment.valueUnit z.castSucc := by
    rw [show prefixBong =
        (S.sourcePrefixGoodBONG k hk T).castLength hell.symm by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    have hpref := S.sourcePrefixGoodBONG_valueUnit k hk T
      (⟨z.val, by omega⟩ : Fin (S.componentStart k))
    rw [hpref, hsegmentValues]
    apply congrArg a.valueUnit
    apply Fin.ext
    rfl
  have hsuffixValues (z : Fin (p + 2)) :
      suffix.valueUnit z =
        a.valueUnit ⟨i.val + z.val, by
          change S.componentStart k + z.val < n.succ + 1
          have hz := z.isLt
          omega⟩ := by
    rw [show suffix =
        (S.sourceSuffixGoodBONG k hk T).castLength hp.symm by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    have hsuf := S.sourceSuffixGoodBONG_valueUnit k hk T
      (⟨z.val, by omega⟩ :
        Fin (n.succ + 1 - S.componentStart k))
    rw [hsuf]
  let prefixCandidate := a.prefixSegmentAlphaCandidate i hprefixLen
  have hglobalAlpha : (a.alphaValue i : WithTop ℚ) =
      min prefixCandidate (alphaSuffix : WithTop ℚ) := by
    dsimp only [prefixCandidate, alphaSuffix]
    exact a.alphaValue_eq_min_prefix_suffix i hprefixLen suffix hp hsuffixValues
  have hgapQ : (a.orderGap i : ℚ) = C - B := by
    unfold GoodBONG.orderGap
    dsimp only [B, C]
    push_cast
    ring
  have hprefixCandidateBase : prefixCandidate =
      (((C - B : ℚ) : WithTop ℚ) +
        (segment.alphaValue ⟨ell, by omega⟩ : WithTop ℚ)) := by
    dsimp only [prefixCandidate]
    rw [a.prefixSegmentAlphaCandidate_eq_gap_add_alpha i hprefixLen]
    rw [← hsegmentAlphaLast, hgapQ]
    norm_cast
  let last : Fin (ell + 1) := Fin.last ell
  have hlastCastValue : segment.valueUnit last.castSucc =
      a.valueUnit j.castSucc := by
    rw [hsegmentValues]
    apply congrArg a.valueUnit
    apply Fin.ext
    change ell = S.componentStart k - 1
    omega
  have hlastSuccValue : segment.valueUnit last.succ =
      a.valueUnit i.castSucc := by
    rw [hsegmentValues]
    apply congrArg a.valueUnit
    apply Fin.ext
    change ell + 1 = S.componentStart k
    omega
  have hlastCastOrder : segment.order last.castSucc = a.order j.castSucc := by
    change segment.toBONG.order last.castSucc = a.toBONG.order j.castSucc
    rw [segment.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit]
    change ordUnit K (segment.valueUnit last.castSucc) =
      ordUnit K (a.valueUnit j.castSucc)
    rw [hlastCastValue]
  have hlastSuccOrder : segment.order last.succ = a.order i.castSucc := by
    change segment.toBONG.order last.succ = a.toBONG.order i.castSucc
    rw [segment.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit]
    change ordUnit K (segment.valueUnit last.succ) =
      ordUnit K (a.valueUnit i.castSucc)
    rw [hlastSuccValue]
  have hsegmentHalf : segment.halfGapCandidate last =
      (((B - A) / 2 + E : ℚ) : WithTop ℚ) := by
    unfold GoodBONG.halfGapCandidate
    rw [hlastCastOrder, hlastSuccOrder]
    dsimp only [A, B, E]
    norm_cast
  have hsegmentDefect : segment.leftDefectCandidate last last =
      (((B - A : ℚ) : WithTop ℚ) + delta) := by
    unfold GoodBONG.leftDefectCandidate GoodBONG.adjacentDefect
      GoodBONG.adjacentProduct
    rw [hlastCastOrder, hlastSuccOrder, hlastCastValue, hlastSuccValue]
    dsimp only [A, B, delta]
    unfold GoodBONG.adjacentDefect GoodBONG.adjacentProduct
    rw [hjSucc]
    norm_cast
  have hsuffixWeightTop :
      ((((Lattice.weightIdealOrder U.space U.lattice : Int) : ℚ) :
          WithTop ℚ)) = ((B + alphaSuffix : ℚ) : WithTop ℚ) :=
    congrArg (fun z : ℚ => (z : WithTop ℚ)) hsuffixWeight
  have hcrossTerm :
      (((((ordUnit K d0 : Int) : ℚ) : WithTop ℚ)) +
          GoodBONG.defectOrder (K := K) (a0 * d0)) =
        (((B + C - A : ℚ) : WithTop ℚ) + delta) := by
    rw [hcrossDefect]
    have hd0Top := congrArg (fun z : ℚ => (z : WithTop ℚ)) hd0Order
    rw [hd0Top]
  by_cases hellZero : ell = 0
  · subst ell
    have hlastZero : last = (0 : Fin 1) := by
      apply Fin.ext
      rfl
    have hsegmentAlphaBinary :
        (segment.alphaValue (0 : Fin 1) : WithTop ℚ) =
          min (((B - A) / 2 + E : ℚ) : WithTop ℚ)
            (((B - A : ℚ) : WithTop ℚ) + delta) := by
      have hbinary := segment.binary_alpha_eq_min_candidates
      have hhalfZero : segment.halfGapCandidate (0 : Fin 1) =
          (((B - A) / 2 + E : ℚ) : WithTop ℚ) := by
        rw [← hlastZero]
        exact hsegmentHalf
      have hdefectZero : segment.leftDefectCandidate (0 : Fin 1) 0 =
          (((B - A : ℚ) : WithTop ℚ) + delta) := by
        rw [← hlastZero]
        exact hsegmentDefect
      rw [hhalfZero, hdefectZero] at hbinary
      exact hbinary
    have hprefixFormula : prefixCandidate =
        (((C - B : ℚ) : WithTop ℚ) +
          min (((B - A) / 2 + E : ℚ) : WithTop ℚ)
            (((B - A : ℚ) : WithTop ℚ) + delta)) := by
      have hbase := hprefixCandidateBase
      have hidx : (⟨0, by omega⟩ : Fin 1) = 0 := by
        apply Fin.ext
        rfl
      rw [hidx, hsegmentAlphaBinary] at hbase
      exact hbase
    have hprefixOrderZero : prefixBong.order 0 = a.order j.castSucc := by
      simpa using hprefixLastOrder
    have hdualUnary := weightIdealOrder_dual_goodBONG_unary prefixBong
    have hdualUnaryQ :
        (Lattice.weightIdealOrder P.space
            (Lattice.dualLattice P.space P.lattice) : ℚ) =
          -(A : ℚ) + E := by
      have hcast := congrArg (fun z : Int => (z : ℚ)) hdualUnary
      push_cast at hcast
      rw [hprefixOrderZero] at hcast
      simpa only [P, A, E] using hcast
    have hprefixRescaleQ :
        (Lattice.weightIdealOrder P.space
            (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) : ℚ) =
          B + C - A + E := by
      have hcast := congrArg (fun z : Int => (z : ℚ)) hrescaleWeight
      push_cast at hcast
      rw [hdualUnaryQ, hcOrder] at hcast
      linarith [hsum]
    have hprefixRescaleTop :
        ((((Lattice.weightIdealOrder P.space
              (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) :
                Int) : ℚ) : WithTop ℚ)) =
          ((B + C - A + E : ℚ) : WithTop ℚ) :=
      congrArg (fun z : ℚ => (z : WithTop ℚ)) hprefixRescaleQ
    have hminimum := fundamentalMinimum_unary
      A B C E alphaSuffix delta hAC hCB hsuffixAlphaBound
    have halphaMinimum := globalAlphaMinimum_unary
      A B C E (a.alphaValue i) alphaSuffix delta prefixCandidate
      hglobalAlpha hprefixFormula
    have hfundamentalTop := huniform
    rw [hsuffixWeightTop, hprefixRescaleTop, hcrossTerm,
      min_assoc, hminimum] at hfundamentalTop
    have htargetTop :
        ((B + a.alphaValue i : ℚ) : WithTop ℚ) =
          min ((B + alphaSuffix : ℚ) : WithTop ℚ)
            (min ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ)
              (((B + C - A : ℚ) : WithTop ℚ) + delta)) :=
      halphaMinimum
    have hfinalTop :
        ((((Lattice.weightIdealOrder q
              (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
            WithTop ℚ)) =
          ((B + a.alphaValue i : ℚ) : WithTop ℚ) :=
      hfundamentalTop.trans htargetTop.symm
    have hfinalQ := WithTop.coe_eq_coe.mp hfinalTop
    simpa only [B, i] using hfinalQ
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hellZero
    let alphaPrefix : ℚ := prefixBong.alphaValue ⟨t, by omega⟩
    have hlastIndex : last = (⟨t + 1, by omega⟩ : Fin (t + 2)) := by
      apply Fin.ext
      rfl
    have hsegmentGapQ : (segment.orderGap last : ℚ) = B - A := by
      unfold GoodBONG.orderGap
      rw [hlastCastOrder, hlastSuccOrder]
      dsimp only [A, B]
      push_cast
      ring
    have hsegmentPrefixBase :=
      prefixSegmentAlphaCandidate_last_eq_gap_add_alpha
        segment prefixBong hprefixSegmentValues
    dsimp only at hsegmentPrefixBase
    have hhelperIndex : (⟨t + 1, by omega⟩ : Fin (t + 2)) = last := by
      exact hlastIndex.symm
    simp only [hhelperIndex] at hsegmentPrefixBase
    have hsegmentPrefix :
        segment.prefixSegmentAlphaCandidate last (by
            change 0 < t + 1
            omega) =
          ((B - A + alphaPrefix : ℚ) : WithTop ℚ) := by
      rw [hsegmentGapQ] at hsegmentPrefixBase
      dsimp only [alphaPrefix]
      simpa only [WithTop.coe_eq_coe] using hsegmentPrefixBase
    have hsegmentAlphaBase :=
      alphaValue_last_eq_min_prefixCandidates segment
    dsimp only at hsegmentAlphaBase
    simp only [hhelperIndex] at hsegmentAlphaBase
    have hsegmentAlphaFormula :
        (segment.alphaValue last : WithTop ℚ) =
          min (((B - A) / 2 + E : ℚ) : WithTop ℚ)
            (min (((B - A : ℚ) : WithTop ℚ) + delta)
              ((B - A + alphaPrefix : ℚ) : WithTop ℚ)) := by
      rw [hsegmentHalf, hsegmentDefect, hsegmentPrefix] at hsegmentAlphaBase
      exact hsegmentAlphaBase
    have hprefixFormula : prefixCandidate =
        (((C - B : ℚ) : WithTop ℚ) +
          min (((B - A) / 2 + E : ℚ) : WithTop ℚ)
            (min (((B - A : ℚ) : WithTop ℚ) + delta)
              ((B - A + alphaPrefix : ℚ) : WithTop ℚ))) := by
      have hbase := hprefixCandidateBase
      have hidx : (⟨t + 1, by omega⟩ : Fin (t + 2)) = last :=
        hlastIndex.symm
      rw [hidx, hsegmentAlphaFormula] at hbase
      exact hbase
    have hdualNonunary := weightIdealOrder_dual_goodBONG prefixBong
    have hprefixLastIndex :
        (⟨t + 1, by omega⟩ : Fin (t + 2)) = Fin.last (t + 1) := by
      apply Fin.ext
      rfl
    rw [hprefixLastIndex, hprefixLastOrder] at hdualNonunary
    have hdualNonunaryQ :
        (Lattice.weightIdealOrder P.space
            (Lattice.dualLattice P.space P.lattice) : ℚ) =
          min (-A + alphaPrefix) (-A + E) := by
      simpa only [P, A, E, alphaPrefix] using hdualNonunary
    have hprefixRescaleQ :
        (Lattice.weightIdealOrder P.space
            (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) : ℚ) =
          min (B + C - A + alphaPrefix) (B + C - A + E) := by
      calc
        (Lattice.weightIdealOrder P.space
            (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) : ℚ) =
            2 * (ordUnit K c : ℚ) +
              (Lattice.weightIdealOrder P.space
                (Lattice.dualLattice P.space P.lattice) : ℚ) := by
          exact_mod_cast hrescaleWeight
        _ = 2 * (ordUnit K (S.sourceJordan.scaleGenerator k) : ℚ) +
              min (-A + alphaPrefix) (-A + E) := by
          rw [hcOrder, hdualNonunaryQ]
        _ = min
              (2 * (ordUnit K (S.sourceJordan.scaleGenerator k) : ℚ) +
                (-A + alphaPrefix))
              (2 * (ordUnit K (S.sourceJordan.scaleGenerator k) : ℚ) +
                (-A + E)) := by
          rw [GoodBONG.lemma214_add_min]
        _ = min (B + C - A + alphaPrefix) (B + C - A + E) := by
          congr 1 <;> linarith [hsum]
    have hprefixRescaleTop :
        ((((Lattice.weightIdealOrder P.space
              (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) :
                Int) : ℚ) : WithTop ℚ)) =
          min ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ)
            ((B + C - A + E : ℚ) : WithTop ℚ) := by
      have hcast := congrArg (fun z : ℚ => (z : WithTop ℚ)) hprefixRescaleQ
      simpa only [WithTop.coe_min] using hcast
    have hminimum := fundamentalMinimum_nonunary
      A B C E alphaPrefix alphaSuffix delta hAC hCB hsuffixAlphaBound
    have halphaMinimum := globalAlphaMinimum_nonunary
      A B C E (a.alphaValue i) alphaPrefix alphaSuffix delta prefixCandidate
      hglobalAlpha hprefixFormula
    have hfundamentalTop := huniform
    rw [hsuffixWeightTop, hprefixRescaleTop, hcrossTerm,
      min_assoc, hminimum] at hfundamentalTop
    have htargetTop :
        ((B + a.alphaValue i : ℚ) : WithTop ℚ) =
          min ((B + alphaSuffix : ℚ) : WithTop ℚ)
            (min ((C + (B - A) / 2 + E : ℚ) : WithTop ℚ)
              (min (((B + C - A : ℚ) : WithTop ℚ) + delta)
                ((B + C - A + alphaPrefix : ℚ) : WithTop ℚ))) :=
      halphaMinimum
    have hfinalTop :
        ((((Lattice.weightIdealOrder q
              (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
            WithTop ℚ)) =
          ((B + a.alphaValue i : ℚ) : WithTop ℚ) :=
      hfundamentalTop.trans htargetTop.symm
    have hfinalQ := WithTop.coe_eq_coe.mp hfinalTop
    simpa only [B, i] using hfinalQ

end BONG.StrictJordanAdaptedAlignment

end Bong
