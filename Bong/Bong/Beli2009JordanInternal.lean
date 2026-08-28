/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanBoundaryOdd
import Bong.Bong.Beli2009JordanFundamentalLayerFormula
import Bong.Bong.Beli2009JordanWeightOrderProof
import Bong.Lattice.JordanReverseDualInvariants

/-!
# Beli (2009), the internal part of Lemma 2.16

This file replaces the unconstrained ideals in the early
`InternalJordanAlphaData` interface by the actual fundamental weight ideals
of a strict Jordan decomposition and its reverse dual.  It first proves the
internal formula on the initial Jordan component.  The tail induction is
developed below from this concrete base.
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

namespace Lattice.JordanDecomposition

/-- The intrinsic lattice at the first scale of a nonempty Jordan
decomposition is the original lattice. -/
theorem fundamentalLattice_zero
    {t : Nat} (J : JordanDecomposition q L t) (hpos : 0 < t) :
    J.fundamentalLattice ⟨0, hpos⟩ = L := by
  unfold fundamentalLattice fundamentalScaleOrder
  rw [J.scaleTruncation_eq_componentwiseRescaleLattice]
  have hfactor : J.scaleTruncationFactor
      (ordUnit K (J.scaleGenerator ⟨0, hpos⟩)) = fun _ ↦ 1 := by
    funext j
    unfold scaleTruncationFactor positivePartUnit
    rw [if_neg]
    intro hpositive
    rw [ordUnit_mul, ordUnit_inv, scaleTruncationUnit,
      ordUnit_uniformizerPowerUnit] at hpositive
    have hindex : (⟨0, hpos⟩ : Fin t) ≤ j := by
      change 0 ≤ j.val
      omega
    have hle : ordUnit K (J.scaleGenerator ⟨0, hpos⟩) ≤
        ordUnit K (J.scaleGenerator j) := by
      by_cases hEq : (⟨0, hpos⟩ : Fin t) = j
      · rw [hEq]
      · exact (J.scaleOrder_strict
          (lt_of_le_of_ne hindex hEq)).le
    omega
  rw [hfactor, J.toOrthogonalDecomposition.componentwiseRescaleLattice_one]

/-- The first fundamental weight is therefore the ordinary weight of the
whole lattice. -/
theorem fundamentalWeightOrder_zero
    {t : Nat} (J : JordanDecomposition q L t) (hpos : 0 < t) :
    J.fundamentalWeightOrder ⟨0, hpos⟩ = Lattice.weightIdealOrder q L := by
  unfold fundamentalWeightOrder
  rw [J.fundamentalLattice_zero hpos]

end Lattice.JordanDecomposition

namespace BONG.StrictJordanAdaptedAlignment

variable {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (m + 1)}

/-- The first component of the nonempty strict Jordan alignment. -/
def sourceFirstComponent
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG) :
    Fin S.componentCount :=
  ⟨0, S.componentCount_pos⟩

@[simp]
theorem sourceFirstComponent_val
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG) :
    S.sourceFirstComponent.val = 0 :=
  rfl

theorem Iio_sourceFirstComponent_eq_empty
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG) :
    Finset.Iio S.sourceFirstComponent = ∅ := by
  ext x
  simp only [Finset.mem_Iio]
  constructor
  · intro hlt
    change x.val < S.sourceFirstComponent.val at hlt
    change x.val < 0 at hlt
    omega
  · intro hx
    simpa using hx

/-- The actual fundamental weight ideal attached to a source Jordan
component. -/
noncomputable def sourceFundamentalWeight
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) : Lattice.OrderedFractionalIdeal K :=
  Beli2009WeightIdealData.weight q
    (S.sourceJordan.fundamentalLattice k)

/-- The actual reverse-dual fundamental weight at the corresponding source
component. -/
noncomputable def sourceDualFundamentalWeight
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) : Lattice.OrderedFractionalIdeal K :=
  Beli2009WeightIdealData.weight q
    (S.sourceJordan.reverseDual.fundamentalLattice (Fin.rev k))

@[simp]
theorem sourceFundamentalWeight_order
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    (S.sourceFundamentalWeight k).order =
      S.sourceJordan.fundamentalWeightOrder k :=
  rfl

theorem sourceDualFundamentalWeight_order
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    (S.sourceDualFundamentalWeight k).order =
      S.sourceJordan.fundamentalWeightOrder k -
        2 * S.sourceJordan.fundamentalScaleOrder k := by
  change S.sourceJordan.reverseDual.fundamentalWeightOrder (Fin.rev k) = _
  rw [S.sourceJordan.reverseDual_fundamentalWeightOrder]
  simp only [Fin.rev_rev]
  ring

/-- Concrete internal-alpha data: the block is an actual component slice,
and both ideals are the genuine fundamental weights of the displayed Jordan
decomposition. -/
noncomputable def sourceInternalAlphaData
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (i : Nat)
    (hstart : S.componentStart k ≤ i)
    (hnext : i + 1 < S.componentStop k) :
    a.InternalJordanAlphaData where
  block := S.sourceComponentCoordinates k
  index := i
  start_le := hstart
  next_lt_stop := hnext
  weight := S.sourceFundamentalWeight k
  dualWeight := S.sourceDualFundamentalWeight k
  dualWeightOrder_eq := by
    rw [S.sourceDualFundamentalWeight_order,
      S.sourceFundamentalWeight_order]
    rfl

/-- A component containing an adjacent pair has descending first two orders
when it is the initial Jordan component. -/
theorem source_order_one_le_order_zero
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (hrank : 2 ≤ S.sourceJordan.toOrthogonalDecomposition.componentRank
      S.sourceFirstComponent) :
    a.order 1 ≤ a.order 0 := by
  let k : Fin S.componentCount := S.sourceFirstComponent
  let C := S.sourceComponentCoordinates k
  have hstart : C.start = 0 := by
    unfold C sourceComponentCoordinates
    change S.componentStart k = 0
    have hempty : Finset.Iio k = ∅ := by
      simpa only [k] using S.Iio_sourceFirstComponent_eq_empty
    rw [componentStart, hempty]
    simp
  have hstop : 1 < C.stop := by
    change 1 < S.componentStop k
    rw [componentStop, show S.componentStart k = 0 by exact hstart]
    have hrankk : 2 ≤
        S.sourceJordan.toOrthogonalDecomposition.componentRank k := by
      simpa only [k] using hrank
    omega
  have hzero := (C.beli2009Lemma213_i 0 (by omega) (by omega)).1 (by omega)
  have hone := (C.beli2009Lemma213_i 1 (by omega) hstop).2 (by omega)
  have hscale : C.scaleOrder ≤ C.normOrder := by
    change ordUnit K (S.sourceJordan.scaleGenerator k) ≤
      jordanEffectiveNormOrder S.sourceJordan k
    exact S.weakAlignment.endpoint.sourceWeak.targetScale_le_effectiveNormOrderAt
      k (ordUnit K (S.weakAlignment.endpoint.sourceWeak.scaleGenerator k))
  have hindex0 : C.index 0 (by omega) = (0 : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hindex1 : C.index 1 hstop = (1 : Fin (m + 1)) := by
    apply Fin.ext
    rw [C.index_val]
    have hm : 1 < m + 1 := hstop.trans_le C.stop_le
    change 1 = 1 % (m + 1)
    rw [Nat.mod_eq_of_lt hm]
  rw [hindex0] at hzero
  rw [hindex1] at hone
  omega

/-- Beli Lemma 2.16(i), left equality, for every internal index of the
initial non-unary Jordan component. -/
theorem source_firstComponent_internal_left
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Nat)
    (hstart : S.componentStart S.sourceFirstComponent ≤ i)
    (hnext : i + 1 < S.componentStop S.sourceFirstComponent) :
    (a.order (S.sourceInternalAlphaData S.sourceFirstComponent i hstart hnext).leftIndex : ℚ) +
        a.alphaValue
          (S.sourceInternalAlphaData S.sourceFirstComponent i hstart hnext).alphaIndex =
      (S.sourceFundamentalWeight S.sourceFirstComponent).order := by
  have hrank : 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank
        S.sourceFirstComponent := by
    unfold componentStop componentStart at hnext
    rw [S.Iio_sourceFirstComponent_eq_empty] at hnext
    simp only [Finset.sum_empty, zero_add] at hnext
    omega
  cases m with
  | zero =>
      have hsum := S.sourceProfile.sum_componentRank_eq_length
      have hterm := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun k ↦ S.sourceJordan.toOrthogonalDecomposition.componentRank k)
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ S.sourceFirstComponent)
      rw [hsum] at hterm
      omega
  | succ n =>
    have hbase := a.beli2009Lemma214_of_firstBlock_not_unary
      (S.source_order_one_le_order_zero hrank)
    have hweightZero := S.sourceJordan.fundamentalWeightOrder_zero
      S.componentCount_pos
    have hfirstIndex :
        (⟨0, S.componentCount_pos⟩ : Fin S.componentCount) =
          S.sourceFirstComponent := by
      apply Fin.ext
      rfl
    rw [hfirstIndex] at hweightZero
    rw [← hweightZero] at hbase
    have hbase' :
        (a.order (0 : Fin (n + 2)) : ℚ) +
            a.alphaValue (0 : Fin (n + 1)) =
          (S.sourceFundamentalWeight S.sourceFirstComponent).order := by
      simpa only [S.sourceFundamentalWeight_order] using hbase.symm
    let C := S.sourceComponentCoordinates S.sourceFirstComponent
    have hCstart : C.start = 0 := by
      unfold C sourceComponentCoordinates
      change S.componentStart S.sourceFirstComponent = 0
      rw [componentStart, S.Iio_sourceFirstComponent_eq_empty]
      simp
    let j : Fin (n + 1) := ⟨i, by
      have hstop : C.stop ≤ n + 2 := C.stop_le
      have hnextC : i + 1 < C.stop := by
        exact hnext
      omega⟩
    let jzero : Fin (n + 1) := ⟨0, by omega⟩
    have hjzero : jzero ≤ j := by
      change 0 ≤ i
      omega
    have hsumZero : a.adjacentOrderSum jzero =
        a.adjacentOrderSum j := by
      unfold GoodBONG.adjacentOrderSum
      have hzeroStop : 0 < C.stop := by
        rw [← hCstart]
        exact C.start_lt_stop
      have honeStop : 1 < C.stop := by
        change i + 1 < C.stop at hnext
        omega
      have hiStop : i < C.stop := by
        change i + 1 < C.stop at hnext
        omega
      have hzero := C.adjacent_order_sum 0 (by
        rw [hCstart]) (by
        change 1 < C.stop
        exact honeStop)
      have hi := C.adjacent_order_sum i (by omega) (by
        change i + 1 < C.stop at hnext
        exact hnext)
      have hzeroCast : C.index 0 hzeroStop =
          jzero.castSucc := by apply Fin.ext; rfl
      have hzeroSucc : C.index 1 honeStop =
          jzero.succ := by apply Fin.ext; rfl
      have hiCast : C.index i hiStop = j.castSucc := by
        apply Fin.ext
        rfl
      have hiSucc : C.index (i + 1) hnext = j.succ := by
        apply Fin.ext
        rfl
      rw [hzeroCast, hzeroSucc] at hzero
      rw [hiCast, hiSucc] at hi
      omega
    have hconstant := (a.beli2009Corollary23 jzero j
      hjzero hsumZero).leftEndpoint_eq j hjzero le_rfl
    unfold GoodBONG.alphaLeftEndpoint at hconstant
    have hleftIndex :
        (S.sourceInternalAlphaData S.sourceFirstComponent i hstart hnext).leftIndex =
          j.castSucc := by apply Fin.ext; rfl
    have halphaIndex :
        (S.sourceInternalAlphaData S.sourceFirstComponent i hstart hnext).alphaIndex =
          j := by apply Fin.ext; rfl
    rw [hleftIndex, halphaIndex]
    calc
      (a.order j.castSucc : ℚ) + a.alphaValue j =
          (a.order (0 : Fin (n + 2)) : ℚ) +
            a.alphaValue (0 : Fin (n + 1)) := by
        simpa [jzero] using hconstant
      _ = (S.sourceFundamentalWeight S.sourceFirstComponent).order :=
        hbase'

/-- Beli Lemma 2.16(i), with both the ordinary and reverse-dual weight
equalities, on the initial non-unary source Jordan component.  The second
equality is forced by the alternating adjacent-order sum and is therefore
not an additional local law. -/
theorem source_firstComponent_internal
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Nat)
    (hstart : S.componentStart S.sourceFirstComponent ≤ i)
    (hnext : i + 1 < S.componentStop S.sourceFirstComponent) :
    let D := S.sourceInternalAlphaData S.sourceFirstComponent i hstart hnext
    ((a.order D.leftIndex : ℚ) + a.alphaValue D.alphaIndex =
        (D.weight.order : ℚ)) ∧
      (-(a.order D.rightIndex : ℚ) + a.alphaValue D.alphaIndex =
        (D.dualWeight.order : ℚ)) := by
  let D := S.sourceInternalAlphaData S.sourceFirstComponent i hstart hnext
  have hleft : (a.order D.leftIndex : ℚ) +
      a.alphaValue D.alphaIndex = (D.weight.order : ℚ) := by
    exact S.source_firstComponent_internal_left i hstart hnext
  refine ⟨hleft, ?_⟩
  have hsum := D.block.adjacent_order_sum D.index D.start_le D.next_lt_stop
  have hsumQ :
      (a.order D.leftIndex : ℚ) + (a.order D.rightIndex : ℚ) =
        2 * (D.block.scaleOrder : ℚ) := by
    exact_mod_cast hsum
  have hdual : (D.dualWeight.order : ℚ) =
      (D.weight.order : ℚ) - 2 * (D.block.scaleOrder : ℚ) := by
    exact_mod_cast D.dualWeightOrder_eq
  linarith

/-- Beli Lemma 2.16(i), left equality, on every noninitial source Jordan
component.  The fundamental-layer calculation supplies the value at the
left endpoint; Corollary 2.3 propagates it across the component. -/
theorem source_noninitialComponent_internal_left
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (i : Nat)
    (hstart : S.componentStart k ≤ i)
    (hnext : i + 1 < S.componentStop k) :
    (a.order (S.sourceInternalAlphaData k i hstart hnext).leftIndex : ℚ) +
        a.alphaValue
          (S.sourceInternalAlphaData k i hstart hnext).alphaIndex =
      (S.sourceFundamentalWeight k).order := by
  have hrank : 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank k := by
    unfold componentStop at hnext
    omega
  cases m with
  | zero =>
      have hstop := S.componentStop_le k
      omega
  | succ n =>
    rcases S.source_hasTwoBlockSplit_componentStart k hk with ⟨T⟩
    have hbase :=
      S.sourceFundamentalWeightOrder_eq_order_add_alpha_componentStart
        k hk T hrank
    let C := S.sourceComponentCoordinates k
    let jstart : Fin (n + 1) := ⟨S.componentStart k, by
      have hstop := S.componentStop_le k
      unfold componentStop at hstop
      omega⟩
    let j : Fin (n + 1) := ⟨i, by
      have hstop := S.componentStop_le k
      omega⟩
    have hjstart_le : jstart ≤ j := by
      change S.componentStart k ≤ i
      exact hstart
    have hbase' :
        (a.order jstart.castSucc : ℚ) + a.alphaValue jstart =
          (S.sourceFundamentalWeight k).order := by
      change (a.order jstart.castSucc : ℚ) + a.alphaValue jstart =
        (Lattice.weightIdealOrder q
          (S.sourceJordan.fundamentalLattice k) : ℚ)
      simpa only [jstart] using hbase.symm
    have hsumStart : a.adjacentOrderSum jstart =
        a.adjacentOrderSum j := by
      unfold GoodBONG.adjacentOrderSum
      have hstartNext : S.componentStart k + 1 < C.stop := by
        change S.componentStart k + 1 < S.componentStop k
        unfold componentStop
        omega
      have hiStop : i < C.stop := by
        change i < S.componentStop k
        omega
      have hstartStop : S.componentStart k < C.stop := by
        omega
      have hstartSum := C.adjacent_order_sum (S.componentStart k)
        (by rfl) hstartNext
      have hiSum := C.adjacent_order_sum i hstart hnext
      have hstartCast : C.index (S.componentStart k) hstartStop =
          jstart.castSucc := by
        apply Fin.ext
        rfl
      have hstartSucc : C.index (S.componentStart k + 1) hstartNext =
          jstart.succ := by
        apply Fin.ext
        rfl
      have hiCast : C.index i hiStop = j.castSucc := by
        apply Fin.ext
        rfl
      have hiSucc : C.index (i + 1) hnext = j.succ := by
        apply Fin.ext
        rfl
      rw [hstartCast, hstartSucc] at hstartSum
      rw [hiCast, hiSucc] at hiSum
      omega
    have hconstant := (a.beli2009Corollary23 jstart j
      hjstart_le hsumStart).leftEndpoint_eq j hjstart_le le_rfl
    unfold GoodBONG.alphaLeftEndpoint at hconstant
    have hleftIndex :
        (S.sourceInternalAlphaData k i hstart hnext).leftIndex =
          j.castSucc := by
      apply Fin.ext
      rfl
    have halphaIndex :
        (S.sourceInternalAlphaData k i hstart hnext).alphaIndex = j := by
      apply Fin.ext
      rfl
    rw [hleftIndex, halphaIndex]
    calc
      (a.order j.castSucc : ℚ) + a.alphaValue j =
          (a.order jstart.castSucc : ℚ) + a.alphaValue jstart := by
        exact hconstant
      _ = (S.sourceFundamentalWeight k).order := hbase'

/-- Beli Lemma 2.16(i), with both ordinary and reverse-dual equalities, on
every internal adjacent pair of every source Jordan component. -/
theorem source_component_internal
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount)
    (i : Nat)
    (hstart : S.componentStart k ≤ i)
    (hnext : i + 1 < S.componentStop k) :
    let D := S.sourceInternalAlphaData k i hstart hnext
    ((a.order D.leftIndex : ℚ) + a.alphaValue D.alphaIndex =
        (D.weight.order : ℚ)) ∧
      (-(a.order D.rightIndex : ℚ) + a.alphaValue D.alphaIndex =
        (D.dualWeight.order : ℚ)) := by
  let D := S.sourceInternalAlphaData k i hstart hnext
  have hleft : (a.order D.leftIndex : ℚ) +
      a.alphaValue D.alphaIndex = (D.weight.order : ℚ) := by
    by_cases hk : k.val = 0
    · have hkFirst : k = S.sourceFirstComponent := by
        apply Fin.ext
        exact hk
      subst k
      exact S.source_firstComponent_internal_left i hstart hnext
    · exact S.source_noninitialComponent_internal_left k
        (Nat.pos_of_ne_zero hk) i hstart hnext
  refine ⟨hleft, ?_⟩
  have hsum := D.block.adjacent_order_sum D.index D.start_le D.next_lt_stop
  have hsumQ :
      (a.order D.leftIndex : ℚ) + (a.order D.rightIndex : ℚ) =
        2 * (D.block.scaleOrder : ℚ) := by
    exact_mod_cast hsum
  have hdual : (D.dualWeight.order : ℚ) =
      (D.weight.order : ℚ) - 2 * (D.block.scaleOrder : ℚ) := by
    exact_mod_cast D.dualWeightOrder_eq
  linarith

end BONG.StrictJordanAdaptedAlignment

end Bong
