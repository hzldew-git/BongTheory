/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveDefectDirect
import Bong.Bong.Beli2019Lemma79DefectOne
import Bong.Lattice.OmearaOddWeightPlane

/-!
# Beli (2019), Section 5: the odd-order alpha bound

When the target norm order is exactly one above the source norm order,
the target fundamental norm generator is an opposite-parity norm-group
value in the source fundamental lattice.  O'Meara's weight bound then gives
`alpha_i <= 1` at an internal Jordan coordinate.  This is the invariant
core of case 2 in the proof of condition 2.1(ii).
-/

namespace Bong

open Dyadic Module

universe u v

namespace JordanProfileOrder

/-- If two alternating profiles have the same scale, ordered effective
norms, and the target entry is exactly one above the source entry, then the
common local coordinate is even. -/
theorem even_of_effective_le_of_localOrder_succ
    {scale sourceEffective targetEffective : Int} {i : Nat}
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (heffective : sourceEffective ≤ targetEffective)
    (hcurrent : localOrder scale targetEffective i =
      localOrder scale sourceEffective i + 1) :
    Even i := by
  by_contra hodd
  rw [localOrder_odd_of_scale_le htargetScale hodd,
    localOrder_odd_of_scale_le hsourceScale hodd] at hcurrent
  omega

/-- Ordered effective norms can produce a strict rise only at an even
coordinate of the alternating profile. -/
theorem even_of_effective_le_of_localOrder_lt
    {scale sourceEffective targetEffective : Int} {i : Nat}
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (heffective : sourceEffective ≤ targetEffective)
    (hcurrent : localOrder scale sourceEffective i <
      localOrder scale targetEffective i) :
    Even i := by
  by_contra hodd
  rw [localOrder_odd_of_scale_le hsourceScale hodd,
    localOrder_odd_of_scale_le htargetScale hodd] at hcurrent
  omega

/-- Ordered effective norms can produce a strict drop only at an odd
coordinate of the alternating profile. -/
theorem odd_of_effective_le_of_localOrder_gt
    {scale sourceEffective targetEffective : Int} {i : Nat}
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (heffective : sourceEffective ≤ targetEffective)
    (hcurrent : localOrder scale targetEffective i <
      localOrder scale sourceEffective i) :
    ¬Even i := by
  intro heven
  rw [localOrder_even_of_scale_le htargetScale heven,
    localOrder_even_of_scale_le hsourceScale heven] at hcurrent
  omega

end JordanProfileOrder

namespace Lattice.WeakJordanDecomposition

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- The effective norm at a modular component's own scale is at most
`scale + e`.  This is the order form of O'Meara's standard inclusion
`2 s(L) ⊆ n(L)`. -/
theorem effectiveNormOrderAt_scale_le_scale_add_ramificationIndex
    {t : Nat} {L : Lattice K V}
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i)) ≤
      ordUnit K (W.scaleGenerator i) + (ramificationIndex K : Int) := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwoOrder : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_eq_coe.mp
    rw [coe_ordUnit]
    change ord K (2 : K) = _
    rw [← ramificationIndex_spec]
  have hideal : Lattice.principalIdeal (K := K)
        (((two * W.scaleGenerator i : Kˣ) : K)) ≤
      Lattice.principalIdeal (K := K) (W.normGeneratorUnit i : K) := by
    rw [← W.normIdeal_eq_normGeneratorUnit]
    have htwoScale := Lattice.twoScaleIdeal_le_normIdeal
      (W.component i).space (W.component i).lattice
    rw [Lattice.Omeara9319ExchangeSetup.twoScaleIdeal_eq_principalIdeal_two_mul_of_modular
      (W.modular i) (W.component_finrank_pos i)] at htwoScale
    simpa only [two, Units.val_mul, Units.val_mk0] using htwoScale
  have hord := (Lattice.principalIdeal_le_iff_ord_ge
    (Units.ne_zero (two * W.scaleGenerator i))
    (Units.ne_zero (W.normGeneratorUnit i))).mp hideal
  have hnorm : ordUnit K (W.normGeneratorUnit i) ≤
      ordUnit K (two * W.scaleGenerator i) := by
    apply WithTop.coe_le_coe.mp
    simpa only [coe_ordUnit] using hord
  rw [ordUnit_mul, htwoOrder] at hnorm
  exact (W.effectiveNormOrderAt_scale_le_normOrder i).trans (by omega)

end Lattice.WeakJordanDecomposition

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}
  {n s t : Nat}

/-- A fundamental-lattice inclusion compares the full internal weight
endpoints even when the two current BONG orders are unequal.  This is the
inequality used in Section 5.5, case 1(b):
`R_i + alpha_i ≤ S_i + beta_i`. -/
theorem order_add_alphaValue_le_of_fundamentalLattice_le
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    {H : Lattice.JordanDecomposition q M s}
    {J : Lattice.JordanDecomposition q N t}
    (Psource : JordanOrderProfileWitness a.toBONG H)
    (Ptarget : JordanOrderProfileWitness b.toBONG J)
    (i : Fin (n + 1))
    (hsourceInternal :
      (Psource.indexEquiv i.castSucc).2.val + 1 <
        H.componentRank (Psource.indexEquiv i.castSucc).1)
    (hfundamental :
      J.fundamentalLattice (Ptarget.indexEquiv i.castSucc).1 ≤
        H.fundamentalLattice (Psource.indexEquiv i.castSucc).1) :
    (a.order i.castSucc : ℚ) + a.alphaValue i ≤
      (b.order i.castSucc : ℚ) + b.alphaValue i := by
  have hweight :=
    Lattice.JordanDecomposition.fundamentalWeightOrder_anti_of_fundamentalLattice_le
      (J := J) (H := H)
      (Ptarget.indexEquiv i.castSucc).1
      (Psource.indexEquiv i.castSucc).1 hfundamental
  have hsourceFormula :=
    Psource.internal_weightOrder_eq_order_add_alpha i hsourceInternal
  have htargetUpper :=
    Ptarget.fundamentalWeightOrder_le_order_add_alpha i
  have hweightQ :
      (H.fundamentalWeightOrder
          (Psource.indexEquiv i.castSucc).1 : ℚ) ≤
        (J.fundamentalWeightOrder
          (Ptarget.indexEquiv i.castSucc).1 : ℚ) := by
    exact_mod_cast hweight
  linarith

/-- The ideal-theoretic core of Section 5, case 2.  The order equalities
are separated from the weak-profile arithmetic so that the same result is
usable after resolving an equal-scale collision. -/
theorem alphaValue_le_one_of_fundamentalLattice_le_current_succ
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    {H : Lattice.JordanDecomposition q M s}
    {J : Lattice.JordanDecomposition q N t}
    (Psource : JordanOrderProfileWitness a.toBONG H)
    (Ptarget : JordanOrderProfileWitness b.toBONG J)
    (i : Fin (n + 1))
    (hsourceInternal :
      (Psource.indexEquiv i.castSucc).2.val + 1 <
        H.componentRank (Psource.indexEquiv i.castSucc).1)
    (hfundamental :
      J.fundamentalLattice (Ptarget.indexEquiv i.castSucc).1 ≤
        H.fundamentalLattice (Psource.indexEquiv i.castSucc).1)
    (hsourceOrder : ordUnit K
        (H.fundamentalNormGenerator
          (Psource.indexEquiv i.castSucc).1) = a.order i.castSucc)
    (htargetOrder : ordUnit K
        (J.fundamentalNormGenerator
          (Ptarget.indexEquiv i.castSucc).1) = b.order i.castSucc)
    (hcurrent : b.order i.castSucc = a.order i.castSucc + 1) :
    a.alphaValue i ≤ 1 := by
  let p := (Psource.indexEquiv i.castSucc).1
  let r := (Ptarget.indexEquiv i.castSucc).1
  let A := H.fundamentalNormGenerator p
  let B := J.fundamentalNormGenerator r
  have hBmem : (B : K) ∈
      Lattice.normGroupSet q (H.fundamentalLattice p) := by
    apply Lattice.normGroupSet_mono hfundamental
    exact (J.fundamentalNormGenerator_spec r).1
  have hodd : Odd (ordUnit K A + ordUnit K B) := by
    refine ⟨ordUnit K A, ?_⟩
    dsimp only [A, B, p, r]
    rw [hsourceOrder, htargetOrder, hcurrent]
    omega
  have hweight :
      H.fundamentalWeightOrder p ≤ ordUnit K B := by
    exact Lattice.weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
      A B (H.fundamentalNormGenerator_spec p) hBmem hodd
  have hformula :=
    Psource.internal_weightOrder_eq_order_add_alpha i hsourceInternal
  have hweightQ : (H.fundamentalWeightOrder p : ℚ) ≤
      (ordUnit K B : ℚ) := by
    exact_mod_cast hweight
  have htargetQ : (ordUnit K B : ℚ) =
      (a.order i.castSucc : ℚ) + 1 := by
    dsimp only [B, r]
    rw [htargetOrder, hcurrent]
    push_cast
    ring
  change a.alphaValue i ≤ (1 : ℚ)
  change (H.fundamentalWeightOrder p : ℚ) =
      (a.order i.castSucc : ℚ) + a.alphaValue i at hformula
  linarith

namespace GoodBONG

/-- An even BONG order gap strictly below `2e` cannot be an equality case
in P3.  Integrality from Corollary 2.8 therefore forces the next integer
step below alpha. -/
theorem orderGap_add_one_le_alphaValue_of_even_of_lt_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {n : Nat} (a : GoodBONG q M (n + 1)) (i : Fin n)
    (heven : Even (a.orderGap i))
    (hlt : a.orderGap i < 2 * (ramificationIndex K : Int)) :
    ((a.orderGap i + 1 : Int) : ℚ) ≤ a.alphaValue i := by
  have hle : a.orderGap i ≤ 2 * (ramificationIndex K : Int) := hlt.le
  have hlower := (a.beli2009Lemma27_iii i hle).1
  have hnotOdd : ¬Odd (a.orderGap i) := by
    intro hodd
    rcases heven with ⟨p, hp⟩
    rcases hodd with ⟨r, hr⟩
    omega
  have hne : a.alphaValue i ≠ (a.orderGap i : ℚ) := by
    intro heq
    rcases (a.beli2009Lemma27_iii i hle).2.mp heq with htop | hodd
    · omega
    · exact hnotOdd hodd
  have hstrict : (a.orderGap i : ℚ) < a.alphaValue i :=
    lt_of_le_of_ne hlower (Ne.symm hne)
  have hintegral := a.beli2009Corollary28_i i (by
    intro hbad
    exact hnotOdd hbad.1)
  rcases hintegral with ⟨z, hz⟩
  have hgapz : a.orderGap i < z := by
    exact_mod_cast (show (a.orderGap i : ℚ) < (z : ℚ) by
      simpa only [← hz] using hstrict)
  have hstep : a.orderGap i + 1 ≤ z := by omega
  rw [hz]
  exact_mod_cast hstep

/-- If the equal-length comparison prefix at `i-1` has odd order and the
two newly adjoined source entries have even total order, the shifted
primary product with prefix lengths `i+1` and `i-1` also has odd order. -/
theorem shiftedPrimaryProduct_odd_of_previousPrefix_odd_of_sourcePair_even
    {n : Nat} (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiPrevious : 1 < i.val)
    (hprefix : Odd (ordUnit K
      (a.prefixProduct (i.val - 1) * b.prefixProduct (i.val - 1))))
    (hpair : Even
      (a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
        a.order ⟨i.val, i.lt_large⟩)) :
    Odd (ordUnit K ((-1 : Kˣ) * a.prefixProduct (i.val + 1) *
      b.prefixProduct (i.val - 1))) := by
  have hiLarge := i.lt_large
  have hiSmall := i.le_small
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  have hbaseOrder :
      ordUnit K (a.prefixProduct (i.val - 1) *
          b.prefixProduct (i.val - 1)) =
        a.orderSequence.prefixSum (i.val - 1) +
          b.orderSequence.prefixSum (i.val - 1) := by
    rw [ordUnit_mul,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i.val - 1) (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i.val - 1) (by omega)]
  have hsourcePrefix :
      a.orderSequence.prefixSum (i.val + 1) =
        a.orderSequence.prefixSum (i.val - 1) +
          a.orderSequence.entryOrZero (i.val - 1) +
            a.orderSequence.entryOrZero i.val := by
    have hfirst := a.orderSequence.prefixSum_succ (i.val - 1)
    have hsecond := a.orderSequence.prefixSum_succ i.val
    have hsub : i.val - 1 + 1 = i.val := by omega
    rw [hsub] at hfirst
    calc
      a.orderSequence.prefixSum (i.val + 1) =
          a.orderSequence.prefixSum i.val +
            a.orderSequence.entryOrZero i.val := hsecond
      _ = (a.orderSequence.prefixSum (i.val - 1) +
            a.orderSequence.entryOrZero (i.val - 1)) +
            a.orderSequence.entryOrZero i.val := by rw [hfirst]
      _ = _ := by ring
  have hshiftedOrder :
      ordUnit K ((-1 : Kˣ) * a.prefixProduct (i.val + 1) *
          b.prefixProduct (i.val - 1)) =
        a.orderSequence.prefixSum (i.val - 1) +
          b.orderSequence.prefixSum (i.val - 1) +
            (a.orderSequence.entryOrZero (i.val - 1) +
              a.orderSequence.entryOrZero i.val) := by
    rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i.val + 1) (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i.val - 1) (by omega), hsourcePrefix]
    ring
  have hpair' : Even
      (a.orderSequence.entryOrZero (i.val - 1) +
        a.orderSequence.entryOrZero i.val) := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hiLarge,
      BONG.GoodBONG.orderSequence_at, BONG.GoodBONG.orderSequence_at]
    exact hpair
  rw [hbaseOrder] at hprefix
  rw [hshiftedOrder]
  rcases hprefix with ⟨z, hz⟩
  rcases hpair' with ⟨w, hw⟩
  exact ⟨z + w, by omega⟩

/-- If the shifted capped defect vanishes, the primary candidate reduces
to its order coefficient `R_(i+1)-S_i`. -/
theorem representationAlphaValue_le_primaryCoefficient_of_defect_zero
    [Beli2006AlphaLaws.{u, v} K]
    {n : Nat} (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hzero : a.truncatedPrefixDefect b (-1)
      (i.val + 1) (i.val - 1) = 0) :
    a.representationAlphaValue b i ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) := by
  have hiSmall := i.le_small
  apply WithTop.coe_le_coe.mp
  rw [a.coe_representationAlphaValue b i]
  calc
    a.representationAlpha b i ≤ a.representationPrimaryDefect b i :=
      a.representationAlpha_le_primary b i
    _ = (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
      unfold representationPrimaryDefect
      rw [hzero, add_zero]

/-- The primary representation candidate can be capped on the target side.
For an internal previous prefix this gives Beli's bound
`A_i ≤ R_{i+1} - S_i + beta_{i-1}`. -/
theorem representationAlphaValue_le_primary_previousAlpha
    {n : Nat} (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiPrevious : 1 < i.val) :
    a.representationAlphaValue b i ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) +
        b.alphaValue ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
  have hiSmall := i.le_small
  have hiLarge := i.lt_large
  apply WithTop.coe_le_coe.mp
  rw [a.coe_representationAlphaValue b i]
  calc
    a.representationAlpha b i ≤ a.representationPrimaryDefect b i :=
      a.representationAlpha_le_primary b i
    _ ≤ (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        b.prefixAlphaCap (i.val - 1) := by
      unfold representationPrimaryDefect
      exact add_le_add_right
        (a.truncatedPrefixDefect_le_rightCap b (-1)
          (i.val + 1) (i.val - 1)) _
    _ = (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) +
        b.alphaValue ⟨i.val - 2, by omega⟩ : ℚ) := by
      rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
      norm_cast

end GoodBONG

end BONG

namespace Lattice.Beli2019Lemma51Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- Case 2 before the distinguished component, first in the strict
no-collision model.  A one-step current-order rise occurs at an even local
coordinate.  The target fundamental norm generator then lies in the source
fundamental lattice and has order one above its source counterpart, so the
preceding ideal-theoretic lemma gives `alpha_i <= 1`. -/
theorem noCollision_alphaValue_le_one_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc = a.order i.castSucc + 1) :
    a.alphaValue i ≤ 1 := by
  let H := D.largeNoCollisionJordan hlarge
  let J := D.smallNoCollisionJordan hsmall
  let Psource := D.largeNoCollisionProfileWitness hlarge a
  let Ptarget := D.smallNoCollisionProfileWitness hsmall b
  let p := (Psource.indexEquiv i.castSucc).1
  let r := (Ptarget.indexEquiv i.castSucc).1
  let localIndex := (Psource.indexEquiv i.castSucc).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b i.castSucc
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (Ptarget.indexEquiv i.castSucc).2.val :=
    hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeNoCollision_order_eq_localOrder
    hlarge a i.castSucc
  have htargetLocal := D.smallNoCollision_order_eq_localOrder
    hsmall b i.castSucc
  have htargetLocalNormalized :
      b.order i.castSucc =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order i.castSucc = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (Ptarget.indexEquiv i.castSucc).2.val := by
        simpa only [Ptarget, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex =
        JordanProfileOrder.localOrder scale sourceEffective localIndex + 1 := by
    change a.order i.castSucc =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order i.castSucc := htargetLocalNormalized.symm
      _ = a.order i.castSucc + 1 := hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex + 1 :=
        congrArg (fun z : Int => z + 1) hsourceLocal
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_succ
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order i.castSucc = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order i.castSucc = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective := by
    rw [← htargetOrderLocal, hcurrent, hsourceOrderLocal]
    omega
  have hrankEven : Even (J.componentRank r) := by
    change Even (finrank K (D.smallAlmostJordan.component r).carrier)
    have hparity := D.smallAlmostJordan_hasImproperEvenRank
    exact hparity.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r
        (by
          calc
            ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
              hscaleTarget
            _ < targetEffective := htargetStrict
            _ = D.smallAlmostJordan.effectiveNormOrderAt r
                (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hsourceInternal :
      (Psource.indexEquiv i.castSucc).2.val + 1 <
        H.componentRank (Psource.indexEquiv i.castSucc).1 := by
    change localIndex + 1 < H.componentRank p
    have hrankEq : H.componentRank p = J.componentRank r := by
      change (D.largeNoCollisionJordan hlarge).componentRank p =
        (D.smallNoCollisionJordan hsmall).componentRank r
      rw [← hrp]
      exact congrFun (D.noCollision_componentRank_eq
        hsmall hlarge hselected) p
    have hlocalLt : localIndex < H.componentRank p :=
      (Psource.indexEquiv i.castSucc).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have hsourceGeneratorOrder :
      ordUnit K (H.fundamentalNormGenerator p) = a.order i.castSucc := by
    have hgen := H.fundamentalNormGenerator_order_eq_effective p
    change ordUnit K (H.fundamentalNormGenerator p) = sourceEffective at hgen
    exact hgen.trans hsourceOrderLocal.symm
  have htargetGeneratorOrder :
      ordUnit K (J.fundamentalNormGenerator r) = b.order i.castSucc := by
    have hgen := J.fundamentalNormGenerator_order_eq_effective r
    change ordUnit K (J.fundamentalNormGenerator r) = targetEffective at hgen
    exact hgen.trans htargetOrderLocal.symm
  have hsourceScaleBound : H.fundamentalScaleOrder p ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K D.input.block.enlargedScaleGenerator
    have hmono := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    simpa only [D.largeAlmostJordan_scaleGenerator_selected] using hmono
  have hfundamental : J.fundamentalLattice r ≤
      H.fundamentalLattice p := by
    apply D.smallFundamentalLattice_le_large_of_scale_le r p
    · change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
        ordUnit K (D.smallAlmostJordan.scaleGenerator r)
      rw [hscaleTarget]
    · exact hsourceScaleBound
  exact BONG.alphaValue_le_one_of_fundamentalLattice_le_current_succ
    a b Psource Ptarget i hsourceInternal hfundamental
      hsourceGeneratorOrder htargetGeneratorOrder hcurrent

/-- Before the distinguished component, a strict rise of the target order
gives the full weight comparison `R_i + alpha_i ≤ S_i + beta_i`.  Unlike
the preceding one-step lemma, no assumption on the size of the rise is
used. -/
theorem noCollision_order_add_alphaValue_le_before_selected_of_current_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc < b.order i.castSucc) :
    (a.order i.castSucc : ℚ) + a.alphaValue i ≤
      (b.order i.castSucc : ℚ) + b.alphaValue i := by
  let H := D.largeNoCollisionJordan hlarge
  let J := D.smallNoCollisionJordan hsmall
  let Psource := D.largeNoCollisionProfileWitness hlarge a
  let Ptarget := D.smallNoCollisionProfileWitness hsmall b
  let p := (Psource.indexEquiv i.castSucc).1
  let r := (Ptarget.indexEquiv i.castSucc).1
  let localIndex := (Psource.indexEquiv i.castSucc).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b i.castSucc
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (Ptarget.indexEquiv i.castSucc).2.val :=
    hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeNoCollision_order_eq_localOrder
    hlarge a i.castSucc
  have htargetLocal := D.smallNoCollision_order_eq_localOrder
    hsmall b i.castSucc
  have htargetLocalNormalized :
      b.order i.castSucc =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order i.castSucc = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (Ptarget.indexEquiv i.castSucc).2.val := by
        simpa only [Ptarget, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex <
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change a.order i.castSucc =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
          a.order i.castSucc := hsourceLocal.symm
      _ < b.order i.castSucc := hcurrent
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex :=
        htargetLocalNormalized
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_lt
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order i.castSucc = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order i.castSucc = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective :=
    hsourceScale.trans_lt (by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent)
  have hrankEven : Even (J.componentRank r) := by
    change Even (finrank K (D.smallAlmostJordan.component r).carrier)
    exact D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq : H.componentRank p = J.componentRank r := by
    change (D.largeNoCollisionJordan hlarge).componentRank p =
      (D.smallNoCollisionJordan hsmall).componentRank r
    rw [← hrp]
    exact congrFun (D.noCollision_componentRank_eq
      hsmall hlarge hselected) p
  have hsourceInternal :
      (Psource.indexEquiv i.castSucc).2.val + 1 <
        H.componentRank (Psource.indexEquiv i.castSucc).1 := by
    change localIndex + 1 < H.componentRank p
    have hlocalLt : localIndex < H.componentRank p :=
      (Psource.indexEquiv i.castSucc).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have hsourceScaleBound : H.fundamentalScaleOrder p ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K D.input.block.enlargedScaleGenerator
    have hmono := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    simpa only [D.largeAlmostJordan_scaleGenerator_selected] using hmono
  have hfundamental : J.fundamentalLattice r ≤
      H.fundamentalLattice p := by
    apply D.smallFundamentalLattice_le_large_of_scale_le r p
    · change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
        ordUnit K (D.smallAlmostJordan.scaleGenerator r)
      rw [hscaleTarget]
    · exact hsourceScaleBound
  exact BONG.order_add_alphaValue_le_of_fundamentalLattice_le
    a b Psource Ptarget i hsourceInternal hfundamental

/-- In the same strict aligned range, a strict rise at the current
coordinate forces the source orders two places apart to be equal.  The
current coordinate is even, hence the next one is odd and its source order
is strictly above the target order.  Condition 2.1(i), already proved by
the explicit almost-Jordan coordinate certificate, rules out its direct
alternative and gives the adjacent-sum inequality.  Goodness supplies the
reverse two-step inequality.  This argument also covers the endpoint where
the second coordinate lies in the next Jordan component. -/
theorem noCollision_source_twoStep_eq_before_selected_of_current_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc < b.order i.castSucc) :
    ∃ htwo : i.val + 2 < n + 2,
      a.order i.castSucc = a.order ⟨i.val + 2, htwo⟩ := by
  let I : Fin (n + 2) := i.castSucc
  let Psource := D.largeNoCollisionProfileWitness hlarge a
  let Ptarget := D.smallNoCollisionProfileWitness hsmall b
  let p := (Psource.indexEquiv I).1
  let r := (Ptarget.indexEquiv I).1
  let localIndex := (Psource.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (Ptarget.indexEquiv I).2.val :=
    hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (Psource.indexEquiv I).1) = scale := rfl
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt
          (Psource.indexEquiv I).1 scale = sourceEffective := rfl
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (Ptarget.indexEquiv I).1) = scale := by
    exact hscaleTarget
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt
          (Ptarget.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator
              (Ptarget.indexEquiv I).1)) = targetEffective := rfl
  have hsourceLocal := D.largeNoCollision_order_eq_localOrder hlarge a I
  have htargetLocal := D.smallNoCollision_order_eq_localOrder hsmall b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (Ptarget.indexEquiv I).2.val := by
        simpa only [Ptarget, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex <
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
          a.order I := hsourceLocal.symm
      _ < b.order I := hcurrent
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex :=
        htargetLocalNormalized
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_lt
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective := by
    exact hsourceScale.trans_lt (by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent)
  have hrankEven : Even
      ((D.smallNoCollisionJordan hsmall).componentRank r) := by
    change Even (finrank K (D.smallAlmostJordan.component r).carrier)
    exact D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      (D.largeNoCollisionJordan hlarge).componentRank p =
        (D.smallNoCollisionJordan hsmall).componentRank r := by
    rw [← hrp]
    exact congrFun (D.noCollision_componentRank_eq
      hsmall hlarge hselected) p
  have hsourceInternal : localIndex + 1 <
      (D.largeNoCollisionJordan hlarge).componentRank p := by
    have hlocalLt : localIndex <
        (D.largeNoCollisionJordan hlarge).componentRank p :=
      (Psource.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have htargetInternal : (Ptarget.indexEquiv I).2.val + 1 <
      (D.smallNoCollisionJordan hsmall).componentRank r := by
    rw [← hlocal, ← hrankEq]
    exact hsourceInternal
  have hglobalNext : i.val + 1 < n + 2 := by omega
  have hoddNext : ¬Even (localIndex + 1) := by
    intro h
    exact (Nat.even_add_one.mp h) heven
  have hsourceNext :
      a.order ⟨i.val + 1, hglobalNext⟩ =
        2 * scale - sourceEffective := by
    have h := Psource.order_succ_eq_jordanExpectedOrder_of_local_succ
      I hglobalNext hsourceInternal
    rw [D.largeNoCollisionJordan_expectedOrder hlarge] at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    change a.order ⟨i.val + 1, hglobalNext⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex + 1) at h
    rw [JordanProfileOrder.localOrder_odd_of_scale_le
      hsourceScale hoddNext] at h
    exact h
  have htargetNext :
      b.order ⟨i.val + 1, hglobalNext⟩ =
        2 * scale - targetEffective := by
    have h := Ptarget.order_succ_eq_jordanExpectedOrder_of_local_succ
      I hglobalNext htargetInternal
    rw [D.smallNoCollisionJordan_expectedOrder hsmall] at h
    simp only [I] at h
    rw [htargetScaleAt] at h
    have htargetEffectiveScale :
        D.smallAlmostJordan.effectiveNormOrderAt
            (Ptarget.indexEquiv I).1 scale = targetEffective := by
      rw [← htargetScaleAt]
    rw [htargetEffectiveScale] at h
    have hlocalNext : (Ptarget.indexEquiv I).2.val + 1 =
        localIndex + 1 := by omega
    change b.order ⟨i.val + 1, hglobalNext⟩ =
      JordanProfileOrder.localOrder scale targetEffective
        ((Ptarget.indexEquiv I).2.val + 1) at h
    rw [hlocalNext, JordanProfileOrder.localOrder_odd_of_scale_le
      htargetScale hoddNext] at h
    exact h
  have hnextReverse :
      b.order ⟨i.val + 1, hglobalNext⟩ <
        a.order ⟨i.val + 1, hglobalNext⟩ := by
    rw [hsourceNext, htargetNext]
    have heffectiveStrict : sourceEffective < targetEffective := by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent
    omega
  rcases (D.noCollision_coordinate hsmall hlarge hselected a b
      (i.val + 1) hglobalNext).compare with hdirect |
        ⟨_hpositive, htwo, hpair⟩
  · have : False := by
      change a.order ⟨i.val + 1, hglobalNext⟩ ≤
        b.order ⟨i.val + 1, hglobalNext⟩ at hdirect
      exact (not_le_of_gt hnextReverse) hdirect
    contradiction
  · refine ⟨by omega, ?_⟩
    have htwoLe : a.order ⟨i.val + 2, by omega⟩ ≤ a.order I := by
      have hpair' : a.order ⟨i.val + 1, hglobalNext⟩ +
            a.order ⟨i.val + 2, by omega⟩ ≤
          b.order ⟨i.val, by omega⟩ +
            b.order ⟨i.val + 1, hglobalNext⟩ := by
        simpa only [BONG.GoodBONG.orderSequence_at,
          show i.val + 1 - 1 = i.val by omega,
          show i.val + 1 + 1 = i.val + 2 by omega] using hpair
      have hcurrentTarget : b.order ⟨i.val, by omega⟩ =
          targetEffective := by
        have hindex : (⟨i.val, by omega⟩ : Fin (n + 2)) = I := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact htargetOrderLocal
      rw [hsourceNext, htargetNext, hcurrentTarget] at hpair'
      rw [hsourceOrderLocal]
      omega
    apply le_antisymm
    · have htwoI : I.val + 2 < n + 2 := by
        change i.val + 2 < n + 2
        omega
      exact a.good I htwoI
    · exact htwoLe

/-- One-step specialization used in the odd-defect branch. -/
theorem noCollision_source_twoStep_eq_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc = a.order i.castSucc + 1) :
    ∃ htwo : i.val + 2 < n + 2,
      a.order i.castSucc = a.order ⟨i.val + 2, htwo⟩ := by
  exact D.noCollision_source_twoStep_eq_before_selected_of_current_lt
    hsmall hlarge hselected a b i hbefore (by omega)

/-- Case 1(b) of Section 5.5 in invariant form.  At a strict current-order
rise before the distinguished component, the common approximation is
bounded by both current alpha caps. -/
theorem noCollision_commonBound_before_selected_of_current_lt
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  let g : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  have hprevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hpreviousIndex :
      (⟨i.val - 1, hprevious⟩ : Fin (n + 2)) = g.castSucc := by
    apply Fin.ext
    rfl
  have hcurrentG : a.order g.castSucc < b.order g.castSucc := by
    rw [← hpreviousIndex]
    exact hcurrent
  obtain ⟨htwo, houterRaw⟩ :=
    D.noCollision_source_twoStep_eq_before_selected_of_current_lt
      hsmall hlarge hselected a b g hbefore hcurrentG
  have hnext : i.val + 1 < n + 2 := by
    have hg : g.val = i.val - 1 := rfl
    rw [hg] at htwo
    have := i.pos
    omega
  have hrightIndex :
      (⟨g.val + 2, htwo⟩ : Fin (n + 2)) =
        ⟨i.val + 1, hnext⟩ := by
    apply Fin.ext
    change g.val + 2 = i.val + 1
    simp only [g, BONG.GoodBONG.representationAlphaIndex]
    have := i.pos
    omega
  have houter : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val + 1, hnext⟩ := by
    calc
      a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          a.order g.castSucc := by
        exact congrArg a.order hpreviousIndex
      _ = a.order ⟨g.val + 2, htwo⟩ := houterRaw
      _ = a.order ⟨i.val + 1, hnext⟩ :=
        congrArg a.order hrightIndex
  have hrecurrenceTop :=
    a.orderGap_add_nextAlpha_eq_alpha_of_twoStep_eq i hnext houter
  have hrecurrence :
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue g := by
    simpa only [g] using (show
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) by
      exact_mod_cast hrecurrenceTop)
  have hcandidate :=
    a.representationAlphaValue_le_primary_nextAlpha b i hnext
  push_cast at hcandidate hrecurrence
  have hupper : a.representationAlphaValue b i ≤
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) -
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
        a.alphaValue g := by
    calc
      a.representationAlphaValue b i ≤
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
            (b.order ⟨i.val - 1,
              (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
            a.alphaValue ⟨i.val, by omega⟩ := hcandidate
      _ = (a.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) -
          (b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
            a.alphaValue g := by linarith [hrecurrence]
  have hweight :=
    D.noCollision_order_add_alphaValue_le_before_selected_of_current_lt
      hsmall hlarge hselected a b g hbefore hcurrentG
  have hcurrentQ :
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) <
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) := by
    exact_mod_cast hcurrent
  have hweightCanonical :
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue g ≤
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          b.alphaValue g := by
    simpa only [← hpreviousIndex] using hweight
  have hsource : a.representationAlphaValue b i ≤ a.alphaValue g := by
    linarith
  have htarget : a.representationAlphaValue b i ≤ b.alphaValue g := by
    linarith
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large,
    ← a.coe_representationAlphaValue b i]
  apply le_min
  · exact_mod_cast hsource
  · exact_mod_cast htarget

/-- Attach the Lemma 5.13 common scalar to the strict-rise cap estimate. -/
theorem noCollision_commonCertificate_before_selected_of_current_lt
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrentLt : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩)
    (hnotSucc : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let localData := D.noCollision_aligned_lemma513LocalData
    hsmall hlarge hselected a b
  obtain ⟨X, hsource, htarget⟩ :=
    localData.commonApproximation i hi hnotSucc
  exact BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.common
    X hsource htarget
      (D.noCollision_commonBound_before_selected_of_current_lt
        hsmall hlarge hselected a b i hbefore hcurrentLt)

/-- Case 2 of Section 5.5 on a common component before the distinguished
component.  The primary candidate for `A_i` is at most
`R_(i+1) - S_i + alpha_(i+1)`.  The preceding two-step equality turns the
first and third terms into `alpha_i`, while `S_i = R_i + 1`; the odd-weight
estimate above gives `alpha_i ≤ 1`. -/
theorem noCollision_representationAlphaValue_le_zero_before_selected
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    a.representationAlphaValue b i ≤ 0 := by
  let g : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  have hprevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hpreviousIndex :
      (⟨i.val - 1, hprevious⟩ : Fin (n + 2)) = g.castSucc := by
    apply Fin.ext
    rfl
  have hcurrentOrder : b.order g.castSucc = a.order g.castSucc + 1 := by
    have h := hcurrent
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hprevious,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hprevious] at h
    simp only [BONG.GoodBONG.orderSequence_at] at h
    rw [← hpreviousIndex]
    exact h
  have halpha : a.alphaValue g ≤ 1 :=
    D.noCollision_alphaValue_le_one_before_selected
      hsmall hlarge hselected a b g hbefore hcurrentOrder
  obtain ⟨htwo, houterRaw⟩ :=
    D.noCollision_source_twoStep_eq_before_selected
      hsmall hlarge hselected a b g hbefore hcurrentOrder
  have hnext : i.val + 1 < n + 2 := by
    have hg : g.val = i.val - 1 := rfl
    rw [hg] at htwo
    omega
  have houter : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val + 1, hnext⟩ := by
    have hrightIndex :
        (⟨g.val + 2, htwo⟩ : Fin (n + 2)) =
          ⟨i.val + 1, hnext⟩ := by
      apply Fin.ext
      change g.val + 2 = i.val + 1
      simp only [g, BONG.GoodBONG.representationAlphaIndex]
      have := i.pos
      omega
    calc
      a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          a.order g.castSucc := by
        apply congrArg a.order
        exact hpreviousIndex
      _ = a.order ⟨g.val + 2, htwo⟩ := houterRaw
      _ = a.order ⟨i.val + 1, hnext⟩ := by
        exact congrArg a.order hrightIndex
  have hrecurrenceTop :=
    a.orderGap_add_nextAlpha_eq_alpha_of_twoStep_eq i hnext houter
  have hrecurrence :
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue g := by
    simpa only [g] using (show
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) by
      exact_mod_cast hrecurrenceTop)
  have hcandidate :=
    a.representationAlphaValue_le_primary_nextAlpha b i hnext
  have hcurrentCanonical : b.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ + 1 := by
    calc
      b.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          b.order g.castSucc := by
        apply congrArg b.order
        exact hpreviousIndex
      _ = a.order g.castSucc + 1 := hcurrentOrder
      _ = a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ + 1 := by
        rw [← congrArg a.order hpreviousIndex]
  have hcurrentCanonicalQ :
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) =
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) + 1 := by
    exact_mod_cast hcurrentCanonical
  push_cast at hcandidate hrecurrence
  calc
    a.representationAlphaValue b i ≤
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ := hcandidate
    _ = ((a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (a.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩) - 1 := by
      rw [hcurrentCanonicalQ]
      ring
    _ = a.alphaValue g - 1 := by rw [hrecurrence]
    _ ≤ 0 := by linarith

/-
/-- In the one-step reverse-order branch `R_i = S_i + 1`, Lemma 5.13(ii)
at the preceding boundary gives an odd comparison prefix.  The even source
Jordan pair preserves oddness after shifting the primary prefix lengths;
P3 and Corollary 2.8 then give `A_i ≤ alpha_i`. -/
theorem noCollision_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1) :
    a.representationAlphaValue b i ≤
      a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change a.representationAlphaValue b i ≤ a.alphaValue g
  change a.order g.castSucc = b.order g.castSucc + 1 at hcurrent
  have hgt : b.order g.castSucc < a.order g.castSucc := by omega
  rcases D.noCollision_source_previous_twoStep_eq_before_selected_of_current_gt
      hsmall hlarge hselected a b g hbefore hgt with
    ⟨hpos, hnext, htwo, hpreviousStrict, hcurrentCases,
      hgapEquality, hevenPair, hgapEven, hgapLt⟩
  have hiPrevious : 1 < i.val := by
    change 0 < i.val - 1 at hpos
    omega
  have hiLarge := i.lt_large
  have hiSmall := i.le_small
  have hpreviousCurrent :
      b.order ⟨g.val - 1, by omega⟩ =
        a.order ⟨g.val - 1, by omega⟩ + 1 := by
    omega
  let j : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val - 1, by omega, by omega, by omega⟩
  have hj : D.Lemma517Range j := by
    change j.val ≤ D.lemma517Cutoff
    change i.val ≤ D.lemma517Cutoff at hi
    dsimp only [j]
    omega
  have hentryIndex :
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 2)) =
        ⟨g.val - 1, by omega⟩ := by
    apply Fin.ext
    rfl
  have hpreviousEntry :
      b.orderSequence.entryOrZero (j.val - 1) =
        a.orderSequence.entryOrZero (j.val - 1) + 1 := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := j.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := j.lt_large; omega),
      BONG.GoodBONG.orderSequence_at, BONG.GoodBONG.orderSequence_at,
      hentryIndex]
    exact hpreviousCurrent
  let localData := D.noCollision_aligned_lemma513LocalData
    hsmall hlarge hselected a b
  have hpreviousSum :=
    localData.previousPrefixSum_eq j hj hpreviousEntry
  have hprefixOddRaw :=
    a.comparisonPrefixProduct_order_odd_of_previous_prefix_eq b
      j.val j.pos j.lt_large.le j.lt_large.le hpreviousSum hpreviousEntry
  have hprefixOdd : Odd (ordUnit K
      (a.prefixProduct (i.val - 1) * b.prefixProduct (i.val - 1))) := by
    simpa only [j] using hprefixOddRaw
  have hnextIndex :
      (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hcurrentIndex : g.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hevenCurrentNext : Even
      (a.order ⟨i.val - 1, by omega⟩ +
        a.order ⟨i.val, i.lt_large⟩) := by
    have hpair := hevenPair
    rw [htwo, hnextIndex, hcurrentIndex] at hpair
    simpa only [add_comm] using hpair
  have hshiftOdd :=
    a.shiftedPrimaryProduct_odd_of_previousPrefix_odd_of_sourcePair_even
      b i hiPrevious hprefixOdd hevenCurrentNext
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed b
    (-1) (i.val + 1) (i.val - 1) hshiftOdd
  have hcandidate :=
    a.representationAlphaValue_le_primaryCoefficient_of_defect_zero b i hzero
  have halphaLower :=
    a.orderGap_add_one_le_alphaValue_of_even_of_lt_twoE g hgapEven hgapLt
  have hnextGapIndex : g.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hcurrentGapIndex : g.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := hcurrentIndex
  push_cast at hcandidate
  push_cast at halphaLower
  unfold BONG.GoodBONG.orderGap at halphaLower
  rw [hnextGapIndex, hcurrentGapIndex] at halphaLower
  push_cast at halphaLower
  have hcurrentQ : (a.order g.castSucc : ℚ) =
      (b.order g.castSucc : ℚ) + 1 := by exact_mod_cast hcurrent
  rw [hcurrentGapIndex] at hcurrentQ
  linarith
-/

/-- In the reverse-order branch, condition (i)'s adjacent-pair alternative,
the target alpha-endpoint monotonicity, and the target cap in the primary
representation candidate already imply `A_i ≤ beta_i`. -/
theorem noCollision_representationAlphaValue_le_targetAlpha_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc <
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc) :
    a.representationAlphaValue b i ≤
      b.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  have hgi : g.val = i.val - 1 := rfl
  change b.order g.castSucc < a.order g.castSucc at hcurrent
  rcases (D.noCollision_coordinate hsmall hlarge hselected a b
      g.val g.castSucc.isLt).compare with hdirect | hpairData
  · have hdirect' : a.order g.castSucc ≤ b.order g.castSucc := by
      have hraw : a.order ⟨g.val, g.castSucc.isLt⟩ ≤
          b.order ⟨g.val, g.castSucc.isLt⟩ := by
        simpa only [BONG.GoodBONG.orderSequence_at] using hdirect
      have hindex : (⟨g.val, g.castSucc.isLt⟩ : Fin (n + 2)) =
          g.castSucc := by
        apply Fin.ext
        rfl
      rw [hindex] at hraw
      exact hraw
    omega
  · obtain ⟨hpositive, hnext, hpair⟩ := hpairData
    have hiPrevious : 1 < i.val := by
      change 0 < i.val - 1 at hpositive
      omega
    let previousAlpha : Fin (n + 1) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    have hpreviousLe : previousAlpha ≤ g := by
      change i.val - 2 ≤ i.val - 1
      omega
    have hendpoint := b.alphaLeftEndpoint_monotone hpreviousLe
    change (b.order previousAlpha.castSucc : ℚ) +
        b.alphaValue previousAlpha ≤
      (b.order g.castSucc : ℚ) + b.alphaValue g at hendpoint
    have hcandidate :=
      a.representationAlphaValue_le_primary_previousAlpha b i hiPrevious
    have hnextIndex :
        (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have hpreviousIndex :
        (⟨g.val - 1, by omega⟩ : Fin (n + 2)) =
          previousAlpha.castSucc := by
      apply Fin.ext
      change (i.val - 1) - 1 = i.val - 2
      omega
    have hpairRaw :
        a.order ⟨g.val, g.castSucc.isLt⟩ +
            a.order ⟨g.val + 1, hnext⟩ ≤
          b.order ⟨g.val - 1, by omega⟩ +
            b.order ⟨g.val, g.castSucc.isLt⟩ := by
      simpa only [BONG.GoodBONG.orderSequence_at] using hpair
    have hpairQ :
        (a.order ⟨g.val, g.castSucc.isLt⟩ : ℚ) +
            (a.order ⟨g.val + 1, hnext⟩ : ℚ) ≤
          (b.order ⟨g.val - 1, by omega⟩ : ℚ) +
            (b.order ⟨g.val, g.castSucc.isLt⟩ : ℚ) := by
      exact_mod_cast hpairRaw
    have hsourceCurrentValue :
        a.order ⟨g.val, g.castSucc.isLt⟩ = a.order g.castSucc := by
      apply congrArg a.order
      apply Fin.ext
      rfl
    have htargetCurrentValue :
        b.order ⟨g.val, g.castSucc.isLt⟩ = b.order g.castSucc := by
      apply congrArg b.order
      apply Fin.ext
      rfl
    have hsourceNextValue :
        a.order ⟨g.val + 1, hnext⟩ =
          a.order ⟨i.val, i.lt_large⟩ := congrArg a.order hnextIndex
    have htargetPreviousValue :
        b.order ⟨g.val - 1, by omega⟩ =
          b.order previousAlpha.castSucc := congrArg b.order hpreviousIndex
    have hcandidate' : a.representationAlphaValue b i ≤
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (b.order g.castSucc : ℚ) + b.alphaValue previousAlpha := by
      have hcurrentMathIndex :
          (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
            g.castSucc := by
        apply Fin.ext
        rfl
      have hpreviousAlphaIndex :
          (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)) =
            previousAlpha := by
        apply Fin.ext
        rfl
      push_cast at hcandidate
      rw [hcurrentMathIndex, hpreviousAlphaIndex] at hcandidate
      exact hcandidate
    have hcurrentQ : (b.order g.castSucc : ℚ) <
        (a.order g.castSucc : ℚ) := by
      exact_mod_cast hcurrent
    rw [hsourceCurrentValue, htargetCurrentValue,
      hsourceNextValue, htargetPreviousValue] at hpairQ
    linarith

/-- In the reverse-order branch `S_i < R_i`, the current coordinate is odd.
Its predecessor is therefore an even coordinate in the same Jordan component.
The already established strict-rise branch, applied at that predecessor, forces
the source two-step equality `R_{i-1} = R_{i+1}` used in Section 5.5(c). -/
theorem noCollision_source_previous_twoStep_eq_before_selected_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc < a.order i.castSucc) :
    ∃ (hpos : 0 < i.val) (hnext : i.val + 1 < n + 2),
      a.order ⟨i.val - 1, by omega⟩ =
        a.order ⟨i.val + 1, hnext⟩ ∧
      a.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val - 1, by omega⟩ ∧
      (a.order i.castSucc = b.order i.castSucc + 1 ∨
        a.order i.castSucc = b.order i.castSucc + 2) ∧
      b.order ⟨i.val - 1, by omega⟩ -
          a.order ⟨i.val - 1, by omega⟩ =
        a.order i.castSucc - b.order i.castSucc ∧
      Even (a.order ⟨i.val - 1, by omega⟩ + a.order i.castSucc) ∧
      Even (a.orderGap i) ∧
      a.orderGap i < 2 * (ramificationIndex K : Int) := by
  let I : Fin (n + 2) := i.castSucc
  let Psource := D.largeNoCollisionProfileWitness hlarge a
  let Ptarget := D.smallNoCollisionProfileWitness hsmall b
  let p := (Psource.indexEquiv I).1
  let r := (Ptarget.indexEquiv I).1
  let localIndex := (Psource.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (Ptarget.indexEquiv I).2.val :=
    hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have heffectiveUpper : targetEffective ≤ sourceEffective + 2 := by
    have hupper := (D.common_effectiveNormOrder_bounds p hbefore).2
    change D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) ≤
      D.largeAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) + 2
    rw [← hrp, ← hscaleRaw]
    exact hupper
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have htargetCeiling :
      targetEffective ≤ scale + (ramificationIndex K : Int) := by
    have h :=
      D.smallAlmostJordan.effectiveNormOrderAt_scale_le_scale_add_ramificationIndex r
    change D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) +
        (ramificationIndex K : Int) at h
    simpa only [targetEffective, hscaleTarget] using h
  have hsourceLocal := D.largeNoCollision_order_eq_localOrder hlarge a I
  have htargetLocal := D.smallNoCollision_order_eq_localOrder hsmall b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (Ptarget.indexEquiv I).2.val := by
        simpa only [Ptarget, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have heffectiveGap :
      targetEffective = sourceEffective + 1 ∨
        targetEffective = sourceEffective + 2 := by
    have hstrict : sourceEffective < targetEffective := by
      rw [JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd,
        JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
        at hlocalCurrent
      omega
    omega
  have hcurrentGap :
      a.order I = b.order I + 1 ∨ a.order I = b.order I + 2 := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
    rcases heffectiveGap with hgap | hgap
    · left
      omega
    · right
      omega
  have hlocalPos : 0 < localIndex := by
    by_contra h
    have hz : localIndex = 0 := by omega
    apply hodd
    rw [hz]
    simp
  have hglobalPos : 0 < i.val := by
    have hindex := Psource.index_val_eq_componentStart_add_local I
    change I.val = _ + localIndex at hindex
    change 0 < I.val
    omega
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hpreviousCast : previous.castSucc =
      Psource.indexEquiv.symm
        ⟨p, ⟨localIndex - 1, by
          change localIndex - 1 <
            (D.largeNoCollisionJordan hlarge).componentRank p
          have := (Psource.indexEquiv I).2.isLt
          change localIndex <
            (D.largeNoCollisionJordan hlarge).componentRank p at this
          omega⟩⟩ := by
    have hpredVal := Psource.inverse_index_val_local_pred
      p (Psource.indexEquiv I).2 (by simpa only [localIndex] using hlocalPos)
    have hcurrentInverse : Psource.indexEquiv.symm (Psource.indexEquiv I) = I :=
      Psource.indexEquiv.symm_apply_apply I
    apply Fin.ext
    change i.val - 1 = _
    have hpredVal' :
        (Psource.indexEquiv.symm
          ⟨p, ⟨localIndex - 1, by
            change localIndex - 1 <
              (D.largeNoCollisionJordan hlarge).componentRank p
            have := (Psource.indexEquiv I).2.isLt
            change localIndex <
              (D.largeNoCollisionJordan hlarge).componentRank p at this
            omega⟩⟩).val + 1 = I.val := by
      simpa only [p, localIndex] using
        hpredVal.trans (congrArg Fin.val hcurrentInverse)
    have hpredVal'' :
        (Psource.indexEquiv.symm
          ⟨p, ⟨localIndex - 1, by
            change localIndex - 1 <
              (D.largeNoCollisionJordan hlarge).componentRank p
            have := (Psource.indexEquiv I).2.isLt
            change localIndex <
              (D.largeNoCollisionJordan hlarge).componentRank p at this
            omega⟩⟩).val + 1 = i.val := by
      exact hpredVal'.trans (show I.val = i.val by rfl)
    omega
  have hpreviousComponent :
      (Psource.indexEquiv previous.castSucc).1 = p := by
    rw [hpreviousCast, Psource.indexEquiv.apply_symm_apply]
  have hpreviousBefore :
      (Psource.indexEquiv previous.castSucc).1 <
        D.largeSelectedPosition := by
    rw [hpreviousComponent]
    exact hbefore
  have hevenPrevious : Even (localIndex - 1) := by
    rcases Nat.not_even_iff_odd.mp hodd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hsourcePrevious : a.order previous.castSucc = sourceEffective := by
    have h := Psource.order_pred_eq_jordanExpectedOrder_of_local_pred I
      (by simpa only [localIndex] using hlocalPos)
    rw [D.largeNoCollisionJordan_expectedOrder hlarge] at h
    change a.order ⟨I.val - 1, by omega⟩ =
      JordanProfileOrder.localOrder scale sourceEffective (localIndex - 1) at h
    rw [JordanProfileOrder.localOrder_even_of_scale_le
      hsourceScale hevenPrevious] at h
    have hindex : (⟨I.val - 1, by omega⟩ : Fin (n + 2)) =
        previous.castSucc := by
      apply Fin.ext
      simp only [I, previous, Fin.val_castSucc]
    rw [hindex] at h
    exact h
  have htargetPrevious : b.order previous.castSucc = targetEffective := by
    have htargetPos : 0 < (Ptarget.indexEquiv I).2.val := by
      rw [← hlocal]
      exact hlocalPos
    have h := Ptarget.order_pred_eq_jordanExpectedOrder_of_local_pred I htargetPos
    rw [D.smallNoCollisionJordan_expectedOrder hsmall] at h
    change b.order ⟨I.val - 1, by omega⟩ =
      JordanProfileOrder.localOrder
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
          ((Ptarget.indexEquiv I).2.val - 1) at h
    have hprevLocal : (Ptarget.indexEquiv I).2.val - 1 = localIndex - 1 := by
      omega
    rw [hscaleTarget, hprevLocal,
      JordanProfileOrder.localOrder_even_of_scale_le
        htargetScale hevenPrevious] at h
    have hindex : (⟨I.val - 1, by omega⟩ : Fin (n + 2)) =
        previous.castSucc := by
      apply Fin.ext
      simp only [I, previous, Fin.val_castSucc]
    rw [hindex] at h
    exact h
  have heffectiveStrict : sourceEffective < targetEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd] at hcurrent
    omega
  have hpreviousStrict : a.order previous.castSucc < b.order previous.castSucc := by
    rw [hsourcePrevious, htargetPrevious]
    exact heffectiveStrict
  have hgapEquality :
      b.order previous.castSucc - a.order previous.castSucc =
        a.order I - b.order I := by
    rw [hsourcePrevious, htargetPrevious, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
    ring
  have hevenPair : Even (a.order previous.castSucc + a.order I) := by
    refine ⟨scale, ?_⟩
    rw [hsourcePrevious, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
    omega
  obtain ⟨htwo, htwoEq⟩ :=
    D.noCollision_source_twoStep_eq_before_selected_of_current_lt
      hsmall hlarge hselected a b previous hpreviousBefore hpreviousStrict
  have hnext : i.val + 1 < n + 2 := by
    change previous.val + 2 < n + 2 at htwo
    dsimp only [previous] at htwo
    omega
  have hrightGap :
      (⟨previous.val + 2, htwo⟩ : Fin (n + 2)) = i.succ := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hleftGap : previous.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have htwoGap :
      a.order ⟨i.val - 1, by omega⟩ = a.order i.succ := by
    rw [← hleftGap, ← hrightGap]
    exact htwoEq
  have hnextEffective : a.order i.succ = sourceEffective := by
    calc
      a.order i.succ = a.order ⟨i.val - 1, by omega⟩ := htwoGap.symm
      _ = a.order previous.castSucc := by rw [hleftGap]
      _ = sourceEffective := hsourcePrevious
  have hgapFormula : a.orderGap i = 2 * (sourceEffective - scale) := by
    unfold BONG.GoodBONG.orderGap
    rw [hnextEffective, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
    ring
  have hgapEven : Even (a.orderGap i) := by
    refine ⟨sourceEffective - scale, ?_⟩
    rw [hgapFormula]
    ring
  have hgapLt : a.orderGap i < 2 * (ramificationIndex K : Int) := by
    have hsourceCeiling :
        sourceEffective < scale + (ramificationIndex K : Int) :=
      heffectiveStrict.trans_le htargetCeiling
    rw [hgapFormula]
    omega
  refine ⟨hglobalPos, hnext, ?_, ?_, ?_, ?_, ?_, hgapEven, hgapLt⟩
  · have hright :
        (⟨previous.val + 2, htwo⟩ : Fin (n + 2)) =
          ⟨i.val + 1, hnext⟩ := by
      apply Fin.ext
      dsimp only [previous]
      omega
    have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft, hright] at htwoEq
    exact htwoEq
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hpreviousStrict
    exact hpreviousStrict
  · exact hcurrentGap
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hgapEquality
    exact hgapEquality
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hevenPair
    exact hevenPair

/-- The preceding numerical estimate together with Lemma 5.13(ii)'s
prefix-sum identity is the complete `odd` certificate on this range. -/
theorem noCollision_oddCertificate_before_selected
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let localData := D.noCollision_aligned_lemma513LocalData
    hsmall hlarge hselected a b
  apply BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.odd
  · exact localData.prefixSum_succ_of_current_succ i hi hcurrent
  · rw [← a.coe_representationAlphaValue b i]
    exact_mod_cast D.noCollision_representationAlphaValue_le_zero_before_selected
      hsmall hlarge hselected a b i hbefore hcurrent

end Lattice.Beli2019Lemma51Data

end Bong
