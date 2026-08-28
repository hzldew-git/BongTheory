/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009SignedDeterminantWeight
import Bong.Bong.Beli2009WeightIdealIsometry
import Bong.Bong.JordanProfileMerge
import Bong.Lattice.BlockProductOrthogonalDecomposition
import Bong.Lattice.OmearaOddRankProper

/-!
# Signed determinant weight bounds for modular lattices

This module applies the many-pair BONG calculation to one modular lattice.
The lattice is regarded as a one-component weak Jordan decomposition.  Beli
(2003), Lemma 4.7 supplies the alternating order profile of an arbitrary
good BONG, and every odd entry has order at most the modular scale.  Thus any
ambient norm order `F` above that scale controls all adjacent pairs.

For even rank this proves the intrinsic estimate

`ord w(L) - F <= d((-1)^(rank/2) det L)`.

It is precisely the arbitrary-rank endpoint fact suppressed when Lemma 3.2
is used at the right boundary of a Jordan component in Beli (2019), Lemma
5.13.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

namespace Lattice.WeakJordanDecomposition

/-- A positive-rank modular lattice as a one-component weak Jordan
decomposition. -/
noncomputable def singleOfModular (s : Kˣ)
    (hmodular : Lattice.IsModular q L s) (hpos : 0 < finrank K V) :
    Lattice.WeakJordanDecomposition q L 1 where
  toOrthogonalDecomposition :=
    Lattice.singleOrthogonalDecomposition q L
  scaleGenerator := fun _ ↦ s
  modular := by
    intro i
    exact hmodular.mapLatticeIsometry
      (Lattice.wholeQuadraticSublatticeIsometry q L)
  component_finrank_pos := by
    intro i
    have hrank :=
      (Lattice.wholeQuadraticSublatticeIsometry q L).toLinearEquiv.finrank_eq
    change 0 < finrank K
      (Lattice.wholeQuadraticSublattice q L).carrier
    omega
  scaleOrder_mono := by
    intro i j hij
    exact le_rfl

/-- The one-component scale sequence is strictly increasing vacuously. -/
theorem singleOfModular_scaleOrder_strict (s : Kˣ)
    (hmodular : Lattice.IsModular q L s) (hpos : 0 < finrank K V) :
    StrictMono (fun i ↦ ordUnit K
      ((singleOfModular s hmodular hpos).scaleGenerator i)) := by
  intro i j hij
  have hi : i.val = 0 := by omega
  have hj : j.val = 0 := by omega
  omega

end Lattice.WeakJordanDecomposition

namespace Lattice.IsModular

set_option maxHeartbeats 1000000 in
/-- The arbitrary-even-rank signed determinant estimate for a modular
lattice.  The integer `F` may be the norm order of any larger fundamental
lattice containing this component; only `ord(s) <= F` is needed. -/
theorem weightIdealOrder_sub_le_defect_signedDeterminant_of_even_rank
    [BONGGoodExistenceLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (hmodular : Lattice.IsModular q L s) (hpos : 0 < finrank K V)
    (pairs : Nat) (hrank : finrank K V = 2 * pairs + 2)
    (F : Int) (hscaleF : ordUnit K s <= F) :
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ) <=
      BONG.GoodBONG.defectOrder (K := K)
        (((-1 : Kˣ) ^ (pairs + 1)) * Lattice.determinantUnit q L) := by
  let cRaw := Classical.choice (Bong.exists_good_bong q L)
  let c : BONG.GoodBONG q L (2 * pairs + 2) := cRaw.castLength hrank
  let W := Lattice.WeakJordanDecomposition.singleOfModular
    s hmodular hpos
  let hstrict :=
    Lattice.WeakJordanDecomposition.singleOfModular_scaleOrder_strict
      s hmodular hpos
  let P : BONG.JordanOrderProfileWitness c.toBONG
      (W.toJordan hstrict) :=
    Classical.choice
      (c.toBONG.beliLemma47_profile c.good (W.toJordan hstrict))
  let x := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
  have horders : ∀ (t : Nat) (ht : t < pairs + 1),
      c.order ⟨2 * t + 1, by omega⟩ <= F := by
    intro t ht
    let I : Fin (2 * pairs + 2) := ⟨2 * t + 1, by omega⟩
    have hcomponent : (x.indexEquiv I).1 = (0 : Fin 1) :=
      Subsingleton.elim _ _
    have hglobal := x.index_val_eq_componentStart_add_local I
    have hlocal : (x.indexEquiv I).2.val = 2 * t + 1 := by
      rw [hcomponent] at hglobal
      have hsum :
          (∑ k ∈ Finset.Iio (0 : Fin 1),
            finrank K (W.component k).carrier) = 0 := by
        simp
      rw [hsum, zero_add] at hglobal
      exact hglobal.symm
    have horder := x.order_eq I
    change c.order I = JordanProfileOrder.localOrder
      (ordUnit K (W.scaleGenerator (x.indexEquiv I).1))
      (W.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at horder
    rw [hcomponent, hlocal] at horder
    let effective := W.effectiveNormOrderAt (0 : Fin 1) (ordUnit K s)
    have hscaleEffective : ordUnit K s <= effective := by
      exact W.targetScale_le_effectiveNormOrderAt (0 : Fin 1)
        (ordUnit K s)
    have hodd : ¬Even (2 * t + 1) := by
      rintro ⟨k, hk⟩
      omega
    have hlocalOrder :
        JordanProfileOrder.localOrder (ordUnit K s) effective (2 * t + 1) =
          2 * ordUnit K s - effective :=
      JordanProfileOrder.localOrder_odd_of_scale_le hscaleEffective hodd
    have heffectiveScale :
        2 * ordUnit K s - effective <= ordUnit K s := by omega
    have horder' : c.order I = 2 * ordUnit K s - effective := by
      simpa only [W, Lattice.WeakJordanDecomposition.singleOfModular,
        effective] using horder.trans hlocalOrder
    change c.order I <= F
    rw [horder']
    exact heffectiveScale.trans hscaleF
  exact c.weightIdealOrder_sub_le_defectOrder_signedDeterminant
    pairs F horders

set_option maxHeartbeats 1000000 in
/-- Sharpened even-rank form with the actual odd BONG order as threshold.
If `A` is a norm generator, a one-component modular profile has odd entries
`2 ord(s) - ord(A)`.  Consequently any `F` above that value can replace the
coarser hypothesis `ord(s) <= F` used by the preceding convenience theorem. -/
theorem weightIdealOrder_sub_le_defect_signedDeterminant_of_even_rank_of_normGenerator
    [BONGGoodExistenceLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (hmodular : Lattice.IsModular q L s) (hpos : 0 < finrank K V)
    (pairs : Nat) (hrank : finrank K V = 2 * pairs + 2)
    (A : Kˣ) (hA : Lattice.IsNormGeneratorValue q L A)
    (F : Int) (hoddF : 2 * ordUnit K s - ordUnit K A <= F) :
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ) <=
      BONG.GoodBONG.defectOrder (K := K)
        (((-1 : Kˣ) ^ (pairs + 1)) * Lattice.determinantUnit q L) := by
  let cRaw := Classical.choice (Bong.exists_good_bong q L)
  let c : BONG.GoodBONG q L (2 * pairs + 2) := cRaw.castLength hrank
  let W := Lattice.WeakJordanDecomposition.singleOfModular
    s hmodular hpos
  let hstrict :=
    Lattice.WeakJordanDecomposition.singleOfModular_scaleOrder_strict
      s hmodular hpos
  let P : BONG.JordanOrderProfileWitness c.toBONG
      (W.toJordan hstrict) :=
    Classical.choice
      (c.toBONG.beliLemma47_profile c.good (W.toJordan hstrict))
  let x := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
  have hAComponent : Lattice.IsNormGeneratorValue
      (W.component (0 : Fin 1)).space
      (W.component (0 : Fin 1)).lattice A := by
    change Lattice.IsNormGeneratorValue
      (Lattice.wholeQuadraticSublattice q L).space
      (Lattice.wholeQuadraticSublattice q L).lattice A
    exact hA.mapLatticeIsometry
      (Lattice.wholeQuadraticSublatticeIsometry q L)
  have hcomponentPrincipal :
      Lattice.principalIdeal (K := K)
          (W.normGeneratorUnit (0 : Fin 1) : K) =
        Lattice.principalIdeal (K := K) (A : K) := by
    exact (W.normIdeal_eq_normGeneratorUnit (0 : Fin 1)).symm.trans
      hAComponent.2
  have hcomponentOrder :
      ordUnit K (W.normGeneratorUnit (0 : Fin 1)) = ordUnit K A :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp hcomponentPrincipal
  let effective :=
    W.effectiveNormOrderAt (0 : Fin 1) (ordUnit K s)
  have heffectiveNorm : effective = ordUnit K A := by
    apply le_antisymm
    · calc
        effective =
            W.effectiveNormOrderAt (0 : Fin 1) (ordUnit K s) := rfl
        _ <= ordUnit K (W.normGeneratorUnit (0 : Fin 1)) := by
          have hscale : W.scaleGenerator (0 : Fin 1) = s := by
            rfl
          rw [← hscale]
          exact W.effectiveNormOrderAt_scale_le_normOrder (0 : Fin 1)
        _ = ordUnit K A := hcomponentOrder
    · have hraw : ordUnit K A =
          ordUnit K (W.normGeneratorUnit (0 : Fin 1)) :=
        hcomponentOrder.symm
      rw [hraw]
      change ordUnit K (W.normGeneratorUnit (0 : Fin 1)) <=
        W.effectiveNormOrderAt (0 : Fin 1) (ordUnit K s)
      unfold Lattice.WeakJordanDecomposition.effectiveNormOrderAt
      apply JordanProfileOrder.le_effectiveAt
      intro j
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      have hscale : W.scaleGenerator (0 : Fin 1) = s := by
        rfl
      unfold JordanProfileOrder.adjustedAt
      unfold Lattice.WeakJordanDecomposition.scaleOrderFamily
        Lattice.WeakJordanDecomposition.normOrderFamily
      rw [hscale]
      simp
  have horders : ∀ (t : Nat) (ht : t < pairs + 1),
      c.order ⟨2 * t + 1, by omega⟩ <= F := by
    intro t ht
    let I : Fin (2 * pairs + 2) := ⟨2 * t + 1, by omega⟩
    have hcomponent : (x.indexEquiv I).1 = (0 : Fin 1) :=
      Subsingleton.elim _ _
    have hglobal := x.index_val_eq_componentStart_add_local I
    have hlocal : (x.indexEquiv I).2.val = 2 * t + 1 := by
      rw [hcomponent] at hglobal
      have hsum :
          (∑ k ∈ Finset.Iio (0 : Fin 1),
            finrank K (W.component k).carrier) = 0 := by
        simp
      rw [hsum, zero_add] at hglobal
      exact hglobal.symm
    have horder := x.order_eq I
    change c.order I = JordanProfileOrder.localOrder
      (ordUnit K (W.scaleGenerator (x.indexEquiv I).1))
      (W.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at horder
    rw [hcomponent, hlocal] at horder
    have hscaleEffective : ordUnit K s <= effective :=
      W.targetScale_le_effectiveNormOrderAt
        (0 : Fin 1) (ordUnit K s)
    have hodd : ¬Even (2 * t + 1) := by
      rintro ⟨k, hk⟩
      omega
    have hlocalOrder :
        JordanProfileOrder.localOrder (ordUnit K s) effective
            (2 * t + 1) = 2 * ordUnit K s - effective :=
      JordanProfileOrder.localOrder_odd_of_scale_le
        hscaleEffective hodd
    have horder' : c.order I = 2 * ordUnit K s - ordUnit K A := by
      simpa only [W, Lattice.WeakJordanDecomposition.singleOfModular,
        effective, heffectiveNorm] using horder.trans hlocalOrder
    change c.order I <= F
    rw [horder']
    exact hoddF
  exact c.weightIdealOrder_sub_le_defectOrder_signedDeterminant
    pairs F horders

set_option maxHeartbeats 1000000 in
/-- The odd-rank modular analogue.  Odd modular lattices are proper by
O'Meara 93:15, so every norm generator has the scale order and every entry
of the one-component BONG profile has that same order.  The extra norm
generator `A` is the one occurring in the odd signed determinant. -/
theorem weightIdealOrder_sub_le_defect_norm_mul_signedDeterminant_of_odd_rank
    [BONGGoodExistenceLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (hmodular : Lattice.IsModular q L s) (hpos : 0 < finrank K V)
    (pairs : Nat) (hrank : finrank K V = 2 * pairs + 1)
    (A : Kˣ) (hA : Lattice.IsNormGeneratorValue q L A)
    (F : Int) (hscaleF : ordUnit K s <= F) :
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ) <=
      BONG.GoodBONG.defectOrder (K := K)
        (((-1 : Kˣ) ^ (pairs + 1)) * A *
          Lattice.determinantUnit q L) := by
  have hrankOdd : Odd (finrank K V) := by
    refine ⟨pairs, ?_⟩
    omega
  have hproper :=
    Lattice.normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
      q L s hmodular hrankOdd
  have hprincipalA : Lattice.principalIdeal (K := K) (A : K) =
      Lattice.principalIdeal (K := K) (s : K) := by
    calc
      Lattice.principalIdeal (K := K) (A : K) =
          Lattice.normIdeal q L := hA.2.symm
      _ = Lattice.scaleIdeal q L := hproper
      _ = Lattice.principalIdeal (K := K) (s : K) :=
        hmodular.scaleIdeal_eq_principal hpos
  have hAOrder : ordUnit K A = ordUnit K s :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp hprincipalA
  let cRaw := Classical.choice (Bong.exists_good_bong q L)
  let c : BONG.GoodBONG q L (2 * pairs + 1) := cRaw.castLength hrank
  let W := Lattice.WeakJordanDecomposition.singleOfModular
    s hmodular hpos
  let hstrict :=
    Lattice.WeakJordanDecomposition.singleOfModular_scaleOrder_strict
      s hmodular hpos
  let P : BONG.JordanOrderProfileWitness c.toBONG
      (W.toJordan hstrict) :=
    Classical.choice
      (c.toBONG.beliLemma47_profile c.good (W.toJordan hstrict))
  let x := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
  have hcomponentRank :
      finrank K (W.component (0 : Fin 1)).carrier = finrank K V := by
    have hiso :=
      (Lattice.wholeQuadraticSublatticeIsometry q L).toLinearEquiv.finrank_eq
    change finrank K
      (Lattice.wholeQuadraticSublattice q L).carrier = finrank K V
    omega
  have hcomponentOdd :
      Odd (finrank K (W.component (0 : Fin 1)).carrier) := by
    rw [hcomponentRank]
    exact hrankOdd
  have hcomponentProper :=
    Lattice.normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
      (W.component (0 : Fin 1)).space
      (W.component (0 : Fin 1)).lattice
      (W.scaleGenerator (0 : Fin 1))
      (W.modular (0 : Fin 1)) hcomponentOdd
  have hcomponentPrincipal :
      Lattice.principalIdeal (K := K)
          (W.normGeneratorUnit (0 : Fin 1) : K) =
        Lattice.principalIdeal (K := K)
          (W.scaleGenerator (0 : Fin 1) : K) := by
    calc
      Lattice.principalIdeal (K := K)
          (W.normGeneratorUnit (0 : Fin 1) : K) =
          Lattice.normIdeal (W.component (0 : Fin 1)).space
            (W.component (0 : Fin 1)).lattice :=
        (W.normIdeal_eq_normGeneratorUnit (0 : Fin 1)).symm
      _ = Lattice.scaleIdeal (W.component (0 : Fin 1)).space
            (W.component (0 : Fin 1)).lattice := hcomponentProper
      _ = Lattice.principalIdeal (K := K)
          (W.scaleGenerator (0 : Fin 1) : K) :=
        (W.modular (0 : Fin 1)).scaleIdeal_eq_principal
          (W.component_finrank_pos (0 : Fin 1))
  have hcomponentOrder :
      ordUnit K (W.normGeneratorUnit (0 : Fin 1)) = ordUnit K s := by
    have hraw :=
      (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
        hcomponentPrincipal
    have hscale : W.scaleGenerator (0 : Fin 1) = s := by
      rfl
    rwa [hscale] at hraw
  let effective :=
    W.effectiveNormOrderAt (0 : Fin 1) (ordUnit K s)
  have heffectiveScale : effective = ordUnit K s := by
    apply le_antisymm
    · calc
        effective =
            W.effectiveNormOrderAt (0 : Fin 1) (ordUnit K s) := rfl
        _ <= ordUnit K (W.normGeneratorUnit (0 : Fin 1)) := by
          have hscale : W.scaleGenerator (0 : Fin 1) = s := by
            rfl
          rw [← hscale]
          exact W.effectiveNormOrderAt_scale_le_normOrder (0 : Fin 1)
        _ = ordUnit K s := hcomponentOrder
    · exact W.targetScale_le_effectiveNormOrderAt
        (0 : Fin 1) (ordUnit K s)
  have horders : ∀ (t : Nat) (ht : t < pairs),
      c.order ⟨2 * t + 2, by omega⟩ <= ordUnit K s := by
    intro t ht
    let I : Fin (2 * pairs + 1) := ⟨2 * t + 2, by omega⟩
    have hcomponent : (x.indexEquiv I).1 = (0 : Fin 1) :=
      Subsingleton.elim _ _
    have hglobal := x.index_val_eq_componentStart_add_local I
    have hlocal : (x.indexEquiv I).2.val = 2 * t + 2 := by
      rw [hcomponent] at hglobal
      have hsum :
          (∑ k ∈ Finset.Iio (0 : Fin 1),
            finrank K (W.component k).carrier) = 0 := by
        simp
      rw [hsum, zero_add] at hglobal
      exact hglobal.symm
    have horder := x.order_eq I
    change c.order I = JordanProfileOrder.localOrder
      (ordUnit K (W.scaleGenerator (x.indexEquiv I).1))
      (W.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at horder
    rw [hcomponent, hlocal] at horder
    have hscaleEffective : ordUnit K s <= effective := by
      exact W.targetScale_le_effectiveNormOrderAt
        (0 : Fin 1) (ordUnit K s)
    have heven : Even (2 * t + 2) := by
      refine ⟨t + 1, ?_⟩
      omega
    have hlocalOrder :
        JordanProfileOrder.localOrder (ordUnit K s) effective
            (2 * t + 2) = effective :=
      JordanProfileOrder.localOrder_even_of_scale_le
        hscaleEffective heven
    have horder' : c.order I = effective := by
      simpa only [W, Lattice.WeakJordanDecomposition.singleOfModular,
        effective] using horder.trans hlocalOrder
    change c.order I <= ordUnit K s
    rw [horder', heffectiveScale]
  have hbase :=
    c.weightIdealOrder_sub_le_defectOrder_norm_mul_signedDeterminant
      pairs A hA (ordUnit K s) hAOrder horders
  calc
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ) <=
        (((Lattice.weightIdealOrder q L - ordUnit K s : Int) : ℚ) :
          WithTop ℚ) := by
      norm_cast
      exact_mod_cast sub_le_sub_left hscaleF
        (Lattice.weightIdealOrder q L)
    _ <= BONG.GoodBONG.defectOrder (K := K)
        (((-1 : Kˣ) ^ (pairs + 1)) * A *
          Lattice.determinantUnit q L) := hbase

end Lattice.IsModular

end Bong
