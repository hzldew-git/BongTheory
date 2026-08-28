/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Lattice.AdjoinVector
import Bong.Lattice.DVRFactorization
import Bong.Lattice.Omeara9325FundamentalMonotonicity

/-!
# The codimension-one lattice-sum case of Beli (2009), Lemma 2.11

Beli's Lemma 2.11 is stated for a sum of arbitrary lattices.  Its use in
Beli (2019), Section 5 is the special case `J = L + O x`, where the norm
orders of `J` and `L` differ by two and their doubled scale ideals agree.
This file proves exactly that specialization from the weight-ideal
characterization in Beli (2009), Lemma 2.10; no orthogonality hypothesis is
introduced.
-/

namespace Bong

open Dyadic

universe u v

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L J : Lattice K V}

/-- In an enlargement of index the maximal ideal, every vector outside the
smaller lattice is another generator of the enlargement. -/
theorem adjoinVector_eq_of_uniformizer_smul_mem_of_not_mem
    {x y : V}
    (hadjoinY : adjoinVector L y = J)
    (hpiY : (uniformizerInteger K) • y ∈ L)
    (hxJ : x ∈ J) (hxnot : x ∉ L) :
    adjoinVector L x = J := by
  apply Lattice.ext
  apply le_antisymm
  · exact adjoinVector_le (by
      rw [← hadjoinY]
      exact le_adjoinVector L y) hxJ
  · rw [← hadjoinY]
    apply adjoinVector_le (le_adjoinVector L x)
    have hx' : x ∈ adjoinVector L y := by
      rw [hadjoinY]
      exact hxJ
    rw [mem_adjoinVector_iff] at hx'
    rcases hx' with ⟨l, hl, c, hrel⟩
    have hcne : c ≠ 0 := by
      intro hc
      rw [hc, zero_smul, add_zero] at hrel
      exact hxnot (hrel ▸ hl)
    rcases exists_eq_uniformizerInteger_pow_mul_unit K c hcne with
      ⟨m, u, hc⟩
    have hm : m = 0 := by
      by_contra hmne
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmne
      apply hxnot
      rw [← hrel]
      apply L.add_mem hl
      have hfactor : c =
          (uniformizerInteger K ^ k * (u : IntegerRing K)) *
            uniformizerInteger K := by
        rw [hc, pow_succ]
        ring
      rw [hfactor, mul_smul]
      exact L.smul_mem (uniformizerInteger K ^ k *
        (u : IntegerRing K)) hpiY
    subst m
    have hcunit : c = (u : IntegerRing K) := by
      simpa using hc
    have hxl : x - l = (u : IntegerRing K) • y := by
      rw [← hcunit, ← hrel]
      abel
    have hxlMem : x - l ∈ adjoinVector L x :=
      (adjoinVector L x).sub_mem (mem_adjoinVector L x)
        (le_adjoinVector L x hl)
    let uinv : IntegerRing K := (u⁻¹ : (IntegerRing K)ˣ)
    have hyEq : uinv • (x - l) = y := by
      rw [hxl, ← mul_smul]
      change (((u⁻¹ : (IntegerRing K)ˣ) : IntegerRing K) *
          (u : IntegerRing K)) • y = y
      simp
    rw [← hyEq]
    exact (adjoinVector L x).smul_mem uinv hxlMem

variable [Beli2009WeightIdealData.{u, v} K]

/-- The codimension-one specialization of Beli (2009), Lemma 2.11 used in
Beli (2019), Section 5.  If `J = L + O x`, the vector `x` is a norm
generator of `J`, `pi^2 Q(x)` is a norm generator of `L`, and the two
lattices have the same doubled scale, then their weight ideals agree. -/
theorem weightIdeal_eq_of_adjoin_normGenerator_gapTwo
    {x : V} (hx : IsNormGenerator q J x)
    (hxne : q.quadratic x ≠ 0)
    (hadjoin : adjoinVector L x = J)
    (hsmall : IsNormGeneratorValue q L
      ((uniformizerUnit K) ^ 2 * Units.mk0 (q.quadratic x) hxne))
    (htwo : twoScaleIdeal q L = twoScaleIdeal q J) :
    weightIdeal q J = weightIdeal q L := by
  let A : Kˣ := Units.mk0 (q.quadratic x) hxne
  let B : Kˣ := (uniformizerUnit K) ^ 2 * A
  have hlarge : IsNormGeneratorValue q J A := by
    simpa only [A] using hx.isNormGeneratorValue hxne
  have hsmall' : IsNormGeneratorValue q L B := by
    simpa only [B, A] using hsmall
  let w : OrderedFractionalIdeal K := Beli2009WeightIdealData.weight q L
  have hsource := (beli2009Lemma210 B hsmall' w
      (twoScaleIdeal_le_weightIdeal q L)).mp rfl
  have htwoLarge : twoScaleIdeal q J ≤ w.carrier := by
    rw [← htwo]
    exact twoScaleIdeal_le_weightIdeal q L
  have htwiceA : twiceIdeal (principalIdeal (K := K) (A : K)) ≤
      w.carrier := by
    exact (OrthogonalDecomposition.twicePrincipalIdeal_le_twoScaleIdeal
      A hlarge).trans htwoLarge
  have hLJ : L ≤ J := by
    rw [← hadjoin]
    exact le_adjoinVector L x
  have hgroup : normGroupSet q J =
      integralSquareCoset (A : K) w.carrier := by
    ext z
    constructor
    · rintro hz
      rcases hz with ⟨y, hy, t, ht, rfl⟩
      have hy' : y ∈ adjoinVector L x := by
        rw [hadjoin]
        exact hy
      rw [mem_adjoinVector_iff] at hy'
      rcases hy' with ⟨l, hl, c, hly⟩
      subst y
      have hcxJ : c • x ∈ J := J.smul_mem c hx.mem
      have hlJ : l ∈ J := hLJ hl
      have hcrossJ : (2 : K) * q.bilin l (c • x) ∈
          twoScaleIdeal q J := by
        refine ⟨q.bilin l (c • x),
          bilin_mem_scaleIdeal_of_mem q J hlJ hcxJ, ?_⟩
        change ((2 : IntegerRing K) : K) * q.bilin l (c • x) =
          (2 : K) * q.bilin l (c • x)
        rfl
      have herrorL : (2 : K) * q.bilin l (c • x) + t ∈
          twoScaleIdeal q L := by
        rw [htwo]
        exact (twoScaleIdeal q J).add_mem hcrossJ ht
      have hbase : q.quadratic l +
          ((2 : K) * q.bilin l (c • x) + t) ∈
          normGroupSet q L :=
        ⟨l, hl, _, herrorL, rfl⟩
      rw [hsource.1] at hbase
      rcases hbase with ⟨d, e, he, hbaseEq⟩
      have hfirst : (A : K) * (c : K) ^ 2 ∈
          integralSquareCoset (A : K) w.carrier :=
        ⟨c, 0, Submodule.zero_mem _, by simp⟩
      have hsecond : (B : K) * (d : K) ^ 2 ∈
          integralSquareCoset (A : K) w.carrier := by
        refine ⟨uniformizerInteger K * d, 0, Submodule.zero_mem _, ?_⟩
        change (B : K) * (d : K) ^ 2 =
          (A : K) * (((uniformizerInteger K * d : IntegerRing K) : K)) ^ 2 + 0
        have hcoe : (((uniformizerInteger K * d : IntegerRing K) : K)) =
            uniformizer K * (d : K) := by
          calc
            (((uniformizerInteger K * d : IntegerRing K) : K)) =
                (uniformizerInteger K : K) * (d : K) :=
              map_mul (algebraMap (IntegerRing K) K) _ _
            _ = uniformizer K * (d : K) := by rw [coe_uniformizerInteger]
        have hunitPow : ((((uniformizerUnit K) ^ 2 : Kˣ) : K)) =
            uniformizer K ^ 2 := by
          simp [coe_uniformizerUnit]
        rw [hcoe]
        simp only [B, Units.val_mul, hunitPow, add_zero]
        ring
      have hsum := add_mem_integralSquareCoset_of_twicePrincipal_le
        A w.carrier htwiceA hfirst hsecond
      have hsumError := add_ideal_mem_integralSquareCoset
        (A : K) w.carrier hsum he
      have hquad : q.quadratic (l + c • x) =
          q.quadratic l + q.quadratic (c • x) +
            (2 : K) * q.bilin l (c • x) := q.quadratic_add l (c • x)
      have hqcx : q.quadratic (c • x) =
          (A : K) * (c : K) ^ 2 := by
        rw [← IsScalarTower.algebraMap_smul K c x, q.quadratic_smul]
        change (c : K) ^ 2 * q.quadratic x = (A : K) * (c : K) ^ 2
        change (c : K) ^ 2 * (A : K) = (A : K) * (c : K) ^ 2
        ring
      have htotal : q.quadratic l + (A : K) * (c : K) ^ 2 +
            (2 : K) * q.bilin l (c • x) + t =
          (A : K) * (c : K) ^ 2 + (B : K) * (d : K) ^ 2 + e := by
        calc
          q.quadratic l + (A : K) * (c : K) ^ 2 +
                (2 : K) * q.bilin l (c • x) + t =
              (A : K) * (c : K) ^ 2 +
                (q.quadratic l +
                  ((2 : K) * q.bilin l (c • x) + t)) := by ring
          _ = (A : K) * (c : K) ^ 2 +
                ((B : K) * (d : K) ^ 2 + e) := by rw [hbaseEq]
          _ = (A : K) * (c : K) ^ 2 +
                (B : K) * (d : K) ^ 2 + e := by ring
      rw [hquad, hqcx, htotal]
      exact hsumError
    · rintro ⟨c, y, hy, rfl⟩
      have hyL : y ∈ normGroupSet q L := by
        rw [hsource.1]
        exact ⟨0, y, hy, by simp⟩
      have hyJ : y ∈ normGroupSet q J := normGroupSet_mono hLJ hyL
      have hsquareJ : (A : K) * (c : K) ^ 2 ∈ normGroupSet q J :=
        normGeneratorValue_integralSquare_mem_normGroupSet hlarge c
      exact add_mem_normGroupSet q J hsquareJ hyJ
  have hterminal : w.carrier = twoScaleIdeal q J ∨
      Odd (ordUnit K A + w.order) := by
    rcases hsource.2 with htwoSource | hodd
    · exact Or.inl (htwoSource.trans htwo)
    · right
      have hpi : ordUnit K (uniformizerUnit K) = 1 := by
        simpa [uniformizerPowerUnit] using
          (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
      have hB : ordUnit K B = ordUnit K A + 2 := by
        simp only [B, ordUnit_mul, ordUnit_pow, hpi]
        omega
      rcases hodd with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      rw [hB] at hk
      omega
  have hconditions : SatisfiesWeightIdealConditions q J A w :=
    ⟨hgroup, hterminal⟩
  have hwJ := (beli2009Lemma210 A hlarge w htwoLarge).mpr hconditions
  exact hwJ.symm

end Lattice

end Bong
