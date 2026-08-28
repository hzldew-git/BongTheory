/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanScaleTruncation
import Bong.Lattice.Omeara9325FundamentalMonotonicity

/-!
# Norm generators realizing an effective Jordan norm

The effective norm order at a target scale is the minimum of the norm
orders of the suitably rescaled Jordan components.  This file upgrades that
numerical minimum to the scalar statement used throughout Beli (2019): if a
component attains the minimum, its chosen norm-generator value, multiplied
by the square of the scale-truncation factor, is a norm generator of the
whole intrinsic scale truncation.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace JordanProfileOrder

/-- A pointwise additive comparison of adjusted component norms passes to
the two effective minima. -/
theorem effectiveAt_le_add_of_pointwise {t : Nat}
    (scale norm scale' norm' : Fin t → Int)
    (anchor anchor' : Fin t) (r c : Int)
    (h : ∀ j, adjustedAt scale' norm' r j ≤
      adjustedAt scale norm r j + c) :
    effectiveAt scale' norm' anchor' r ≤
      effectiveAt scale norm anchor r + c := by
  obtain ⟨j, _hj, hjmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin t)))
    ⟨anchor, Finset.mem_univ anchor⟩ (adjustedAt scale norm r)
  calc
    effectiveAt scale' norm' anchor' r ≤
        adjustedAt scale' norm' r j :=
      effectiveAt_le scale' norm' anchor' j r
    _ ≤ adjustedAt scale norm r j + c := h j
    _ = effectiveAt scale norm anchor r + c := by
      exact congrArg (fun x ↦ x + c) hjmin.symm

end JordanProfileOrder

namespace Lattice.WeakJordanDecomposition

/-- The chosen component norm-generator unit is represented by its chosen
vector and generates the component norm ideal. -/
theorem normGeneratorUnit_spec {t : Nat}
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    Lattice.IsNormGeneratorValue (W.component i).space
      (W.component i).lattice (W.normGeneratorUnit i) := by
  refine ⟨?_, W.normIdeal_eq_normGeneratorUnit i⟩
  refine ⟨W.normGeneratorVector i,
    (W.normGeneratorVector_spec i).1.mem, 0, Submodule.zero_mem _, ?_⟩
  simp [normGeneratorUnit]

/-- Rescaling a component by `c` multiplies its represented norm-generator
value by `c²`. -/
theorem rescaledNormGeneratorUnit_spec {t : Nat}
    (W : WeakJordanDecomposition q L t) (i : Fin t) (c : Kˣ) :
    Lattice.IsNormGeneratorValue (W.component i).space
      (Lattice.rescale c (W.component i).lattice)
      (c ^ 2 * W.normGeneratorUnit i) := by
  let x := W.normGeneratorVector i
  let z : (W.component i).carrier := (c : K) • x
  have hzGenerator : Lattice.IsNormGenerator (W.component i).space
      (Lattice.rescale c (W.component i).lattice) z :=
    (W.normGeneratorVector_spec i).1.rescale c
  have hvalue : ((c ^ 2 * W.normGeneratorUnit i : Kˣ) : K) =
      (W.component i).space.quadratic z := by
    rw [(W.component i).space.quadratic_smul]
    simp only [Units.val_mul]
    congr 1
  refine ⟨?_, ?_⟩
  · refine ⟨z, hzGenerator.mem, 0, Submodule.zero_mem _, ?_⟩
    simpa only [add_zero] using hvalue
  · rw [hvalue]
    exact hzGenerator.normIdeal_eq

/-- A norm generator of a sublattice remains a norm generator of a larger
lattice when their norm-ideal orders agree. -/
theorem _root_.Bong.Lattice.IsNormGeneratorValue.of_le_of_order_eq
    {M : Lattice K V} {a b : Kˣ}
    (ha : Lattice.IsNormGeneratorValue q L a)
    (hb : Lattice.IsNormGeneratorValue q M b)
    (hLM : L ≤ M) (horder : ordUnit K a = ordUnit K b) :
    Lattice.IsNormGeneratorValue q M a := by
  refine ⟨Lattice.normGroupSet_mono hLM ha.1, ?_⟩
  calc
    Lattice.normIdeal q M =
        Lattice.principalIdeal (K := K) (b : K) := hb.2
    _ = Lattice.principalIdeal (K := K) (a : K) :=
      (Lattice.principalIdeal_eq_iff_ordUnit_eq b a).2 horder.symm

/-- Inclusion and equality of norm ideals transport a scalar norm
generator without choosing a comparison generator on the larger lattice. -/
theorem _root_.Bong.Lattice.IsNormGeneratorValue.of_le_of_normIdeal_eq
    {M : Lattice K V} {a : Kˣ}
    (ha : Lattice.IsNormGeneratorValue q L a)
    (hLM : L ≤ M)
    (hnorm : Lattice.normIdeal q M = Lattice.normIdeal q L) :
    Lattice.IsNormGeneratorValue q M a := by
  exact ⟨Lattice.normGroupSet_mono hLM ha.1, hnorm.trans ha.2⟩

/-- Rescaling a positive-rank lattice by `c` carries a scalar norm generator
to the square-scaled scalar `c²a`. -/
theorem _root_.Bong.Lattice.IsNormGeneratorValue.rescale_of_finrank_pos
    {a c : Kˣ} (ha : Lattice.IsNormGeneratorValue q L a)
    (hpos : 0 < Module.finrank K V) :
    Lattice.IsNormGeneratorValue q (Lattice.rescale c L) (c ^ 2 * a) := by
  refine ⟨Lattice.sq_mul_mem_normGroupSet_rescale c ha.1, ?_⟩
  exact Lattice.normIdeal_rescale_eq_principal_of_finrank_pos
    hpos c a ha.2

/-- A Jordan component whose scale is already at least the truncation target
is not rescaled in the componentwise calculation of the truncation. -/
@[simp]
theorem _root_.Bong.Lattice.JordanDecomposition.scaleTruncationFactor_eq_one_of_le
    {t : Nat} (J : Lattice.JordanDecomposition q L t)
    (r : Int) (i : Fin t)
    (hr : r ≤ ordUnit K (J.scaleGenerator i)) :
    J.scaleTruncationFactor r i = 1 := by
  unfold Lattice.JordanDecomposition.scaleTruncationFactor
    Lattice.positivePartUnit
  have hnot : ¬0 < ordUnit K
      (Lattice.scaleTruncationUnit (K := K) r *
        (J.scaleGenerator i)⁻¹) := by
    rw [ordUnit_mul, ordUnit_inv, Lattice.scaleTruncationUnit,
      ordUnit_uniformizerPowerUnit]
    omega
  rw [if_neg hnot]

/-- The value of the chosen component norm generator after the component is
rescaled inside the intrinsic truncation at `r`. -/
noncomputable def adjustedNormGeneratorUnit {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (r : Int) (i : Fin t) : Kˣ :=
  let J := W.toJordan hstrict
  J.scaleTruncationFactor r i ^ 2 * W.normGeneratorUnit i

@[simp]
theorem adjustedNormGeneratorUnit_eq_of_le {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (r : Int) (i : Fin t)
    (hr : r ≤ ordUnit K (W.scaleGenerator i)) :
    W.adjustedNormGeneratorUnit hstrict r i = W.normGeneratorUnit i := by
  let J := W.toJordan hstrict
  have hfactor : J.scaleTruncationFactor r i = 1 :=
    J.scaleTruncationFactor_eq_one_of_le r i (by
      simpa only [J, Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
        using hr)
  change J.scaleTruncationFactor r i ^ 2 * W.normGeneratorUnit i =
    W.normGeneratorUnit i
  rw [hfactor]
  simp

/-- A component attaining the effective-norm minimum supplies an actual
norm-generator value for the whole scale truncation. -/
theorem adjustedNormGeneratorUnit_spec {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (anchor i : Fin t) (r : Int)
    (hmin : JordanProfileOrder.adjustedAt W.scaleOrderFamily
        W.normOrderFamily r i = W.effectiveNormOrderAt anchor r) :
    Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q L r)
      (W.adjustedNormGeneratorUnit hstrict r i) := by
  let J := W.toJordan hstrict
  let c := J.scaleTruncationFactor r i
  let x := W.normGeneratorVector i
  let z : V := (c : K) • (x : V)
  have hxmem : x ∈ (W.component i).lattice :=
    (W.normGeneratorVector_spec i).1.mem
  have hzmem : z ∈ Lattice.scaleTruncation q L r := by
    let D := J.scaleTruncationDecomposition r
    let y : (D.component i).carrier := ⟨z, by
      change z ∈ (W.component i).carrier
      exact (W.component i).carrier.smul_mem (c : K) x.property⟩
    have hy : y ∈ (D.component i).lattice := by
      change ((c : K) • x) ∈ Lattice.rescale c (W.component i).lattice
      exact Lattice.smul_mem_rescale c (W.component i).lattice hxmem
    exact D.component_ambientSubmodule_le i ⟨y, hy, rfl⟩
  have hzgroup : (W.adjustedNormGeneratorUnit hstrict r i : K) ∈
      Lattice.normGroupSet q (Lattice.scaleTruncation q L r) := by
    refine ⟨z, hzmem, 0, Submodule.zero_mem _, ?_⟩
    simp only [add_zero]
    unfold adjustedNormGeneratorUnit
    rw [q.quadratic_smul]
    change ((c ^ 2 * W.normGeneratorUnit i : Kˣ) : K) =
      (c : K) ^ 2 * q.quadratic (x : V)
    simp only [Units.val_mul]
    congr 1
  refine ⟨hzgroup, ?_⟩
  rw [J.normIdeal_scaleTruncation_eq_powerIdeal anchor r,
    Lattice.principalIdeal_eq_powerIdeal]
  congr 1
  unfold adjustedNormGeneratorUnit
  rw [ordUnit_mul, ordUnit_pow, J.ordUnit_scaleTruncationFactor]
  change W.effectiveNormOrderAt anchor r =
    2 * max 0 (r - W.scaleOrderFamily i) + W.normOrderFamily i
  rw [← hmin]
  simp only [JordanProfileOrder.adjustedAt]
  split <;> omega

/-- The adjusted scalar attached to a minimizing component has valuation
equal to the effective norm order. -/
theorem ordUnit_adjustedNormGeneratorUnit_eq_effective {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (anchor i : Fin t) (r : Int)
    (hmin : JordanProfileOrder.adjustedAt W.scaleOrderFamily
        W.normOrderFamily r i = W.effectiveNormOrderAt anchor r) :
    ordUnit K (W.adjustedNormGeneratorUnit hstrict r i) =
      W.effectiveNormOrderAt anchor r := by
  unfold adjustedNormGeneratorUnit
  rw [ordUnit_mul, ordUnit_pow,
    (W.toJordan hstrict).ordUnit_scaleTruncationFactor]
  simp only [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
  change 2 * max 0 (r - W.scaleOrderFamily i) + W.normOrderFamily i =
    W.effectiveNormOrderAt anchor r
  rw [← hmin]
  simp only [JordanProfileOrder.adjustedAt]
  split <;> omega

/-- Every effective norm is attained by an explicitly adjusted component
norm generator. -/
theorem exists_adjustedNormGeneratorUnit_spec {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i)))
    (anchor : Fin t) (r : Int) :
    ∃ i : Fin t,
      JordanProfileOrder.adjustedAt W.scaleOrderFamily
          W.normOrderFamily r i = W.effectiveNormOrderAt anchor r ∧
        Lattice.IsNormGeneratorValue q
          (Lattice.scaleTruncation q L r)
          (W.adjustedNormGeneratorUnit hstrict r i) := by
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin t)))
    ⟨anchor, Finset.mem_univ anchor⟩
    (JordanProfileOrder.adjustedAt W.scaleOrderFamily W.normOrderFamily r)
  have hmin' : JordanProfileOrder.adjustedAt W.scaleOrderFamily
      W.normOrderFamily r i = W.effectiveNormOrderAt anchor r := by
    simpa only [effectiveNormOrderAt, JordanProfileOrder.effectiveAt] using
      hmin.symm
  refine ⟨i, hmin', ?_⟩
  exact W.adjustedNormGeneratorUnit_spec hstrict anchor i r hmin'

end Lattice.WeakJordanDecomposition

end Bong
