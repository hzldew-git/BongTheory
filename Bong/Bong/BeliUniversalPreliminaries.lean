/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ProjectionNormIdeal
import Bong.Lattice.Universality

/-!
# Beli, universal integral forms: preliminary reductions

This file begins the formalization of Section 2 of Beli's *Universal
integral quadratic forms over dyadic local fields*.  In particular it keeps
the paper's definition of integrality in terms of represented values and
derives the norm-ideal and first-BONG-order formulations.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Beli, Lemma 2.2: a lattice with a nonempty BONG is integral exactly
when the first BONG order is nonnegative. -/
theorem beliUniversalLemma22 (b : BONG V q L (n + 1)) :
    Lattice.IsIntegral q L ↔ 0 ≤ b.order 0 := by
  rw [Lattice.isIntegral_iff_normIdeal_le,
    b.normIdeal_eq_powerIdeal_order_zero]
  have hzero :
      Lattice.unitIdeal (K := K) = Lattice.powerIdeal (K := K) 0 := by
    unfold Lattice.unitIdeal Lattice.powerIdeal Dyadic.uniformizerPowerUnit
    simp
  rw [hzero, Lattice.powerIdeal_le_iff]

end BONG

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A represented nonzero scalar gives the integral representation of its
standard unary lattice. -/
noncomputable def unaryRepresentationOfRepresentsScalar
    (a : Kˣ) (h : RepresentsScalar q L (a : K)) :
    Representation
      (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K)) q
      (BONG.unaryModelLattice (K := K)) L := by
  rw [representsScalar_iff] at h
  let x : V := Classical.choose h
  have hxL : x ∈ L := (Classical.choose_spec h).1
  have hqx : q.quadratic x = (a : K) := (Classical.choose_spec h).2
  have hxne : x ≠ 0 := by
    intro hx
    have ha : (a : K) = 0 := by
      rw [← hqx, hx]
      simp
    exact Units.ne_zero a ha
  refine
    { toLinearMap :=
        { toFun := fun c : K ↦ c • x
          map_add' := fun c d ↦ add_smul c d x
          map_smul' := fun c d ↦ by simp [mul_smul] }
      injective := ?_
      map_bilin := ?_
      map_mem := ?_ }
  · intro c d hcd
    change c • x = d • x at hcd
    have hzero : (c - d) • x = 0 := by
      rw [sub_smul, hcd, sub_self]
    have : c - d = 0 := by
      simpa [hxne] using hzero
    exact sub_eq_zero.mp this
  · intro c d
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.line_bilin_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    change d * (c * q.quadratic x) = (a : K) * (c * d)
    rw [hqx]
    ring
  · intro c hc
    rw [BONG.mem_unaryModelLattice_iff] at hc
    exact L.smul_mem ⟨c, hc⟩ hxL

/-- Representing a standard unary lattice is exactly representing its
nonzero coefficient as a scalar. -/
theorem represents_unaryModel_iff_representsScalar (a : Kˣ) :
    Represents q (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K))
        L (BONG.unaryModelLattice (K := K)) ↔
      RepresentsScalar q L (a : K) := by
  constructor
  · rintro ⟨f⟩
    rw [representsScalar_iff]
    refine ⟨f.toLinearMap 1, f.map_mem ?_, ?_⟩
    · rw [BONG.mem_unaryModelLattice_iff]
      exact one_mem (IntegerRing K)
    · simpa only [QuadraticSpace.rescaleUnit_quadratic,
        QuadraticSpace.line_quadratic, one_pow, mul_one] using
        f.map_quadratic 1
  · intro h
    exact ⟨unaryRepresentationOfRepresentsScalar a h⟩

/-- Multiplying a represented scalar by the square of an integral scalar
preserves integral representability. -/
theorem RepresentsScalar.mul_square {a c : K}
    (ha : RepresentsScalar q L a) (hc : Dyadic.IsIntegral K c) :
    RepresentsScalar q L (a * c ^ 2) := by
  rw [representsScalar_iff] at ha ⊢
  obtain ⟨x, hxL, hqx⟩ := ha
  refine ⟨c • x, L.smul_mem ⟨c, ?_⟩ hxL, ?_⟩
  · exact (mem_integerRing_iff K).2 hc
  · rw [q.quadratic_smul, hqx]
    ring

end Lattice

namespace Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Every nonzero scalar is a square times a coefficient of order zero or
one.  Unlike the integral version below, the square factor may have negative
valuation. -/
theorem exists_order_zero_or_one_mul_square_any (a : Kˣ) :
    ∃ b c : Kˣ,
      (ordUnit K b = 0 ∨ ordUnit K b = 1) ∧ a = b * c ^ 2 := by
  let k : Int := ordUnit K a / 2
  let c : Kˣ := uniformizerPowerUnit K k
  let b : Kˣ := a / c ^ 2
  have hbOrder : ordUnit K b = ordUnit K a % 2 := by
    simp only [b, c, div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      ordUnit_pow, ordUnit_uniformizerPowerUnit]
    omega
  have hbParity : ordUnit K b = 0 ∨ ordUnit K b = 1 := by
    rw [hbOrder]
    omega
  refine ⟨b, c, hbParity, ?_⟩
  simp [b]

/-- Every nonzero integral scalar is a square of an integral scalar times a
coefficient of order zero or one.  This is the valuation-theoretic step in
Beli's reduction to `O^times union pi O^times`. -/
theorem exists_order_zero_or_one_mul_square (a : Kˣ)
    (ha : 0 ≤ ordUnit K a) :
    ∃ b c : Kˣ,
      (ordUnit K b = 0 ∨ ordUnit K b = 1) ∧
        IsIntegral K (c : K) ∧ a = b * c ^ 2 := by
  let k : Int := ordUnit K a / 2
  let c : Kˣ := uniformizerPowerUnit K k
  let b : Kˣ := a / c ^ 2
  have hk : 0 ≤ k := by
    exact Int.ediv_nonneg ha (by omega)
  have hbOrder : ordUnit K b = ordUnit K a % 2 := by
    simp only [b, c, div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      ordUnit_pow, ordUnit_uniformizerPowerUnit]
    omega
  have hbParity : ordUnit K b = 0 ∨ ordUnit K b = 1 := by
    rw [hbOrder]
    omega
  have hcIntegral : IsIntegral K (c : K) := by
    rw [IsIntegral, ← coe_ordUnit]
    dsimp only [c]
    rw [ordUnit_uniformizerPowerUnit]
    exact_mod_cast hk
  refine ⟨b, c, hbParity, hcIntegral, ?_⟩
  simp [b]

end Dyadic

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- An integral lattice is universal exactly when it represents every
nonzero coefficient of order zero or one.  This is the scalar form of the
reduction immediately preceding Beli's Lemma 2.3. -/
theorem isUniversal_iff_represents_order_zero_or_one :
    IsUniversal q L ↔
      IsIntegral q L ∧
        ∀ a : Kˣ, ordUnit K a = 0 ∨ ordUnit K a = 1 →
          RepresentsScalar q L (a : K) := by
  constructor
  · intro h
    refine ⟨h.isIntegral, ?_⟩
    intro a ha
    apply h.representsScalar
    rw [Dyadic.IsIntegral, ← coe_ordUnit]
    rcases ha with ha | ha <;> rw [ha] <;> norm_num
  · rintro ⟨hintegral, hsmall⟩
    rw [isUniversal_iff]
    refine ⟨hintegral, ?_⟩
    intro a ha
    by_cases hzero : a = 0
    · rw [hzero, representsScalar_iff]
      exact ⟨0, L.zero_mem, by simp⟩
    · let au : Kˣ := Units.mk0 a hzero
      have hauNonnegative : 0 ≤ ordUnit K au := by
        have ha' : (0 : WithTop Int) ≤ (ordUnit K au : WithTop Int) := by
          change 0 ≤ ord K a at ha
          simpa only [au, Units.val_mk0, coe_ordUnit] using ha
        exact WithTop.coe_le_coe.mp ha'
      obtain ⟨b, c, hbOrder, hcIntegral, hfactor⟩ :=
        Dyadic.exists_order_zero_or_one_mul_square au hauNonnegative
      have hb := hsmall b hbOrder
      have hrepresented := hb.mul_square hcIntegral
      change RepresentsScalar q L (au : K)
      rw [hfactor]
      exact hrepresented

end Lattice

end Bong
