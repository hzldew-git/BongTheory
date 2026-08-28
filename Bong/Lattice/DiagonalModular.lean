/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BasisUnits
import Bong.Lattice.OrthogonalBasis

/-!
# Modular lattices from orthogonal bases

The dual of an anisotropic orthogonal basis is obtained by dividing each
basis vector by its diagonal quadratic value.  If all those values have the
same order, the resulting coordinate factors differ from one global rescaling
only by valuation units.  Hence the basis lattice is modular.
-/

namespace Bong

open Dyadic
open Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The dual of an anisotropic orthogonal basis is obtained by reciprocally
scaling its basis vectors by their quadratic values. -/
theorem dualBasis_eq_unitsSMul_of_iIsOrtho
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V)
    (horth : q.bilin.iIsOrtho b)
    (hne : ∀ i, q.quadratic (b i) ≠ 0) :
    q.bilin.dualBasis q.nondegenerate b =
      b.unitsSMul
        (fun i => (Units.mk0 (q.quadratic (b i)) (hne i))⁻¹) := by
  apply DFunLike.ext _ _
  have hfun : ⇑(q.bilin.dualBasis q.nondegenerate b) =
      fun i => b.unitsSMul
        (fun j => (Units.mk0 (q.quadratic (b j)) (hne j))⁻¹) i := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    rw [Basis.unitsSMul_apply, Units.smul_def,
      LinearMap.BilinForm.smul_left]
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      change ((Units.mk0 (q.quadratic (b i)) (hne i))⁻¹ : K) *
        q.quadratic (b i) = 1
      simp [hne i]
    · rw [if_neg hji]
      have hij : i ≠ j := fun h => hji h.symm
      rw [(LinearMap.BilinForm.iIsOrtho_def.mp horth) i j hij,
        mul_zero]
  exact congrFun hfun

/-- An anisotropic orthogonal basis lattice whose diagonal values all have
the order of `a` is `a`-modular. -/
theorem isModular_basisLattice_of_iIsOrtho_of_orders_eq
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V)
    (horth : q.bilin.iIsOrtho b)
    (hne : ∀ i, q.quadratic (b i) ≠ 0) (a : Kˣ)
    (horder : ∀ i,
      ordUnit K (Units.mk0 (q.quadratic (b i)) (hne i)) =
        ordUnit K a) :
    IsModular q (basisLattice b) a := by
  let d : ι → Kˣ :=
    fun i => Units.mk0 (q.quadratic (b i)) (hne i)
  let scaled : Basis ι K V := a⁻¹ • b
  let u : ι → Kˣ := fun i => (d i)⁻¹ * a
  have hu : ∀ i, IsValuationUnit K (u i : K) := by
    intro i
    change IsValuationUnit K (((d i)⁻¹ * a : Kˣ) : K)
    rw [isValuationUnit_iff_ordUnit_eq_zero,
      ordUnit_mul, ordUnit_inv]
    change -ordUnit K
      (Units.mk0 (q.quadratic (b i)) (hne i)) + ordUnit K a = 0
    rw [horder i]
    omega
  have hbases :
      b.unitsSMul (fun i => (d i)⁻¹) = scaled.unitsSMul u := by
    ext i
    rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply]
    change ((d i)⁻¹ : K) • b i =
      (((d i)⁻¹ * a : Kˣ) : K) • (((a⁻¹ : Kˣ) : K) • b i)
    rw [smul_smul]
    simp
  rw [IsModular, dualLattice_basisLattice,
    dualBasis_eq_unitsSMul_of_iIsOrtho q b horth hne,
    rescale_basisLattice]
  change basisLattice (b.unitsSMul (fun i => (d i)⁻¹)) =
    basisLattice scaled
  rw [hbases, basisLattice_unitsSMul_eq scaled u hu]

/-- Conversely, the modular parameter of an anisotropic orthogonal basis
lattice has the order of every diagonal quadratic value. -/
theorem orders_eq_of_isModular_basisLattice_of_iIsOrtho
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V)
    (horth : q.bilin.iIsOrtho b)
    (hne : ∀ i, q.quadratic (b i) ≠ 0) (a : Kˣ)
    (hmodular : IsModular q (basisLattice b) a) (i : ι) :
    ordUnit K (Units.mk0 (q.quadratic (b i)) (hne i)) =
      ordUnit K a := by
  let d : Kˣ := Units.mk0 (q.quadratic (b i)) (hne i)
  let dualBasis := q.bilin.dualBasis q.nondegenerate b
  have hdualApply : dualBasis i = ((d⁻¹ : Kˣ) : K) • b i := by
    change (q.bilin.dualBasis q.nondegenerate b) i =
      (((Units.mk0 (q.quadratic (b i)) (hne i))⁻¹ : Kˣ) : K) • b i
    rw [dualBasis_eq_unitsSMul_of_iIsOrtho q b horth hne,
      Basis.unitsSMul_apply, Units.smul_def]
  have hdualMem : dualBasis i ∈ dualLattice q (basisLattice b) := by
    rw [dualLattice_basisLattice]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [hdualApply] at hdualMem
  have hrescale : ((d⁻¹ : Kˣ) : K) • b i ∈
      rescale a⁻¹ (basisLattice b) := by
    rw [← hmodular]
    exact hdualMem
  rw [mem_rescale_iff] at hrescale
  rcases hrescale with ⟨y, hy, hay⟩
  have hyEq : y = (((a * d⁻¹ : Kˣ) : K) • b i) := by
    calc
      y = (a : K) • (((a⁻¹ : Kˣ) : K) • y) := by
        simp [smul_smul]
      _ = (a : K) • (((d⁻¹ : Kˣ) : K) • b i) :=
        congrArg (fun z : V => (a : K) • z) hay
      _ = (((a * d⁻¹ : Kˣ) : K) • b i) := by
        rw [smul_smul]
        rfl
  have hcoord :=
    (mem_basisLattice_iff_repr_mem_integerRing b y).1 hy i
  have hratioMem : ((a * d⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
    rw [hyEq] at hcoord
    simpa using hcoord
  have hda : ordUnit K d ≤ ordUnit K a := by
    have hnonneg :=
      ordUnit_nonneg_of_mem_integerRing (a * d⁻¹) hratioMem
    rw [ordUnit_mul, ordUnit_inv] at hnonneg
    omega
  have hscaledMem : ((a⁻¹ : Kˣ) : K) • b i ∈
      rescale a⁻¹ (basisLattice b) :=
    smul_mem_rescale a⁻¹ (basisLattice b)
      (Submodule.subset_span ⟨i, rfl⟩)
  have hscaledDual : ((a⁻¹ : Kˣ) : K) • b i ∈
      dualLattice q (basisLattice b) := by
    rw [hmodular]
    exact hscaledMem
  have hpair := (mem_dualLattice_iff q (basisLattice b)
    (((a⁻¹ : Kˣ) : K) • b i)).1 hscaledDual
      (b i) (Submodule.subset_span ⟨i, rfl⟩)
  have hinverseRatioMem : ((a⁻¹ * d : Kˣ) : K) ∈ IntegerRing K := by
    rw [LinearMap.BilinForm.smul_left] at hpair
    change ((a⁻¹ : Kˣ) : K) * q.quadratic (b i) ∈
      IntegerRing K at hpair
    simpa [d] using hpair
  have had : ordUnit K a ≤ ordUnit K d := by
    have hnonneg :=
      ordUnit_nonneg_of_mem_integerRing (a⁻¹ * d) hinverseRatioMem
    rw [ordUnit_mul, ordUnit_inv] at hnonneg
    omega
  change ordUnit K d = ordUnit K a
  omega

/-- Exact modularity criterion for an anisotropic orthogonal basis lattice. -/
theorem isModular_basisLattice_iff_orders_eq
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V)
    (horth : q.bilin.iIsOrtho b)
    (hne : ∀ i, q.quadratic (b i) ≠ 0) (a : Kˣ) :
    IsModular q (basisLattice b) a ↔
      ∀ i, ordUnit K (Units.mk0 (q.quadratic (b i)) (hne i)) =
        ordUnit K a := by
  constructor
  · intro hmodular i
    exact orders_eq_of_isModular_basisLattice_of_iIsOrtho
      q b horth hne a hmodular i
  · exact isModular_basisLattice_of_iIsOrtho_of_orders_eq
      q b horth hne a

end Lattice

end Bong
