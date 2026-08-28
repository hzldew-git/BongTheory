/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DVRFactorization
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Smith bases with uniformizer-power coefficients

For a lattice inclusion `N ≤ M`, Smith normal form gives compatible integral
bases with nonzero diagonal coefficients.  DVR factorization absorbs every
unit coefficient into the basis of `N`, leaving only powers of the selected
uniformizer.  These exponents are the discrete data from which a prime chain
will be constructed.
-/

namespace Bong.Lattice

open Module
open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The copy of `N` inside the ambient module `M` of an inclusion. -/
noncomputable def relativeSubmodule (N M : Lattice K V) :
    Submodule (IntegerRing K) M.toSubmodule :=
  N.toSubmodule.comap M.toSubmodule.subtype

@[simp]
theorem mem_relativeSubmodule_iff {N M : Lattice K V}
    (x : M.toSubmodule) :
    x ∈ relativeSubmodule N M ↔ (x : V) ∈ N :=
  Iff.rfl

/-- An inclusion identifies `N` with its relative submodule inside `M`. -/
noncomputable def relativeSubmoduleEquiv
    {N M : Lattice K V} (hNM : N ≤ M) :
    relativeSubmodule N M ≃ₗ[IntegerRing K] N.toSubmodule where
  toFun x := ⟨(x : M.toSubmodule), x.property⟩
  invFun x := ⟨⟨(x : V), hNM x.property⟩, x.property⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' a x := by ext; rfl

@[simp]
theorem coe_relativeSubmoduleEquiv
    {N M : Lattice K V} (hNM : N ≤ M)
    (x : relativeSubmodule N M) :
    ((relativeSubmoduleEquiv hNM x : N.toSubmodule) : V) =
      ((x : M.toSubmodule) : V) :=
  rfl

/-- The relative submodule has the full integral rank of the larger lattice. -/
theorem relativeSubmodule_finrank_eq
    {N M : Lattice K V} (hNM : N ≤ M) :
    Module.finrank (IntegerRing K) (relativeSubmodule N M) =
      Module.finrank (IntegerRing K) M.toSubmodule := by
  rw [LinearEquiv.finrank_eq (relativeSubmoduleEquiv hNM)]
  rw [Module.finrank_eq_card_basis N.integralBasis,
    Module.finrank_eq_card_basis M.integralBasis]
  letI := Fintype.ofFinite N.BasisIndex
  letI := Fintype.ofFinite M.BasisIndex
  rw [← Module.finrank_eq_card_basis N.ambientBasis,
    ← Module.finrank_eq_card_basis M.ambientBasis]

/-- Compatible bases for an inclusion, with pure uniformizer powers on the
diagonal. -/
structure SmithPowerBasisData (N M : Lattice K V) : Type (max u v) where
  topBasis : Basis (Fin (Module.finrank K V)) (IntegerRing K) M.toSubmodule
  botBasis : Basis (Fin (Module.finrank K V)) (IntegerRing K) N.toSubmodule
  exponent : Fin (Module.finrank K V) → Nat
  botBasis_eq (i : Fin (Module.finrank K V)) :
    (botBasis i : V) =
      ((uniformizerInteger K ^ exponent i : IntegerRing K) : K) •
        (topBasis i : V)

/-- Smith normal form and DVR factorization produce compatible power bases
for every lattice inclusion. -/
theorem exists_smithPowerBasisData
    (N M : Lattice K V) (hNM : N ≤ M) :
    Nonempty (SmithPowerBasisData N M) := by
  classical
  let S := relativeSubmodule N M
  have hRank : Module.finrank (IntegerRing K) S =
      Module.finrank (IntegerRing K) M.toSubmodule :=
    relativeSubmodule_finrank_eq hNM
  let b := M.standardIntegralBasis
  let top := S.smithNormalFormTopBasis b hRank
  let bot := S.smithNormalFormBotBasis b hRank
  let coeff := S.smithNormalFormCoeffs b hRank
  have hcoeff : ∀ i, coeff i ≠ 0 := by
    intro i
    exact S.smithNormalFormCoeffs_ne_zero b hRank i
  have hfactor : ∀ i, ∃ n : Nat, ∃ unit : (IntegerRing K)ˣ,
      coeff i = uniformizerInteger K ^ n * (unit : IntegerRing K) := by
    intro i
    exact exists_eq_uniformizerInteger_pow_mul_unit K (coeff i) (hcoeff i)
  choose exponent unit hfactor using hfactor
  let bot' := bot.unitsSMul (fun i => (unit i)⁻¹)
  let botN := bot'.map (relativeSubmoduleEquiv hNM)
  refine ⟨⟨top, botN, exponent, ?_⟩⟩
  intro i
  have hsnf := S.smithNormalFormBotBasis_def b hRank i
  change ((botN i : N.toSubmodule) : V) = _
  rw [show (botN i : N.toSubmodule) =
      relativeSubmoduleEquiv hNM (bot' i) by rfl]
  rw [coe_relativeSubmoduleEquiv]
  change (((bot' i : S) : M.toSubmodule) : V) = _
  rw [Basis.unitsSMul_apply]
  change ((((unit i)⁻¹ : (IntegerRing K)ˣ) : IntegerRing K) : K) •
      (((bot i : S) : M.toSubmodule) : V) = _
  rw [hsnf]
  change ((((unit i)⁻¹ : (IntegerRing K)ˣ) : IntegerRing K) : K) •
      (((coeff i : IntegerRing K) : K) • (top i : V)) = _
  rw [hfactor i]
  let unitK : K := (((unit i : (IntegerRing K)ˣ) : IntegerRing K) : K)
  let unitInvK : K :=
    ((((unit i)⁻¹ : (IntegerRing K)ˣ) : IntegerRing K) : K)
  let powerK : K :=
    ((uniformizerInteger K ^ exponent i : IntegerRing K) : K)
  change unitInvK • ((powerK * unitK) • (top i : V)) =
    powerK • (top i : V)
  rw [smul_smul]
  have hunit : unitInvK * unitK = 1 := by
    have hunitO :
        (((unit i)⁻¹ : (IntegerRing K)ˣ) : IntegerRing K) *
            ((unit i : (IntegerRing K)ˣ) : IntegerRing K) = 1 := by
      have hU : (unit i)⁻¹ * unit i = 1 := by simp
      exact congrArg (fun x : (IntegerRing K)ˣ =>
        (x : IntegerRing K)) hU
    exact congrArg (fun x : IntegerRing K => (x : K)) hunitO
  have hreorder :
      unitInvK * (powerK * unitK) = powerK * (unitInvK * unitK) := by
    calc
      unitInvK * (powerK * unitK) =
          (unitInvK * powerK) * unitK := (mul_assoc _ _ _).symm
      _ = (powerK * unitInvK) * unitK := by
        rw [mul_comm unitInvK powerK]
      _ = powerK * (unitInvK * unitK) := mul_assoc _ _ _
  rw [hreorder, hunit, mul_one]

end Bong.Lattice
