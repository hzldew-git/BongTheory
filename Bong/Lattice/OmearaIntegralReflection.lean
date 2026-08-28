/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Reflection
import Bong.Lattice.ScaleTruncation

/-!
# O'Meara's scale-truncation criterion for integral reflections

This file formalizes the criterion used in Beli (2003), Lemma 6.5, with
reference to O'Meara, Section 91B.  Membership in
`L^r = L ∩ π^r L♯` gives `B(v,L) ⊆ π^r`; when
`ord Q(v) = r + e`, multiplication by `2` makes every reflection
coefficient integral.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Pairing a vector in `L^r` with the parent lattice has order at least
`r`. -/
theorem ord_bilin_ge_of_mem_scaleTruncation
    {r : Int} {x y : V}
    (hx : x ∈ scaleTruncation q L r) (hy : y ∈ L) :
    (r : WithTop Int) ≤ ord K (q.bilin x y) := by
  rcases (mem_scaleTruncation_iff_inf q L r x).1 hx with ⟨_, hxScaled⟩
  rw [mem_rescale_iff] at hxScaled
  rcases hxScaled with ⟨z, hzDual, hzx⟩
  have hzIntegral : q.bilin z y ∈ IntegerRing K :=
    (mem_dualLattice_iff q L z).1 hzDual y hy
  have hzOrder : (0 : WithTop Int) ≤ ord K (q.bilin z y) := by
    rw [← Dyadic.IsIntegral]
    exact hzIntegral
  have hxPair : q.bilin x y =
      (scaleTruncationUnit (K := K) r : K) * q.bilin z y := by
    rw [← hzx, LinearMap.BilinForm.smul_left]
  rw [hxPair, ord_mul, ← coe_ordUnit]
  have hscaleOrder : ordUnit K (scaleTruncationUnit (K := K) r) = r := by
    rw [scaleTruncationUnit, ordUnit_uniformizerPowerUnit]
  rw [hscaleOrder]
  calc
    (r : WithTop Int) = (r : WithTop Int) + 0 := (add_zero _).symm
    _ ≤ (r : WithTop Int) + ord K (q.bilin z y) :=
      add_le_add_right hzOrder _

/-- Intrinsic pairing criterion for O'Meara's auxiliary lattice.  This is
the converse of `ord_bilin_ge_of_mem_scaleTruncation`: an integral vector is
in `L^r` exactly when all of its pairings with `L` have order at least `r`.
The formulation is especially convenient when an orthogonal decomposition
is used only to prove the pairing bounds. -/
theorem mem_scaleTruncation_iff_ord_bilin_ge
    {r : Int} {x : V} :
    x ∈ scaleTruncation q L r ↔
      x ∈ L ∧ ∀ y : V, y ∈ L →
        (r : WithTop Int) ≤ ord K (q.bilin x y) := by
  constructor
  · intro hx
    exact ⟨(mem_scaleTruncation_iff_inf q L r x).1 hx |>.1,
      fun _ hy ↦ ord_bilin_ge_of_mem_scaleTruncation hx hy⟩
  · rintro ⟨hxL, hpair⟩
    rw [mem_scaleTruncation_iff_inf]
    refine ⟨hxL, ?_⟩
    let a : Kˣ := scaleTruncationUnit (K := K) r
    let z : V := ((a⁻¹ : Kˣ) : K) • x
    have hzDual : z ∈ dualLattice q L := by
      rw [mem_dualLattice_iff]
      intro y hy
      rw [mem_integerRing_iff, Dyadic.IsIntegral]
      change (0 : WithTop Int) ≤ ord K (q.bilin z y)
      rw [show q.bilin z y = ((a⁻¹ : Kˣ) : K) * q.bilin x y by
        simp only [z, LinearMap.BilinForm.smul_left, smul_eq_mul],
        ord_mul, ← coe_ordUnit, ordUnit_inv]
      have haOrder : ordUnit K a = r := by
        simp only [a, scaleTruncationUnit,
          ordUnit_uniformizerPowerUnit]
      rw [haOrder]
      have h := hpair y hy
      calc
        (0 : WithTop Int) = (-(r : Int) : WithTop Int) + (r : WithTop Int) := by
          norm_cast
          omega
        _ ≤ (-(r : Int) : WithTop Int) + ord K (q.bilin x y) := by
          simpa [add_comm] using
            (add_le_add_right h (-(r : Int) : WithTop Int))
    rw [mem_rescale_iff]
    refine ⟨z, hzDual, ?_⟩
    dsimp only [z]
    rw [smul_smul]
    change ((a : K) * ((a⁻¹ : Kˣ) : K)) • x = x
    simp

/-- Ideal-valued form of the intrinsic pairing criterion.  This avoids
repeating the conversion from membership in `\mathfrak p^r` to a valuation
inequality in the Jordan-component calculations used below. -/
theorem mem_scaleTruncation_of_pairing_mem_powerIdeal
    {r : Int} {x : V} (hx : x ∈ L)
    (hpair : ∀ y : V, y ∈ L →
      q.bilin x y ∈ powerIdeal (K := K) r) :
    x ∈ scaleTruncation q L r := by
  rw [mem_scaleTruncation_iff_ord_bilin_ge]
  refine ⟨hx, ?_⟩
  intro y hy
  exact (mem_powerIdeal_iff (K := K) r (q.bilin x y)).1
    (hpair y hy)

/-- O'Meara, Section 91B: a vector in `L^r` whose norm has order `r+e`
defines an integral reflection of `L`. -/
theorem isIntegralReflection_of_mem_scaleTruncation
    {r : Int} {x : V} (hx : x ∈ scaleTruncation q L r)
    (horder : ord K (q.quadratic x) =
      ((r + ramificationIndex K : Int) : WithTop Int)) :
    IsIntegralReflection (L := L)
      (show q.IsAnisotropic x by
        intro hzero
        rw [hzero, ord_zero] at horder
        exact WithTop.top_ne_coe horder) := by
  let anisotropic : q.IsAnisotropic x := by
    intro hzero
    rw [hzero, ord_zero] at horder
    exact WithTop.top_ne_coe horder
  have hxL : x ∈ L :=
    (mem_scaleTruncation_iff_inf q L r x).1 hx |>.1
  apply isIntegralReflection_of_coefficient_mem_integerRing anisotropic hxL
  intro y hy
  have hpair : (r : WithTop Int) ≤ ord K (q.bilin x y) :=
    ord_bilin_ge_of_mem_scaleTruncation hx hy
  have htwoOrder : ord K ((2 : K) * q.bilin x y) =
      ((ramificationIndex K : Int) : WithTop Int) +
        ord K (q.bilin x y) := by
    rw [ord_mul, ramificationIndex_spec]
  have hprincipal : (2 : K) * q.bilin x y ∈
      principalIdeal (K := K) (q.quadratic x) := by
    apply mem_principalIdeal_of_ord_le anisotropic
    rw [horder, htwoOrder]
    change (r : WithTop Int) +
        ((ramificationIndex K : Int) : WithTop Int) ≤
      ((ramificationIndex K : Int) : WithTop Int) +
        ord K (q.bilin x y)
    calc
      (r : WithTop Int) +
          ((ramificationIndex K : Int) : WithTop Int) =
        ((ramificationIndex K : Int) : WithTop Int) + r := add_comm _ _
      _ ≤ ((ramificationIndex K : Int) : WithTop Int) +
          ord K (q.bilin x y) := add_le_add_right hpair _
  rw [principalIdeal, Submodule.mem_span_singleton] at hprincipal
  rcases hprincipal with ⟨c, hc⟩
  have hcoefficient :
      2 * q.bilin x y / q.quadratic x =
        algebraMap (IntegerRing K) K c := by
    rw [div_eq_iff anisotropic]
    simpa only [Algebra.smul_def, map_ofNat] using hc.symm
  rw [hcoefficient]
  convert c.property using 1
  exact ValuationSubring.algebraMap_apply (IntegerRing K) c

end Lattice

end Bong
