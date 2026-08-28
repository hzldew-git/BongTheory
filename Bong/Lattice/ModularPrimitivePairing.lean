/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularMembership
import Bong.Lattice.PowerIdeal

/-!
# Primitive vectors in modular lattices

This file isolates the local fact used in Beli (2019), Lemma 5.1.  If `L` is
`a`-modular and `x` is primitive in `L`, then pairing with `x` attains the
scale generator `a`.  Equivalently, the pairing ideal `B(x, L)` is the full
scale ideal rather than its maximal-ideal multiple.

The proof uses O'Meara 82:14a: if every pairing with `x` acquired one further
uniformizer factor, then `π⁻¹x` would lie in `L`, contradicting primitivity.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- A primitive vector in an `a`-modular lattice has a pairing which generates
the principal scale ideal `(a)`. -/
theorem IsModular.exists_pairing_ideal_eq_of_not_mem_rescale
    {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}
    (hmodular : IsModular q L a) {x : V} (hx : x ∈ L)
    (hprimitive : x ∉ Lattice.rescale (uniformizerUnit K) L) :
    ∃ y : V, y ∈ L ∧
      principalIdeal (K := K) (q.bilin x y) =
        principalIdeal (K := K) (a : K) := by
  classical
  by_contra hnone
  push Not at hnone
  have hpair : ∀ y : V, y ∈ L →
      q.bilin ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • x) y ∈
        principalIdeal (K := K) (a : K) := by
    intro y hy
    by_cases hxy : q.bilin x y = 0
    · rw [LinearMap.BilinForm.smul_left, hxy, mul_zero]
      exact Submodule.zero_mem _
    · let b : Kˣ := Units.mk0 (q.bilin x y) hxy
      have hmem : q.bilin x y ∈ principalIdeal (K := K) (a : K) :=
        hmodular.scaleIdeal_le_principal
          (bilin_mem_scaleIdeal_of_mem q L hx hy)
      have horderWithTop : ord K (a : K) ≤ ord K (q.bilin x y) :=
        ord_le_of_mem_principalIdeal (Units.ne_zero a) hmem
      have horder : ordUnit K a ≤ ordUnit K b := by
        apply WithTop.coe_le_coe.mp
        simpa [b] using horderWithTop
      have horderNe : ordUnit K a ≠ ordUnit K b := by
        intro heq
        apply hnone y hy
        calc
          principalIdeal (K := K) (q.bilin x y) =
              principalIdeal (K := K) (b : K) := by rfl
          _ = powerIdeal (K := K) (ordUnit K b) :=
            principalIdeal_eq_powerIdeal b
          _ = powerIdeal (K := K) (ordUnit K a) :=
            congrArg (powerIdeal (K := K)) heq.symm
          _ = principalIdeal (K := K) (a : K) :=
            (principalIdeal_eq_powerIdeal a).symm
      have hstrict : ordUnit K a < ordUnit K b :=
        lt_of_le_of_ne horder horderNe
      have hpi : ordUnit K (uniformizerUnit K) = 1 := by
        simpa [uniformizerPowerUnit] using
          (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
      have hscaledOrder :
          ordUnit K a ≤ ordUnit K ((uniformizerUnit K)⁻¹ * b) := by
        rw [ordUnit_mul, ordUnit_inv, hpi]
        omega
      have hscaledOrderWithTop :
          ord K (a : K) ≤
            ord K ((((uniformizerUnit K)⁻¹ * b : Kˣ) : K)) := by
        rw [← coe_ordUnit, ← coe_ordUnit]
        exact_mod_cast hscaledOrder
      have hscaledMem :
          ((((uniformizerUnit K)⁻¹ * b : Kˣ) : K)) ∈
            principalIdeal (K := K) (a : K) :=
        mem_principalIdeal_of_ord_le (Units.ne_zero a)
          hscaledOrderWithTop
      rw [LinearMap.BilinForm.smul_left]
      simpa [b] using hscaledMem
  have hinv : (((uniformizerUnit K)⁻¹ : Kˣ) : K) • x ∈ L :=
    (hmodular.mem_iff_pairing_mem_principal _).2 hpair
  apply hprimitive
  have hscaled := smul_mem_rescale (uniformizerUnit K) L hinv
  simpa [smul_smul, uniformizer_ne_zero K] using hscaled

/-- The pairing generator can be normalized to the chosen generator `a` by
rescaling the second vector by a valuation-ring unit. -/
theorem IsModular.exists_pairing_eq_of_not_mem_rescale
    {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}
    (hmodular : IsModular q L a) {x : V} (hx : x ∈ L)
    (hprimitive : x ∉ Lattice.rescale (uniformizerUnit K) L) :
    ∃ y : V, y ∈ L ∧ q.bilin x y = (a : K) := by
  obtain ⟨y, hy, hideal⟩ :=
    hmodular.exists_pairing_ideal_eq_of_not_mem_rescale hx hprimitive
  have hxy : q.bilin x y ≠ 0 := by
    intro hzero
    have haMem := generator_mem_principalIdeal (K := K) (a : K)
    rw [← hideal, hzero, principalIdeal] at haMem
    exact Units.ne_zero a (by simpa using haMem)
  let b : Kˣ := Units.mk0 (q.bilin x y) hxy
  obtain ⟨c, hcUnit, hc⟩ :=
    exists_valuationUnit_mul_eq_of_principalIdeal_eq b a (by
      simpa [b] using hideal)
  let cInteger : IntegerRing K :=
    ⟨(c : K), (mem_integerRing_iff K).2 (by
      change 0 ≤ ord K (c : K)
      rw [hcUnit])⟩
  have hcy : (c : K) • y ∈ L := by
    change cInteger • y ∈ L
    exact L.smul_mem cInteger hy
  refine ⟨(c : K) • y, hcy, ?_⟩
  rw [LinearMap.BilinForm.smul_right]
  have hcField := congrArg (fun z : Kˣ ↦ (z : K)) hc
  simpa [b] using hcField

end Lattice

end Bong
