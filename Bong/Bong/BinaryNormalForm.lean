/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryStrictModular
import Bong.Bong.Existence
import Bong.Lattice.ModularScale

/-!
# Modular binary normal forms

This file packages Beli (2003), Lemma 3.3(iii), and Corollary 3.4(iii).
A prescribed anisotropic norm generator is extended to a binary BONG, whose
second value is determined by the determinant class and modular scale.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- Beli (2003), Lemma 3.3(iii), in invariant form: a prescribed norm
generator extends to a BONG with the asserted modular order and determinant
formulas. -/
theorem exists_of_normGenerator_with_modular_normal_form
    (x : V) (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (hfin : finrank K V = 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    ∃ b : BONG V q L 2,
      b.head = x ∧
      b.value 0 = q.quadratic x ∧
      b.order 1 = 2 * ordUnit K a - b.order 0 ∧
      b.binaryOrderGap = 2 * ordUnit K a - 2 * b.order 0 ∧
      unitSquareClass K (b.valueUnit 1) =
        Lattice.determinantClass q L *
          (unitSquareClass K (b.valueUnit 0))⁻¹ := by
  let b := ofNormGeneratorBinary q L x generator anisotropic hfin
  refine ⟨b, head_ofNormGeneratorBinary q L x generator anisotropic hfin,
    ?_, b.order_one_eq_of_isModular a hmodular,
    b.binaryOrderGap_eq_of_isModular a hmodular,
    b.valueUnitSquareClass_one_eq_determinant_div_zero⟩
  rw [b.value_zero_eq_quadratic_head,
    head_ofNormGeneratorBinary q L x generator anisotropic hfin]

/-- The ideal and order formulas of Beli (2003), Corollary 3.4(iii), for a
supplied modular parameter. -/
theorem modular_binary_ideal_formulas
    (b : BONG V q L 2) (a : Kˣ)
    (hmodular : Lattice.IsModular q L a) :
    Lattice.scaleIdeal q L =
        Lattice.principalIdeal (K := K) (a : K) ∧
      Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (b.value 0) ∧
      Lattice.normIdeal q (Lattice.dualLattice q L) =
        Lattice.principalIdeal (K := K)
          (q.quadratic (((a⁻¹ : Kˣ) : K) • b.head)) ∧
      2 * ordUnit K a = b.order 0 + b.order 1 ∧
      ord K (q.quadratic (((a⁻¹ : Kˣ) : K) • b.head)) =
        ((-b.order 1 : Int) : WithTop Int) ∧
      b.order 0 ≡ b.order 1 [ZMOD 2] := by
  have hfin : 0 < finrank K V := by
    rw [← b.length_eq_finrank]
    norm_num
  exact ⟨hmodular.scaleIdeal_eq_principal hfin,
    b.normIdeal_eq_principal_value_zero,
    b.normIdeal_dualLattice_eq_principal_inverseModularParameter_smul_head
      a hmodular,
    b.two_mul_modularOrder_eq_order_add a hmodular,
    b.ord_quadratic_inverseModularParameter_smul_head a hmodular,
    b.orders_modEq_two_of_isModular a hmodular⟩

/-- The order hypothesis in Corollary 3.4(iii) supplies a modular parameter
and all three ideal formulas. -/
theorem exists_modular_parameter_with_binary_ideal_formulas
    (b : BONG V q L 2) (horder : b.order 1 ≤ b.order 0) :
    ∃ a : Kˣ,
      Lattice.IsModular q L a ∧
      Lattice.scaleIdeal q L =
        Lattice.principalIdeal (K := K) (a : K) ∧
      Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (b.value 0) ∧
      Lattice.normIdeal q (Lattice.dualLattice q L) =
        Lattice.principalIdeal (K := K)
          (q.quadratic (((a⁻¹ : Kˣ) : K) • b.head)) ∧
      2 * ordUnit K a = b.order 0 + b.order 1 ∧
      ord K (q.quadratic (((a⁻¹ : Kˣ) : K) • b.head)) =
        ((-b.order 1 : Int) : WithTop Int) ∧
      b.order 0 ≡ b.order 1 [ZMOD 2] := by
  rcases b.exists_isModular_iff_order_one_le_order_zero.mpr horder with
    ⟨a, hmodular⟩
  refine ⟨a, hmodular, ?_⟩
  exact b.modular_binary_ideal_formulas a hmodular

end BONG

end Bong
