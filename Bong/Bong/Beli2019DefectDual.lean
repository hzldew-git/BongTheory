/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ApproximationDual

/-!
# Beli (2019): duality of capped prefix defects

For two BONGs in the same quadratic space, their total value products differ
by a square.  Prefixes of reverse-dual BONGs are complementary original
prefixes divided by those total products.  Consequently, after swapping the
two BONGs, every capped comparison defect agrees with the defect at the
complementary original boundary.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Inversion does not change quadratic-defect order. -/
theorem defectOrder_inv (x : Kˣ) :
    defectOrder (K := K) x⁻¹ = defectOrder (K := K) x := by
  have hfactor : x⁻¹ = x * (x⁻¹) ^ 2 := by group
  rw [hfactor, defectOrder_mul_square]

/-- Capped prefix defects of a swapped reverse-dual pair are the original
defects at the two complementary boundaries, in reversed order. -/
theorem truncatedPrefixDefect_reverseDual_swap_general
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haValues : ∀ j,
      aDual.toBONG.valueUnit j = (a.toBONG.valueUnit (Fin.rev j))⁻¹)
    (hbValues : ∀ j,
      bDual.toBONG.valueUnit j = (b.toBONG.valueUnit (Fin.rev j))⁻¹)
    (haAlpha : ∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j))
    (hbAlpha : ∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j))
    (i j : Nat) (hi : i ≤ n + 1) (hj : j ≤ n + 1)
    (epsilon : Kˣ) :
    bDual.truncatedPrefixDefect aDual epsilon i j =
      a.truncatedPrefixDefect b epsilon
        (n + 1 - j) (n + 1 - i) := by
  have haPrefix :=
    a.toBONG.prefixProduct_mul_valueProduct_of_reverseValues
      aDual.toBONG haValues j hj
  have hbPrefix :=
    b.toBONG.prefixProduct_mul_valueProduct_of_reverseValues
      bDual.toBONG hbValues i hi
  change aDual.prefixProduct j * a.toBONG.valueProduct =
    a.prefixProduct (n + 1 - j) at haPrefix
  change bDual.prefixProduct i * b.toBONG.valueProduct =
    b.prefixProduct (n + 1 - i) at hbPrefix
  have haPrefix' : aDual.prefixProduct j =
      a.prefixProduct (n + 1 - j) * a.toBONG.valueProduct⁻¹ := by
    calc
      aDual.prefixProduct j =
          (aDual.prefixProduct j * a.toBONG.valueProduct) *
            a.toBONG.valueProduct⁻¹ := by group
      _ = a.prefixProduct (n + 1 - j) *
            a.toBONG.valueProduct⁻¹ := by rw [haPrefix]
  have hbPrefix' : bDual.prefixProduct i =
      b.prefixProduct (n + 1 - i) * b.toBONG.valueProduct⁻¹ := by
    calc
      bDual.prefixProduct i =
          (bDual.prefixProduct i * b.toBONG.valueProduct) *
            b.toBONG.valueProduct⁻¹ := by group
      _ = b.prefixProduct (n + 1 - i) *
            b.toBONG.valueProduct⁻¹ := by rw [hbPrefix]
  rcases BONG.exists_valueProduct_eq_mul_square
    a.toBONG b.toBONG with ⟨p, hp⟩
  let squareRoot : Kˣ := (a.toBONG.valueProduct * p)⁻¹
  have hraw : epsilon * bDual.prefixProduct i * aDual.prefixProduct j =
      (epsilon * a.prefixProduct (n + 1 - j) *
        b.prefixProduct (n + 1 - i)) * squareRoot ^ 2 := by
    rw [haPrefix', hbPrefix', hp]
    dsimp only [squareRoot]
    simp only [mul_inv_rev, pow_two]
    ac_rfl
  have haCap := a.prefixAlphaCap_eq_reverseDual
    aDual haAlpha j hj
  have hbCap := b.prefixAlphaCap_eq_reverseDual
    bDual hbAlpha i hi
  unfold truncatedPrefixDefect
  rw [hraw, defectOrder_mul_square, haCap, hbCap]
  simp only [min_comm]

/-- Equal-boundary specialization of reverse-dual capped-defect transport. -/
theorem truncatedPrefixDefect_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haValues : ∀ j,
      aDual.toBONG.valueUnit j = (a.toBONG.valueUnit (Fin.rev j))⁻¹)
    (hbValues : ∀ j,
      bDual.toBONG.valueUnit j = (b.toBONG.valueUnit (Fin.rev j))⁻¹)
    (haAlpha : ∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j))
    (hbAlpha : ∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j))
    (i : Nat) (hi : i ≤ n + 1) (epsilon : Kˣ) :
    bDual.truncatedPrefixDefect aDual epsilon i i =
      a.truncatedPrefixDefect b epsilon (n + 1 - i) (n + 1 - i) := by
  exact truncatedPrefixDefect_reverseDual_swap_general
    a b aDual bDual haValues hbValues haAlpha hbAlpha
    i i hi hi epsilon

/-- Existence form: reverse-dual BONGs can be chosen so that all
complementary capped-defect identities hold simultaneously. -/
theorem exists_reverseDualPair_with_truncatedPrefixDefect
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1)) :
    ∃ (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
      (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1)),
      (∀ j, aDual.order j = -a.order (Fin.rev j)) ∧
      (∀ j, bDual.order j = -b.order (Fin.rev j)) ∧
      (∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j)) ∧
      (∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j)) ∧
      ∀ (i j : Nat), i ≤ n + 1 → j ≤ n + 1 → ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon i j =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - j) (n + 1 - i) := by
  rcases a.exists_reverseDual_with_alpha with
    ⟨aDual, _, haValues, haOrders, haAlpha⟩
  rcases b.exists_reverseDual_with_alpha with
    ⟨bDual, _, hbValues, hbOrders, hbAlpha⟩
  have haUnits : ∀ j,
      aDual.toBONG.valueUnit j =
        (a.toBONG.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    apply Units.ext
    exact haValues j
  have hbUnits : ∀ j,
      bDual.toBONG.valueUnit j =
        (b.toBONG.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    apply Units.ext
    exact hbValues j
  refine ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha, ?_⟩
  intro i j hi hj epsilon
  exact truncatedPrefixDefect_reverseDual_swap_general
    a b aDual bDual haUnits hbUnits haAlpha hbAlpha i j hi hj epsilon

end BONG.GoodBONG

end Bong
