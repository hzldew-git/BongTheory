/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanEffectiveNorm
import Bong.Lattice.JordanReverseDual

/-!
# Reverse duals of weak Jordan decompositions

Reverse component order after taking integral duals.  The construction
preserves nondecreasing scale order.  Its chosen norm generators need not be
definitionally related to the original choices, so the order relation is
proved through their principal norm ideals.  This also proves that O'Meara's
improper-even-rank invariant is preserved by reverse duality.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace Lattice.WeakJordanDecomposition

/-- Reverse the components of a weak Jordan decomposition after taking
their integral duals. -/
noncomputable def reverseDual
    (W : WeakJordanDecomposition q L t) :
    WeakJordanDecomposition q (Lattice.dualLattice q L) t where
  toOrthogonalDecomposition := W.toOrthogonalDecomposition.reverseDual
  scaleGenerator := fun i => (W.scaleGenerator (Fin.rev i))⁻¹
  modular := by
    intro i
    exact (W.modular (Fin.rev i)).dual
  component_finrank_pos := by
    intro i
    exact W.component_finrank_pos (Fin.rev i)
  scaleOrder_mono := by
    intro i j hij
    dsimp only
    rw [ordUnit_inv, ordUnit_inv]
    have hrev : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
    exact neg_le_neg (W.scaleOrder_mono hrev)

@[simp]
theorem reverseDual_component
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    W.reverseDual.component i = (W.component (Fin.rev i)).dual :=
  rfl

@[simp]
theorem reverseDual_scaleGenerator
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    W.reverseDual.scaleGenerator i = (W.scaleGenerator (Fin.rev i))⁻¹ :=
  rfl

@[simp]
theorem reverseDual_componentRank
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    W.reverseDual.componentRank i = W.componentRank (Fin.rev i) :=
  rfl

/-- Strict scale order is preserved after reversing and negating all scale
orders. -/
theorem reverseDual_scaleOrder_strict
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i => ordUnit K (W.scaleGenerator i))) :
    StrictMono (fun i => ordUnit K (W.reverseDual.scaleGenerator i)) := by
  intro i j hij
  change ordUnit K (W.reverseDual.scaleGenerator i) <
    ordUnit K (W.reverseDual.scaleGenerator j)
  rw [W.reverseDual_scaleGenerator, W.reverseDual_scaleGenerator,
    ordUnit_inv, ordUnit_inv]
  have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hij
  exact neg_lt_neg (hstrict hrev)

/-- The chosen norm generator of a reverse-dual weak component has the
expected inverse-square transformed order. -/
theorem reverseDual_normGeneratorUnit_order
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    ordUnit K (W.reverseDual.normGeneratorUnit i) =
      -2 * ordUnit K (W.scaleGenerator (Fin.rev i)) +
        ordUnit K (W.normGeneratorUnit (Fin.rev i)) := by
  let j := Fin.rev i
  let c : Kˣ := (W.scaleGenerator j)⁻¹
  let a : Kˣ := W.normGeneratorUnit j
  have hscaled :
      Lattice.normIdeal (W.component j).space
          (Lattice.rescale c (W.component j).lattice) =
        Lattice.principalIdeal (K := K) ((c ^ 2 * a : Kˣ) : K) :=
    Lattice.normIdeal_rescale_eq_principal_of_finrank_pos
      (W.component_finrank_pos j) c a (W.normIdeal_eq_normGeneratorUnit j)
  have hdual :
      Lattice.normIdeal (W.component j).space
          (Lattice.dualLattice (W.component j).space (W.component j).lattice) =
        Lattice.principalIdeal (K := K) ((c ^ 2 * a : Kˣ) : K) := by
    rw [W.modular j]
    exact hscaled
  have hprincipal :
      Lattice.principalIdeal (K := K) (W.reverseDual.normGeneratorUnit i : K) =
        Lattice.principalIdeal (K := K) ((c ^ 2 * a : Kˣ) : K) := by
    calc
      Lattice.principalIdeal (K := K) (W.reverseDual.normGeneratorUnit i : K) =
          Lattice.normIdeal (W.reverseDual.component i).space
            (W.reverseDual.component i).lattice :=
        (W.reverseDual.normIdeal_eq_normGeneratorUnit i).symm
      _ = Lattice.normIdeal (W.component j).space
            (Lattice.dualLattice (W.component j).space
              (W.component j).lattice) := by rfl
      _ = Lattice.principalIdeal (K := K) ((c ^ 2 * a : Kˣ) : K) := hdual
  have hord := (Lattice.principalIdeal_eq_iff_ordUnit_eq
    (W.reverseDual.normGeneratorUnit i) (c ^ 2 * a)).mp hprincipal
  rw [ordUnit_mul, ordUnit_pow, ordUnit_inv] at hord
  dsimp only [j, c, a] at hord
  norm_num at hord
  omega

/-- O'Meara's parity invariant for improper modular components is stable
under reverse duality. -/
theorem HasImproperEvenRank.reverseDual
    (W : WeakJordanDecomposition q L t) (hW : W.HasImproperEvenRank) :
    W.reverseDual.HasImproperEvenRank := by
  intro i hstrict
  have horder := W.reverseDual_normGeneratorUnit_order i
  rw [W.reverseDual_scaleGenerator, ordUnit_inv] at hstrict
  have hold : ordUnit K (W.scaleGenerator (Fin.rev i)) <
      ordUnit K (W.normGeneratorUnit (Fin.rev i)) := by
    omega
  change Even (finrank K (W.component (Fin.rev i)).carrier)
  exact hW (Fin.rev i) hold

end Lattice.WeakJordanDecomposition

end Bong
