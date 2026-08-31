/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem
import Bong.Bong.BeliUniversalPreliminaries
import Bong.Bong.UnaryModelBONG

/-!
# Beli, universal integral forms: unary representation criterion

This file formalizes Lemma 2.3 of Beli's *Universal integral quadratic forms
over dyadic local fields*.  It specializes the fully proved revised Beli
(2019) representation theorem to unary targets of orders zero and one.
-/

namespace Bong

open Dyadic

namespace BONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The canonical unary BONG is automatically good. -/
noncomputable def unaryModelGoodBONG (a : Kˣ) :
    GoodBONG
      (QuadraticSpace.rescaleUnit a (QuadraticSpace.line K))
      (unaryModelLattice (K := K)) 1 where
  toBONG := unaryModelBONG a
  good := (unaryModelBONG a).isGood_of_length_le_two (by omega)

@[simp]
theorem unaryModelGoodBONG_order (a : Kˣ) :
    (unaryModelGoodBONG a).order 0 = ordUnit K a := by
  change (unaryModelBONG a).order 0 = ordUnit K a
  rw [BONG.order_eq_ordUnit, unaryModelBONG_valueUnit]

end BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}

/-- Beli, Lemma 2.3: for an integral lattice, universality is equivalent to
the ambient and four revised representation conditions for every unary
target whose coefficient has order zero or one. -/
theorem beliUniversalLemma23 (a : BONG.GoodBONG q L (m + 1))
    (hintegral : Lattice.IsIntegral q L) :
    Lattice.IsUniversal q L ↔
      ∀ b : Kˣ, ordUnit K b = 0 ∨ ordUnit K b = 1 →
        q.Represents
            (QuadraticSpace.rescaleUnit b (QuadraticSpace.line K)) ∧
          RepresentationConditionsPrime a (BONG.unaryModelGoodBONG b)
            (Nat.zero_le m) := by
  rw [Lattice.isUniversal_iff_represents_order_zero_or_one]
  constructor
  · rintro ⟨_, hscalar⟩ b hb
    have hlattice :
        Lattice.Represents q
          (QuadraticSpace.rescaleUnit b (QuadraticSpace.line K)) L
          (BONG.unaryModelLattice (K := K)) :=
      (Lattice.represents_unaryModel_iff_representsScalar b).2
        (hscalar b hb)
    rcases hlattice with ⟨f⟩
    let hambient :
        q.Represents
          (QuadraticSpace.rescaleUnit b (QuadraticSpace.line K)) :=
      ⟨f.toQuadraticSpaceRepresentation⟩
    refine ⟨hambient, ?_⟩
    exact (beli2019Theorem21_prime (Nat.zero_le m) hambient a
      (BONG.unaryModelGoodBONG b)).1 ⟨f⟩
  · intro h
    refine ⟨hintegral, ?_⟩
    intro b hb
    have hdata := h b hb
    have hlattice :
        Lattice.Represents q
          (QuadraticSpace.rescaleUnit b (QuadraticSpace.line K)) L
          (BONG.unaryModelLattice (K := K)) :=
      (beli2019Theorem21_prime (Nat.zero_le m) hdata.1 a
        (BONG.unaryModelGoodBONG b)).2 hdata.2
    exact (Lattice.represents_unaryModel_iff_representsScalar b).1 hlattice

end Bong
