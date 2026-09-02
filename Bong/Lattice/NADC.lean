/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OMaximal

/-!
# Local n-ADC quadratic lattices

This file formalizes Definition 1.1(ii) of Zilong He,
*On n-ADC integral quadratic lattices over algebraic number fields*.
It also proves the maximal-lattice reduction used as Lemma 2.1 in that paper.

All notions in this file are local.  The global definitions, localization
data, and `n`-regularity are deliberately kept separate so that local and
global quantifiers cannot be conflated.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A local integral lattice is `n`-ADC when it integrally represents every
integral rank-`n` lattice whose ambient quadratic space is represented by its
own ambient quadratic space. -/
def IsNADC (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) : Prop :=
  IsIntegral q L ∧
    ∀ {W : Type w} [AddCommGroup W] [Module K W]
      (r : QuadraticSpace K W) (M : Lattice K W),
      finrank K W = n → IsIntegral r M → q.Represents r →
        Represents q r L M

namespace IsNADC

theorem isIntegral (h : IsNADC.{u, v, w} q L n) : IsIntegral q L :=
  h.1

theorem represents
    (h : IsNADC.{u, v, w} q L n)
    {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W)
    (hrank : finrank K W = n) (hM : IsIntegral r M)
    (hambient : q.Represents r) : Represents q r L M :=
  h.2 r M hrank hM hambient

end IsNADC

/-- Local `n`-universality implies local `n`-ADC-ness. -/
theorem IsNUniversal.isNADC
    (h : IsNUniversal.{u, v, w} q L n) : IsNADC.{u, v, w} q L n := by
  refine ⟨h.1, ?_⟩
  intro W _ _ r M hr hM _
  exact h.2 r M hr hM

/-- The restricted test family from He, Lemma 2.1: maximal rank-`n`
lattices whose ambient spaces are represented by the target ambient space. -/
def RepresentsAllRelevantOMaximalOfRank
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W),
    finrank K W = n → IsOMaximal r M → q.Represents r →
      Represents q r L M

/-- He (2025), Lemma 2.1: the local `n`-ADC condition can be tested only on
`O`-maximal rank-`n` lattices in ambient spaces represented by the target. -/
theorem isNADC_iff_representsAllRelevantOMaximal
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) :
    IsNADC.{u, v, w} q L n ↔
      IsIntegral q L ∧
        RepresentsAllRelevantOMaximalOfRank.{u, v, w} q L n := by
  constructor
  · rintro ⟨hintegral, hall⟩
    refine ⟨hintegral, ?_⟩
    intro W _ _ r M hr hmaximal hambient
    exact hall r M hr hmaximal.isIntegral hambient
  · rintro ⟨hintegral, hmaximal⟩
    refine ⟨hintegral, ?_⟩
    intro W _ _ r N hr hN hambient
    obtain ⟨M, hNM, hMmaximal⟩ :=
      exists_oMaximal_superlattice (q := r) (L := N) hN
    exact (hmaximal r M hr hMmaximal hambient).trans
      (represents_of_le r hNM)

end Lattice

end Bong
