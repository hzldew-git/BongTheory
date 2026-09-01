/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalMain
import Bong.Lattice.OMaximal

/-!
# Beli, Universal integral quadratic forms, Lemma 4.1

The paper works throughout Section 4 with an integral source lattice.  The
right-hand side below therefore records source integrality explicitly; this
is the hypothesis implicit in the sentence introducing `n`-universality.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The Section 4 test family: all `O`-maximal rank-`n` lattices. -/
def RepresentsAllOMaximalOfRank
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W),
    Module.finrank K W = n → IsOMaximal r M → Represents q r L M

/-- Beli, Lemma 4.1: an integral lattice is `n`-universal exactly when it
represents every `O`-maximal lattice of rank `n`. -/
theorem beliUniversalLemma41
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) :
    IsNUniversal.{u, v, w} q L n ↔
      IsIntegral q L ∧
        RepresentsAllOMaximalOfRank.{u, v, w} q L n := by
  constructor
  · rintro ⟨hintegral, hall⟩
    refine ⟨hintegral, ?_⟩
    intro W _ _ r M hr hmaximal
    exact hall r M hr hmaximal.isIntegral
  · rintro ⟨hintegral, hmaximal⟩
    refine ⟨hintegral, ?_⟩
    intro W _ _ r N hr hN
    obtain ⟨M, hNM, hMmaximal⟩ :=
      exists_oMaximal_superlattice (q := r) (L := N) hN
    exact (hmaximal r M hr hMmaximal).trans (represents_of_le r hNM)

end Lattice

end Bong
