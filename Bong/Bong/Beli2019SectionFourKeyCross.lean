/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyNextCandidates

/-!
# Beli (2019), Lemma 4.2: closing the crossed left-direct subcase

The candidate eliminations and strict defect triangle now combine to rule
out failure when `T_(i-2) ≤ S_i`.  This is lines 2230--2249.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- The final contradiction after all Section 4 candidate calculations have
been exposed as separate checked inequalities. -/
theorem leftDirect_sourceBound_of_cross_of_certificates
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hcommon :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
        (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          b.representationAlpha c (previousRepresentationIndex j hi.1))
    (hnextPrimary :
      a.representationAlpha b (nextRepresentationIndex j hi.2) =
        a.representationPrimaryDefect b (nextRepresentationIndex j hi.2))
    (hreverse :
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
          b.representationAlpha c (previousRepresentationIndex j hi.1) <
        (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationPrimaryDefect b (nextRepresentationIndex j hi.2)) : False := by
  rw [hnextPrimary] at hcommon
  exact (not_lt_of_ge hcommon) hreverse

end BONG.GoodBONG

end Bong
