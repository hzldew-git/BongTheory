/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyEndpointFirst

/-!
# Beli (2019), Lemma 4.2: the nonterminal left-direct branch

This file combines the first-boundary calculation with the interior
calculation.  Thus only the terminal endpoint remains separate.
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

/-- Lemma 4.2(i)'s two direct conclusions whenever the following ordinary
boundary exists. -/
theorem leftDirect_bounds_of_not_last
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hnext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j ≤ a.representationAlpha b j ∧
      a.representationAlpha c j ≤ b.representationAlpha c j := by
  by_cases hfirst : j.val = 1
  · exact ⟨a.representationAlpha_le_leftDirect_sourceAlpha_of_eq_one
      b c hbcOrder j hfirst,
      a.leftDirect_middleBound_of_eq_one_of_not_last
        (sourceLaws := sourceLaws) (middleLaws := middleLaws)
        (targetLaws := targetLaws) b c hab habDefect hbcOrder hbcDefect
          j hfirst hnext hessential⟩
  · have hinterior : 1 < j.val ∧ j.val + 1 < n + 1 := by
      constructor
      · have := j.pos
        omega
      · exact hnext
    exact ⟨a.leftDirect_sourceBound_of_interior
        (sourceLaws := sourceLaws) (middleLaws := middleLaws)
        (targetLaws := targetLaws) b c hab habDefect hbcOrder hbcDefect
          j hinterior hessential hdirect,
      a.leftDirect_middleBound_of_interior
        (sourceLaws := sourceLaws) (middleLaws := middleLaws)
        (targetLaws := targetLaws) b c hab habDefect hbcOrder hbcDefect
          j hinterior hessential hdirect⟩

end BONG.GoodBONG

end Bong
