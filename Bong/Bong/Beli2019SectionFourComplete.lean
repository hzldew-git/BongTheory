/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyEndpointLast
import Bong.Bong.Beli2019SectionFourKeyFallbackComplete
import Bong.Bong.Beli2019SectionFourKeyDual

/-!
# Beli (2019), Section 4: complete key-lemma bounds

This file assembles Lemma 4.2(i), its reverse-dual part (ii), and both
fallback branches into the certificate consumed by defect transitivity.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 1200000 in
-- Reverse duality selects three aligned BONGs and invokes the already proved
-- left branch uniformly over their dual lattices.
/-- All four bounds in Beli (2019), Lemma 4.2. -/
theorem sectionFourKeyLemmaBounds
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c) :
    SectionFourKeyLemmaBounds a b c where
  current j hcurrent := by
    constructor
    · intro hdirect
      apply a.currentDirectBounds_of_nextDirectBounds_reverseDual b c
        (fun x y z hxy hxyDefect hyz hyzDefect k hessential hleft =>
          x.leftDirect_bounds y z hxy hxyDefect hyz hyzDefect
            k hessential hleft)
        hab habDefect hbcOrder hbcDefect j hcurrent hdirect
    · intro hfailure
      have hfailureRaw := hfailure
      unfold KeyLemmaRightDirectTrigger at hfailureRaw
      push Not at hfailureRaw
      rcases hfailureRaw with ⟨hiPos, _, _⟩
      have hprev : 1 < j.val := by
        simp only [currentEssentialIndex] at hiPos
        omega
      refine ⟨hprev, ?_⟩
      exact a.currentFallbackBound_of_nextFallbackBound_reverseDual b c
        (fun x y z hxy hxyDefect hyz hyzDefect k hk hessential hleft =>
          x.leftFallback_bound_of_interior y z hxy hxyDefect hyz
            hyzDefect k hk hessential hleft)
        hab habDefect hbcOrder hbcDefect j hprev hcurrent hfailure
  next j hessential := by
    constructor
    · intro hdirect
      exact a.leftDirect_bounds b c hab habDefect hbcOrder hbcDefect
        j hessential hdirect
    · intro hfailure
      have hfailureRaw := hfailure
      unfold KeyLemmaLeftDirectTrigger at hfailureRaw
      push Not at hfailureRaw
      rcases hfailureRaw with ⟨hiTwo, hiNext, _⟩
      refine ⟨hiNext, ?_⟩
      exact a.leftFallback_bound_of_interior b c hab habDefect hbcOrder
        hbcDefect j ⟨hiTwo, hiNext⟩ hessential hfailure

end BONG.GoodBONG

end Bong
