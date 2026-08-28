/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeITargetEquality
import Bong.Bong.Beli2019Lemma79EvenTypeITargetNonintegralAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 3: central target prefix

This file assembles the domination reduction, the nonintegral preceding-alpha
branch, and the final equality branch.  It completes the target self-prefix
bound throughout the central type-I interval.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- The reduction expands two dependent exceptional branches.
/-- The target self-prefix bound in the central even range of type I. -/
theorem beli2019Lemma79_typeI_central_even_target
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  rcases beli2019Lemma79_typeI_central_even_target_reduction
      a b c D C hfirst hnorm i hiTwo hiEven hiLeft hiRight hcross with
    hdone | ⟨j, hjEven, hjBefore, hjOrder, hjDefect, _, _, hexception⟩
  · exact hdone
  · rcases hexception with hnotAlpha | heq
    · exact
        beli2019Lemma79_typeI_central_even_target_of_previousAlpha_not_integral
          a b c D C hfirst hnorm i hiTwo hiEven hiLeft hiRight hnotAlpha
    · exact
        beli2019Lemma79_typeI_central_even_target_of_domination_equality
          a b c D C hfirst hnorm i hiTwo hiEven hiLeft hiRight hcross
            j hjEven hjBefore hjOrder hjDefect heq

end BONG.GoodBONG

end Bong
