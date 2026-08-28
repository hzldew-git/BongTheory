/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62PrimaryPair

/-!
# Beli (2019), Proposition 6.2: noninitial even coordinates

The candidate reduction and the closed primary branch together give exactly
the two alternatives required by Beli's sequence order at every noninitial
even coordinate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Proposition 6.2(a) at a noninitial boundary. -/
theorem representationWeightEven_direct_or_pair
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val) :
    a.representationWeightEvenDirect b i ∨
      a.representationWeightEvenPair b i hi := by
  rcases a.representationWeightEven_direct_or_pair_or_primary
      b horder hdefect i hi with hdirect | hpair | hprimary
  · exact Or.inl hdirect
  · exact Or.inr hpair
  · by_cases hdirect : a.representationWeightEvenDirect b i
    · exact Or.inl hdirect
    · exact Or.inr <|
        a.representationWeightEvenPair_of_primary b horder hdefect i hi
          hprimary hdirect

end BONG.GoodBONG

end Bong
