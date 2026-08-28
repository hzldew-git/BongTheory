/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeII

/-!
# Beli (2019), Lemma 7.9(ii), case 6: type-II second-parity assembly

The target current order is either congruent modulo two to the preceding
third order or to that order plus one.  The two alternatives are exactly the
same-current-parity and opposite-current-parity branches proved previously.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The complete type-II second-parity branch of case 6. -/
theorem beli2019Lemma79_typeII_caseSix_secondParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases modEq_two_or_add_one
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)) with hsame | hopposite
  · exact beli2019Lemma79_typeII_caseSix_secondParity_sameCurrentParity
      a b c D hfirst hnorm i hright hthroughLast heven hcomparison hsame
  · exact beli2019Lemma79_typeII_caseSix_secondParity_oppositeCurrentParity
      a b c D hfirst hnorm i hright hthroughLast heven hcomparison hopposite

end BONG.GoodBONG

end Bong
