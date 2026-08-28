/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIStrictWitness

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the type-III boundary witness

The domination witness is always at least `R + 1`.  If it is at least
`R + 2`, the strict-witness theorem finishes condition 2.1(ii).  Hence the
only remaining branch has exact witness order `R + 1`; this structure keeps
all domination data needed by the paper's final integrality split.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The unique boundary configuration left after the strict type-III
domination branch. -/
def Lemma79CaseSixTypeIIIBoundaryWitness
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (i : RepresentationIndex (n + 2) (n + 2)) : Prop :=
  ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i.val - 1 ∧
    c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ) ∧
    (((((c.order j.castSucc -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) ≤
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ) ∧
    c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1

/-- Exact third-prefix domination either proves condition 2.1(ii), or
returns the sole boundary witness `T_j = R + 1`. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_or_boundaryWitness
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hthird : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        b.truncatedPrefixDefect c 1 i.val i.val ∨
      Lemma79CaseSixTypeIIIBoundaryWitness a b c D i := by
  rcases beli2019Lemma79_typeIII_caseSix_exists_dominationWitness
      a b c D hfirst hnorm i hright heven hthird with
    ⟨j, hjEven, hjlt, hjDefect, hjCoefficient, hjLower⟩
  have hiTwo : 2 ≤ i.val := by omega
  have hjCoefficient' :
      (((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) ≤
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ) := by
    simpa only [evenTargetPreviousIndex, evenTargetPreviousAlphaIndex] using
      hjCoefficient
  by_cases hstrict :
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 2 ≤
        c.order j.castSucc
  · exact Or.inl
      (beli2019Lemma79_typeIII_caseSix_secondParity_of_strictWitness
        a b c D i hright hthroughLast heven hiTwo j hjCoefficient' hstrict)
  · refine Or.inr ⟨j, hjEven, hjlt, hjDefect, hjCoefficient', ?_⟩
    omega

end BONG.GoodBONG

end Bong
