/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeySecondaryContradiction

/-!
# Beli (2019), Lemma 4.2: extracting the primary source candidate

The half-gap candidate was excluded first, and the preceding file excludes
the secondary source candidate.  Thus a failure of the first direct bound
can only occur when `A_(i-1)` is its primary-defect candidate.  This is the
conclusion on line 2181 of the paper.
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

/-- In the interior left-direct branch, strict failure of `C ≤ A` forces
`A` to be exactly its primary-defect candidate. -/
theorem leftDirect_sourceFailure_eq_primary
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hfailure : ¬a.representationAlpha c j ≤
      a.representationAlpha b j) :
    a.representationAlpha b j = a.representationPrimaryDefect b j ∧
      a.representationPrimaryDefect b j < a.representationAlpha c j := by
  rcases a.leftDirect_sourceFailure_candidate_eq
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab hbcOrder j hi hessential hdirect hfailure with
    hprimary | hsecondary
  · exact hprimary
  · have hlower := a.shift_middleTargetAlpha_le_secondaryCurrentSource
      b c hbcOrder hbcDefect j hi hessential hsecondary.2
    have hmiddlePrimary :=
      a.middleTargetAlpha_eq_primary_of_sourceSecondaryFailure
        (middleLaws := middleLaws) (targetLaws := targetLaws)
        b c hab hbcOrder hbcDefect j hi hessential hdirect
          hsecondary.1 hsecondary.2
    have hcurrent :=
      a.middleTargetPrimaryDefect_eq_sourceMiddleCurrentDefect
        b c hbcOrder j hi hessential hdirect hmiddlePrimary
          hsecondary.2 hlower
    exact False.elim
      (a.sourceSecondaryCandidate_impossible_of_leftDirectFailure
        (middleLaws := middleLaws) b c j hi hessential hsecondary.1
          hmiddlePrimary hcurrent hlower)

end BONG.GoodBONG

end Bong
