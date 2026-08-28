/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionSevenReduction
import Bong.Bong.Beli2019SectionNineComplete

/-!
# Beli (2019): the equal-rank rank-volume induction

This file combines the concrete reductions of Sections 7 and 9 with the
well-founded rank-volume measure.  With the literal rank-three and rank-four
endpoints of Section 9 now available, only ranks one and two remain as base
cases.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Abstract form of Beli's final equal-rank induction.  Section 7 and the
complete Section 9 both apply from rank three onward, leaving only the unary
and binary base cases. -/
theorem not_counterexample_of_equalRank_reductions
    (lowRank : ∀ p : Beli2019RepresentationProblem.{u, v, w} K,
      p.sourceIndex = p.targetIndex → p.sourceIndex < 2 →
        ¬p.Counterexample)
    (sectionSeven : ∀ p : Beli2019RepresentationProblem.{u, v, w} K,
      p.sourceIndex = p.targetIndex → 2 ≤ p.sourceIndex →
        p.Counterexample →
        p.EqualNorm ∨
          ∃ next, next.Counterexample ∧
            next.sourceIndex = next.targetIndex ∧
            Beli2019ProblemSmaller measure next p)
    (sectionNine : ∀ p : Beli2019RepresentationProblem.{u, v, w} K,
      p.sourceIndex = p.targetIndex → 2 ≤ p.sourceIndex →
        p.Counterexample → p.EqualNorm →
          ∃ next, next.Counterexample ∧
            next.sourceIndex = next.targetIndex ∧
            Beli2019ProblemSmaller measure next p)
    (p : Beli2019RepresentationProblem.{u, v, w} K) :
    p.sourceIndex = p.targetIndex → ¬p.Counterexample := by
  apply (beli2019ProblemSmaller_wellFounded measure).induction p
  intro current ih hindex hcounterexample
  by_cases hsectionSeven : 2 ≤ current.sourceIndex
  · rcases sectionSeven current hindex hsectionSeven hcounterexample with
      hequal | ⟨next, hnext, hnextIndex, hsmaller⟩
    · rcases sectionNine current hindex hsectionSeven hcounterexample hequal with
        ⟨next, hnext, hnextIndex, hsmaller⟩
      exact ih next hsmaller hnextIndex hnext
    · exact ih next hsmaller hnextIndex hnext
  · exact lowRank current hindex (by omega) hcounterexample

end Beli2019RepresentationProblem

end Bong
