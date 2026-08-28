/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93Problem
import Bong.Bong.Beli2019Lemma96Problem

/-!
# Beli (2019), Section 9: exhaustive head cases

This module contains only the logical trichotomy used in the final descent.
Keeping it independent of `Beli2019FinalStep` lets the constructive proof of
Lemma 9.12 consume the literal residual case without introducing an import
cycle.
-/

namespace Bong

open Dyadic

universe u v w x

/-- The three mutually exhaustive branches isolated in Section 9. -/
inductive Beli2019SectionNineCase
    {P : Type x} (ordinaryHead exceptionalHead residual : P → Prop)
    (p : P) : Prop
  | lemma93 (ordinary : ordinaryHead p)
  | lemma96 (exceptional : exceptionalHead p)
  | lemma912 (remaining : residual p)

/-- The literal residual case of Section 9: neither of the two solved-head
inputs has been constructed.  This is the hypothesis handled by Lemma 9.12. -/
def Beli2019SectionNineResidual
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (p : Beli2019RepresentationProblem.{u, v, w} K) : Prop :=
  ¬Nonempty (Beli2019RepresentationProblem.Lemma93Input p) ∧
    ¬Nonempty (Beli2019RepresentationProblem.Lemma96Input p)

/-- The three Section 9 branches are exhaustive once their predicates are
fixed to the concrete Lemma 9.3 and Lemma 9.6 inputs. -/
theorem beli2019SectionNine_cases
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (p : Beli2019RepresentationProblem.{u, v, w} K) :
    Beli2019SectionNineCase
      (fun p ↦ Nonempty (Beli2019RepresentationProblem.Lemma93Input p))
      (fun p ↦ Nonempty (Beli2019RepresentationProblem.Lemma96Input p))
      Beli2019SectionNineResidual p := by
  classical
  by_cases ordinary : Nonempty (Beli2019RepresentationProblem.Lemma93Input p)
  · exact .lemma93 ordinary
  · by_cases exceptional :
        Nonempty (Beli2019RepresentationProblem.Lemma96Input p)
    · exact .lemma96 exceptional
    · exact .lemma912 ⟨ordinary, exceptional⟩

end Bong
