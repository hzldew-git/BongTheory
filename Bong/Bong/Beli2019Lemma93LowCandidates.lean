/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma812
import Bong.Bong.Beli2019Lemma93InputAssembly

/-!
# Beli (2019), Lemma 9.3: low comparison candidates

For the four low indices not covered automatically by Lemma 9.2, the paper
compares the primary and secondary capped-defect candidates defining `A_i`.
This file proves that those candidate equalities are sufficient.  At the
first tail boundary, the original index is the second boundary; Lemma 8.12(ii)
removes the extra secondary candidate exactly as in the paper.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n N : Nat}

private theorem representationIndex_eq_of_val_eq
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- Beyond the first tail boundary, equality of the primary and (when
present) secondary candidates gives equality of the complete comparison
alpha.  The half-gap candidate is automatically invariant under deleting
the two heads. -/
theorem representationAlpha_tail_eq_shift_of_primary_secondary_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val)
    (hprimary :
      a.tail.representationPrimaryDefect b.tail i =
        a.representationPrimaryDefect b i.tailShift)
    (hsecondary : ∀ hinterior : i.val + 1 < n + 1,
      a.tail.representationSecondaryDefect b.tail i ⟨hi, hinterior⟩ =
        a.representationSecondaryDefect b i.tailShift
          ⟨by
            simp only [RepresentationIndex.tailShift_val]
            omega,
           by
            simp only [RepresentationIndex.tailShift_val]
            omega⟩) :
    a.tail.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift := by
  rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i,
    a.representationAlpha_eq_min_halfGap_prime b i.tailShift,
    a.representationHalfGap_tail_eq_shift b i]
  by_cases hinterior : i.val + 1 < n + 1
  · have htailInterior : 1 < i.val ∧ i.val + 1 < n + 1 :=
      ⟨hi, hinterior⟩
    have horiginalInterior :
        1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rw [a.tail.representationAlphaPrime_eq_min_primary_secondary
        b.tail i htailInterior,
      a.representationAlphaPrime_eq_min_primary_secondary
        b i.tailShift horiginalInterior,
      hprimary, hsecondary hinterior]
  · have htailEndpoint :
        ¬(1 < i.val ∧ i.val + 1 < n + 1) := by omega
    have horiginalEndpoint :
        ¬(1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2) := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rw [a.tail.representationAlphaPrime_eq_primary_of_not_interior
        b.tail i htailEndpoint,
      a.representationAlphaPrime_eq_primary_of_not_interior
        b i.tailShift horiginalEndpoint,
      hprimary]

/-- At the first tail boundary, Lemma 8.12(ii) identifies the shifted
original comparison alpha with the minimum of its half-gap and primary
candidates.  Therefore primary-candidate equality is again sufficient. -/
theorem representationAlpha_tail_first_eq_originalSecond_of_primary_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M (N + 3))
    (hfirst : a.order (0 : Fin (N + 3)) =
      b.order (0 : Fin (N + 3)))
    (hprimary :
      a.tail.representationPrimaryDefect b.tail
          (firstRepresentationIndex N (N + 1)) =
        a.representationPrimaryDefect b
          (secondRepresentationIndex N (N + 1))) :
    a.tail.representationAlpha b.tail
        (firstRepresentationIndex N (N + 1)) =
      a.representationAlpha b
        (secondRepresentationIndex N (N + 1)) := by
  let first := firstRepresentationIndex N (N + 1)
  have hshift : first.tailShift = secondRepresentationIndex N (N + 1) := by
    apply representationIndex_eq_of_val_eq
    simp only [RepresentationIndex.tailShift_val, first,
      firstRepresentationIndex, secondRepresentationIndex]
  have hhalf := a.representationHalfGap_tail_eq_shift b first
  rw [hshift] at hhalf
  have hprimary' :
      a.tail.representationPrimaryDefect b.tail first =
        a.representationPrimaryDefect b
          (secondRepresentationIndex N (N + 1)) := by
    simpa only [first] using hprimary
  rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail first,
    a.tail.representationAlphaPrime_eq_primary_of_not_interior
      b.tail first (by simp [first, firstRepresentationIndex])]
  rw [hprimary', hhalf, a.beli2019Lemma812_ii b hfirst]
  simp only [representationHalfGap_second_eq_formula,
    representationPrimaryDefect_second_eq_formula]

/-- A paper-facing low-index dispatcher.  It turns the capped-defect
candidate equalities at values `1,2,3,4` into the exact `A_i=A_i^*`
equalities required by the Lemma 9.3 tail argument. -/
theorem lowRepresentationAlpha_eq_of_candidate_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hhead : a.value 0 = b.value 0)
    (hprimary : ∀ i : RepresentationIndex (N + 3) (N + 3),
      (a.tail.IsCurrentEssential b.tail i ∨
        a.tail.IsNextEssential b.tail i) →
      i.val ≤ 4 →
      a.tail.representationPrimaryDefect b.tail i =
        a.representationPrimaryDefect b i.tailShift)
    (hsecondary : ∀ (i : RepresentationIndex (N + 3) (N + 3))
      (_ : a.tail.IsCurrentEssential b.tail i ∨
        a.tail.IsNextEssential b.tail i)
      (hi : 1 < i.val) (_ : i.val ≤ 4)
      (hinterior : i.val + 1 < N + 3),
        a.tail.representationSecondaryDefect b.tail i
            ⟨hi, hinterior⟩ =
          a.representationSecondaryDefect b i.tailShift
            ⟨by
              simp only [RepresentationIndex.tailShift_val]
              omega,
             by
              simp only [RepresentationIndex.tailShift_val]
              omega⟩) :
    ∀ i : RepresentationIndex (N + 3) (N + 3),
      (a.tail.IsCurrentEssential b.tail i ∨
        a.tail.IsNextEssential b.tail i) →
      i.val ≤ 4 →
      a.tail.representationAlpha b.tail i =
        a.representationAlpha b i.tailShift := by
  intro i hessential hlow
  by_cases hone : i.val = 1
  · have hi : i = firstRepresentationIndex (N + 1) (N + 2) := by
      apply representationIndex_eq_of_val_eq
      simpa only [firstRepresentationIndex] using hone
    have hshift :
        (firstRepresentationIndex (N + 1) (N + 2)).tailShift =
        secondRepresentationIndex (N + 1) (N + 2) := by
      apply representationIndex_eq_of_val_eq
      simp only [RepresentationIndex.tailShift_val,
        firstRepresentationIndex, secondRepresentationIndex]
    have horder : a.order (0 : Fin (N + 4)) =
        b.order (0 : Fin (N + 4)) := by
      change ordUnit K (a.valueUnit 0) = ordUnit K (b.valueUnit 0)
      congr 1
      apply Units.ext
      exact hhead
    have hp := hprimary i hessential hlow
    rw [hi, hshift] at hp
    rw [hi, hshift]
    exact a.representationAlpha_tail_first_eq_originalSecond_of_primary_eq
      b horder hp
  · have hi : 1 < i.val := by
      have := i.pos
      omega
    exact a.representationAlpha_tail_eq_shift_of_primary_secondary_eq
      b i hi (hprimary i hessential hlow)
        (hsecondary i hessential hi hlow)

end BONG.GoodBONG

namespace Beli2019RepresentationProblem.Lemma93Input

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {p : Beli2019RepresentationProblem.{u, v, w} K}

local instance : AddCommGroup p.Target := p.targetAddCommGroup
local instance : Module K p.Target := p.targetModule
local instance : AddCommGroup p.Source := p.sourceAddCommGroup
local instance : Module K p.Source := p.sourceModule

/-- Complete the Lemma 9.2-to-Lemma 9.3 assembly using the capped-defect
candidate equalities proved in the low-index case split of Section 9. -/
noncomputable def ofLemma92TransformsOfLowCandidates
    [targetAlphaLaws : Beli2006AlphaLaws.{u, v} K]
    [classificationTarget : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationSource : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    (N : Nat)
    (htarget : p.targetIndex = N + 3)
    (hsource : p.sourceIndex = N + 3)
    (Ta : BONG.GoodBONG.Beli2019Lemma92Transform
      (p.lemma93TargetBONG (N + 2) (by omega)))
    (Tb : BONG.GoodBONG.Beli2019Lemma92Transform
      (p.lemma93SourceBONG (N + 2) (by omega)))
    (hhead : Ta.transformed.value 0 = Tb.transformed.value 0)
    (hsecond : Ta.transformed.order ⟨1, by omega⟩ ≤
      Tb.transformed.order ⟨1, by omega⟩)
    (hprimary : ∀ i : RepresentationIndex (N + 3) (N + 3),
      (Ta.transformed.tail.IsCurrentEssential Tb.transformed.tail i ∨
        Ta.transformed.tail.IsNextEssential Tb.transformed.tail i) →
      i.val ≤ 4 →
      Ta.transformed.tail.representationPrimaryDefect
          Tb.transformed.tail i =
        Ta.transformed.representationPrimaryDefect
          Tb.transformed i.tailShift)
    (hsecondary : ∀ (i : RepresentationIndex (N + 3) (N + 3))
      (_ : Ta.transformed.tail.IsCurrentEssential Tb.transformed.tail i ∨
        Ta.transformed.tail.IsNextEssential Tb.transformed.tail i)
      (hi : 1 < i.val) (_ : i.val ≤ 4)
      (hinterior : i.val + 1 < N + 3),
      Ta.transformed.tail.representationSecondaryDefect
          Tb.transformed.tail i ⟨hi, hinterior⟩ =
        Ta.transformed.representationSecondaryDefect
          Tb.transformed i.tailShift
            ⟨by
              simp only [RepresentationIndex.tailShift_val]
              omega,
             by
              simp only [RepresentationIndex.tailShift_val]
              omega⟩) :
    Lemma93Input p :=
  ofLemma92Transforms (p := p)
    (classificationTarget := classificationTarget)
    (classificationSource := classificationSource)
    N htarget hsource Ta Tb hhead hsecond
    (Ta.transformed.lowRepresentationAlpha_eq_of_candidate_eq
      Tb.transformed hhead hprimary hsecondary)

end Beli2019RepresentationProblem.Lemma93Input

end Bong
