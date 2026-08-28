/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary311
import Bong.Bong.Beli2019Lemma93Early
import Bong.Bong.Beli2019Lemma93Problem

/-!
# Beli (2019), Lemma 9.3: assembling the selected-BONG input

This file connects the arithmetic normalization of Lemma 9.2 to the concrete
rank-reduction input of Lemma 9.3.  After both selected BONGs have the later
alpha/tail-alpha agreement, all comparison-alpha equalities with index
greater than four follow automatically.  Thus the paper-facing constructor
asks only for the four endpoint-sensitive low-index equalities.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019RepresentationProblem.Lemma93Input

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {p : Beli2019RepresentationProblem.{u, v, w} K}

local instance : AddCommGroup p.Target := p.targetAddCommGroup
local instance : Module K p.Target := p.targetModule
local instance : AddCommGroup p.Source := p.sourceAddCommGroup
local instance : Module K p.Source := p.sourceModule

/-- Assemble a Lemma 9.3 input from freely selected BONGs.  Once the later
alpha values agree with those of the corresponding tails, only indices at
most four remain as explicit local obligations. -/
noncomputable def ofSelectedBONGs
    (tailIndex : Nat)
    (htarget : p.targetIndex = tailIndex + 1)
    (hsource : p.sourceIndex = tailIndex + 1)
    (a : BONG.GoodBONG p.targetQ p.targetLattice (tailIndex + 2))
    (b : BONG.GoodBONG p.sourceQ p.sourceLattice (tailIndex + 2))
    (conditions : RepresentationConditions a b
      (Nat.le_refl (tailIndex + 1)))
    (hhead : a.value 0 = b.value 0)
    (hsecond : a.order ⟨1, by omega⟩ ≤ b.order ⟨1, by omega⟩)
    (halphaA : ∀ k : Fin tailIndex, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin tailIndex, 2 ≤ k.1 →
      b.alphaValue k.succ = b.tail.alphaValue k)
    (hlow : ∀ i : RepresentationIndex (tailIndex + 1) (tailIndex + 1),
      (a.tail.IsCurrentEssential b.tail i ∨
        a.tail.IsNextEssential b.tail i) →
      i.val ≤ 4 →
      a.tail.representationAlpha b.tail i =
        a.representationAlpha b i.tailShift) :
    Lemma93Input p where
  tailIndex := tailIndex
  targetIndex_eq := htarget
  sourceIndex_eq := hsource
  targetBONG := a
  sourceBONG := b
  selectedConditions := conditions
  headValue_eq := hhead
  secondOrder_le := hsecond
  essentialAlpha_eq := by
    intro i hessential
    by_cases hi : i.val ≤ 4
    · exact hlow i hessential hi
    · exact a.representationAlpha_tail_eq_shift_of_laterAlphaValue_eq
        b hhead halphaA halphaB i (by omega)

/-- Lemma 9.2 supplies the complete high-index part of Lemma 9.3.  The four
conditions of Theorem 2.1 are transported to the normalized BONGs by
Corollary 3.11; the remaining hypotheses are exactly the head comparison and
the low-index case split carried out in Section 9 of the paper. -/
noncomputable def ofLemma92Transforms
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
    (hlow : ∀ i : RepresentationIndex (N + 3) (N + 3),
      (Ta.transformed.tail.IsCurrentEssential Tb.transformed.tail i ∨
        Ta.transformed.tail.IsNextEssential Tb.transformed.tail i) →
      i.val ≤ 4 →
      Ta.transformed.tail.representationAlpha Tb.transformed.tail i =
        Ta.transformed.representationAlpha Tb.transformed i.tailShift) :
    Lemma93Input p := by
  let a := p.lemma93TargetBONG (N + 2) (by omega)
  let b := p.lemma93SourceBONG (N + 2) (by omega)
  have originalConditions :
      RepresentationConditions a b (Nat.le_refl (N + 3)) :=
    p.lemma93AlignedConditions (N + 2) (by omega) (by omega)
  have transformedConditions :
      RepresentationConditions Ta.transformed Tb.transformed
        (Nat.le_refl (N + 3)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationTarget)
      (classificationW := classificationSource)
      Ta.transformed b Tb.transformed (Nat.le_refl (N + 3))).mp
        originalConditions
  refine ofSelectedBONGs (p := p) (N + 2) (by omega) (by omega)
    Ta.transformed Tb.transformed transformedConditions hhead hsecond ?_ ?_ hlow
  · intro k hk
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationTarget
    exact Ta.transformed_laterAlpha_eq_tail k hk
  · intro k hk
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationSource
    exact Tb.transformed_laterAlpha_eq_tail k hk

/-- If both original BONGs satisfy Lemma 9.2's early alternative, its extra
alpha equality discharges tail index four.  Only values at most three remain
for the local Section 9 argument. -/
noncomputable def ofLemma92TransformsEarly
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
    (hcaseTarget :
      (p.lemma93TargetBONG (N + 2) (by omega)).Lemma92EarlyAlternative)
    (hcaseSource :
      (p.lemma93SourceBONG (N + 2) (by omega)).Lemma92EarlyAlternative)
    (hhead : Ta.transformed.value 0 = Tb.transformed.value 0)
    (hsecond : Ta.transformed.order ⟨1, by omega⟩ ≤
      Tb.transformed.order ⟨1, by omega⟩)
    (hlow : ∀ i : RepresentationIndex (N + 3) (N + 3),
      (Ta.transformed.tail.IsCurrentEssential Tb.transformed.tail i ∨
        Ta.transformed.tail.IsNextEssential Tb.transformed.tail i) →
      i.val ≤ 3 →
      Ta.transformed.tail.representationAlpha Tb.transformed.tail i =
        Ta.transformed.representationAlpha Tb.transformed i.tailShift) :
    Lemma93Input p :=
  ofLemma92Transforms (p := p)
    (classificationTarget := classificationTarget)
    (classificationSource := classificationSource)
    N htarget hsource Ta Tb hhead hsecond (by
      intro i hessential hi
      by_cases hthree : i.val ≤ 3
      · exact hlow i hessential hthree
      · exact BONG.GoodBONG.representationAlpha_tail_eq_shift_of_lemma92Transforms_early
            (classificationV := classificationTarget)
            (classificationW := classificationSource)
            (p.lemma93TargetBONG (N + 2) (by omega))
            (p.lemma93SourceBONG (N + 2) (by omega))
            Ta Tb hcaseTarget hcaseSource hhead i (by omega))

end Beli2019RepresentationProblem.Lemma93Input

end Bong
