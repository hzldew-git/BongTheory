/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93Normalization
import Bong.Bong.Beli2019Lemma93Essential
import Bong.Bong.Beli2019Lemma93Problem

/-!
# Beli (2019), Lemma 9.3: ordinary branch interface

After Lemmas 9.1 and 9.2 have selected the two normalized BONGs, the only
nonautomatic part of the ordinary branch is the reverse inequality
`A_i^* ≤ A_i` at the finitely many low important boundaries.  The opposite
inequality was proved uniformly, so this weaker and paper-faithful certificate
is enough to construct the concrete recursive input used by the final
well-founded descent.
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
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The exact remaining arithmetic obligation in the ordinary branch of
Lemma 9.3.  It is deliberately an inequality, not equality of all defining
candidates: Beli's proof often obtains `A_i=A_i^*` while individual capped
defects remain unequal. -/
structure Beli2019Lemma93LowReverseCertificate
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (D : Beli2019Lemma93NormalizedPair a b) : Prop where
  reverseAtImportant
    (i : RepresentationIndex (N + 3) (N + 3))
    (himportant :
      D.targetTransform.transformed.tail.IsCurrentEssential
          D.sourceTransform.transformed.tail i ∨
        D.targetTransform.transformed.tail.IsNextEssential
          D.sourceTransform.transformed.tail i)
    (hlow : i.val ≤ 4) :
    D.targetTransform.transformed.tail.representationAlpha
        D.sourceTransform.transformed.tail i ≤
      D.targetTransform.transformed.representationAlpha
        D.sourceTransform.transformed i.tailShift

/-- In the early/early Lemma 9.2 branch the boundary of value four is
automatic, so only the first three low reverse inequalities remain. -/
structure Beli2019Lemma93LowThreeReverseCertificate
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (D : Beli2019Lemma93NormalizedPair a b) : Prop where
  reverseAtImportant
    (i : RepresentationIndex (N + 3) (N + 3))
    (himportant :
      D.targetTransform.transformed.tail.IsCurrentEssential
          D.sourceTransform.transformed.tail i ∨
        D.targetTransform.transformed.tail.IsNextEssential
          D.sourceTransform.transformed.tail i)
    (hlow : i.val ≤ 3) :
    D.targetTransform.transformed.tail.representationAlpha
        D.sourceTransform.transformed.tail i ≤
      D.targetTransform.transformed.representationAlpha
        D.sourceTransform.transformed i.tailShift

/-- Promote the three-boundary certificate in the early/early branch to the
uniform low certificate used below. -/
theorem Beli2019Lemma93LowReverseCertificate.ofEarly
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93NormalizedPair a b)
    (hcaseTarget : D.targetBeforeLemma92.Lemma92EarlyAlternative)
    (hcaseSource : D.sourceBeforeLemma92.Lemma92EarlyAlternative)
    (C : Beli2019Lemma93LowThreeReverseCertificate a b D) :
    Beli2019Lemma93LowReverseCertificate a b D where
  reverseAtImportant i himportant hlow := by
    by_cases hthree : i.val ≤ 3
    · exact C.reverseAtImportant i himportant hthree
    · exact (representationAlpha_tail_eq_shift_of_lemma92Transforms_early
        (classificationV := classificationV)
        (classificationW := classificationW)
        D.targetBeforeLemma92 D.sourceBeforeLemma92
          D.targetTransform D.sourceTransform
          hcaseTarget hcaseSource D.headValue_eq i (by omega)).le

/-- A low reverse certificate, monotonicity under head deletion, and Lemma
9.2's high-index normalization give all important equalities required by the
tail argument. -/
theorem Beli2019Lemma93NormalizedPair.essentialAlpha_eq_of_lowReverse
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93NormalizedPair a b)
    (C : Beli2019Lemma93LowReverseCertificate a b D) :
    ∀ i : RepresentationIndex (N + 3) (N + 3),
      (D.targetTransform.transformed.tail.IsCurrentEssential
          D.sourceTransform.transformed.tail i ∨
        D.targetTransform.transformed.tail.IsNextEssential
          D.sourceTransform.transformed.tail i) →
      D.targetTransform.transformed.tail.representationAlpha
          D.sourceTransform.transformed.tail i =
        D.targetTransform.transformed.representationAlpha
          D.sourceTransform.transformed i.tailShift := by
  intro i himportant
  by_cases hlow : i.val ≤ 4
  · exact
      D.targetTransform.transformed.representationAlpha_tail_eq_shift_of_tail_le_shift
        D.sourceTransform.transformed D.headValue_eq i
          (C.reverseAtImportant i himportant hlow)
  · exact representationAlpha_tail_eq_shift_of_lemma92Transforms
      (classificationV := classificationV) (classificationW := classificationW)
      D.targetBeforeLemma92 D.sourceBeforeLemma92
        D.targetTransform D.sourceTransform
        D.headValue_eq i (by omega)

/-- The normalized pair and its low reverse certificate construct the exact
ordinary-branch input expected by the Section 9 descent.  The selected BONGs
may differ from the BONGs stored in the root problem, but they lie on the same
two lattices and carry the transported four conditions. -/
noncomputable def Beli2019Lemma93NormalizedPair.toLemma93Input
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (D : Beli2019Lemma93NormalizedPair a b)
    (C : Beli2019Lemma93LowReverseCertificate a b D) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 3))
        ambient conditions) := by
  let p := Beli2019RepresentationProblem.ofData a b
    (Nat.le_refl (N + 3)) ambient conditions
  refine
    { tailIndex := N + 2
      targetIndex_eq := by rfl
      sourceIndex_eq := by rfl
      targetBONG := D.targetTransform.transformed
      sourceBONG := D.sourceTransform.transformed
      selectedConditions := D.selectedConditions
      headValue_eq := D.headValue_eq
      secondOrder_le := D.secondOrder_le
      essentialAlpha_eq :=
        D.essentialAlpha_eq_of_lowReverse
          (classificationV := classificationV)
          (classificationW := classificationW) C }

end BONG.GoodBONG

end Bong
