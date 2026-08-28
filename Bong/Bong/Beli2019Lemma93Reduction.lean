/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93TailConditions
import Bong.Bong.Beli2019RepresentationProblem

/-!
# Beli (2019), Lemma 9.3 as a concrete rank reduction

An equal-head pair of same-rank good BONGs, together with the assembled tail
conditions, determines the literal `HeadReduction` consumed by the final
well-founded induction.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Equal first BONG values and verified tail conditions give the exact
projected lower-rank problem used in Lemma 9.3. -/
noncomputable def headReduction_of_equalBONGHeads
    (a : BONG.GoodBONG q L (n + 2))
    (b : BONG.GoodBONG r M (n + 2))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (n + 1)))
    (hhead : a.value 0 = b.value 0)
    (tailConditions :
      RepresentationConditions a.tail b.tail (Nat.le_refl n)) :
    HeadReduction (ofData a b (Nat.le_refl (n + 1)) ambient conditions) where
  targetHead := a.toBONG.head
  sourceHead := b.toBONG.head
  targetHeadGenerator := a.toBONG.head_isNormGenerator
  sourceHeadGenerator := b.toBONG.head_isNormGenerator
  targetHeadAnisotropic := a.toBONG.head_isAnisotropic
  sourceHeadAnisotropic := b.toBONG.head_isAnisotropic
  headValue_eq := by
    change q.quadratic a.toBONG.head = r.quadratic b.toBONG.head
    rw [← a.toBONG.value_zero_eq_quadratic_head,
      ← b.toBONG.value_zero_eq_quadratic_head]
    exact hhead
  tailIndex := n
  targetIndex_eq := rfl
  sourceIndex_eq := rfl
  targetTail := a.tail
  sourceTail := b.tail
  tailConditions := tailConditions

/-- Paper-facing Lemma 9.3 constructor.  All four projected conditions are
assembled from the explicit local arithmetic inputs before the rank-reduction
object is created. -/
noncomputable def lemma93HeadReduction
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (b : BONG.GoodBONG r M (n + 2))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (n + 1)))
    (hhead : a.value 0 = b.value 0)
    (hfirst : a.order ⟨1, by omega⟩ ≤ b.order ⟨1, by omega⟩)
    (hrepresentationAlpha :
      ∀ i : RepresentationIndex (n + 1) (n + 1),
        (a.tail.IsCurrentEssential b.tail i ∨
          a.tail.IsNextEssential b.tail i) →
        a.tail.representationAlpha b.tail i =
          a.representationAlpha b i.tailShift) :
    HeadReduction (ofData a b (Nat.le_refl (n + 1)) ambient conditions) :=
  headReduction_of_equalBONGHeads a b ambient conditions hhead
    (a.representationConditions_tail
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      b conditions hhead hfirst
      hrepresentationAlpha)

end Beli2019RepresentationProblem

end Bong
