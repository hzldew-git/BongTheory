/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93TailOrder
import Bong.Bong.Beli2019Lemma93TailDefect
import Bong.Bong.Beli2019Lemma93TailAlpha
import Bong.Bong.Beli2019Lemma93TailRepresentation
import Bong.Bong.Beli2019Lemma93TailCentral
import Bong.Bong.Beli2019Lemma213Nonessential

/-!
# Beli (2019), Lemma 9.3: assembled tail conditions

This file combines the four independently verified descent arguments into
the exact `RepresentationConditions` certificate needed by the projected
rank-`n+1` problem.  Its remaining hypotheses are the local arithmetic
statements singled out in Beli's proof: equality of `A_i` at essential
endpoints.  Lemma 2.13 at nonessential endpoints, shifted alpha domination,
and the central-trigger comparison are proved internally.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The four conditions of Theorem 2.1 descend after deleting equal heads,
under exactly the local arithmetic inputs isolated in Lemma 9.3. -/
theorem representationConditions_tail
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (conditions : RepresentationConditions a b (Nat.le_refl (n + 1)))
    (hhead : a.value 0 = b.value 0)
    (hfirst : a.order ⟨1, by omega⟩ ≤ b.order ⟨1, by omega⟩)
    (hrepresentationAlpha :
      ∀ i : RepresentationIndex (n + 1) (n + 1),
        (a.tail.IsCurrentEssential b.tail i ∨
          a.tail.IsNextEssential b.tail i) →
        a.tail.representationAlpha b.tail i =
          a.representationAlpha b i.tailShift) :
    RepresentationConditions a.tail b.tail (Nat.le_refl n) where
  orderCondition :=
    a.representationOrderCondition_tail b conditions.orderCondition hfirst
  defectCondition :=
    a.representationDefectCondition_tail b conditions.defectCondition
      hhead a.alphaValue_shift_le_tail b.alphaValue_shift_le_tail
        hrepresentationAlpha
          (a.tail.representationDefectAt_of_not_essential
            (sourceLaws := sourceLaws) (targetLaws := targetLaws) b.tail)
  centralRepresentations :=
    a.centralRepresentationConditions_tail_of_trigger b
      conditions.centralRepresentations hhead
        (a.centralAlphaTrigger_tailShift_of_essentialAlpha
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          b hrepresentationAlpha)
  longRepresentations :=
    a.longRepresentationConditions_tail b conditions.longRepresentations hhead

end BONG.GoodBONG

end Bong
