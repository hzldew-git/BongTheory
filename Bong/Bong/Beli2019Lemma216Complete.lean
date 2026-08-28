/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma216Terminal

/-!
# Beli (2019), Lemma 2.16

The ordinary and exceptional terminal cases combine to prove the pointwise
equivalence between condition (iii) and the revised v2 condition (iii').
-/

namespace Bong

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Beli (2019), Lemma 2.16, including Definition 4's exceptional terminal
value.  Conditions 2.1(i) and (ii) discharge every hypothesis of the
pointwise equivalence. -/
theorem beli2019Lemma216
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b) :
    a.CentralTriggerEquivalence b := by
  intro i
  by_cases hi : i.val ≤ n + 1
  · exact a.centralAlphaTrigger_iff_defectTrigger_of_ordinary
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b hRank horder hdefect i hi
  · have hterminal : i.val = n + 2 := by
      have := i.le_small_succ
      omega
    exact a.centralAlphaTrigger_iff_defectTrigger_of_terminal
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b hdefect i hterminal

end BONG.GoodBONG

end Bong
