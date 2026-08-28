/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIIICenterLocal
import Bong.Bong.Beli2019Lemma78Dual

/-!
# Beli (2019), Lemma 6.9(i): the local target type-III centre

Reverse duality exchanges the source and target type-III profiles.  The
general local source theorem can therefore be applied even when the original
pair has a proper common suffix: the reflected first unequal coordinate need
not be zero.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Lemma 6.9(i) at the target type-III boundary, without assuming that the
last unequal order is the final BONG entry. -/
theorem beli2019Lemma69_i_typeIII_target_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2)) :
    b.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≤ 1 := by
  rcases a.exists_reverseDual_typeIII_local b D horder hdefect htotal with
    ⟨aDual, bDual, Ddual, _, _, _, hbAlpha, _, hconditionDual, _,
      hdualLeft, _⟩
  let dualCenter : Fin (n + 1) :=
    ⟨Ddual.outer.transition.lastZero, by
      have hbound := Ddual.outer.transition.firstTwo_le_rank
      rw [Ddual.adjacent] at hbound
      omega⟩
  let center : Fin (n + 1) :=
    ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩
  have hdualAlpha : bDual.alphaValue dualCenter ≤ 1 := by
    simpa only [dualCenter] using
      bDual.beli2019Lemma69_i_typeIII_local
        (alphaV := alpha) (alphaW := alpha)
        aDual Ddual hconditionDual
  have hreverse : Fin.rev dualCenter = center := by
    apply Fin.ext
    simp only [dualCenter, center, Fin.rev]
    rw [hdualLeft, D.adjacent]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hmap := hbAlpha dualCenter
  rw [hreverse] at hmap
  rw [← hmap]
  simpa only [center] using hdualAlpha

end BONG.GoodBONG

end Bong
