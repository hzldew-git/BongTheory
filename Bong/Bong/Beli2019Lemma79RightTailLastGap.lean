/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderRightAlternating
import Bong.Bong.Beli2019Lemma79RightTailBoundaryData

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the last order gap

At the last coordinate where the source and intermediate order sequences
differ, the intermediate order is one or two above the source order.  The
no-gap-two types II and III force the first alternative.  This is the
structural split `S_u = R_u + 1` or `S_u = R_u + 2` used in case 8.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- In type I the final changed order differs by either one or two. -/
theorem beli2019Lemma79_typeI_caseEight_lastGap
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) :
    b.orderSequence.entryOrZero D.profile.last =
        a.orderSequence.entryOrZero D.profile.last + 1 ∨
      b.orderSequence.entryOrZero D.profile.last =
        a.orderSequence.entryOrZero D.profile.last + 2 := by
  have hupper := D.target_le_source_add_two
    D.profile.last D.profile.lastDifference.bound
  by_cases hanchor : D.anchor = D.profile.last
  · exact Or.inr (by
      rw [<- hanchor]
      exact D.anchor_gap)
  · have hanchorLast : D.anchor < D.profile.last :=
      lt_of_le_of_ne D.profile.anchor_le_last hanchor
    have hstrict := (D.profile.rightProfile hanchorLast).2.1
    by_cases htwo : b.orderSequence.entryOrZero D.profile.last =
        a.orderSequence.entryOrZero D.profile.last + 2
    · exact Or.inr htwo
    · exact Or.inl (by omega)

/-- The final changed order differs by exactly one in type II. -/
theorem beli2019Lemma79_typeII_caseEight_lastGap
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) :
    b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero D.outer.last + 1 := by
  have heven := D.outer.right_even_distance
  have htarget := D.outer.target_rightEven_eq_boundary
    D.outer.last D.outer.right_le_last le_rfl heven
  have hsource := D.outer.source_rightBoundary_eq_last D.no_gap_two
  have hboundary := D.outer.transition.rightBoundary
  omega

/-- The final changed order differs by exactly one in type III. -/
theorem beli2019Lemma79_typeIII_caseEight_lastGap
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) :
    b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero D.outer.last + 1 := by
  have heven := D.outer.right_even_distance
  have htarget := D.outer.target_rightEven_eq_boundary
    D.outer.last D.outer.right_le_last le_rfl heven
  have hsource := D.outer.source_rightBoundary_eq_last D.no_gap_two
  have hboundary := D.outer.transition.rightBoundary
  omega

end BONG.GoodBONG

end Bong
