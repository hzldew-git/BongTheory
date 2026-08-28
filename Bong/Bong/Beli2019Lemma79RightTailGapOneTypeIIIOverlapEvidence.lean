/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIIOverlap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: overlap evidence

The adjacent type-III profile with central source gap one has the type-II
prefix class.  Extending that class along the strict gap-one tail lets the
common parity engine construct the concrete beta evidence.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Concrete gap-one evidence for the overlapping type-II/III branch. -/
theorem beli2019Lemma79_typeIII_overlap_caseEight_gapOne_evidence
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last (by
        have hi := i.lt_large
        omega)) (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i)) :
    CaseEightGapOneBetaEvidence b c i
      (b.order (Fin.mk D.outer.last (by
        have hi := i.lt_large
        omega)).castSucc) := by
  let first : Fin (n + 1) := ⟨D.outer.last, by
    have hi := i.lt_large
    omega⟩
  let last := caseEightLastAlphaIndex i
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hlastTarget :=
    beli2019Lemma79_typeIII_overlap_lastTarget_eq_left_add_one
      a b D hoverlap
  have hbase : b.order first.castSucc = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simpa only [first, T, Fin.val_castSucc] using hlastTarget
  have hprefixFirst : Int.ModEq 2
      (b.orderSequence.prefixSum (first.val + 1))
      (((first.val + 1 : Nat) : Int) * T + 1) := by
    simpa only [first, T] using
      beli2019Lemma72_typeIII_overlap_target_last_succ
        a b D hfirst hoverlap
  have hfirstLast : first ≤ last := by
    change D.outer.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have hformulaData := beli2019Lemma79_typeIII_caseEight_gapOne_formula
    a b D last (by
      change D.outer.last ≤ i.val - 1
      have hiPos := i.pos
      omega)
      (by simpa only [first, last] using H) hstrictLast
  have hformula : ∀ j : Fin (n + 1), first ≤ j → j ≤ last →
      b.alphaValue j =
        ((b.order j.succ - b.order first.castSucc : Int) : Rat) := by
    intro j hjFirst hjLast
    simpa only [first, last] using
      hformulaData.2 j (by simpa only [first] using hjFirst)
        (by simpa only [last] using hjLast)
  have htargetCurrent := H.targetPrefix_modEq_of_gapOne
    T hbase hformula hprefixFirst i.val (by
      change D.outer.last + 1 ≤ i.val
      exact hafter) (by
      change i.val ≤ i.val - 1 + 2
      have hiPos := i.pos
      omega)
  have htargetNext := H.targetPrefix_modEq_of_gapOne
    T hbase hformula hprefixFirst (i.val + 1) (by
      change D.outer.last + 1 ≤ i.val + 1
      omega) (by
      change i.val + 1 ≤ i.val - 1 + 2
      have hiPos := i.pos
      omega)
  have hcomparisonCurrent : Int.ModEq 2
      (c.orderSequence.prefixSum i.val)
      ((i.val : Int) * T + 1) :=
    hprefix.symm.trans htargetCurrent
  have hfirstLower :=
    beli2019Lemma79_typeIII_overlap_reference_le_thirdFirst
      a b c D hfirst hnorm
  have E := caseEight_gapOne_evidence_of_prefix_parity
    b c i T htargetNext hcomparisonCurrent
      (by simpa only [T] using hfirstLower)
  rw [hbase]
  exact E

end BONG.GoodBONG

end Bong
