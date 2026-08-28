/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOnePrefix
import Bong.Bong.Beli2019Lemma72TypeICanonical
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeII

/-!
# Beli (2019), Lemma 7.9(ii), case 8: type-I/type-II evidence

For types I and II, Lemma 7.2 supplies the initial prefix class
`u * T + 1`.  The strict gap-one tail extends this class to the current
boundary.  The common parity engine then constructs the concrete beta
evidence, with final beta base `S = T + 1`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The concrete gap-one evidence in type I. -/
theorem beli2019Lemma79_typeI_caseEight_gapOne_evidence
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 ≤ i.val)
    (hgapOne : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 1)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last (by
        have hi := i.lt_large
        omega)) (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i)) :
    CaseEightGapOneBetaEvidence b c i
      (b.order (Fin.mk D.profile.last (by
        have hi := i.lt_large
        omega)).castSucc) := by
  let first : Fin (n + 1) := ⟨D.profile.last, by
    have hi := i.lt_large
    omega⟩
  let last := caseEightLastAlphaIndex i
  let T := a.orderSequence.entryOrZero D.anchor + 1
  rcases a.lemma67TypeICanonicalData b D hfirst with ⟨C⟩
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    by_cases heq : D.anchor = D.profile.last
    · rw [← heq]
      exact ⟨0, by omega⟩
    · have hlt : D.anchor < D.profile.last :=
        lt_of_le_of_ne D.profile.anchor_le_last heq
      exact (D.profile.rightProfile hlt).1
  have hlastEven : Even D.profile.last := by
    rcases hanchorEven with ⟨d, hd⟩
    rcases hlastDistance with ⟨e, he⟩
    refine ⟨d + e, ?_⟩
    have hanchorLast := D.profile.anchor_le_last
    omega
  have htargetLast : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    calc
      b.orderSequence.entryOrZero D.profile.last =
          b.orderSequence.entryOrZero D.anchor :=
        C.target_from_anchor D.profile.last D.profile.anchor_le_last
          le_rfl hlastDistance
      _ = a.orderSequence.entryOrZero D.anchor + 2 := D.anchor_gap
  have hbase : b.order first.castSucc = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simp only [first, T, Fin.val_castSucc]
    omega
  have hprefixRaw := a.lemma72_typeI_target_after_of_canonical
    b D C hfirst (D.profile.last + 1) (by
      have hleft := C.left_le_anchor.trans D.profile.anchor_le_last
      omega) le_rfl
  have hprefixReference : Int.ModEq 2
      (((D.profile.last + 1 : Nat) : Int) *
        (a.orderSequence.entryOrZero D.anchor + 2))
      (((D.profile.last + 1 : Nat) : Int) * T + 1) := by
    rcases hlastEven with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    have hdInt : (D.profile.last : Int) =
        (d : Int) + (d : Int) := by exact_mod_cast hd
    push_cast
    dsimp only [T]
    rw [hdInt]
    ring
  have hprefixFirst : Int.ModEq 2
      (b.orderSequence.prefixSum (first.val + 1))
      (((first.val + 1 : Nat) : Int) * T + 1) := by
    simpa only [first] using hprefixRaw.trans hprefixReference
  have hfirstLast : first ≤ last := by
    change D.profile.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have hformulaData := beli2019Lemma79_typeI_caseEight_gapOne_formula
    a b D last (by
      change D.profile.last ≤ i.val - 1
      have hiPos := i.pos
      omega)
      (by simpa only [first, last] using H) hstrictLast hgapOne
  have hformula : ∀ j : Fin (n + 1), first ≤ j → j ≤ last →
      b.alphaValue j =
        ((b.order j.succ - b.order first.castSucc : Int) : Rat) := by
    intro j hjFirst hjLast
    simpa only [first, last] using
      hformulaData.2 j (by simpa only [first] using hjFirst)
        (by simpa only [last] using hjLast)
  have htargetCurrent := H.targetPrefix_modEq_of_gapOne
    T hbase hformula hprefixFirst i.val (by
      change D.profile.last + 1 ≤ i.val
      exact hafter) (by
      change i.val ≤ i.val - 1 + 2
      have hiPos := i.pos
      omega)
  have htargetNext := H.targetPrefix_modEq_of_gapOne
    T hbase hformula hprefixFirst (i.val + 1) (by
      change D.profile.last + 1 ≤ i.val + 1
      omega) (by
      change i.val + 1 ≤ i.val - 1 + 2
      have hiPos := i.pos
      omega)
  have hcomparisonCurrent : Int.ModEq 2
      (c.orderSequence.prefixSum i.val)
      ((i.val : Int) * T + 1) :=
    hprefix.symm.trans htargetCurrent
  have hsourceZero : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero D.anchor :=
    C.source_to_anchor 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : T ≤ c.orderSequence.entryOrZero 0 := by
    calc
      T = a.orderSequence.entryOrZero 0 + 1 := by
        dsimp only [T]
        rw [hsourceZero]
      _ = a.order 0 + 1 := by
        rw [a.orderSequence_entryOrZero_eq_order
          (⟨0, by omega⟩ : Fin (n + 2))]
        simp only [Fin.zero_eta]
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence_entryOrZero_eq_order
          (⟨0, by omega⟩ : Fin (n + 2))]
        simp only [Fin.zero_eta]
  have E := caseEight_gapOne_evidence_of_prefix_parity
    b c i T htargetNext hcomparisonCurrent hfirstLower
  rw [hbase]
  exact E

/-- The concrete gap-one evidence in type II. -/
theorem beli2019Lemma79_typeII_caseEight_gapOne_evidence
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
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
  let right := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hrightEven := D.outer.right_even_distance
  have htargetBoundary := D.outer.target_rightEven_eq_boundary
    D.outer.last D.outer.right_le_last le_rfl hrightEven
  have hbase : b.order first.castSucc = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simp only [first, Fin.val_castSucc]
    rw [htargetBoundary, D.right_target]
  let P := a.beli2019Lemma72_ii b D hfirst
  have hprefixRaw := P.target_after (D.outer.last + 1)
    (by have hright := D.outer.right_le_last; omega) le_rfl
  have hprefixReference : Int.ModEq 2
      (((D.outer.last + 1 : Nat) : Int) * (T + 1) +
        ((right : Nat) : Int))
      (((D.outer.last + 1 : Nat) : Int) * T + 1) := by
    rcases hrightEven with ⟨d, hd⟩
    have hlastNat : D.outer.last = right + d + d := by
      simp only [right] at hd ⊢
      have hright := D.outer.right_le_last
      omega
    have hlastInt : (D.outer.last : Int) =
        (right : Int) + (d : Int) + (d : Int) := by
      exact_mod_cast hlastNat
    rw [Int.modEq_iff_dvd]
    refine ⟨-((right : Int) + (d : Int)), ?_⟩
    push_cast
    rw [hlastInt]
    ring
  have hprefixFirst : Int.ModEq 2
      (b.orderSequence.prefixSum (first.val + 1))
      (((first.val + 1 : Nat) : Int) * T + 1) := by
    simpa only [P, first, T, right] using
      hprefixRaw.trans hprefixReference
  have hfirstLast : first ≤ last := by
    change D.outer.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have hformulaData := beli2019Lemma79_typeII_caseEight_gapOne_formula
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
    beli2019Lemma79_typeII_caseSix_reference_le_thirdFirst
      a b c D hfirst hnorm
  have E := caseEight_gapOne_evidence_of_prefix_parity
    b c i T htargetNext hcomparisonCurrent
      (by simpa only [T] using hfirstLower)
  rw [hbase]
  exact E

end BONG.GoodBONG

end Bong
