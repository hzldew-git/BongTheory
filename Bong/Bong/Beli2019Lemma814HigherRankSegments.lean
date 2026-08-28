/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRank

/-!
# Beli (2019), Lemma 8.14: suffix and rank-five segments

This file develops the two consecutive segments used to eliminate the last
quaternary exceptional case in rank at least five.  Its main localization
identity groups the candidates for `alpha_i` into the preceding-alpha term
and the alpha of the suffix beginning with the literal pair at `i`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- Corollary 2.5 with all candidates on and to the right of `i` grouped
as the alpha of the suffix pair segment. -/
theorem alpha_eq_min_predecessorNeighbor_suffixPairAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (i : Fin (N + 1)) (hi : 0 < i.1)
    (w : BONG.SegmentWitness a.toBONG
      (suffixPairLocalization i).start
      (suffixPairLocalization i).length
      (suffixPairLocalization i).bound) :
    (a.alphaValue i : WithTop ℚ) =
      min (a.neighborAlphaCandidate i ⟨i.1 - 1, by omega⟩)
        ((w.toGoodBONG a.good).alphaValue
          (suffixPairLocalization i).localPivot : WithTop ℚ) := by
  classical
  let s := suffixPairLocalization i
  let p : Fin (N + 1) := ⟨i.1 - 1, by omega⟩
  let tail := w.toGoodBONG a.good
  have hp : p.1 + 1 = i.1 := by
    dsimp [p]
    omega
  have hspivot : s.pivotFin = i := by
    apply Fin.ext
    rfl
  have hglobalTail := a.beli2009Lemma21_le_segmentAlpha s w
  rw [hspivot] at hglobalTail
  rw [a.coe_alphaValue, tail.coe_alphaValue]
  apply le_antisymm
  · apply le_min
    · exact a.alpha_le_neighborAlphaCandidate i p (Or.inl hp)
    · exact hglobalTail
  · unfold alpha
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · have hlocal := tail.alpha_le_halfGapCandidate s.localPivot
      rw [a.segment_halfGapCandidate_local s w, hspivot] at hlocal
      exact (min_le_right _ _).trans hlocal
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji : j ≤ i := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      by_cases hjiEq : j = i
      · subst j
        have hstart : s.start ≤ i.1 := by
          dsimp [s, suffixPairLocalization]
          exact le_rfl
        have hstop : i.1 < s.stop := by
          dsimp [s, suffixPairLocalization]
          exact i.isLt
        have hlocalIndex : s.localAdjacent i hstart hstop ≤
            s.localPivot := by
          apply le_of_eq
          apply Fin.ext
          dsimp [s, suffixPairLocalization,
            AlphaLocalizationIndex.localAdjacent,
            AlphaLocalizationIndex.localPivot]
        have hlocal := tail.alpha_le_leftDefectCandidate hlocalIndex
        rw [a.segment_leftDefectCandidate_local s w i hstart hstop
          le_rfl, hspivot] at hlocal
        exact (min_le_right _ _).trans hlocal
      · have hjp : j ≤ p := by
          change j.1 ≤ p.1
          dsimp [p]
          change j.1 ≤ i.1 at hji
          omega
        exact (min_le_left _ _).trans
          (a.predecessorNeighbor_le_leftDefectCandidate i p j hp hjp)
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij : i ≤ j := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hstart : s.start ≤ j.1 := by
        change i.1 ≤ j.1
        exact hij
      have hstop : j.1 < s.stop := by
        dsimp [s, suffixPairLocalization]
        exact j.isLt
      have hpivotj : s.pivotFin ≤ j := by
        simpa only [hspivot] using hij
      have hlocalIndex : s.localPivot ≤
          s.localAdjacent j hstart hstop := by
        change s.pivot - s.start ≤ j.1 - s.start
        change i.1 ≤ j.1 at hij
        dsimp [s, suffixPairLocalization]
        omega
      have hlocal := tail.alpha_le_rightDefectCandidate hlocalIndex
      rw [a.segment_rightDefectCandidate_local s w j hstart hstop
        hpivotj, hspivot] at hlocal
      exact (min_le_right _ _).trans hlocal

/-- If a global alpha attains its half gap, then every consecutive segment
containing its literal adjacent pair has exactly the same local alpha. -/
theorem segmentAlpha_eq_global_of_attainsHalfGap
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (s : AlphaLocalizationIndex (N + 1))
    (w : BONG.SegmentWitness a.toBONG s.start s.length s.bound)
    (hhalf : a.AttainsHalfGap s.pivotFin) :
    (w.toGoodBONG a.good).alphaValue s.localPivot =
      a.alphaValue s.pivotFin := by
  let c := w.toGoodBONG a.good
  have hglobalLeLocal := a.beli2009Lemma21_le_segmentAlpha s w
  have hlocalLeHalf := c.alpha_le_halfGapCandidate s.localPivot
  rw [a.segment_halfGapCandidate_local s w,
    ← a.coe_halfGapValue] at hlocalLeHalf
  rw [← c.coe_alphaValue] at hlocalLeHalf
  rw [← a.coe_alphaValue, ← c.coe_alphaValue] at hglobalLeLocal
  have hlocalLeGlobal : (c.alphaValue s.localPivot : WithTop ℚ) ≤
      (a.alphaValue s.pivotFin : WithTop ℚ) := by
    rw [hhalf]
    exact hlocalLeHalf
  exact_mod_cast le_antisymm hlocalLeGlobal hglobalLeLocal

/-- The suffix `[a₄, ..., aₙ]` in the rank-at-least-five argument. -/
noncomputable def lemma814TailSegment (a : GoodBONG q L (N + 5)) :
    BONG.SegmentWitness a.toBONG 3 (N + 2) (by omega) :=
  a.toBONG.segmentWitness 3 (N + 2) (by omega)

/-- The same suffix regarded as a good BONG of rank `N + 2`, ready for an
application of Lemma 8.8. -/
noncomputable def lemma814Tail (a : GoodBONG q L (N + 5)) :
    GoodBONG
      (q.restrict a.lemma814TailSegment.carrier
        a.lemma814TailSegment.nondegenerate)
      a.lemma814TailSegment.lattice (N + 2) :=
  a.lemma814TailSegment.toGoodBONG a.good

/-- Scalar values of the suffix are the ambient values shifted by three. -/
theorem lemma814Tail_valueUnit_eq
    (a : GoodBONG q L (N + 5)) (i : Fin (N + 2)) :
    a.lemma814Tail.valueUnit i =
      a.valueUnit ⟨3 + i.1, by omega⟩ := by
  let w := a.lemma814TailSegment
  change w.bong.valueUnit i = a.toBONG.valueUnit ⟨3 + i.1, by omega⟩
  calc
    w.bong.valueUnit i = a.toBONG.valueUnit (w.sourceIndex i) :=
      w.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨3 + i.1, by omega⟩ := by
      congr 1

/-- Orders of the suffix are the ambient orders shifted by three. -/
theorem lemma814Tail_order_eq
    (a : GoodBONG q L (N + 5)) (i : Fin (N + 2)) :
    a.lemma814Tail.order i = a.order ⟨3 + i.1, by omega⟩ := by
  let w := a.lemma814TailSegment
  change w.bong.order i = a.toBONG.order ⟨3 + i.1, by omega⟩
  calc
    w.bong.order i = a.toBONG.order (w.sourceIndex i) := w.order_eq i
    _ = a.toBONG.order ⟨3 + i.1, by omega⟩ := by
      congr 1

/-- The first half-gap of `[a₄, ..., aₙ]` is the fourth ambient half-gap. -/
theorem lemma814Tail_halfGapValue_zero_eq
    (a : GoodBONG q L (N + 5)) :
    a.lemma814Tail.halfGapValue (0 : Fin (N + 1)) =
      a.halfGapValue (⟨3, by omega⟩ : Fin (N + 4)) := by
  unfold halfGapValue orderGap
  rw [a.lemma814Tail_order_eq (0 : Fin (N + 1)).castSucc,
    a.lemma814Tail_order_eq (0 : Fin (N + 1)).succ]
  congr 3

/-- At the fourth alpha, Corollary 2.5 groups the whole right-hand candidate
family into the alpha of `[a₄, ..., aₙ]`. -/
theorem lemma814FourthAlpha_eq_min_predecessor_tailAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) :
    (a.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) : WithTop ℚ) =
      min (a.neighborAlphaCandidate
          (⟨3, by omega⟩ : Fin (N + 4))
          (⟨2, by omega⟩ : Fin (N + 4)))
        ((a.lemma814Tail.alphaValue (0 : Fin (N + 1))) : WithTop ℚ) := by
  have h := a.alpha_eq_min_predecessorNeighbor_suffixPairAlpha
    (⟨3, by omega⟩ : Fin (N + 4)) (by norm_num)
    a.lemma814TailSegment
  simp only [lemma814TailSegment,
    suffixPairLocalization, AlphaLocalizationIndex.localPivot,
    Nat.reduceSub] at h
  convert h using 1
  congr 2

/-- In the branch `R₃ < R₅`, the predecessor term in the preceding minimum
is strictly larger than `α₄`. -/
theorem lemma814FourthAlpha_lt_predecessorNeighbor_of_third_lt_fifth
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) <
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    (a.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) : WithTop ℚ) <
      a.neighborAlphaCandidate
        (⟨3, by omega⟩ : Fin (N + 4))
        (⟨2, by omega⟩ : Fin (N + 4)) := by
  have hthird : a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
      a.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) := by
    simpa using D.third_eq_halfGap
  have hsum : a.alphaValue (1 : Fin (N + 4)) +
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
        2 * (ramificationIndex K : ℚ) := by
    simpa using D.second_third_sum
  have hordersQ : (a.order (⟨2, by omega⟩ : Fin (N + 5)) : ℚ) <
      a.order (⟨4, by omega⟩ : Fin (N + 5)) := by
    exact_mod_cast hthirdFifth
  have hrat : a.alphaValue (1 : Fin (N + 4)) <
      a.alphaGapValue (⟨3, by omega⟩ : Fin (N + 4)) +
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) := by
    unfold halfGapValue orderGap at hthird
    change a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
      ((a.order (⟨3, by omega⟩ : Fin (N + 5)) -
        a.order (⟨2, by omega⟩ : Fin (N + 5)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) at hthird
    unfold alphaGapValue
    change a.alphaValue (1 : Fin (N + 4)) <
      ((a.order (⟨4, by omega⟩ : Fin (N + 5)) -
        a.order (⟨3, by omega⟩ : Fin (N + 5)) : Int) : ℚ) +
          a.alphaValue (⟨2, by omega⟩ : Fin (N + 4))
    push_cast at hthird ⊢
    linarith
  rw [D.fourth_eq_second]
  unfold neighborAlphaCandidate
  exact_mod_cast hrat

/-- The strict predecessor inequality forces the suffix alpha itself to be
the ambient fourth alpha. -/
theorem lemma814Tail_alpha_zero_eq_fourthAlpha_of_third_lt_fifth
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) <
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    a.lemma814Tail.alphaValue (0 : Fin (N + 1)) =
      a.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) := by
  let previous := a.neighborAlphaCandidate
    (⟨3, by omega⟩ : Fin (N + 4))
    (⟨2, by omega⟩ : Fin (N + 4))
  let tailAlpha : WithTop ℚ :=
    a.lemma814Tail.alphaValue (0 : Fin (N + 1))
  have hformula := a.lemma814FourthAlpha_eq_min_predecessor_tailAlpha
  have hstrict :=
    a.lemma814FourthAlpha_lt_predecessorNeighbor_of_third_lt_fifth
      D hthirdFifth
  have htailLe : tailAlpha ≤ previous := by
    by_contra hnot
    have hpreviousLt : previous < tailAlpha := lt_of_not_ge hnot
    rw [min_eq_left hpreviousLt.le] at hformula
    exact (ne_of_lt hstrict) hformula
  rw [min_eq_right htailLe] at hformula
  dsimp only [tailAlpha] at hformula
  exact_mod_cast hformula.symm

/-- The same order inequality puts the suffix alpha strictly below its own
half gap, exactly the hypothesis used to invoke Lemma 8.8. -/
theorem lemma814Tail_alpha_zero_lt_halfGap_of_third_lt_fifth
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) <
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    a.lemma814Tail.alphaValue (0 : Fin (N + 1)) <
      a.lemma814Tail.halfGapValue (0 : Fin (N + 1)) := by
  have hthird : a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
      a.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) := by
    simpa using D.third_eq_halfGap
  have hsum : a.alphaValue (1 : Fin (N + 4)) +
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
        2 * (ramificationIndex K : ℚ) := by
    simpa using D.second_third_sum
  have hordersQ : (a.order (⟨2, by omega⟩ : Fin (N + 5)) : ℚ) <
      a.order (⟨4, by omega⟩ : Fin (N + 5)) := by
    exact_mod_cast hthirdFifth
  have hambient : a.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) <
      a.halfGapValue (⟨3, by omega⟩ : Fin (N + 4)) := by
    rw [D.fourth_eq_second]
    unfold halfGapValue orderGap at hthird ⊢
    change a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
      ((a.order (⟨3, by omega⟩ : Fin (N + 5)) -
        a.order (⟨2, by omega⟩ : Fin (N + 5)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) at hthird
    change a.alphaValue (1 : Fin (N + 4)) <
      ((a.order (⟨4, by omega⟩ : Fin (N + 5)) -
        a.order (⟨3, by omega⟩ : Fin (N + 5)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)
    push_cast at hthird ⊢
    linarith
  rw [a.lemma814Tail_alpha_zero_eq_fourthAlpha_of_third_lt_fifth
      D hthirdFifth,
    a.lemma814Tail_halfGapValue_zero_eq]
  exact hambient

/-- Lemma 8.8 applies to the suffix in the strict-order branch.  Its
exceptional predicate starts with half-gap attainment, so the preceding
strict inequality excludes all three exceptional alternatives at once. -/
theorem exists_lemma814TailFirstValueTransform_of_third_lt_fifth
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) <
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    Nonempty a.lemma814Tail.Beli2019FirstValueTransform := by
  apply a.lemma814Tail.beli2019Lemma88_sufficiency
  rintro ⟨hattains, _⟩
  exact (ne_of_lt
    (a.lemma814Tail_alpha_zero_lt_halfGap_of_third_lt_fifth
      D hthirdFifth)) hattains

end BONG.GoodBONG

end Bong
