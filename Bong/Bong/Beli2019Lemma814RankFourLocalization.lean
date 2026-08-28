/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814RankReduction
import Bong.Bong.Beli2019Corollary811

/-!
# Beli (2019), Lemma 8.14: rank-four alpha localization

This file formalizes the local-alpha identities used in the equality branch
of the quaternary proof.  Under α₂ + α₃ = 2e, the final binary
segment realizes the global third alpha, while the first ternary segment
retains the first two global alphas.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The final literal binary alpha realizes the global final alpha whenever
the latter attains its half-gap. -/
theorem lastBinaryAlpha_eq_alpha_of_halfGap {N : Nat}
    (b : GoodBONG q L (N + 2))
    (hhalf : b.AttainsHalfGap (Fin.last N)) :
    b.lastBinaryAlpha =
      (b.alphaValue (Fin.last N) : WithTop ℚ) := by
  apply le_antisymm
  · unfold lastBinaryAlpha adjacentBinaryAlpha
    calc
      min (b.halfGapCandidate (Fin.last N))
          (b.leftDefectCandidate (Fin.last N) (Fin.last N)) ≤
          b.halfGapCandidate (Fin.last N) := min_le_left _ _
      _ = (b.alphaValue (Fin.last N) : WithTop ℚ) := by
        rw [← b.coe_halfGapValue]
        exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf.symm
  · unfold lastBinaryAlpha adjacentBinaryAlpha
    apply le_min
    · rw [← b.coe_halfGapValue]
      exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf |>.le
    · rw [b.coe_alphaValue]
      exact b.alpha_le_leftDefectCandidate le_rfl

/-- In rank four, the final global alpha is the minimum of the literal
last-binary alpha and the unique predecessor-neighbor term. -/
theorem rankFour_thirdAlpha_eq_min_lastBinary_predecessor
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) :
    (a.alphaValue (2 : Fin 3) : WithTop ℚ) =
      min a.lastBinaryAlpha
        (a.neighborAlphaCandidate (2 : Fin 3) (1 : Fin 3)) := by
  rw [a.coe_alphaValue]
  rw [a.beli2009Corollary25_i (n := 2) (2 : Fin 3)]
  unfold recursiveAlphaCandidates neighborAlphaCandidates lastBinaryAlpha
    adjacentBinaryAlpha
  have hfilter :
      (Finset.univ.filter fun j : Fin 3 =>
        j.1 = 1 ∨ 3 = j.1) =
        {(1 : Fin 3)} := by
    decide
  simp [hfilter, min_assoc]

/-- If the final global alpha is strictly below its predecessor-neighbor
term, it is already realized by the literal final binary segment. -/
theorem rankFour_lastBinaryAlpha_eq_of_lt_neighbor
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (hlt : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
      a.neighborAlphaCandidate (2 : Fin 3) (1 : Fin 3)) :
    a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
  have hformula := rankFour_thirdAlpha_eq_min_lastBinary_predecessor a
  have hminLt :
      min a.lastBinaryAlpha
          (a.neighborAlphaCandidate (2 : Fin 3) (1 : Fin 3)) <
        a.neighborAlphaCandidate (2 : Fin 3) (1 : Fin 3) := by
    rw [← hformula]
    exact hlt
  have hbinaryLt : a.lastBinaryAlpha <
      a.neighborAlphaCandidate (2 : Fin 3) (1 : Fin 3) :=
    (min_lt_iff.mp hminLt).resolve_right (lt_irrefl _)
  rw [min_eq_left hbinaryLt.le] at hformula
  exact hformula.symm

/-- Under the equality boundary α₂ + α₃ = 2e, the literal final
binary alpha equals the global third alpha. -/
theorem rankFour_boundary_lastBinaryAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
  by_cases hhalf : a.AttainsHalfGap (2 : Fin 3)
  · have hlast : Fin.last 2 = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    simpa only [hlast] using
      lastBinaryAlpha_eq_alpha_of_halfGap a hhalf
  · have hstrict : a.alphaValue (2 : Fin 3) <
        a.halfGapValue (2 : Fin 3) :=
      lt_of_le_of_ne (a.alphaValue_le_halfGapValue (2 : Fin 3)) hhalf
    have hneighborQ : a.alphaValue (2 : Fin 3) <
        a.alphaGapValue (2 : Fin 3) + a.alphaValue (1 : Fin 3) := by
      unfold halfGapValue orderGap at hstrict
      unfold alphaGapValue
      push_cast at hstrict ⊢
      linarith
    apply rankFour_lastBinaryAlpha_eq_of_lt_neighbor a
    unfold neighborAlphaCandidate
    exact_mod_cast hneighborQ

/-- Segment form of the preceding identity for the final coefficient pair. -/
theorem rankFour_boundary_lastPairAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG
      (suffixPairLocalization (N := 2) (2 : Fin 3)).start
      (suffixPairLocalization (N := 2) (2 : Fin 3)).length
      (suffixPairLocalization (N := 2) (2 : Fin 3)).bound)
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    (segment.toGoodBONG a.good).alphaValue
        (suffixPairLocalization (N := 2) (2 : Fin 3)).localPivot =
      a.alphaValue (2 : Fin 3) := by
  have hsegment :=
    a.adjacentBinaryAlpha_eq_segmentAlpha (2 : Fin 3) segment
  have hlast := rankFour_boundary_lastBinaryAlpha_eq a hsum
  have hlastIndex : Fin.last 2 = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  rw [lastBinaryAlpha, hlastIndex] at hlast
  have htop :
      ((segment.toGoodBONG a.good).alphaValue
          (suffixPairLocalization (N := 2) (2 : Fin 3)).localPivot :
            WithTop ℚ) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
    hsegment.symm.trans hlast
  exact_mod_cast htop

/-- In rank four, the second global alpha is the minimum of the second
alpha of the first ternary segment and the successor-neighbor term. -/
theorem rankFour_secondAlpha_eq_min_prefix_neighbor
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound) :
    (a.alphaValue (1 : Fin 3) : WithTop ℚ) =
      min
        ((segment.toGoodBONG a.good).alphaValue
          (prefixPairLocalization (N := 2) (1 : Fin 3)).localPivot :
            WithTop ℚ)
        (a.neighborAlphaCandidate (1 : Fin 3) (2 : Fin 3)) := by
  let p := prefixPairLocalization (N := 2) (1 : Fin 3)
  have hpivot : p.pivotFin = (1 : Fin 3) := by
    apply Fin.ext
    rfl
  have hglobalPrefix :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        ((segment.toGoodBONG a.good).alphaValue p.localPivot :
          WithTop ℚ) := by
    rw [a.coe_alphaValue, (segment.toGoodBONG a.good).coe_alphaValue]
    simpa only [hpivot] using
      a.beli2009Lemma21_le_segmentAlpha p segment
  have hglobalNeighbor :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        a.neighborAlphaCandidate (1 : Fin 3) (2 : Fin 3) := by
    rw [a.coe_alphaValue]
    exact a.alpha_le_neighborAlphaCandidate (1 : Fin 3) (2 : Fin 3)
      (Or.inr rfl)
  rw [a.coe_alphaValue] at hglobalPrefix hglobalNeighbor ⊢
  apply le_antisymm
  · exact le_min (by simpa only [p] using hglobalPrefix) hglobalNeighbor
  · unfold alpha
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · have hlocal :=
        (segment.toGoodBONG a.good).alpha_le_halfGapCandidate p.localPivot
      rw [a.segment_halfGapCandidate_local p segment, hpivot] at hlocal
      rw [← (segment.toGoodBONG a.good).coe_alphaValue] at hlocal
      exact (min_le_left _ _).trans (by simpa only [p] using hlocal)
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji : j ≤ (1 : Fin 3) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hstart : p.start ≤ j.1 := by
        dsimp [p, prefixPairLocalization]
        omega
      have hstop : j.1 < p.stop := by
        dsimp [p, prefixPairLocalization]
        change j.1 ≤ 1 at hji
        omega
      have hjpivot : j ≤ p.pivotFin := by
        simpa only [hpivot] using hji
      have hlocalIndex :
          p.localAdjacent j hstart hstop ≤ p.localPivot := by
        change j.1 - p.start ≤ p.pivot - p.start
        change j.1 ≤ 1 at hji
        dsimp [p, prefixPairLocalization]
        omega
      have hlocal :=
        (segment.toGoodBONG a.good).alpha_le_leftDefectCandidate
          hlocalIndex
      rw [a.segment_leftDefectCandidate_local p segment j hstart hstop
        hjpivot, hpivot] at hlocal
      rw [← (segment.toGoodBONG a.good).coe_alphaValue] at hlocal
      exact (min_le_left _ _).trans (by simpa only [p] using hlocal)
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij : (1 : Fin 3) ≤ j := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      by_cases hji : j = (1 : Fin 3)
      · subst j
        have hstart : p.start ≤ (1 : Fin 3).1 := by
          dsimp [p, prefixPairLocalization]
          omega
        have hstop : (1 : Fin 3).1 < p.stop := by
          dsimp [p, prefixPairLocalization]
          omega
        have hlocal :=
          (segment.toGoodBONG a.good).alpha_le_rightDefectCandidate
            (show p.localPivot ≤ p.localPivot from le_rfl)
        have hcandidate :=
          a.segment_rightDefectCandidate_local p segment p.pivotFin
            p.start_le_pivot p.pivot_lt_stop le_rfl
        rw [localAdjacent_pivot, hpivot] at hcandidate
        rw [hcandidate] at hlocal
        rw [← (segment.toGoodBONG a.good).coe_alphaValue] at hlocal
        exact (min_le_left _ _).trans (by simpa only [p] using hlocal)
      · have hjTwo : j = (2 : Fin 3) := by
          apply Fin.ext
          change j.1 = 2
          change 1 ≤ j.1 at hij
          have hne : j.1 ≠ 1 := by
            intro h
            apply hji
            apply Fin.ext
            exact h
          omega
        subst j
        exact (min_le_right _ _).trans
          (a.successorNeighbor_le_rightDefectCandidate
            (1 : Fin 3) (2 : Fin 3) (2 : Fin 3) rfl le_rfl)

/-- Under α₂ + α₃ = 2e, the first ternary segment retains the
second global alpha. -/
theorem rankFour_boundary_prefixSecondAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound)
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    (segment.toGoodBONG a.good).alphaValue
        (prefixPairLocalization (N := 2) (1 : Fin 3)).localPivot =
      a.alphaValue (1 : Fin 3) := by
  let p := prefixPairLocalization (N := 2) (1 : Fin 3)
  have hformula := rankFour_secondAlpha_eq_min_prefix_neighbor a segment
  by_cases hhalf : a.AttainsHalfGap (1 : Fin 3)
  · have hglobalLePrefix :
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
          ((segment.toGoodBONG a.good).alphaValue p.localPivot :
            WithTop ℚ) := by
      rw [hformula]
      exact min_le_left _ _
    have hprefixLeGlobal :
        ((segment.toGoodBONG a.good).alphaValue p.localPivot :
            WithTop ℚ) ≤
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      have hlocal :=
        (segment.toGoodBONG a.good).alpha_le_halfGapCandidate p.localPivot
      rw [← (segment.toGoodBONG a.good).coe_alphaValue] at hlocal
      have hhalfLocal := a.segment_halfGapCandidate_local p segment
      have hpivot : p.pivotFin = (1 : Fin 3) := by
        apply Fin.ext
        rfl
      rw [hhalfLocal, hpivot, ← a.coe_halfGapValue] at hlocal
      exact hlocal.trans_eq
        (congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf.symm)
    exact_mod_cast le_antisymm hprefixLeGlobal hglobalLePrefix
  · have hstrict : a.alphaValue (1 : Fin 3) <
        a.halfGapValue (1 : Fin 3) :=
      lt_of_le_of_ne (a.alphaValue_le_halfGapValue (1 : Fin 3)) hhalf
    have hneighborQ : a.alphaValue (1 : Fin 3) <
        a.alphaGapValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) := by
      unfold halfGapValue orderGap at hstrict
      unfold alphaGapValue
      push_cast at hstrict ⊢
      linarith
    have hneighbor : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
        a.neighborAlphaCandidate (1 : Fin 3) (2 : Fin 3) := by
      unfold neighborAlphaCandidate
      exact_mod_cast hneighborQ
    have hminLt :
        min
            ((segment.toGoodBONG a.good).alphaValue p.localPivot :
              WithTop ℚ)
            (a.neighborAlphaCandidate (1 : Fin 3) (2 : Fin 3)) <
          a.neighborAlphaCandidate (1 : Fin 3) (2 : Fin 3) := by
      rw [← hformula]
      exact hneighbor
    have hprefixLt :
        ((segment.toGoodBONG a.good).alphaValue p.localPivot :
            WithTop ℚ) <
          a.neighborAlphaCandidate (1 : Fin 3) (2 : Fin 3) :=
      (min_lt_iff.mp hminLt).resolve_right (lt_irrefl _)
    rw [min_eq_left hprefixLt.le] at hformula
    exact_mod_cast hformula.symm

/-- Under the rank-four boundary hypotheses, the first ternary segment
retains both of the first two global alphas. -/
theorem rankFour_boundary_prefixAlphas_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    (segment.toGoodBONG a.good).alphaValue (0 : Fin 2) =
        a.alphaValue (0 : Fin 3) ∧
      (segment.toGoodBONG a.good).alphaValue (1 : Fin 2) =
        a.alphaValue (1 : Fin 3) := by
  let p := prefixPairLocalization (N := 2) (1 : Fin 3)
  let s := segment.toGoodBONG a.good
  have hlocalPivot : p.localPivot = (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have hsecondRaw :=
    rankFour_boundary_prefixSecondAlpha_eq a segment hsum
  have hsecond : s.alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin 3) := by
    simpa only [s, p, hlocalPivot] using hsecondRaw
  have horder0 : s.order (0 : Fin 3) = a.order (0 : Fin 4) := by
    change segment.bong.order 0 = a.toBONG.order 0
    calc
      segment.bong.order 0 =
          a.toBONG.order (segment.sourceIndex (0 : Fin 3)) :=
        segment.order_eq (0 : Fin 3)
      _ = a.toBONG.order 0 := by
        congr 1
  have horder1 : s.order (1 : Fin 3) = a.order (1 : Fin 4) := by
    change segment.bong.order 1 = a.toBONG.order 1
    calc
      segment.bong.order 1 =
          a.toBONG.order (segment.sourceIndex (1 : Fin 3)) :=
        segment.order_eq (1 : Fin 3)
      _ = a.toBONG.order 1 := by
        congr 1
  have horder2 : s.order (2 : Fin 3) = a.order (2 : Fin 4) := by
    change segment.bong.order 2 = a.toBONG.order 2
    calc
      segment.bong.order 2 =
          a.toBONG.order (segment.sourceIndex (2 : Fin 3)) :=
        segment.order_eq (2 : Fin 3)
      _ = a.toBONG.order 2 := by
        congr 1
  have hlocalOuter : s.order (0 : Fin 3) = s.order (2 : Fin 3) := by
    rw [horder0, horder2, houter]
  have hglobalRelation :=
    (a.beli2019Remark87 (0 : Fin 2) houter).currentAlpha_eq
  have hlocalRelation :=
    (s.beli2019Remark87 (0 : Fin 1) hlocalOuter).currentAlpha_eq
  change a.alphaValue (1 : Fin 3) =
      ((a.order (0 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
        a.alphaValue (0 : Fin 3) at hglobalRelation
  change s.alphaValue (1 : Fin 2) =
      ((s.order (0 : Fin 3) - s.order (1 : Fin 3) : Int) : ℚ) +
        s.alphaValue (0 : Fin 2) at hlocalRelation
  rw [hsecond, horder0, horder1] at hlocalRelation
  constructor
  · linarith
  · exact hsecond

/-- All local-alpha information extracted from the rank-four equality
boundary.  The witnesses are the canonical first ternary and final binary
segments of the given good BONG. -/
structure Beli2019Lemma814RankFourBoundaryLocalizationData
    (a : GoodBONG q L 4) where
  firstThree : BONG.SegmentWitness a.toBONG
    (prefixPairLocalization (N := 2) (1 : Fin 3)).start
    (prefixPairLocalization (N := 2) (1 : Fin 3)).length
    (prefixPairLocalization (N := 2) (1 : Fin 3)).bound
  lastPair : BONG.SegmentWitness a.toBONG
    (suffixPairLocalization (N := 2) (2 : Fin 3)).start
    (suffixPairLocalization (N := 2) (2 : Fin 3)).length
    (suffixPairLocalization (N := 2) (2 : Fin 3)).bound
  firstAlpha_eq :
    (firstThree.toGoodBONG a.good).alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin 3)
  secondAlpha_eq :
    (firstThree.toGoodBONG a.good).alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin 3)
  thirdAlpha_eq :
    (lastPair.toGoodBONG a.good).alphaValue
        (suffixPairLocalization (N := 2) (2 : Fin 3)).localPivot =
      a.alphaValue (2 : Fin 3)
  first_isValuationUnitDefect :
    IsValuationUnitDefect (K := K) (a.alphaValue (0 : Fin 3))
  second_isValuationUnitDefect :
    IsValuationUnitDefect (K := K) (a.alphaValue (1 : Fin 3))
  third_isValuationUnitDefect :
    IsValuationUnitDefect (K := K) (a.alphaValue (2 : Fin 3))

/-- Canonical localizations realizing all three global alphas in the
rank-four equality boundary. -/
theorem rankFour_boundaryLocalizationData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    Nonempty a.Beli2019Lemma814RankFourBoundaryLocalizationData := by
  let firstThree := a.toBONG.segmentWitness
    (prefixPairLocalization (N := 2) (1 : Fin 3)).start
    (prefixPairLocalization (N := 2) (1 : Fin 3)).length
    (prefixPairLocalization (N := 2) (1 : Fin 3)).bound
  let lastPair := a.toBONG.segmentWitness
    (suffixPairLocalization (N := 2) (2 : Fin 3)).start
    (suffixPairLocalization (N := 2) (2 : Fin 3)).length
    (suffixPairLocalization (N := 2) (2 : Fin 3)).bound
  have hprefix := a.rankFour_boundary_prefixAlphas_eq
    firstThree houter hsum
  have hlast := a.rankFour_boundary_lastPairAlpha_eq lastPair hsum
  have hdefects := a.rankFour_boundaryAlphas_areValuationUnitDefects
    houter hsecondFourth hsum
  exact ⟨{
    firstThree := firstThree
    lastPair := lastPair
    firstAlpha_eq := hprefix.1
    secondAlpha_eq := hprefix.2
    thirdAlpha_eq := hlast
    first_isValuationUnitDefect := hdefects.1
    second_isValuationUnitDefect := hdefects.2.1
    third_isValuationUnitDefect := hdefects.2.2
  }⟩

end BONG.GoodBONG
end Bong
