/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814RankFourNormalization
import Bong.Bong.Beli2019Corollary89

/-!
# Beli (2019), Lemma 8.14: rank-four assembly and higher-rank reduction

The three numerical branches of the quaternary proof were established in
separate files.  This file first assembles them into a single theorem after
normalizing the first literal binary segment by Corollary 8.11.  The remaining
declarations implement the reduction of rank at least five to this quaternary
result.
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

/-- The canonical initial quaternary segment in the rank-at-least-five
argument. -/
noncomputable def lemma814InitialFourSegment
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) :
    BONG.SegmentWitness a.toBONG 0 4 (by omega) :=
  a.toBONG.segmentWitness 0 4 (by omega)

/-- The initial quaternary segment, regarded as a good BONG. -/
noncomputable def lemma814InitialFour
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) :
    GoodBONG
      (q.restrict (a.lemma814InitialFourSegment hfive).carrier
        (a.lemma814InitialFourSegment hfive).nondegenerate)
      (a.lemma814InitialFourSegment hfive).lattice 4 :=
  (a.lemma814InitialFourSegment hfive).toGoodBONG a.good

/-- Scalar values of the initial quaternary segment are the first four
ambient scalar values. -/
theorem lemma814InitialFour_valueUnit_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) (i : Fin 4) :
    (a.lemma814InitialFour hfive).valueUnit i =
      a.valueUnit ⟨i.1, by omega⟩ := by
  let w := a.lemma814InitialFourSegment hfive
  change w.bong.valueUnit i = a.toBONG.valueUnit ⟨i.1, by omega⟩
  calc
    w.bong.valueUnit i = a.toBONG.valueUnit (w.sourceIndex i) :=
      w.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- Valuation orders of the initial quaternary segment are the first four
ambient orders. -/
theorem lemma814InitialFour_order_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) (i : Fin 4) :
    (a.lemma814InitialFour hfive).order i =
      a.order ⟨i.1, by omega⟩ := by
  let w := a.lemma814InitialFourSegment hfive
  change w.bong.order i = a.toBONG.order ⟨i.1, by omega⟩
  calc
    w.bong.order i = a.toBONG.order (w.sourceIndex i) := w.order_eq i
    _ = a.toBONG.order ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- Prefix products through the initial quaternary segment agree with the
corresponding ambient prefix products. -/
theorem lemma814InitialFour_prefixProduct_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3)
    (k : Nat) (hk : k ≤ 4) :
    (a.lemma814InitialFour hfive).prefixProduct k = a.prefixProduct k := by
  induction k with
  | zero =>
      simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero]
  | succ k ih =>
      have hkFour : k < 4 := by omega
      have hkAmbient : k < N + 3 := by omega
      unfold GoodBONG.prefixProduct
      rw [(a.lemma814InitialFour hfive).toBONG.prefixProduct_succ k hkFour,
        a.toBONG.prefixProduct_succ k hkAmbient]
      have ih' := ih (by omega)
      change (a.lemma814InitialFour hfive).toBONG.prefixProduct k =
        a.toBONG.prefixProduct k at ih'
      rw [ih']
      congr 1
      exact a.lemma814InitialFour_valueUnit_eq hfive ⟨k, hkFour⟩

/-- Prefix coefficient functions of length at most four agree. -/
theorem lemma814InitialFour_prefixValues_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3)
    (k : Nat) (hk : k ≤ 4) :
    (a.lemma814InitialFour hfive).prefixValues k hk =
      a.prefixValues k (by omega) := by
  funext i
  unfold prefixValues
  rw [← (a.lemma814InitialFour hfive).coe_valueUnit,
    ← a.coe_valueUnit, a.lemma814InitialFour_valueUnit_eq hfive]

/-- The initial four entries, localized at one of their three alpha
indices. -/
def lemma814InitialFourLocalization (i : Fin 3) (hfive : 5 ≤ N + 3) :
    AlphaLocalizationIndex (N + 2) where
  start := 0
  pivot := i.1
  stop := 3
  start_le_pivot := by omega
  pivot_lt_stop := i.isLt
  stop_lt := by omega

/-- The literal third binary alpha is unchanged on passage from the ambient
BONG to its initial quaternary segment. -/
theorem lemma814InitialFour_thirdAdjacentBinaryAlpha_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) :
    (a.lemma814InitialFour hfive).adjacentBinaryAlpha (2 : Fin 3) =
      a.adjacentBinaryAlpha (⟨2, by omega⟩ : Fin (N + 2)) := by
  let w := a.lemma814InitialFourSegment hfive
  let s := a.lemma814InitialFour hfive
  let ambientThird : Fin (N + 2) := ⟨2, by omega⟩
  have horder2 : s.order (2 : Fin 3).castSucc =
      a.order ambientThird.castSucc := by
    change w.bong.order (2 : Fin 3).castSucc =
      a.toBONG.order ambientThird.castSucc
    calc
      w.bong.order (2 : Fin 3).castSucc =
          a.toBONG.order (w.sourceIndex (2 : Fin 3).castSucc) :=
        w.order_eq (2 : Fin 3).castSucc
      _ = a.toBONG.order ambientThird.castSucc := by
        congr 1
  have horder3 : s.order (2 : Fin 3).succ =
      a.order ambientThird.succ := by
    change w.bong.order (2 : Fin 3).succ =
      a.toBONG.order ambientThird.succ
    calc
      w.bong.order (2 : Fin 3).succ =
          a.toBONG.order (w.sourceIndex (2 : Fin 3).succ) :=
        w.order_eq (2 : Fin 3).succ
      _ = a.toBONG.order ambientThird.succ := by
        congr 1
  have hvalue2 : s.valueUnit (2 : Fin 3).castSucc =
      a.valueUnit ambientThird.castSucc := by
    change w.bong.valueUnit (2 : Fin 3).castSucc =
      a.toBONG.valueUnit ambientThird.castSucc
    calc
      w.bong.valueUnit (2 : Fin 3).castSucc =
          a.toBONG.valueUnit (w.sourceIndex (2 : Fin 3).castSucc) :=
        w.valueUnit_eq (2 : Fin 3).castSucc
      _ = a.toBONG.valueUnit ambientThird.castSucc := by
        congr 1
  have hvalue3 : s.valueUnit (2 : Fin 3).succ =
      a.valueUnit ambientThird.succ := by
    change w.bong.valueUnit (2 : Fin 3).succ =
      a.toBONG.valueUnit ambientThird.succ
    calc
      w.bong.valueUnit (2 : Fin 3).succ =
          a.toBONG.valueUnit (w.sourceIndex (2 : Fin 3).succ) :=
        w.valueUnit_eq (2 : Fin 3).succ
      _ = a.toBONG.valueUnit ambientThird.succ := by
        congr 1
  have hadjacent : s.adjacentDefect (2 : Fin 3) =
      a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 2)) := by
    unfold adjacentDefect adjacentProduct
    rw [hvalue2, hvalue3]
  unfold adjacentBinaryAlpha halfGapCandidate leftDefectCandidate
  rw [horder2, horder3, hadjacent]

/-- If Corollary 8.11 realizes the third ambient alpha on the literal pair
`[a₃,a₄]`, then the third alpha of the initial quaternary segment equals the
ambient third alpha. -/
theorem lemma814InitialFour_thirdAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3)
    (hbinary : a.adjacentBinaryAlpha (⟨2, by omega⟩ : Fin (N + 2)) =
      (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ)) :
    (a.lemma814InitialFour hfive).alphaValue (2 : Fin 3) =
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) := by
  let p := lemma814InitialFourLocalization (N := N) (2 : Fin 3) hfive
  let w := a.lemma814InitialFourSegment hfive
  let s := a.lemma814InitialFour hfive
  have hpivot : p.pivotFin = (⟨2, by omega⟩ : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  have hglobalLeLocalRaw := a.beli2009Lemma21_le_segmentAlpha p w
  have hglobalLeLocal :
      (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) ≤
        (s.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    rw [a.coe_alphaValue, s.coe_alphaValue]
    rw [hpivot, hlocalPivot] at hglobalLeLocalRaw
    exact hglobalLeLocalRaw
  have hlocalLeBinary :
      (s.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
        s.adjacentBinaryAlpha (2 : Fin 3) := by
    unfold adjacentBinaryAlpha
    apply le_min
    · rw [s.coe_alphaValue]
      exact s.alpha_le_halfGapCandidate (2 : Fin 3)
    · rw [s.coe_alphaValue]
      exact s.alpha_le_leftDefectCandidate
        (i := (2 : Fin 3)) (j := (2 : Fin 3)) le_rfl
  rw [a.lemma814InitialFour_thirdAdjacentBinaryAlpha_eq hfive,
    hbinary] at hlocalLeBinary
  exact_mod_cast le_antisymm hlocalLeBinary hglobalLeLocal

/-- Once the third local alpha has been identified with the third ambient
alpha, every alpha of the initial quaternary segment agrees with its ambient
counterpart.  This is the finite-candidate-set version of
`αᵢ = min {\widetilde αᵢ, R₃ - Rᵢ + α₃}` used in the paper. -/
theorem lemma814InitialFour_alpha_eq_of_thirdAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3)
    (hthird : (a.lemma814InitialFour hfive).alphaValue (2 : Fin 3) =
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)))
    (i : Fin 3) :
    (a.lemma814InitialFour hfive).alphaValue i =
      a.alphaValue ⟨i.1, by omega⟩ := by
  classical
  let p := lemma814InitialFourLocalization (N := N) i hfive
  let w : BONG.SegmentWitness a.toBONG p.start p.length p.bound :=
    a.toBONG.segmentWitness p.start p.length p.bound
  let s := w.toGoodBONG a.good
  let ambientIndex : Fin (N + 2) := ⟨i.1, by omega⟩
  let ambientThird : Fin (N + 2) := ⟨2, by omega⟩
  have hw : w = a.lemma814InitialFourSegment hfive := by
    rfl
  cases hw
  have hs : s = a.lemma814InitialFour hfive := by
    rfl
  have hpivot : p.pivotFin = ambientIndex := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = i := by
    apply Fin.ext
    simp only [p, lemma814InitialFourLocalization,
      AlphaLocalizationIndex.localPivot]
    omega
  have hglobalLeLocalRaw := a.beli2009Lemma21_le_segmentAlpha p w
  have hglobalLeLocal :
      (a.alphaValue ambientIndex : WithTop ℚ) ≤
        (s.alphaValue i : WithTop ℚ) := by
    rw [a.coe_alphaValue, s.coe_alphaValue]
    rw [hpivot, hlocalPivot] at hglobalLeLocalRaw
    exact hglobalLeLocalRaw
  have hthird' : s.alphaValue (2 : Fin 3) =
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) := by
    rw [hs]
    exact hthird
  have horderIndex : s.order i.castSucc =
      a.order ambientIndex.castSucc := by
    change w.bong.order i.castSucc = a.toBONG.order ambientIndex.castSucc
    calc
      w.bong.order i.castSucc =
          a.toBONG.order (w.sourceIndex i.castSucc) :=
        w.order_eq i.castSucc
      _ = a.toBONG.order ambientIndex.castSucc := by
        congr 1
        apply Fin.ext
        simp [p, lemma814InitialFourLocalization,
          BONG.SegmentWitness.sourceIndex, ambientIndex]
  have horderThird : s.order (2 : Fin 3).castSucc =
      a.order ambientThird.castSucc := by
    change w.bong.order (2 : Fin 3).castSucc =
      a.toBONG.order ambientThird.castSucc
    calc
      w.bong.order (2 : Fin 3).castSucc =
          a.toBONG.order (w.sourceIndex (2 : Fin 3).castSucc) :=
        w.order_eq (2 : Fin 3).castSucc
      _ = a.toBONG.order ambientThird.castSucc := by
        congr 1
  have hiThird : i ≤ (2 : Fin 3) := by
    exact Fin.le_last i
  have hlocalEndpoint := s.alphaLeftEndpoint_monotone hiThird
  unfold alphaLeftEndpoint at hlocalEndpoint
  change (s.order i.castSucc : ℚ) + s.alphaValue i ≤
      (s.order (2 : Fin 3).castSucc : ℚ) +
        s.alphaValue (2 : Fin 3) at hlocalEndpoint
  have hlocalBoundaryQ : s.alphaValue i ≤
      ((s.order (2 : Fin 3).castSucc - s.order i.castSucc : Int) : ℚ) +
        s.alphaValue (2 : Fin 3) := by
    have hthirdIndex : (2 : Fin 3).castSucc = (2 : Fin 4) := by
      rfl
    push_cast at hlocalEndpoint
    rw [hthirdIndex]
    rw [Int.cast_sub]
    linarith
  rw [horderIndex, horderThird, hthird'] at hlocalBoundaryQ
  have hlocalBoundary : (s.alphaValue i : WithTop ℚ) ≤
      (((a.order ambientThird.castSucc - a.order ambientIndex.castSucc :
          Int) : ℚ) : WithTop ℚ) +
        (a.alphaValue ambientThird : WithTop ℚ) := by
    exact_mod_cast hlocalBoundaryQ
  have hlocalLeGlobal : (s.alphaValue i : WithTop ℚ) ≤
      (a.alphaValue ambientIndex : WithTop ℚ) := by
    rw [a.coe_alphaValue, ← hpivot, a.beli2009Lemma21 p w]
    apply Finset.le_min'
    intro y hy
    simp only [localizedReplacementCandidates, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · rw [← s.coe_alphaValue, hlocalPivot]
    · rcases Finset.mem_sdiff.mp hy with ⟨hyCandidate, hnotBlock⟩
      simp only [alphaCandidates, Finset.mem_insert,
        Finset.mem_union] at hyCandidate
      rcases hyCandidate with rfl | hyLeft | hyRight
      · exact (hnotBlock (Finset.mem_insert_self _ _)).elim
      · rcases Finset.mem_image.mp hyLeft with ⟨j, hj, rfl⟩
        have hji : j ≤ ambientIndex := by
          have hji' : j ≤ p.pivotFin := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
          rw [hpivot] at hji'
          exact hji'
        have hmem : a.leftDefectCandidate ambientIndex j ∈
            a.localizationBlockCandidates p := by
          apply Finset.mem_insert_of_mem
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨j, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · dsimp [p, lemma814InitialFourLocalization]
              omega
            · simpa only [hpivot] using hji
          · rw [hpivot]
        exact (hnotBlock hmem).elim
      · rcases Finset.mem_image.mp hyRight with ⟨j, hj, rfl⟩
        have hij : ambientIndex ≤ j := by
          have hij' : p.pivotFin ≤ j := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
          rw [hpivot] at hij'
          exact hij'
        by_cases hinside : j.1 < p.stop
        · have hmem : a.rightDefectCandidate ambientIndex j ∈
              a.localizationBlockCandidates p := by
            apply Finset.mem_insert_of_mem
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            refine ⟨j, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨by simpa only [hpivot] using hij, hinside⟩
            · rw [hpivot]
          exact (hnotBlock hmem).elim
        · have hthirdJ : ambientThird ≤ j := by
            change 2 ≤ j.1
            dsimp [p, lemma814InitialFourLocalization] at hinside
            omega
          have hthirdLe : (a.alphaValue ambientThird : WithTop ℚ) ≤
              a.rightDefectCandidate ambientThird j := by
            rw [a.coe_alphaValue]
            exact a.alpha_le_rightDefectCandidate hthirdJ
          have hadd := add_le_add_left hthirdLe
            ((((a.order ambientThird.castSucc -
              a.order ambientIndex.castSucc : Int) : ℚ) : WithTop ℚ))
          have hshifted :
              ((((a.order ambientThird.castSucc -
                a.order ambientIndex.castSucc : Int) : ℚ) : WithTop ℚ)) +
                  (a.alphaValue ambientThird : WithTop ℚ) ≤
                ((((a.order ambientThird.castSucc -
                  a.order ambientIndex.castSucc : Int) : ℚ) : WithTop ℚ)) +
                  a.rightDefectCandidate ambientThird j := by
            simpa only [add_comm] using hadd
          rw [a.right_shift_candidate_at ambientIndex ambientThird j] at hshifted
          simpa only [hpivot] using hlocalBoundary.trans hshifted
  have heq : s.alphaValue i = a.alphaValue ambientIndex := by
    exact_mod_cast le_antisymm hlocalLeGlobal hglobalLeLocal
  rw [hs] at heq
  exact heq

/-- Corollary 8.11 therefore makes all three alphas of the initial
quaternary segment equal to the ambient alphas. -/
theorem lemma814InitialFour_alphas_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3)
    (hbinary : a.adjacentBinaryAlpha (⟨2, by omega⟩ : Fin (N + 2)) =
      (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ)) :
    ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩ := by
  intro i
  exact a.lemma814InitialFour_alpha_eq_of_thirdAlpha hfive
    (a.lemma814InitialFour_thirdAlpha_eq hfive hbinary) i

/-- The unary-boundary capped defect used in Lemma 8.13 is unchanged on
passing to the initial quaternary segment. -/
theorem lemma814InitialFour_firstDefect_eq
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩) :
    (a.lemma814InitialFour hfive).truncatedPrefixDefect b 1 1 1 =
      a.truncatedPrefixDefect b 1 1 1 := by
  let s := a.lemma814InitialFour hfive
  unfold truncatedPrefixDefect
  rw [a.lemma814InitialFour_prefixProduct_eq hfive 1 (by omega),
    s.prefixAlphaCap_of_internal (by omega) (by omega),
    a.prefixAlphaCap_of_internal (by omega) (by omega),
    b.prefixAlphaCap_last]
  have hlocal : (⟨1 - 1, by omega⟩ : Fin 3) = (0 : Fin 3) := by
    apply Fin.ext
    rfl
  have hambient : (⟨1 - 1, by omega⟩ : Fin (N + 2)) =
      (0 : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  have hembed : (⟨(0 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
      (0 : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  rw [hlocal, hambient, halphas (0 : Fin 3), hembed]

/-- The capped defect `d[-a₁a₂a₃b₁]` is likewise unchanged. -/
theorem lemma814InitialFour_firstThirdDefect_eq
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩) :
    (a.lemma814InitialFour hfive).truncatedPrefixDefect b (-1) 3 1 =
      a.truncatedPrefixDefect b (-1) 3 1 := by
  let s := a.lemma814InitialFour hfive
  unfold truncatedPrefixDefect
  rw [a.lemma814InitialFour_prefixProduct_eq hfive 3 (by omega),
    s.prefixAlphaCap_of_internal (by omega) (by omega),
    a.prefixAlphaCap_of_internal (by omega) (by omega),
    b.prefixAlphaCap_last]
  have hlocal : (⟨3 - 1, by omega⟩ : Fin 3) = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  have hambient : (⟨3 - 1, by omega⟩ : Fin (N + 2)) =
      (⟨2, by omega⟩ : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  have hembed : (⟨(2 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
      (⟨2, by omega⟩ : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  rw [hlocal, hambient, halphas (2 : Fin 3), hembed]

/-- The explicit representation hypotheses of Lemma 8.13 descend from the
ambient BONG to its initial quaternary segment once the first three alphas
have been localized. -/
theorem lemma814InitialFour_conditions
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (conditions : a.Lemma813Conditions b) :
    (a.lemma814InitialFour hfive).Lemma813Conditions b := by
  let s := a.lemma814InitialFour hfive
  have hfirstDefect := a.lemma814InitialFour_firstDefect_eq b hfive halphas
  have hthirdDefect :=
    a.lemma814InitialFour_firstThirdDefect_eq b hfive halphas
  refine {
    defectEquality := ?_
    binaryRankTwo := ?_
    binaryHigher := ?_
    ternaryRankThree := ?_
    ternaryHigher := ?_
  }
  · calc
      s.truncatedPrefixDefect b 1 1 1 =
          a.truncatedPrefixDefect b 1 1 1 := hfirstDefect
      _ = (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) :=
        conditions.defectEquality
      _ = (s.alphaValue (0 : Fin 3) : WithTop ℚ) := by
        exact_mod_cast (halphas (0 : Fin 3)).symm
  · intro hm
    omega
  · intro _hm htrigger
    have htrigger' := htrigger
    unfold lemma813CentralTrigger at htrigger'
    simp only [a.lemma814InitialFour_order_eq hfive, halphas,
      hthirdDefect] at htrigger'
    have htriggerAmbient : a.lemma813CentralTrigger b (by omega) := by
      unfold lemma813CentralTrigger
      exact htrigger'
    have hrepresentation :=
      conditions.binaryHigher (by omega) htriggerAmbient
    rw [a.lemma814InitialFour_prefixValues_eq hfive 2 (by omega)]
    exact hrepresentation
  · intro hm
    omega
  · intro _hm htrigger
    have htrigger' := htrigger
    unfold lemma813LongTrigger at htrigger'
    simp only [a.lemma814InitialFour_order_eq hfive] at htrigger'
    have htriggerAmbient : a.lemma813LongTrigger b (by omega) := by
      unfold lemma813LongTrigger
      exact htrigger'
    have hrepresentation :=
      conditions.ternaryHigher (by omega) htriggerAmbient
    rw [a.lemma814InitialFour_prefixValues_eq hfive 3 (by omega)]
    exact hrepresentation

/-- Isotropy of the first ternary prefix is unchanged on passage to the
initial quaternary segment. -/
theorem lemma814InitialFour_firstThreeIsotropic_iff
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) :
    (a.lemma814InitialFour hfive).Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic := by
  unfold Lemma814FirstThreeIsotropic lemma814FirstThreeValues
  rw [a.lemma814InitialFour_prefixValues_eq hfive 3 (by omega)]

/-- The corresponding anisotropy predicate is also unchanged. -/
theorem lemma814InitialFour_firstThreeAnisotropic_iff
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) :
    (a.lemma814InitialFour hfive).Lemma814FirstThreeAnisotropic ↔
      a.Lemma814FirstThreeAnisotropic := by
  unfold Lemma814FirstThreeAnisotropic lemma814FirstThreeValues
  rw [a.lemma814InitialFour_prefixValues_eq hfive 3 (by omega)]

/-- The complement-anisotropy predicate in exception (c) depends only on
the first four coefficients and is therefore unchanged. -/
theorem lemma814InitialFour_complementAnisotropic_iff
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3) :
    (a.lemma814InitialFour hfive).Lemma814FirstFourComplementAnisotropic
        b (by omega) ↔
      a.Lemma814FirstFourComplementAnisotropic b (by omega) := by
  unfold Lemma814FirstFourComplementAnisotropic
  rw [a.lemma814InitialFour_prefixValues_eq hfive 4 (by omega)]

/-- A local exception (a) for the initial quaternary segment is an ambient
exception (a). -/
theorem lemma814ExceptionA_of_initialFour
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (A : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionA b) :
    a.Beli2019Lemma814ExceptionA b := by
  let s := a.lemma814InitialFour hfive
  have hdefect :=
    a.lemma814InitialFour_firstThirdDefect_eq b hfive halphas
  refine {
    firstThirdOrders_eq := ?_
    defectSum_strict := ?_
    firstThree_anisotropic :=
      (a.lemma814InitialFour_firstThreeAnisotropic_iff hfive).mp
        A.firstThree_anisotropic
  }
  · have h := A.firstThirdOrders_eq
    simp only [a.lemma814InitialFour_order_eq hfive] at h
    have hzero : (⟨(0 : Fin 4).1, by omega⟩ : Fin (N + 3)) =
        (0 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have htwo : (⟨(2 : Fin 4).1, by omega⟩ : Fin (N + 3)) =
        (2 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    rw [hzero, htwo] at h
    exact h
  · have h := A.defectSum_strict
    unfold lemma814FirstThirdCappedDefect at h ⊢
    rw [halphas (1 : Fin 3), hdefect] at h
    exact h

/-- A local exception (b) for the initial quaternary segment is an ambient
exception (b). -/
theorem lemma814ExceptionB_of_initialFour
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (B : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionB b) :
    a.Beli2019Lemma814ExceptionB b := by
  have hdefect :=
    a.lemma814InitialFour_firstThirdDefect_eq b hfive halphas
  refine {
    firstThirdOrders_eq := ?_
    residueTwo := B.residueTwo
    firstAlpha_strict := ?_
    defectSum_eq := ?_
    firstThree_isotropic :=
      (a.lemma814InitialFour_firstThreeIsotropic_iff hfive).mp
        B.firstThree_isotropic
    laterAlphaSum_strict := ?_
  }
  · have h := B.firstThirdOrders_eq
    simp only [a.lemma814InitialFour_order_eq hfive] at h
    have hzero : (⟨(0 : Fin 4).1, by omega⟩ : Fin (N + 3)) =
        (0 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have htwo : (⟨(2 : Fin 4).1, by omega⟩ : Fin (N + 3)) =
        (2 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    rw [hzero, htwo] at h
    exact h
  · have h := B.firstAlpha_strict
    unfold halfGapValue orderGap at h ⊢
    simp only [a.lemma814InitialFour_order_eq hfive, halphas] at h
    exact h
  · have h := B.defectSum_eq
    unfold lemma814FirstThirdCappedDefect at h ⊢
    rw [halphas (1 : Fin 3), hdefect] at h
    exact h
  · intro _hfour
    have h := B.laterAlphaSum_strict (by omega)
    simp only [halphas] at h
    have hone : (⟨(1 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
        (1 : Fin (N + 2)) := by
      apply Fin.ext
      rfl
    rw [hone] at h
    exact h

/-- Ambient nonexceptionality consequently rules out local exceptions
(a) and (b). -/
theorem lemma814InitialFour_not_exceptionAB
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    ¬(a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionA b ∧
      ¬(a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionB b := by
  constructor
  · intro A
    exact hnotExceptional
      (Or.inl (a.lemma814ExceptionA_of_initialFour b hfive halphas A))
  · intro B
    exact hnotExceptional
      (Or.inr (Or.inl
        (a.lemma814ExceptionB_of_initialFour b hfive halphas B)))

/-- The complementary third-gap value is the same in the initial
quaternary segment and in the ambient BONG. -/
theorem lemma814InitialFour_thirdComplementaryDefect_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) :
    (a.lemma814InitialFour hfive).lemma814ThirdComplementaryDefect
        (by omega) =
      a.lemma814ThirdComplementaryDefect (by omega) := by
  unfold lemma814ThirdComplementaryDefect orderGap
  simp only [a.lemma814InitialFour_order_eq hfive]
  congr 2

/-- If the fourth ambient alpha is strictly above the complementary value,
a local exception (c) lifts to an ambient exception (c). -/
theorem lemma814ExceptionC_of_initialFour_of_fourth_strict
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (C : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionC b)
    (hfourthStrict : a.lemma814ThirdComplementaryDefect (by omega) <
      a.alphaValue (⟨3, by omega⟩ : Fin (N + 2))) :
    a.Beli2019Lemma814ExceptionC b := by
  let s := a.lemma814InitialFour hfive
  have hthirdDefect :=
    a.lemma814InitialFour_firstThirdDefect_eq b hfive halphas
  have hcomplement :=
    a.lemma814InitialFour_thirdComplementaryDefect_eq hfive
  have halphaOne := halphas (1 : Fin 3)
  have hindexOne : (⟨(1 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
      (1 : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  rw [hindexOne] at halphaOne
  have halphaTwo := halphas (2 : Fin 3)
  have hindexTwo : (⟨(2 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
      (⟨2, by omega⟩ : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  rw [hindexTwo] at halphaTwo
  have hrawLocal :=
    s.lemma814FirstFourRawDefect_eq_secondAlpha_of_exceptionC b C
  have hrawAmbient : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    calc
      defectOrder (K := K) (a.prefixProduct 4) =
          defectOrder (K := K) (s.prefixProduct 4) := by
        rw [a.lemma814InitialFour_prefixProduct_eq hfive 4 (by omega)]
      _ = (s.alphaValue (1 : Fin 3) : WithTop ℚ) := hrawLocal
      _ = (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
        exact congrArg (fun x : ℚ => (x : WithTop ℚ)) halphaOne
  have hsecondComplement : a.alphaValue (1 : Fin (N + 2)) =
      a.lemma814ThirdComplementaryDefect (by omega) := by
    have h := C.secondAlpha_eq_complement
    rw [hcomplement] at h
    exact halphaOne.symm.trans h
  have hfirstFour : a.lemma814FirstFourCappedDefect (by omega) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    have hmin := a.lemma814FirstFourCappedDefect_eq_min (by omega)
    rw [a.prefixAlphaCap_of_internal (i := 4) (by omega) (by omega)] at hmin
    have hindex : (⟨4 - 1, by omega⟩ : Fin (N + 2)) =
        (⟨3, by omega⟩ : Fin (N + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex, hrawAmbient] at hmin
    have hlt : (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        (a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) : WithTop ℚ) := by
      exact_mod_cast hsecondComplement.symm ▸ hfourthStrict
    rw [min_eq_left hlt.le] at hmin
    exact hmin
  refine {
    rank_four := by omega
    firstThirdOrders_eq := ?_
    residueTwo := C.residueTwo
    secondFourthOrders_lt := ?_
    firstThirdDefect_eq_alpha := ?_
    thirdAlpha_eq_halfGap := ?_
    firstFourDefect_eq_secondAlpha := hfirstFour
    secondAlpha_eq_complement := hsecondComplement
    firstFourComplement_anisotropic :=
      (a.lemma814InitialFour_complementAnisotropic_iff b hfive).mp
        C.firstFourComplement_anisotropic
    laterAlpha_strict := fun _ ↦ hfourthStrict
  }
  · have h := C.firstThirdOrders_eq
    simp only [a.lemma814InitialFour_order_eq hfive] at h
    have hzero : (⟨(0 : Fin 4).1, by omega⟩ : Fin (N + 3)) =
        (0 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have htwo : (⟨(2 : Fin 4).1, by omega⟩ : Fin (N + 3)) =
        (2 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    rw [hzero, htwo] at h
    exact h
  · have h := C.secondFourthOrders_lt
    simp only [a.lemma814InitialFour_order_eq hfive] at h
    have hone : (⟨(1 : Fin 4).1, by omega⟩ : Fin (N + 3)) =
        (1 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    rw [hone] at h
    exact h
  · have h := C.firstThirdDefect_eq_alpha
    unfold lemma814FirstThirdCappedDefect at h ⊢
    have hlocalTwo : (⟨2, by omega⟩ : Fin 3) = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hthirdDefect, hlocalTwo, halphaTwo] at h
    exact h
  · have h := C.thirdAlpha_eq_halfGap
    unfold halfGapValue orderGap at h ⊢
    simp only [a.lemma814InitialFour_order_eq hfive, halphas] at h
    exact h

/-- Therefore ambient nonexceptionality forces the fourth alpha to be at
most the complementary third-gap value whenever local exception (c) holds.
-/
theorem lemma814FourthAlpha_not_gt_of_initialFour_exceptionC
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (C : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionC b) :
    ¬a.lemma814ThirdComplementaryDefect (by omega) <
      a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) := by
  intro hstrict
  exact hnotExceptional (Or.inr (Or.inr
    (a.lemma814ExceptionC_of_initialFour_of_fourth_strict
      b hfive halphas C hstrict)))

/-- Property P1 supplies the reverse inequality, so the fourth ambient
alpha is exactly the complementary third-gap value. -/
theorem lemma814FourthAlpha_eq_of_initialFour_exceptionC
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (C : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionC b) :
    a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) =
      a.lemma814ThirdComplementaryDefect (by omega) := by
  have hthird : a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) =
      a.halfGapValue (⟨2, by omega⟩ : Fin (N + 2)) := by
    have h := C.thirdAlpha_eq_halfGap
    unfold halfGapValue orderGap at h ⊢
    simp only [a.lemma814InitialFour_order_eq hfive, halphas] at h
    exact h
  exact a.fourthAlpha_eq_lemma814ThirdComplementaryDefect_of_not_strict
    hfive hthird
      (a.lemma814FourthAlpha_not_gt_of_initialFour_exceptionC
        b hfive halphas hnotExceptional C)

/-- At any adjacent index, attainment of the half gap forces the literal
binary alpha to equal the global alpha.  The endpoint version used in
Lemma 8.8 is `firstBinaryAlpha_eq_alpha_of_halfGap`; the high-rank proof of
Lemma 8.14 needs the same observation at the third adjacent pair. -/
theorem adjacentBinaryAlpha_eq_alpha_of_attainsHalfGap
    (a : GoodBONG q L (N + 2)) (i : Fin (N + 1))
    (hhalf : a.AttainsHalfGap i) :
    a.adjacentBinaryAlpha i = (a.alphaValue i : WithTop ℚ) := by
  apply le_antisymm
  · unfold adjacentBinaryAlpha
    calc
      min (a.halfGapCandidate i) (a.leftDefectCandidate i i) ≤
          a.halfGapCandidate i := min_le_left _ _
      _ = (a.alphaValue i : WithTop ℚ) := by
        rw [← a.coe_halfGapValue]
        exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hhalf.symm
  · unfold adjacentBinaryAlpha
    apply le_min
    · rw [← a.coe_halfGapValue]
      exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hhalf |>.le
    · rw [a.coe_alphaValue]
      exact a.alpha_le_leftDefectCandidate le_rfl

/-- Every literal adjacent defect in the initial quaternary segment is the
corresponding ambient adjacent defect. -/
theorem lemma814InitialFour_adjacentDefect_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) (i : Fin 3) :
    (a.lemma814InitialFour hfive).adjacentDefect i =
      a.adjacentDefect ⟨i.1, by omega⟩ := by
  unfold adjacentDefect adjacentProduct
  rw [a.lemma814InitialFour_valueUnit_eq hfive i.castSucc,
    a.lemma814InitialFour_valueUnit_eq hfive i.succ]
  congr 2

/-- Literal binary alphas in the initial four entries agree with their
ambient counterparts. -/
theorem lemma814InitialFour_adjacentBinaryAlpha_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) (i : Fin 3) :
    (a.lemma814InitialFour hfive).adjacentBinaryAlpha i =
      a.adjacentBinaryAlpha ⟨i.1, by omega⟩ := by
  unfold adjacentBinaryAlpha halfGapCandidate leftDefectCandidate
  rw [a.lemma814InitialFour_order_eq hfive i.castSucc,
    a.lemma814InitialFour_order_eq hfive i.succ,
    a.lemma814InitialFour_adjacentDefect_eq hfive i]
  congr 3

/-- The first literal normal form of the ambient BONG descends to the
initial quaternary segment once its alphas have been localized. -/
theorem lemma814InitialFour_firstBinaryAlpha_eq
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)) :
    (a.lemma814InitialFour hfive).firstBinaryAlpha =
      ((a.lemma814InitialFour hfive).alphaValue (0 : Fin 3) :
        WithTop ℚ) := by
  rw [show (a.lemma814InitialFour hfive).firstBinaryAlpha =
      (a.lemma814InitialFour hfive).adjacentBinaryAlpha (0 : Fin 3) by
        rfl,
    a.lemma814InitialFour_adjacentBinaryAlpha_eq hfive (0 : Fin 3)]
  rw [show a.adjacentBinaryAlpha
      (⟨(0 : Fin 3).1, by omega⟩ : Fin (N + 2)) = a.firstBinaryAlpha by
        rfl,
    hbinary]
  exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (halphas 0).symm

/-- The equality and parity package extracted from a surviving local
exception (c).  It records precisely the three assertions used after the
second application of Corollary 8.11 in the paper. -/
structure Beli2019Lemma814HigherRankAlphaData
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3) : Prop where
  first_odd : IsOddRationalInteger
    (a.alphaValue (0 : Fin (N + 2)))
  second_odd : IsOddRationalInteger
    (a.alphaValue (1 : Fin (N + 2)))
  third_odd : IsOddRationalInteger
    (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)))
  first_lt_twoE : a.alphaValue (0 : Fin (N + 2)) <
    2 * (ramificationIndex K : ℚ)
  second_lt_twoE : a.alphaValue (1 : Fin (N + 2)) <
    2 * (ramificationIndex K : ℚ)
  third_lt_twoE : a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) <
    2 * (ramificationIndex K : ℚ)
  second_third_sum : a.alphaValue (1 : Fin (N + 2)) +
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) =
    2 * (ramificationIndex K : ℚ)
  third_eq_halfGap : a.alphaValue
      (⟨2, by omega⟩ : Fin (N + 2)) =
    a.halfGapValue (⟨2, by omega⟩ : Fin (N + 2))
  fourth_eq_second : a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) =
    a.alphaValue (1 : Fin (N + 2))

/-- A local exception (c), together with ambient nonexceptionality, gives
the odd-`< 2e` alpha data and the paper's equality `α₄ = α₂`. -/
theorem lemma814HigherRankAlphaData_of_initialFour_exceptionC
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (C : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionC b) :
    a.Beli2019Lemma814HigherRankAlphaData hfive := by
  let s := a.lemma814InitialFour hfive
  have hsum : s.alphaValue (1 : Fin 3) + s.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ) :=
    s.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
      b C (by omega)
  have D := s.rankFour_boundaryAlphaData C.firstThirdOrders_eq
    C.secondFourthOrders_lt hsum
  have hfourth := a.lemma814FourthAlpha_eq_of_initialFour_exceptionC
    b hfive halphas hnotExceptional C
  have hcomplement :=
    a.lemma814InitialFour_thirdComplementaryDefect_eq hfive
  have hfourthSecond :
      a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) =
        a.alphaValue (1 : Fin (N + 2)) := by
    calc
      a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) =
          a.lemma814ThirdComplementaryDefect (by omega) := hfourth
      _ = s.lemma814ThirdComplementaryDefect (by omega) :=
        hcomplement.symm
      _ = s.alphaValue (1 : Fin 3) := C.secondAlpha_eq_complement.symm
      _ = a.alphaValue (1 : Fin (N + 2)) := by
        simpa using halphas (1 : Fin 3)
  refine {
    first_odd := ?_
    second_odd := ?_
    third_odd := ?_
    first_lt_twoE := ?_
    second_lt_twoE := ?_
    third_lt_twoE := ?_
    second_third_sum := ?_
    third_eq_halfGap := ?_
    fourth_eq_second := hfourthSecond
  }
  · simpa using halphas (0 : Fin 3) ▸ D.first_odd
  · simpa using halphas (1 : Fin 3) ▸ D.second_odd
  · simpa using halphas (2 : Fin 3) ▸ D.third_odd
  · simpa using halphas (0 : Fin 3) ▸ D.first_lt_twoE
  · simpa using halphas (1 : Fin 3) ▸ D.second_lt_twoE
  · simpa using halphas (2 : Fin 3) ▸ D.third_lt_twoE
  · have hsecond : s.alphaValue (1 : Fin 3) =
        a.alphaValue (1 : Fin (N + 2)) := by
      have h := halphas (1 : Fin 3)
      change s.alphaValue (1 : Fin 3) = _ at h
      have hindex : (⟨(1 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
          (1 : Fin (N + 2)) := by
        apply Fin.ext
        rfl
      rw [hindex] at h
      exact h
    have hthird : s.alphaValue (2 : Fin 3) =
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) := by
      have h := halphas (2 : Fin 3)
      change s.alphaValue (2 : Fin 3) = _ at h
      have hindex : (⟨(2 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
          (⟨2, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        rfl
      rw [hindex] at h
      exact h
    rw [← hsecond, ← hthird]
    exact hsum
  · have h := C.thirdAlpha_eq_halfGap
    unfold halfGapValue orderGap at h ⊢
    simp only [a.lemma814InitialFour_order_eq hfive, halphas] at h
    exact h

/-- In the first-binary normal form, local exception (c) gives the first
raw adjacent defect `d(-a₁a₂)=α₂`. -/
theorem lemma814FirstAdjacentDefect_eq_secondAlpha_of_initialFour_exceptionC
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (C : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionC b) :
    a.adjacentDefect (0 : Fin (N + 2)) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  let s := a.lemma814InitialFour hfive
  have hlocalBinary :=
    a.lemma814InitialFour_firstBinaryAlpha_eq hfive halphas hbinary
  have hlocal := s.adjacentDefect_zero_eq_secondAlpha_of_firstBinary
    hlocalBinary C.firstThirdOrders_eq
      (s.firstAlpha_lt_halfGap_of_lemma814ExceptionC b C)
  calc
    a.adjacentDefect (0 : Fin (N + 2)) =
        s.adjacentDefect (0 : Fin 3) := by
      symm
      have hindex : (⟨(0 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
          (0 : Fin (N + 2)) := by
        apply Fin.ext
        rfl
      simpa only [s, hindex] using
        a.lemma814InitialFour_adjacentDefect_eq hfive (0 : Fin 3)
    _ = (s.alphaValue (1 : Fin 3) : WithTop ℚ) := hlocal
    _ = (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
      exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) <| by
        simpa using halphas (1 : Fin 3)

/-- A surviving local exception (c) also identifies the raw determinant
defect of the ambient first four entries with the second alpha. -/
theorem lemma814FirstFourRawDefect_eq_secondAlpha_of_initialFour_exceptionC
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (C : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionC b) :
    defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  let s := a.lemma814InitialFour hfive
  calc
    defectOrder (K := K) (a.prefixProduct 4) =
        defectOrder (K := K) (s.prefixProduct 4) := by
      rw [a.lemma814InitialFour_prefixProduct_eq hfive 4 (by omega)]
    _ = (s.alphaValue (1 : Fin 3) : WithTop ℚ) :=
      s.lemma814FirstFourRawDefect_eq_secondAlpha_of_exceptionC b C
    _ = (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
      exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) <| by
        simpa using halphas (1 : Fin 3)

/-- Lemma 8.1(ii) then yields the strict opposite adjacent defect
`α₂ < d(-a₃a₄)` used in both high-rank branches. -/
theorem lemma814SecondAlpha_lt_thirdAdjacentDefect_of_initialFour_exceptionC
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 5 ≤ N + 3)
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour hfive).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (C : (a.lemma814InitialFour hfive).Beli2019Lemma814ExceptionC b) :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 2)) := by
  let s := a.lemma814InitialFour hfive
  have hlocalBinary :=
    a.lemma814InitialFour_firstBinaryAlpha_eq hfive halphas hbinary
  have hlocal :=
    s.secondAlpha_lt_adjacentDefect_two_of_lemma814ExceptionC
      b hlocalBinary C (by omega)
  calc
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) =
        (s.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) <| by
        simpa using (halphas (1 : Fin 3)).symm
    _ < s.adjacentDefect (2 : Fin 3) := by simpa using hlocal
    _ = a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 2)) := by
      have hindex : (⟨(2 : Fin 3).1, by omega⟩ : Fin (N + 2)) =
          (⟨2, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        rfl
      simpa only [s, hindex] using
        a.lemma814InitialFour_adjacentDefect_eq hfive (2 : Fin 3)

/-- The complete quaternary sufficiency theorem in the outer-order branch
`R₁ = R₃ < R₄`.  Corollary 8.11 first makes the literal first binary
alpha equal to the invariant first alpha; trichotomy of
`α₂ + α₃` then dispatches to the strict-below, equality, and strict-above
proofs. -/
theorem beli2019Lemma814_rankFour
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
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a original : GoodBONG q L 4) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.beli2019Corollary811 (0 : Fin 3) with ⟨C⟩
  let changed := C.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have horder' : changed.order (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin 4)]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  have hnotExceptional' : ¬changed.Beli2019Lemma814Exceptional b :=
    fun E ↦ hnotExceptional (hinvariant.mpr E)
  have houter' : changed.order (0 : Fin 4) = changed.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact houter
  have hsecondFourth' : changed.order (1 : Fin 4) <
      changed.order (3 : Fin 4) := by
    rw [← horders (1 : Fin 4), ← horders (3 : Fin 4)]
    exact hsecondFourth
  have hbinary : changed.firstBinaryAlpha =
      (changed.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    simpa only [adjacentBinaryAlpha_zero] using C.adjacentBinaryAlpha_eq
  rcases lt_trichotomy
      (changed.alphaValue (1 : Fin 3) + changed.alphaValue (2 : Fin 3))
      (2 * (ramificationIndex K : ℚ)) with hbelow | hequal | habove
  · exact changed.beli2019Lemma814_rankFour_alphaSum_lt
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder' hconditions houter' hbinary hbelow hsecondFourth'
  · exact changed.beli2019Lemma814_rankFour_boundary
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder' hconditions hnotExceptional' houter'
        hsecondFourth' hequal
  · exact changed.beli2019Lemma814_rankFour_alphaSum_gt
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder' hconditions hnotExceptional' houter' hbinary habove

end BONG.GoodBONG

end Bong
