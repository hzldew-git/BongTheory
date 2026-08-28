/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeIISMinusOne
import Bong.Bong.Beli2019Lemma716TypeIIDefect

/-!
# Beli (2019), Lemma 7.16(ii): the type-II boundary `i = s - 2`

If the following endpoint is nonessential, Lemma 2.13 closes the boundary.
Otherwise its two-term strict inequality, the good-BONG lower gap bound, and
the parity of a negative gap force the comparison prefix to have the same
alternating endpoint orders as the constructed prefix.  Lemma 7.5 then gives
defect at least `2e` on both self-prefixes, hence on their mixed product.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [DyadicDiscriminantClassLaws K]
variable [Beli2006AlphaLaws.{u, v} K]

/-- The constructed length-`s - 2` type-II prefix has the endpoint profile
required by Lemma 7.5. -/
theorem lemma716_typeII_sMinusTwo_sourceProfile
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (hsFour : 4 ≤ s) :
    Beli2019Lemma716TypeIIFailureProfile b R (s - 2)
      (by omega) (by have := D.le_rank; omega) := by
  have hfirstOrder : b.order (0 : Fin (n + 3)) = R + 1 := by
    let zero : Fin (n + 3) := ⟨0, by omega⟩
    have hzero := a.lemma716_typeII_prefix_order_eq_high b R s D hthird hII
      epsilon eta hvalues zero (by
        dsimp only [zero]
        omega) (by
          dsimp only [zero]
          exact ⟨0, rfl⟩)
    have hindex : zero = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp only [zero, Fin.val_zero]
    simpa only [hindex] using hzero
  let high : Fin (n + 3) := ⟨(s - 2) - 2, by
    have := D.le_rank
    omega⟩
  let low : Fin (n + 3) := ⟨(s - 2) - 1, by
    have := D.le_rank
    omega⟩
  have hhighEven : Even high.val := by
    rcases D.even with ⟨d, hd⟩
    refine ⟨d - 2, ?_⟩
    dsimp only [high]
    omega
  have hlowOdd : Odd low.val := by
    rcases D.even with ⟨d, hd⟩
    refine ⟨d - 2, ?_⟩
    dsimp only [low]
    omega
  have hhigh : b.order high = R + 1 :=
    a.lemma716_typeII_prefix_order_eq_high b R s D hthird hII
      epsilon eta hvalues high (by dsimp only [high]; omega) hhighEven
  have hlow : b.order low =
      R - 2 * (ramificationIndex K : Int) + 1 :=
    a.lemma716_typeII_prefix_order_eq_low b R s D hthird hII
      epsilon eta hvalues low (by dsimp only [low]; omega) hlowOdd
  exact {
    first := hfirstOrder
    high := by simpa only [high] using hhigh
    low := by simpa only [low] using hlow }

/-- Next essentiality at `i = s - 2` rigidifies the comparison prefix to
the same length-`s - 2` Lemma 7.5 endpoint profile. -/
theorem lemma716_typeII_sMinusTwo_comparisonProfile_of_essential
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (hsFour : 4 ≤ s)
    (hessential : b.IsEssentialFor c ⟨s - 2, by
      have := D.le_rank
      omega⟩) :
    Beli2019Lemma716TypeIIFailureProfile c R (s - 2)
      (by omega) (by have := D.le_rank; omega) := by
  let boundary : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  let high : Fin (n + 3) := ⟨boundary.val - 2, by
    have := D.le_rank
    omega⟩
  let low : Fin (n + 3) := ⟨boundary.val - 1, by
    have := D.le_rank
    omega⟩
  let sourceRight : Fin (n + 3) := ⟨boundary.val + 1, by
    have hs : s < n + 3 := Classical.choose hII
    dsimp only [boundary]
    omega⟩
  let sourceTail : Fin (n + 3) := ⟨boundary.val + 2, by
    have hs : s < n + 3 := Classical.choose hII
    dsimp only [boundary]
    omega⟩
  have hessential' : b.IsEssentialFor c boundary := by
    simpa only [boundary] using hessential
  unfold IsEssentialFor BeliOrderSequence.IsEssentialFor at hessential'
  have hsumRaw := hessential'.2 (by
      dsimp only [boundary]
      omega) (by
      dsimp only [boundary]
      have hs : s < n + 3 := Classical.choose hII
      omega)
  have hsum : c.order high + c.order low <
      b.order sourceRight + b.order sourceTail := by
    simpa only [orderSequence_at, high, low, sourceRight, sourceTail] using
      hsumRaw
  have hsourceRight : b.order sourceRight =
      R - 2 * (ramificationIndex K : Int) + 3 := by
    have hindex : sourceRight = ⟨s - 1, by
        have hs : s < n + 3 := Classical.choose hII
        omega⟩ := by
      apply Fin.ext
      dsimp only [sourceRight, boundary]
      omega
    rw [hindex]
    exact a.lemma716_typeII_rightBoundary_order_eq b R s D hII
      epsilon eta hepsilonUnit hetaUnit hvalues
  have hsourceTail : b.order sourceTail = R + 1 := by
    have hindex : sourceTail = ⟨s, Classical.choose hII⟩ := by
      apply Fin.ext
      dsimp only [sourceTail, boundary]
      omega
    rw [hindex]
    exact a.lemma716_typeII_tailBoundary_order_eq b R s D hII
      epsilon eta hepsilonUnit hetaUnit hvalues
  have hhighEven : Even high.val := by
    rcases D.even with ⟨d, hd⟩
    refine ⟨d - 2, ?_⟩
    dsimp only [high, boundary]
    omega
  have hhighLower : R + 1 ≤ c.order high :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm high hhighEven
  let gap : Fin (n + 2) := ⟨high.val, by
    dsimp only [high, boundary]
    have := D.le_rank
    omega⟩
  have hgapDef : c.orderGap gap = c.order low - c.order high := by
    unfold orderGap
    have hsucc : gap.succ = low := by
      apply Fin.ext
      simp only [gap, low, high, boundary, Fin.val_succ, Fin.val_mk]
      have := hsFour
      omega
    have hcast : gap.castSucc = high := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  have hgapLower := c.orderGap_ge_neg_two_mul_e gap
  rw [hgapDef] at hgapLower
  have hhighEq : c.order high = R + 1 := by
    rw [hsourceRight, hsourceTail] at hsum
    omega
  have hgapNegative : c.orderGap gap < 0 := by
    rw [hgapDef, hhighEq]
    rw [hsourceRight, hsourceTail, hhighEq] at hsum
    have he := ramificationIndex_pos (K := K)
    omega
  have hgapEven := c.orderGap_even_of_negative gap hgapNegative
  rw [hgapDef] at hgapEven
  rcases hgapEven with ⟨z, hz⟩
  rw [hhighEq] at hgapLower hz
  rw [hsourceRight, hsourceTail, hhighEq] at hsum
  have hlowEq : c.order low =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    omega
  let zero : Fin (n + 3) := 0
  have hzeroLower : R + 1 ≤ c.order zero := by
    simpa only [zero] using
      a.lemma716_comparison_order_zero_ge c R hfirst hnorm
  have hzeroHighEven : Even (high.val - zero.val) := by
    simpa only [zero, Fin.val_zero, Nat.sub_zero] using hhighEven
  have hzeroHigh : c.order zero ≤ c.order high :=
    lemma716_order_le_of_evenGap c zero high (by
      simp only [zero, Fin.val_zero]
      exact Nat.zero_le _) hzeroHighEven
  have hzeroEq : c.order zero = R + 1 := by omega
  refine {
    first := by simpa only [zero] using hzeroEq
    high := ?_
    low := ?_ }
  · have hindex : (⟨(s - 2) - 2, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) = high := by
      apply Fin.ext
      rfl
    simpa only [hindex] using hhighEq
  · have hindex : (⟨(s - 2) - 1, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) = low := by
      apply Fin.ext
      rfl
    simpa only [hindex] using hlowEq

/-- Condition 2.1(ii) at the type-II boundary with paper index `s - 2`. -/
theorem lemma716_typeII_sMinusTwo_representationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (hsFour : 4 ≤ s) :
    b.RepresentationDefectAt c
      { val := s - 2
        pos := by omega
        lt_large := by have := D.le_rank; omega
        le_small := by have := D.le_rank; omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s - 2
      pos := by omega
      lt_large := by have := D.le_rank; omega
      le_small := by have := D.le_rank; omega }
  have hcurrentNot : ¬b.IsCurrentEssential c i := by
    apply a.lemma716_typeII_not_essential b c R s D hfirst hthird hnorm
      hII epsilon eta hepsilonUnit hetaUnit hvalues
      (currentEssentialIndex i)
    · simp only [currentEssentialIndex]
      dsimp only [i]
      omega
    · simp only [currentEssentialIndex]
      dsimp only [i]
      omega
  by_cases hnext : b.IsNextEssential c i
  · have hessential : b.IsEssentialFor c ⟨s - 2, by
        have := D.le_rank
        omega⟩ := by
      unfold IsNextEssential at hnext
      simpa only [nextEssentialIndex, i] using hnext
    have Psource := a.lemma716_typeII_sMinusTwo_sourceProfile b R s D
      hthird hII epsilon eta hvalues hsFour
    have Pcomparison := a.lemma716_typeII_sMinusTwo_comparisonProfile_of_essential
      b c R s D hfirst hnorm hII epsilon eta hepsilonUnit hetaUnit
      hvalues hsFour hessential
    have hsMinusTwoEven : Even (s - 2) := by
      rcases D.even with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hsMinusTwoInterior : s - 2 < n + 3 := by
      have := D.le_rank
      omega
    have hsourceSelf := b.lemma716_typeII_comparisonPrefixDefect_ge_twoE
      R (s - 2) (by omega) hsMinusTwoInterior hsMinusTwoEven Psource
    have hcomparisonSelf := c.lemma716_typeII_comparisonPrefixDefect_ge_twoE
      R (s - 2) (by omega) hsMinusTwoInterior hsMinusTwoEven Pcomparison
    let theta : Kˣ := (-1) ^ ((s - 2) / 2)
    have htheta : theta * theta = 1 := by
      dsimp only [theta]
      rw [← mul_pow]
      simp
    have hmixed :
        (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
          b.truncatedPrefixDefect c 1 (s - 2) (s - 2) := by
      exact mixedPrefixDefect_ge_of_selfPrefixDefects b c
        (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))
        theta theta 1 (s - 2) (s - 2)
        (by simpa only [theta] using hsourceSelf)
        (by simpa only [theta] using hcomparisonSelf) htheta
    have hsourceBoundary := a.lemma716_typeII_leftBoundary_order_eq
      b R s D hII epsilon eta hepsilonUnit hetaUnit hvalues
    unfold RepresentationDefectAt
    change b.representationAlpha c i ≤
      b.truncatedPrefixDefect c 1 i.val i.val
    calc
      b.representationAlpha c i ≤ b.representationHalfGap c i :=
        b.representationAlpha_le_halfGap c i
      _ = (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) := by
        unfold representationHalfGap
        have hcurrentIndex : (⟨i.val, i.lt_large⟩ : Fin (n + 3)) =
            ⟨s - 2, by have := D.le_rank; omega⟩ := by
          apply Fin.ext
          rfl
        have hpreviousIndex :
            (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 3)) =
              ⟨(s - 2) - 1, by have := D.le_rank; omega⟩ := by
          apply Fin.ext
          rfl
        rw [hcurrentIndex, hpreviousIndex, hsourceBoundary, Pcomparison.low]
        apply WithTop.coe_eq_coe.mpr
        push_cast
        norm_num
        exact (two_mul (ramificationIndex K : ℚ)).symm
      _ ≤ b.truncatedPrefixDefect c 1 i.val i.val := by
        simpa only [i] using hmixed
  · have hdefect := b.representationDefectAt_of_not_essential c i
      hcurrentNot hnext
    simpa only [i] using hdefect

end BONG.GoodBONG

end Bong
