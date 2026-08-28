/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715AlphaTypeI

/-!
# Beli (2019), Lemma 7.15: the type-II boundary alpha

The type-II coefficient at the stopping index is multiplied by `eta`, whose
defect is `2e-1`.  If the old adjacent defect is smaller, the domination
principle leaves it unchanged.  Otherwise both old and new local defect terms
are dominated by the common half-gap term.  This is exactly the final case
split in the paper's proof of Lemma 7.15.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

variable [DyadicDiscriminantClassLaws K]
variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]

/-- The boundary equality `alpha_(s+1) = beta_(s+1)` in the type-II
branch, translated to zero-based alpha index `s`. -/
theorem lemma715_typeII_boundary_alpha_eq
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII b R s)
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeIITargetValues b s D.two_le
        (Classical.choose hII) ε η i)
    (hsBoundary : s + 2 ≤ n + 3) :
    b.alpha ⟨s, by omega⟩ = result.alpha ⟨s, by omega⟩ := by
  let hsCurrent : s < n + 3 := Classical.choose hII
  have hsourceCurrent : b.order ⟨s, hsCurrent⟩ = R + 1 :=
    Classical.choose_spec hII
  let boundary : Fin (n + 2) := ⟨s, by omega⟩
  have hsPositive : 0 < s := lt_of_lt_of_le (by omega) D.two_le
  have hboundaryPositive : 0 < boundary.val := by
    simpa [boundary] using hsPositive
  have hcurrent : b.order boundary.castSucc =
      result.order boundary.castSucc := by
    exact lemma715_typeII_order_eq b R s D hII ε η hεUnit hηUnit
      result hvalues boundary.castSucc (by simp [boundary])
  have hnextOrder : b.order boundary.succ =
      result.order boundary.succ := by
    exact lemma715_typeII_order_eq b R s D hII ε η hεUnit hηUnit
      result hvalues boundary.succ (by simp [boundary])
  have htail : ∀ j : Fin (n + 3), boundary.val < j.val →
      b.valueUnit j = result.valueUnit j := by
    intro j hj
    calc
      b.valueUnit j = lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η j :=
        (lemma714TypeIITargetValues_suffix b s D.two_le
          (Classical.choose hII) ε η j (by
            simpa [boundary] using hj)).symm
      _ = result.valueUnit j := (hvalues j).symm
  have hsourcePreviousGap :
      2 * (ramificationIndex K : Int) ≤
        b.order boundary.castSucc -
          b.order ⟨boundary.val - 1, by omega⟩ := by
    by_cases hsTwo : s = 2
    · have hprevious :
          b.order ⟨boundary.val - 1, by omega⟩ =
            R - 2 * (ramificationIndex K : Int) := by
        simpa [boundary, hsTwo] using hsecond
      have hcurrentExact : b.order boundary.castSucc = R + 1 := by
        simpa [boundary, hsCurrent] using hsourceCurrent
      omega
    · have hsFour : 4 ≤ s := by
        have hsTwoLe := D.two_le
        rcases D.even with ⟨d, hd⟩
        omega
      have hprevious := b.lemma714_selected_last_order R s
        D.toLemma714MinimalityData hsFour hthird
      have hprevious' :
          b.order ⟨boundary.val - 1, by omega⟩ =
            R - 2 * (ramificationIndex K : Int) + 1 := by
        simpa [boundary] using hprevious
      have hcurrentExact : b.order boundary.castSucc = R + 1 := by
        simpa [boundary, hsCurrent] using hsourceCurrent
      omega
  have htargetPreviousOrder :
      result.order ⟨boundary.val - 1, by omega⟩ =
        R - 2 * (ramificationIndex K : Int) + 3 := by
    calc
      result.order ⟨boundary.val - 1, by omega⟩ =
          ordUnit K (result.valueUnit
            ⟨boundary.val - 1, by omega⟩) :=
        result.toBONG.order_eq_ordUnit _
      _ = ordUnit K (lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η
            ⟨boundary.val - 1, by omega⟩) :=
        congrArg (ordUnit K) (hvalues _)
      _ = R - 2 * (ramificationIndex K : Int) + 3 := by
        simpa [boundary, hsCurrent] using
          (ordUnit_lemma714TypeIITargetValues_one b R s D.two_le
            (Classical.choose hII) (Classical.choose_spec hII)
            ε η hεUnit hηUnit)
  have htargetPreviousGap :
      result.order boundary.castSucc -
          result.order ⟨boundary.val - 1, by omega⟩ =
        2 * (ramificationIndex K : Int) - 2 := by
    have htargetCurrent : result.order boundary.castSucc = R + 1 := by
      rw [← hcurrent]
      simpa [boundary, hsCurrent] using hsourceCurrent
    omega
  have hsourceGap :
      2 - 2 * (ramificationIndex K : Int) ≤ b.orderGap boundary := by
    have hstop := b.lemma714_typeII_stopOrder_ge R s D hII hsBoundary
    have hcurrentExact : b.order boundary.castSucc = R + 1 := by
      simpa [boundary, hsCurrent] using hsourceCurrent
    unfold orderGap
    change 2 - 2 * (ramificationIndex K : Int) ≤
      b.order boundary.succ - b.order boundary.castSucc
    have hnext : R - 2 * (ramificationIndex K : Int) + 3 ≤
        b.order boundary.succ := by
      simpa [boundary] using hstop
    omega
  have htargetGap :
      2 - 2 * (ramificationIndex K : Int) ≤
        result.orderGap boundary := by
    unfold orderGap
    rw [← hnextOrder, ← hcurrent]
    exact hsourceGap
  have hsourcePrefixAlpha : 2 * (ramificationIndex K : ℚ) ≤
      ((b.prefixAlphaSegmentWitness boundary hboundaryPositive).toGoodBONG
        b.good).alphaValue
        (prefixAlphaLocalizationIndex boundary hboundaryPositive).localPivot :=
    b.prefixSegmentAlphaValue_ge_twoE_of_predecessor_gap boundary
      hboundaryPositive hsourcePreviousGap
  have htargetPrefixAlpha :
      ((result.prefixAlphaSegmentWitness boundary hboundaryPositive).toGoodBONG
        result.good).alphaValue
          (prefixAlphaLocalizationIndex boundary hboundaryPositive).localPivot =
        2 * (ramificationIndex K : ℚ) - 1 :=
    result.prefixSegmentAlphaValue_eq_twoE_sub_one_of_predecessor_gap_eq
      boundary hboundaryPositive htargetPreviousGap
  have hprefixSource : ∀ x ∈ b.prefixSegmentAlphaCandidates boundary,
      b.halfGapCandidate boundary ≤ x := by
    intro x hx
    have hx' : x = b.prefixSegmentAlphaCandidate boundary
        hboundaryPositive := by
      simpa only [prefixSegmentAlphaCandidates, dif_pos hboundaryPositive,
        Finset.mem_singleton] using hx
    subst x
    exact b.halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE
      boundary hboundaryPositive hsourcePrefixAlpha
  have hprefixTarget :
      ∀ x ∈ result.prefixSegmentAlphaCandidates boundary,
        result.halfGapCandidate boundary ≤ x := by
    intro x hx
    have hx' : x = result.prefixSegmentAlphaCandidate boundary
        hboundaryPositive := by
      simpa only [prefixSegmentAlphaCandidates, dif_pos hboundaryPositive,
        Finset.mem_singleton] using hx
    subst x
    apply result.halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE_sub_one
      boundary hboundaryPositive htargetGap
    exact htargetPrefixAlpha.ge
  have htargetLeftValue : result.valueUnit boundary.castSucc =
      b.valueUnit boundary.castSucc * η := by
    calc
      result.valueUnit boundary.castSucc =
          lemma714TypeIITargetValues b s D.two_le
            (Classical.choose hII) ε η boundary.castSucc :=
        hvalues boundary.castSucc
      _ = lemma712TargetValues
          (b.valueUnit ⟨s, Classical.choose hII⟩) ε η 2 := by
        simpa [boundary, hsCurrent] using
          (lemma714TypeIITargetValues_two b s D.two_le
            (Classical.choose hII) ε η)
      _ = b.valueUnit boundary.castSucc * η := by
        simpa [boundary, hsCurrent] using
          (lemma712TargetValues_two
            (b.valueUnit ⟨s, Classical.choose hII⟩) ε η)
  have htargetRightValue : result.valueUnit boundary.succ =
      b.valueUnit boundary.succ :=
    (htail boundary.succ (by simp)).symm
  have hproduct : result.adjacentProduct boundary =
      b.adjacentProduct boundary * η := by
    unfold adjacentProduct
    rw [htargetLeftValue, htargetRightValue]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (mul_neg η
        (b.valueUnit boundary.castSucc * b.valueUnit boundary.succ)).symm
  let threshold : WithTop ℚ :=
    (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)
  by_cases hsmall : b.adjacentDefect boundary < threshold
  · have hsmallEta : defectOrder (K := K) (b.adjacentProduct boundary) <
        defectOrder (K := K) η := by
      simpa only [adjacentDefect, threshold, hηDefect] using hsmall
    have hdefectProduct :=
      defectOrder_mul_eq_left_of_lt_right (K := K) hsmallEta
    have hdefect : b.adjacentDefect boundary =
        result.adjacentDefect boundary := by
      unfold adjacentDefect
      rw [hproduct, hdefectProduct]
    have hlocal : b.leftDefectCandidate boundary boundary =
        result.leftDefectCandidate boundary boundary := by
      unfold leftDefectCandidate
      rw [hcurrent, hnextOrder, hdefect]
    simpa only [boundary] using
      b.alpha_eq_of_boundary_local_eq result boundary hcurrent htail
        hprefixSource hprefixTarget hlocal
  · have hsourceDefect : threshold ≤ b.adjacentDefect boundary :=
      le_of_not_gt hsmall
    have htargetDefect : threshold ≤ result.adjacentDefect boundary := by
      have hdom := defectOrder_mul_ge_min (K := K)
        (b.adjacentProduct boundary) η
      have hdom' : min (b.adjacentDefect boundary) threshold ≤
          result.adjacentDefect boundary := by
        simpa only [adjacentDefect, threshold, hηDefect, hproduct] using hdom
      rw [min_eq_right hsourceDefect] at hdom'
      exact hdom'
    have hlocalSource : b.halfGapCandidate boundary ≤
        b.leftDefectCandidate boundary boundary :=
      b.halfGapCandidate_le_leftDefectCandidate_self_of_typeII_bounds
        boundary hsourceGap hsourceDefect
    have hlocalTarget : result.halfGapCandidate boundary ≤
        result.leftDefectCandidate boundary boundary :=
      result.halfGapCandidate_le_leftDefectCandidate_self_of_typeII_bounds
        boundary htargetGap htargetDefect
    simpa only [boundary] using
      b.alpha_eq_of_boundary_local_dominated result boundary hcurrent htail
        hprefixSource hprefixTarget hlocalSource hlocalTarget

end BONG.GoodBONG

end Bong
