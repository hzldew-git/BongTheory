/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715AlphaCommon

/-!
# Beli (2019), Lemma 7.15: the type-I boundary alpha

In type I the coefficient at the stopping index and the entire strict suffix
are unchanged.  Hence the local adjacent defect at the first relevant alpha
is unchanged.  The preceding order gaps in both BONGs are at least `2e`, so
the two prefix-alpha terms are dominated by the common half-gap term.
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

/-- The boundary equality `alpha_(s+1) = beta_(s+1)` in the type-I
branch, translated to zero-based alpha index `s`. -/
theorem lemma715_typeI_boundary_alpha_eq
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI b R s)
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeITargetValues b s D.two_le D.le_rank i)
    (hsBoundary : s + 2 ≤ n + 3) :
    b.alpha ⟨s, by omega⟩ = result.alpha ⟨s, by omega⟩ := by
  let boundary : Fin (n + 2) := ⟨s, by omega⟩
  have hsPositive : 0 < s := lt_of_lt_of_le (by omega) D.two_le
  have hboundaryPositive : 0 < boundary.val := by
    simpa [boundary] using hsPositive
  have hsInterior : s < n + 3 := by omega
  have hnext : R + 2 ≤ b.order ⟨s, hsInterior⟩ :=
    b.lemma714_typeI_nextOrder_ge R s hI hsInterior
  have hcurrent : b.order boundary.castSucc =
      result.order boundary.castSucc := by
    exact lemma715_typeI_order_eq b s D.two_le D.le_rank result
      hvalues boundary.castSucc (by simp [boundary])
  have htail : ∀ j : Fin (n + 3), boundary.val < j.val →
      b.valueUnit j = result.valueUnit j := by
    intro j hj
    calc
      b.valueUnit j = lemma714TypeITargetValues
          b s D.two_le D.le_rank j :=
        (lemma714TypeITargetValues_suffix b s D.two_le D.le_rank j
          (by simpa [boundary] using hj.le)).symm
      _ = result.valueUnit j := (hvalues j).symm
  have hleftValue : b.valueUnit boundary.castSucc =
      result.valueUnit boundary.castSucc := by
    calc
      b.valueUnit boundary.castSucc = lemma714TypeITargetValues
          b s D.two_le D.le_rank boundary.castSucc :=
        (lemma714TypeITargetValues_suffix b s D.two_le D.le_rank
          boundary.castSucc (by simp [boundary])).symm
      _ = result.valueUnit boundary.castSucc :=
        (hvalues boundary.castSucc).symm
  have hrightValue : b.valueUnit boundary.succ =
      result.valueUnit boundary.succ :=
    htail boundary.succ (by simp)
  have hlocal : b.leftDefectCandidate boundary boundary =
      result.leftDefectCandidate boundary boundary :=
    b.leftDefectCandidate_self_eq_of_pair_valueUnits_eq result boundary
      hleftValue hrightValue
  have hsourcePreviousGap :
      2 * (ramificationIndex K : Int) ≤
        b.order boundary.castSucc -
          b.order ⟨boundary.val - 1, by omega⟩ := by
    by_cases hsTwo : s = 2
    · have hprevious :
          b.order ⟨boundary.val - 1, by omega⟩ =
            R - 2 * (ramificationIndex K : Int) := by
        simpa [boundary, hsTwo] using hsecond
      have hcurrentLower : R + 2 ≤ b.order boundary.castSucc := by
        simpa [boundary] using hnext
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
      have hcurrentLower : R + 2 ≤ b.order boundary.castSucc := by
        simpa [boundary] using hnext
      omega
  have htargetPreviousOrder :
      result.order ⟨boundary.val - 1, by omega⟩ =
        R - 2 * (ramificationIndex K : Int) + 2 := by
    have hpi : ordUnit K (uniformizerUnit K) = 1 := by
      simpa [uniformizerPowerUnit] using
        (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
    calc
      result.order ⟨boundary.val - 1, by omega⟩ =
          ordUnit K (result.valueUnit
            ⟨boundary.val - 1, by omega⟩) :=
        result.toBONG.order_eq_ordUnit _
      _ = ordUnit K (lemma714TypeITargetValues
          b s D.two_le D.le_rank
            ⟨boundary.val - 1, by omega⟩) :=
        congrArg (ordUnit K) (hvalues _)
      _ = ordUnit K (uniformizerUnit K ^ 2 * b.valueUnit 1) := by
        congr 1
        simpa [boundary] using
          (lemma714TypeITargetValues_one b s D.two_le D.le_rank)
      _ = 2 + b.order ⟨1, by omega⟩ := by
        have hb1 : ordUnit K (b.valueUnit (1 : Fin (n + 3))) =
            b.order (1 : Fin (n + 3)) :=
          (b.toBONG.order_eq_ordUnit (1 : Fin (n + 3))).symm
        rw [ordUnit_mul, ordUnit_pow, hpi, hb1]
        norm_num
      _ = R - 2 * (ramificationIndex K : Int) + 2 := by
        rw [hsecond]
        ring
  have htargetPreviousGap :
      2 * (ramificationIndex K : Int) ≤
        result.order boundary.castSucc -
          result.order ⟨boundary.val - 1, by omega⟩ := by
    have hcurrentLower : R + 2 ≤ result.order boundary.castSucc := by
      rw [← hcurrent]
      simpa [boundary] using hnext
    omega
  have hsourcePrefixAlpha : 2 * (ramificationIndex K : ℚ) ≤
      ((b.prefixAlphaSegmentWitness boundary hboundaryPositive).toGoodBONG
        b.good).alphaValue
        (prefixAlphaLocalizationIndex boundary hboundaryPositive).localPivot :=
    b.prefixSegmentAlphaValue_ge_twoE_of_predecessor_gap boundary
      hboundaryPositive hsourcePreviousGap
  have htargetPrefixAlpha : 2 * (ramificationIndex K : ℚ) ≤
      ((result.prefixAlphaSegmentWitness boundary hboundaryPositive).toGoodBONG
        result.good).alphaValue
        (prefixAlphaLocalizationIndex boundary hboundaryPositive).localPivot :=
    result.prefixSegmentAlphaValue_ge_twoE_of_predecessor_gap boundary
      hboundaryPositive htargetPreviousGap
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
    exact result.halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE
      boundary hboundaryPositive htargetPrefixAlpha
  simpa only [boundary] using
    b.alpha_eq_of_boundary_local_eq result boundary hcurrent htail
      hprefixSource hprefixTarget hlocal

end BONG.GoodBONG

end Bong
