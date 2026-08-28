/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTrigger
import Bong.Bong.Beli2019Lemma79CentralBoundary
import Bong.Bong.Beli2019Lemma79RightTailSource
import Bong.Bong.Beli2019Lemma216Complete
import Bong.Bong.Beli2019Lemma79PointwiseComplete

/-!
# Beli (2019), Lemma 7.9(iii): the common right suffix

After the last unequal order of the source BONG `a` and the index-`p`
target BONG `b`, Lemma 6.3 identifies every comparison alpha with the
corresponding target alpha.  Remark 6.16 transfers the two mixed defects
needed by the revised central trigger.  The two alternatives of Lemma 2.18
then activate exactly one of the two Lemma 1.5 certificates.

This is the uniform part of cases 4 and 10, away from the first common
boundary.  The nonterminal and full-prefix endpoints are exposed as
separate theorems because the second Lemma 2.18 alternative is closed in
different ways there.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- On a common right suffix, a strict sum of two adjacent target alphas
activates the original central trigger for `(a,b)`. -/
theorem centralAlphaTrigger_of_rightSuffixAlphaSum
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hdefectAB : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hsuffix : ∀ k, i.val - 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩) :
    a.centralAlphaTrigger b i := by
  let previousIdx : RepresentationIndex (n + 2) (n + 2) := i.previous
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  have hpreviousSuffix : ∀ k, previousIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simpa only [previousIdx, CentralRepresentationIndex.previous] using hk
    · exact hkn
  have hcurrentSuffix : ∀ k, currentIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simp only [currentIdx, CentralRepresentationIndex.current] at hk ⊢
      omega
    · exact hkn
  have hprevious := a.beli2019Lemma63_sameRank_right_value
    b hdefectAB previousIdx hpreviousSuffix
  have hcurrent := a.beli2019Lemma63_sameRank_right_value
    b hdefectAB currentIdx hcurrentSuffix
  have hmiddleEntry := hsuffix (i.val - 1) le_rfl (by
    have := i.lt_large
    omega)
  have hcurrentEntry := hsuffix i.val (by omega) i.lt_large
  have hmiddleOrder :
      a.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hmiddleEntry
  have hcurrentOrder :
      a.order ⟨i.val, i.lt_large⟩ = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentEntry
  apply a.centralAlphaTrigger_of_targetAlphaPair b i
  · change a.representationAlphaValue b i.previous = _
    dsimp only [previousIdx] at hprevious
    convert hprevious using 1
    congr 1
  · simpa only [currentIdx, CentralRepresentationIndex.current] using hcurrent
  · exact hmiddleOrder
  · exact hcurrentOrder
  · exact hsum

/-- The revised central trigger transfers from `(b,c)` to `(a,c)` on a
common right suffix.  The two component defects are compared separately by
Remark 6.16. -/
theorem centralAlphaTrigger_transfer_of_rightSuffix
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hsuffix : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htriggerBC : b.centralAlphaTrigger c i) :
    a.centralAlphaTrigger c i := by
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  have hcurrentSuffix : ∀ k, currentIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simpa only [currentIdx, CentralRepresentationIndex.current] using hk
    · exact hkn
  have hcurrentAlpha := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition currentIdx hcurrentSuffix
  have hpreviousTransfer :
      b.centralPreviousDefect c i ≤ a.centralPreviousDefect c i := by
    unfold centralPreviousDefect
    simpa only [currentIdx, CentralRepresentationIndex.current] using
      (truncatedPrefixDefect_le_source_of_rightAlpha
        a b c hab.defectCondition currentIdx hcurrentAlpha (-1) (i.val - 2))
  have hcurrentTransfer :
      b.centralCurrentDefect c i ≤ a.centralCurrentDefect c i := by
    by_cases hfull : i.val + 1 = n + 2
    · unfold centralCurrentDefect
      simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change
          a b c (-1) (i.val - 1)).le
    · have hiNext : i.val + 1 < n + 2 := by
        have := i.lt_large
        omega
      let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 1, by omega, hiNext, hiNext.le⟩
      have hnextSuffix : ∀ k, nextIdx.val ≤ k → k < n + 2 →
          a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
        intro k hk hkn
        apply hsuffix k
        · simp only [nextIdx] at hk ⊢
          omega
        · exact hkn
      have hnextAlpha := a.beli2019Lemma63_sameRank_right_value
        b hab.defectCondition nextIdx hnextSuffix
      unfold centralCurrentDefect
      simpa only [nextIdx] using
        (truncatedPrefixDefect_le_source_of_rightAlpha
          a b c hab.defectCondition nextIdx hnextAlpha (-1) (i.val - 1))
  have hcurrentEntry := hsuffix i.val le_rfl i.lt_large
  have hcurrentOrder :
      a.order ⟨i.val, i.lt_large⟩ = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentEntry
  have hdefectTriggerBC : b.centralDefectTrigger c i :=
    ((b.beli2019Lemma216 c le_rfl horderBC hdefectBC) i).mp htriggerBC
  have hdefectTriggerAC : a.centralDefectTrigger c i := by
    unfold centralDefectTrigger at hdefectTriggerBC ⊢
    rcases hdefectTriggerBC with ⟨horder, hdefects⟩
    constructor
    · rw [hcurrentOrder]
      exact horder
    · rw [hcurrentOrder]
      exact hdefects.trans_le
        (add_le_add hpreviousTransfer hcurrentTransfer)
  exact ((a.beli2019Lemma216 c le_rfl hac.orderCondition
    hac.defectCondition) i).mpr hdefectTriggerAC

/-- Cases 4 and 10 on a strict common suffix.  Lemma 2.18 chooses the
first or second four-space diagram; the adjacent-alpha trigger for that
diagram is forced by P6. -/
theorem lemma79CentralCertificate_of_rightSuffix
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hsuffix : ∀ k, i.val - 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a b c i := by
  have hiOne : 1 < i.val := i.one_lt
  have hiLarge : i.val < n + 2 := i.lt_large
  have hiAlphaNext : i.val < n + 1 := by omega
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNext, hiNext.le⟩
  let j : CentralRepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by
      have := hiOne
      omega, hiNext, by
      have := hiNext
      omega⟩
  have hcurrentSuffix : ∀ k, currentIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simp only [currentIdx, CentralRepresentationIndex.current] at hk ⊢
      omega
    · exact hkn
  have hnextSuffix : ∀ k, nextIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simp only [nextIdx] at hk ⊢
      omega
    · exact hkn
  have hcurrentAlpha := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition currentIdx hcurrentSuffix
  have hnextAlpha := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition nextIdx hnextSuffix
  have hbeta : b.prefixAlphaCap i.val ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large]
    have hraw := hab.defectCondition currentIdx
    rw [hcurrentAlpha] at hraw
    simpa only [currentIdx, CentralRepresentationIndex.current] using hraw
  have hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i := by
    unfold centralCurrentDefect
    simpa only [nextIdx] using
      (truncatedPrefixDefect_le_source_of_rightAlpha
        a b c hab.defectCondition nextIdx hnextAlpha (-1) (i.val - 1))
  have htriggerAC : a.centralAlphaTrigger c i :=
    a.centralAlphaTrigger_transfer_of_rightSuffix b c hab hac horderBC
      hdefectBC i (by
        intro k hk hkn
        exact hsuffix k (by omega) hkn) htriggerBC
  apply Lemma79CentralCertificate.of_lemma218_target_by_cases
    hab hac hdefectBC i htriggerBC hbeta hcurrentTransfer htriggerAC
      j rfl
  · intro hfirst
    have hpreviousBound : b.representationAlpha c i.previous ≤
        (b.alphaValue ⟨i.val - 2, by
          have := hiOne
          have := hiLarge
          omega⟩ : WithTop ℚ) := by
      calc
        b.representationAlpha c i.previous =
            (b.representationAlphaValue c i.previous : WithTop ℚ) := by
              rw [b.coe_representationAlphaValue c i.previous]
        _ ≤ b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) :=
          hdefectBC i.previous
        _ ≤ b.prefixAlphaCap (i.val - 1) :=
          b.truncatedPrefixDefect_le_leftCap c 1 (i.val - 1) (i.val - 1)
        _ = (b.alphaValue ⟨i.val - 2, by
            have := hiOne
            have := hiLarge
            omega⟩ : WithTop ℚ) := by
          rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
          congr 2
    have hcurrentCap : b.prefixAlphaCap i.val =
        (b.alphaValue ⟨i.val - 1, by
          have := hiLarge
          omega⟩ : WithTop ℚ) :=
      b.prefixAlphaCap_of_internal (by omega) i.lt_large
    have hsumTop :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) +
            (b.alphaValue ⟨i.val - 2, by omega⟩ : WithTop ℚ) := by
      exact hfirst.trans_le (add_le_add hcurrentCap.le hpreviousBound)
    have hsum : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 2, by omega⟩ +
          b.alphaValue ⟨i.val - 1, by omega⟩ := by
      rw [add_comm] at hsumTop
      exact_mod_cast hsumTop
    exact a.centralAlphaTrigger_of_rightSuffixAlphaSum
      b hab.defectCondition i hsuffix hsum
  · intro hsecond
    have hcurrentBound : b.centralCurrentDefect c i ≤
        (b.alphaValue ⟨i.val, hiAlphaNext⟩ : WithTop ℚ) := by
      unfold centralCurrentDefect
      calc
        b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
            b.prefixAlphaCap (i.val + 1) :=
          b.truncatedPrefixDefect_le_leftCap c (-1)
            (i.val + 1) (i.val - 1)
        _ = (b.alphaValue ⟨i.val, hiAlphaNext⟩ : WithTop ℚ) := by
          rw [b.prefixAlphaCap_of_internal (by omega) hiNext]
          congr 2
    have hcurrentCap : b.prefixAlphaCap i.val =
        (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) :=
      b.prefixAlphaCap_of_internal (by omega) i.lt_large
    have hsumTop :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) +
            (b.alphaValue ⟨i.val, hiAlphaNext⟩ : WithTop ℚ) := by
      exact hsecond.trans_le (add_le_add hcurrentCap.le hcurrentBound)
    have hsum : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨j.val - 2, by
          have := j.one_lt
          have := j.lt_large
          omega⟩ +
          b.alphaValue ⟨j.val - 1, by
            have := j.lt_large
            omega⟩ := by
      simp only [j]
      exact_mod_cast hsumTop
    have hjSuffix : ∀ k, j.val - 1 ≤ k → k < n + 2 →
        a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
      intro k hk hkn
      apply hsuffix k
      · simp only [j] at hk ⊢
        omega
      · exact hkn
    exact a.centralAlphaTrigger_of_rightSuffixAlphaSum
      b hab.defectCondition j hjSuffix hsum

/-- The terminal common-suffix case.  The first Lemma 2.18 alternative is
identical to the nonterminal argument.  In the second alternative the
`(i+1)`-prefix is the complete BONG, so the concrete full-BONG coordinate
change supplies the middle representation and no next central boundary is
needed. -/
theorem lemma79CentralCertificate_of_rightSuffix_endpoint
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfull : i.val + 1 = n + 2)
    (hsuffix : ∀ k, i.val - 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a b c i := by
  have hiOne : 1 < i.val := i.one_lt
  have hiLarge : i.val < n + 2 := i.lt_large
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  have hcurrentSuffix : ∀ k, currentIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simp only [currentIdx, CentralRepresentationIndex.current] at hk ⊢
      omega
    · exact hkn
  have hcurrentAlpha := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition currentIdx hcurrentSuffix
  have hbeta : b.prefixAlphaCap i.val ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large]
    have hraw := hab.defectCondition currentIdx
    rw [hcurrentAlpha] at hraw
    simpa only [currentIdx, CentralRepresentationIndex.current] using hraw
  have hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i := by
    unfold centralCurrentDefect
    simpa only [hfull] using
      (truncatedPrefixDefect_fullLeft_change
        a b c (-1) (i.val - 1)).le
  have htriggerAC : a.centralAlphaTrigger c i :=
    a.centralAlphaTrigger_transfer_of_rightSuffix b c hab hac horderBC
      hdefectBC i (by
        intro k hk hkn
        exact hsuffix k (by omega) hkn) htriggerBC
  apply Lemma79CentralCertificate.of_lemma218_target_endpoint
    hab hac hdefectBC i hfull htriggerBC hbeta hcurrentTransfer htriggerAC
  intro hfirst
  have hpreviousBound : b.representationAlpha c i.previous ≤
      (b.alphaValue ⟨i.val - 2, by
        have := hiOne
        have := hiLarge
        omega⟩ : WithTop ℚ) := by
    calc
      b.representationAlpha c i.previous =
          (b.representationAlphaValue c i.previous : WithTop ℚ) := by
            rw [b.coe_representationAlphaValue c i.previous]
      _ ≤ b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) :=
        hdefectBC i.previous
      _ ≤ b.prefixAlphaCap (i.val - 1) :=
        b.truncatedPrefixDefect_le_leftCap c 1 (i.val - 1) (i.val - 1)
      _ = (b.alphaValue ⟨i.val - 2, by
          have := hiOne
          have := hiLarge
          omega⟩ : WithTop ℚ) := by
        rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
        congr 2
  have hcurrentCap : b.prefixAlphaCap i.val =
      (b.alphaValue ⟨i.val - 1, by
        have := hiLarge
        omega⟩ : WithTop ℚ) :=
    b.prefixAlphaCap_of_internal (by omega) i.lt_large
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) +
          (b.alphaValue ⟨i.val - 2, by omega⟩ : WithTop ℚ) := by
    exact hfirst.trans_le (add_le_add hcurrentCap.le hpreviousBound)
  have hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by omega⟩ +
        b.alphaValue ⟨i.val - 1, by omega⟩ := by
    rw [add_comm] at hsumTop
    exact_mod_cast hsumTop
  exact a.centralAlphaTrigger_of_rightSuffixAlphaSum
    b hab.defectCondition i hsuffix hsum

/-- The first common boundary, nonterminal form.  Equality of orders starts
at `i`, rather than at `i-1`.  Consequently the second Lemma 2.18
alternative is still forced uniformly by the adjacent target alphas, while
the first alternative asks only for the single profile-specific boundary
trigger proved separately in cases 4 and 10. -/
theorem lemma79CentralCertificate_of_rightSuffix_boundary
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hsuffix : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htriggerBC : b.centralAlphaTrigger c i)
    (hfirstBoundary :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap i.val + b.representationAlpha c i.previous →
        a.centralAlphaTrigger b i) :
    Lemma79CentralCertificate a b c i := by
  have hiLarge : i.val < n + 2 := i.lt_large
  have hiAlphaNext : i.val < n + 1 := by omega
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNext, hiNext.le⟩
  let j : CentralRepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by
      have := i.one_lt
      omega, hiNext, by
      have := hiNext
      omega⟩
  have hcurrentSuffix : ∀ k, currentIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simpa only [currentIdx, CentralRepresentationIndex.current] using hk
    · exact hkn
  have hnextSuffix : ∀ k, nextIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simp only [nextIdx] at hk ⊢
      omega
    · exact hkn
  have hcurrentAlpha := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition currentIdx hcurrentSuffix
  have hnextAlpha := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition nextIdx hnextSuffix
  have hbeta : b.prefixAlphaCap i.val ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large]
    have hraw := hab.defectCondition currentIdx
    rw [hcurrentAlpha] at hraw
    simpa only [currentIdx, CentralRepresentationIndex.current] using hraw
  have hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i := by
    unfold centralCurrentDefect
    simpa only [nextIdx] using
      (truncatedPrefixDefect_le_source_of_rightAlpha
        a b c hab.defectCondition nextIdx hnextAlpha (-1) (i.val - 1))
  have htriggerAC : a.centralAlphaTrigger c i :=
    a.centralAlphaTrigger_transfer_of_rightSuffix b c hab hac horderBC
      hdefectBC i hsuffix htriggerBC
  apply Lemma79CentralCertificate.of_lemma218_target_by_cases
    hab hac hdefectBC i htriggerBC hbeta hcurrentTransfer htriggerAC
      j rfl hfirstBoundary
  intro hsecond
  have hcurrentBound : b.centralCurrentDefect c i ≤
      (b.alphaValue ⟨i.val, hiAlphaNext⟩ : WithTop ℚ) := by
    unfold centralCurrentDefect
    calc
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
          b.prefixAlphaCap (i.val + 1) :=
        b.truncatedPrefixDefect_le_leftCap c (-1)
          (i.val + 1) (i.val - 1)
      _ = (b.alphaValue ⟨i.val, hiAlphaNext⟩ : WithTop ℚ) := by
        rw [b.prefixAlphaCap_of_internal (by omega) hiNext]
        congr 2
  have hcurrentCap : b.prefixAlphaCap i.val =
      (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) :=
    b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) +
          (b.alphaValue ⟨i.val, hiAlphaNext⟩ : WithTop ℚ) := by
    exact hsecond.trans_le (add_le_add hcurrentCap.le hcurrentBound)
  have hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨j.val - 2, by
        have := j.one_lt
        have := j.lt_large
        omega⟩ +
        b.alphaValue ⟨j.val - 1, by
          have := j.lt_large
          omega⟩ := by
    simp only [j]
    exact_mod_cast hsumTop
  have hjSuffix : ∀ k, j.val - 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simp only [j] at hk ⊢
      omega
    · exact hkn
  exact a.centralAlphaTrigger_of_rightSuffixAlphaSum
    b hab.defectCondition j hjSuffix hsum

/-- The first common boundary when `i+1` is the complete BONG.  The second
Lemma 2.18 alternative is closed by full-BONG coordinate change, so only the
profile-specific first-alternative trigger remains. -/
theorem lemma79CentralCertificate_of_rightSuffix_boundary_endpoint
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfull : i.val + 1 = n + 2)
    (hsuffix : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htriggerBC : b.centralAlphaTrigger c i)
    (hfirstBoundary :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap i.val + b.representationAlpha c i.previous →
        a.centralAlphaTrigger b i) :
    Lemma79CentralCertificate a b c i := by
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  have hcurrentSuffix : ∀ k, currentIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hsuffix k
    · simpa only [currentIdx, CentralRepresentationIndex.current] using hk
    · exact hkn
  have hcurrentAlpha := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition currentIdx hcurrentSuffix
  have hbeta : b.prefixAlphaCap i.val ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    rw [b.prefixAlphaCap_of_internal (by omega) i.lt_large]
    have hraw := hab.defectCondition currentIdx
    rw [hcurrentAlpha] at hraw
    simpa only [currentIdx, CentralRepresentationIndex.current] using hraw
  have hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i := by
    unfold centralCurrentDefect
    simpa only [hfull] using
      (truncatedPrefixDefect_fullLeft_change
        a b c (-1) (i.val - 1)).le
  have htriggerAC : a.centralAlphaTrigger c i :=
    a.centralAlphaTrigger_transfer_of_rightSuffix b c hab hac horderBC
      hdefectBC i hsuffix htriggerBC
  exact Lemma79CentralCertificate.of_lemma218_target_endpoint
    hab hac hdefectBC i hfull htriggerBC hbeta hcurrentTransfer htriggerAC
      hfirstBoundary

/-- The paper's condition `i > u`, expressed uniformly for the three
normalized Lemma 6.7 profiles.  Since the stored coordinates are zero-based,
`u` is one more than the last unequal coordinate. -/
def Lemma79NormalizedClassification.IsStrictCommonSuffixAt
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (_D : Lemma79NormalizedClassification a b)
    (i : CentralRepresentationIndex (n + 2) (n + 2)) : Prop :=
  ∃ last, BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last ∧ last + 1 < i.val

/-- The paper's first common boundary `i = u`, again with the one-based
paper index translated to the zero-based last unequal coordinate. -/
def Lemma79NormalizedClassification.IsFirstCommonBoundaryAt
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (_D : Lemma79NormalizedClassification a b)
    (i : CentralRepresentationIndex (n + 2) (n + 2)) : Prop :=
  ∃ last, BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last ∧ i.val = last + 1

/-- Profile-facing form of the common-suffix certificate.  This discharges
the strict `i > u` portions of cases 4 and 10 simultaneously for all three
normalized types. -/
theorem Lemma79NormalizedClassification.centralCertificate_of_strictCommonSuffix
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (htail : D.IsStrictCommonSuffixAt i)
    (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a b c i := by
  rcases htail with ⟨last, hlast, hstrict⟩
  apply lemma79CentralCertificate_of_rightSuffix
    a b c hab hac horderBC hdefectBC i hiNext
  · intro k hk hkn
    exact hlast.after k (by omega) hkn
  · exact htriggerBC

/-- Profile-facing terminal form of the strict common-suffix certificate. -/
theorem Lemma79NormalizedClassification.centralCertificate_of_strictCommonSuffix_endpoint
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfull : i.val + 1 = n + 2)
    (htail : D.IsStrictCommonSuffixAt i)
    (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a b c i := by
  rcases htail with ⟨last, hlast, hstrict⟩
  apply lemma79CentralCertificate_of_rightSuffix_endpoint
    a b c hab hac horderBC hdefectBC i hfull
  · intro k hk hkn
    exact hlast.after k (by omega) hkn
  · exact htriggerBC

/-- Profile-facing first-common-boundary certificate, nonterminal form.  The
three profile-specific boundary estimates are selected internally. -/
theorem Lemma79NormalizedClassification.centralCertificate_of_firstCommonBoundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hboundary : D.IsFirstCommonBoundaryAt i)
    (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a b c i := by
  rcases hboundary with ⟨last, hlast, hboundary⟩
  apply lemma79CentralCertificate_of_rightSuffix_boundary
    a b c hab hac horderBC hdefectBC i hiNext
  · intro k hk hkn
    exact hlast.after k (by omega) hkn
  · exact htriggerBC
  · exact D.firstBoundary_trigger hab hdefectBC htotal i last hlast
      hboundary

/-- Profile-facing first-common-boundary certificate at the full endpoint. -/
theorem Lemma79NormalizedClassification.centralCertificate_of_firstCommonBoundary_endpoint
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfull : i.val + 1 = n + 2)
    (hboundary : D.IsFirstCommonBoundaryAt i)
    (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a b c i := by
  rcases hboundary with ⟨last, hlast, hboundary⟩
  apply lemma79CentralCertificate_of_rightSuffix_boundary_endpoint
    a b c hab hac horderBC hdefectBC i hfull
  · intro k hk hkn
    exact hlast.after k (by omega) hkn
  · exact htriggerBC
  · exact D.firstBoundary_trigger hab hdefectBC htotal i last hlast
      hboundary

end BONG.GoodBONG

end Bong
