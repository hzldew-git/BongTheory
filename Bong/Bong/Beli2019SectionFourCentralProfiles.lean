/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourLemma45Dual

/-!
# Beli (2019), Section 4: the three final central profiles

The last part of the proof of Theorem 2.1(iii) reduces every remaining
central boundary to one of three numerical profiles.  They are discharged,
respectively, by the three diagrams in Lemma 1.5; profiles two and three use
the two halves of Lemma 4.5.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-! ## The two direct tests and their order consequences -/

/-- The left boundary alternative in profiles one and three is exactly the
direct branch of Lemma 4.2(i).  The lower endpoint is vacuous. -/
theorem sectionFourLeftDirectTrigger_of_boundary
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hboundary :
      (∃ hiPrev : 2 < i.val,
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩) ∨
        i.val = 2) :
    a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex i.previous) := by
  unfold KeyLemmaLeftDirectTrigger
  intro hiTwo hiNext
  simp only [nextEssentialIndex, CentralRepresentationIndex.previous] at hiTwo hiNext ⊢
  rcases hboundary with ⟨hiPrev, hboundary⟩ | hiEndpoint
  · have houter := htrigger.1
    have hsum :
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ +
            c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ +
            b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
      omega
    have hleft : i.val - 1 - 2 = i.val - 3 := by omega
    have hright : i.val - 1 - 1 = i.val - 2 := by omega
    have hnext : i.val - 1 + 1 = i.val := by omega
    simpa only [hleft, hright, hnext] using hsum
  · omega

/-- The right boundary alternative in profiles one and two is exactly the
direct branch of Lemma 4.2(ii).  The upper endpoint is vacuous. -/
theorem sectionFourRightDirectTrigger_of_boundary
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hboundary :
      (∃ hiNext : i.val + 1 < n + 1,
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val + 1, hiNext⟩) ∨
        i.val + 1 = n + 1) :
    a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex (i.current i.lt_large.le)) := by
  unfold KeyLemmaRightDirectTrigger
  intro hiPos hiTwo
  simp only [currentEssentialIndex, CentralRepresentationIndex.current] at hiPos hiTwo ⊢
  rcases hboundary with ⟨hiNext, hboundary⟩ | hiEndpoint
  · have houter := htrigger.1
    have hsum :
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
            c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ := by
      omega
    have hprevious : i.val - 1 - 1 = i.val - 2 := by omega
    have hcurrent : i.val - 1 + 1 = i.val := by omega
    have hnext : i.val - 1 + 2 = i.val + 1 := by omega
    simpa only [hprevious, hcurrent, hnext] using hsum
  · omega

/-- The left direct test, together with condition 2.1(i) for `(b,c)`, gives
`R_(i+1) > S_(i-1)`. -/
theorem sectionFour_targetCurrent_gt_middlePrevious_of_leftDirect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hleft : a.KeyLemmaLeftDirectTrigger b c
      (nextEssentialIndex i.previous)) :
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩ := by
  let k : Fin (n + 1) := ⟨i.val - 2, by have := i.lt_large; omega⟩
  rcases hbcOrder k with hdirect | ⟨hkPos, hkNext, hpair⟩
  · have hdirect' :
        b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ ≤
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      simpa only [k, orderSequence_at] using hdirect
    exact hdirect'.trans_lt htrigger.1
  · have hiPrev : 2 < i.val := by
      dsimp only [k] at hkPos
      omega
    have hleftRaw := hleft (by
      simp only [nextEssentialIndex, CentralRepresentationIndex.previous]
      omega) (by
      simp only [nextEssentialIndex, CentralRepresentationIndex.previous]
      have := i.lt_large
      omega)
    have hleft' :
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ +
            c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ +
            b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
      simpa only [nextEssentialIndex, CentralRepresentationIndex.previous,
        Nat.sub_sub, one_add_one_eq_two,
        Nat.sub_add_cancel i.one_lt.le] using hleftRaw
    have hpair' :
        b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ +
            b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ ≤
          c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ +
            c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      have hkSucc :
          (⟨k.val + 1, hkNext⟩ : Fin (n + 1)) =
            ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        dsimp only [k]
        omega
      have hcPrevious :
          (⟨k.val - 1, by omega⟩ : Fin (n + 1)) =
            ⟨i.val - 3, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        dsimp only [k]
        omega
      simpa only [k, hkSucc, hcPrevious, orderSequence_at] using hpair
    by_contra hnot
    have hmiddle :
        a.order ⟨i.val, i.lt_large⟩ ≤
          b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ :=
      le_of_not_gt hnot
    omega

/-- The right direct test, together with condition 2.1(i) for `(a,b)`, gives
`S_(i+1) > T_(i-1)`. -/
theorem sectionFour_middleNext_gt_sourcePrevious_of_rightDirect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (habOrder : a.RepresentationOrderCondition b le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hright : a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex (i.current i.lt_large.le))) :
    c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val, i.lt_large⟩ := by
  let k : Fin (n + 1) := ⟨i.val, i.lt_large⟩
  rcases habOrder k with hdirect | ⟨hkPos, hkNext, hpair⟩
  · have hdirect' :
        a.order ⟨i.val, i.lt_large⟩ ≤
          b.order ⟨i.val, i.lt_large⟩ := by
      simpa only [k, orderSequence_at] using hdirect
    exact htrigger.1.trans_le hdirect'
  · have hrightRaw := hright (by
      simp only [currentEssentialIndex, CentralRepresentationIndex.current]
      have := i.one_lt
      omega) (by
      simp only [currentEssentialIndex, CentralRepresentationIndex.current]
      have hiNext : i.val + 1 < n + 1 := by
        simpa only [k] using hkNext
      have hval : i.val - 1 + 2 = i.val + 1 := by
        have := i.one_lt
        omega
      simpa only [hval] using hiNext)
    have hnextVal : i.val - 1 + 2 = i.val + 1 := by
      have := i.one_lt
      omega
    have hright' :
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
            c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hkNext⟩ := by
      simpa only [currentEssentialIndex, CentralRepresentationIndex.current,
        Nat.sub_sub, one_add_one_eq_two,
        Nat.sub_add_cancel i.one_lt.le, hnextVal] using hrightRaw
    have hpair' :
        a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hkNext⟩ ≤
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
            b.order ⟨i.val, i.lt_large⟩ := by
      have hkPrevious :
          (⟨k.val - 1, by omega⟩ : Fin (n + 1)) =
            ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        rfl
      have hkSucc :
          (⟨k.val + 1, hkNext⟩ : Fin (n + 1)) =
            ⟨i.val + 1, hkNext⟩ := by
        apply Fin.ext
        rfl
      simpa only [k, hkPrevious, hkSucc, orderSequence_at] using hpair
    by_contra hnot
    have hsource :
        b.order ⟨i.val, i.lt_large⟩ ≤
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ :=
      le_of_not_gt hnot
    omega

/-! ## Adjacent central triggers extracted from Lemma 4.2 -/

/-- A left direct bound and the first comparison assemble the active central
trigger for `(a,b)`. -/
theorem sectionFour_middleCentralTrigger_of_leftDirect
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hleft : a.KeyLemmaLeftDirectTrigger b c
      (nextEssentialIndex i.previous))
    (hforward :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) :
    a.centralAlphaTrigger b i := by
  have hprevious :=
    ((a.sectionFourPreviousBounds_of_centralAlphaTrigger
      b c hlocal i htrigger).1 hleft).1
  have hcross :=
    a.sectionFour_targetCurrent_gt_middlePrevious_of_leftDirect
      b c hlocal.hbcOrder i htrigger hleft
  unfold centralAlphaTrigger at htrigger ⊢
  constructor
  · exact hcross
  · have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum ⊢
    rw [dif_pos i.lt_large.le] at hsum ⊢
    rw [← a.coe_representationAlphaValue c i.previous,
      ← a.coe_representationAlphaValue b i.previous] at hprevious
    rw [← a.coe_representationAlphaValue c (i.current i.lt_large.le),
      ← a.coe_representationAlphaValue b (i.current i.lt_large.le)] at hforward
    norm_cast at hsum hprevious hforward ⊢
    push_cast at hsum hprevious hforward ⊢
    linarith

/-- A right direct bound and the reverse first comparison assemble the active
central trigger for `(b,c)`. -/
theorem sectionFour_sourceCentralTrigger_of_rightDirect
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hright : a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex (i.current i.lt_large.le)))
    (hbackward :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous) :
    b.centralAlphaTrigger c i := by
  have hcurrent :=
    ((a.sectionFourCurrentBounds_of_centralAlphaTrigger
      b c hlocal i htrigger).1 hright).2
  have hcross :=
    a.sectionFour_middleNext_gt_sourcePrevious_of_rightDirect
      b c hlocal.habOrder i htrigger hright
  unfold centralAlphaTrigger at htrigger ⊢
  constructor
  · exact hcross
  · have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum ⊢
    rw [dif_pos i.lt_large.le] at hsum ⊢
    rw [← a.coe_representationAlphaValue c
      (i.current i.lt_large.le),
      ← b.coe_representationAlphaValue c
        (i.current i.lt_large.le)] at hcurrent
    rw [← a.coe_representationAlphaValue c i.previous,
      ← b.coe_representationAlphaValue c i.previous] at hbackward
    norm_cast at hsum hcurrent hbackward ⊢
    push_cast at hsum hcurrent hbackward ⊢
    linarith

/-! ## The three parity profiles -/

/-- Direct-trigger form of profile 1.  This is the form needed in the last
subcase of Section 4, where Lemma 4.2 has already supplied both direct
triggers and no stronger neighbouring-order boundary is available. -/
theorem sectionFourCentralCertificate_of_profileOne_direct
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hleft : a.KeyLemmaLeftDirectTrigger b c
      (nextEssentialIndex i.previous))
    (hright : a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex (i.current i.lt_large.le)))
    (hforward :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le))
    (hbackward :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous) :
    CentralRepresentationCertificate a b c i := by
  let hlocal := SectionFourLocalConditions.ofRepresentationConditions
    a b c hab hbc
  have htriggerAB := a.sectionFour_middleCentralTrigger_of_leftDirect
    b c hlocal i htrigger hleft hforward
  have htriggerBC := a.sectionFour_sourceCentralTrigger_of_rightDirect
    b c hlocal i htrigger hright hbackward
  have hmiddle := hab.centralRepresentations i htriggerAB
  have hsource := hbc.centralRepresentations i htriggerBC
  apply CentralRepresentationCertificate.of_caseI_truncatedDefects
    hmiddle hsource
  have hsumAlpha :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.representationAlpha b (i.current i.lt_large.le) +
          b.representationAlpha c i.previous := by
    have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos i.lt_large.le] at hsum
    rw [← a.coe_representationAlphaValue c
      (i.current i.lt_large.le),
      ← a.coe_representationAlphaValue b
        (i.current i.lt_large.le)] at hforward
    rw [← a.coe_representationAlphaValue c i.previous,
      ← b.coe_representationAlphaValue c i.previous] at hbackward
    rw [← a.coe_representationAlphaValue b
      (i.current i.lt_large.le),
      ← b.coe_representationAlphaValue c i.previous]
    norm_cast at hsum hforward hbackward ⊢
    push_cast at hsum hforward hbackward ⊢
    linarith
  have habBound := hab.defectCondition (i.current i.lt_large.le)
  have hbcBound := hbc.defectCondition i.previous
  rw [a.coe_representationAlphaValue b
    (i.current i.lt_large.le)] at habBound
  rw [b.coe_representationAlphaValue c i.previous] at hbcBound
  apply hsumAlpha.trans_le
  simpa only [CentralRepresentationIndex.current,
    CentralRepresentationIndex.previous, one_mul] using
      add_le_add habBound hbcBound

/-- Profile 1 in the paper: both direct Lemma 4.2 bounds are available, and
the two first comparisons feed Lemma 1.5(i). -/
theorem sectionFourCentralCertificate_of_profileOne
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hleftBoundary :
      (∃ hiPrev : 2 < i.val,
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩) ∨
        i.val = 2)
    (hrightBoundary :
      (∃ hiNext : i.val + 1 < n + 1,
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val + 1, hiNext⟩) ∨
        i.val + 1 = n + 1)
    (hforward :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le))
    (hbackward :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous) :
    CentralRepresentationCertificate a b c i := by
  let hlocal := SectionFourLocalConditions.ofRepresentationConditions
    a b c hab hbc
  have hleft := a.sectionFourLeftDirectTrigger_of_boundary
    b c i htrigger hleftBoundary
  have hright := a.sectionFourRightDirectTrigger_of_boundary
    b c i htrigger hrightBoundary
  have htriggerAB := a.sectionFour_middleCentralTrigger_of_leftDirect
    b c hlocal i htrigger hleft hforward
  have htriggerBC := a.sectionFour_sourceCentralTrigger_of_rightDirect
    b c hlocal i htrigger hright hbackward
  have hmiddle := hab.centralRepresentations i htriggerAB
  have hsource := hbc.centralRepresentations i htriggerBC
  apply CentralRepresentationCertificate.of_caseI_truncatedDefects
    hmiddle hsource
  have hsumAlpha :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.representationAlpha b (i.current i.lt_large.le) +
          b.representationAlpha c i.previous := by
    have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos i.lt_large.le] at hsum
    rw [← a.coe_representationAlphaValue c
      (i.current i.lt_large.le),
      ← a.coe_representationAlphaValue b
        (i.current i.lt_large.le)] at hforward
    rw [← a.coe_representationAlphaValue c i.previous,
      ← b.coe_representationAlphaValue c i.previous] at hbackward
    rw [← a.coe_representationAlphaValue b
      (i.current i.lt_large.le),
      ← b.coe_representationAlphaValue c i.previous]
    norm_cast at hsum hforward hbackward ⊢
    push_cast at hsum hforward hbackward ⊢
    linarith
  have habBound := hab.defectCondition (i.current i.lt_large.le)
  have hbcBound := hbc.defectCondition i.previous
  rw [a.coe_representationAlphaValue b
    (i.current i.lt_large.le)] at habBound
  rw [b.coe_representationAlphaValue c i.previous] at hbcBound
  apply hsumAlpha.trans_le
  simpa only [CentralRepresentationIndex.current,
    CentralRepresentationIndex.previous, one_mul] using
      add_le_add habBound hbcBound

/-- Profile 2 in the paper: the right direct bound activates the `(b,c)`
central representation, while Lemma 4.5(i) supplies the extended `(a,b)`
representation and its Hilbert symbol. -/
theorem sectionFourCentralCertificate_of_profileTwo
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hboundary :
      (∃ hiNext : i.val + 1 < n + 1,
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val + 1, hiNext⟩) ∨
        i.val + 1 = n + 1)
    (hbackward :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous)
    (hshift :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) :
    CentralRepresentationCertificate a b c i := by
  let hlocal := SectionFourLocalConditions.ofRepresentationConditions
    a b c hab hbc
  have hright := a.sectionFourRightDirectTrigger_of_boundary
    b c i htrigger hboundary
  have htriggerBC := a.sectionFour_sourceCentralTrigger_of_rightDirect
    b c hlocal i htrigger hright hbackward
  have hsource := hbc.centralRepresentations i htriggerBC
  have hlemma := a.sectionFourLemma45_forward
    b c hab i htrigger hboundary hshift
  exact CentralRepresentationCertificate.of_caseII
    hlemma.middleCurrent hsource hlemma.hilbert

/-- Profile 3 in the paper: the left direct bound activates the `(a,b)`
central representation, while Lemma 4.5(ii) supplies the preceding `(b,c)`
representation and its Hilbert symbol. -/
theorem sectionFourCentralCertificate_of_profileThree
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hboundary :
      (∃ hiPrev : 2 < i.val,
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩) ∨
        i.val = 2)
    (hforward :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le))
    (hshift :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous) :
    CentralRepresentationCertificate a b c i := by
  let hlocal := SectionFourLocalConditions.ofRepresentationConditions
    a b c hab hbc
  have hleft := a.sectionFourLeftDirectTrigger_of_boundary
    b c i htrigger hboundary
  have htriggerAB := a.sectionFour_middleCentralTrigger_of_leftDirect
    b c hlocal i htrigger hleft hforward
  have hmiddle := hab.centralRepresentations i htriggerAB
  have hlemma := a.sectionFourLemma45_backward
    b c hbc i htrigger hboundary hshift
  exact CentralRepresentationCertificate.of_caseIII
    hmiddle hlemma.sourcePrevious hlemma.hilbert

end BONG.GoodBONG

end Bong
