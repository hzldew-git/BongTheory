/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoBoundaryAlpha
import Bong.Bong.Beli2019Lemma79StrictPrimaryReduction

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the gap-two central defect

At the last unequal type-I coordinate, the preceding target order is
strictly smaller than the corresponding source order.  Together with
two-step monotonicity and the common suffix, this makes the secondary
coefficient strictly positive.  The Section 2.7--2.9 reduction therefore
forces the primary candidate to equal `beta_u`, giving the displayed
central mixed-defect identity in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- In the type-I gap-two branch, the target order immediately before the
last unequal coordinate is strictly smaller than the source order there.
This covers both possibilities `anchor = last` and `anchor < last`. -/
theorem beli2019Lemma79_typeI_caseEight_previousTarget_lt_source
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlastPos : 0 < D.profile.last) :
    b.orderSequence.entryOrZero (D.profile.last - 1) <
      a.orderSequence.entryOrZero (D.profile.last - 1) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  by_cases hanchor : D.anchor = D.profile.last
  · have hfirstAnchor : D.profile.first < D.anchor := by
      rw [hfirst, hanchor]
      exact hlastPos
    have hleft := D.profile.leftProfile hfirstAnchor
    rcases I.last_even with ⟨d, hd⟩
    have hlastTwo : 2 ≤ D.profile.last := by omega
    have hpreviousEven :
        Even ((D.profile.last - 2) - D.profile.first) := by
      refine ⟨d - 1, ?_⟩
      rw [hfirst]
      omega
    have hsourceEarlier := hleft.2.2 (D.profile.last - 2) (by
        rw [hfirst]
        omega) (by omega) hpreviousEven
    have htargetMonotone :=
      b.orderSequence.entryOrZero_le_of_evenGap
        D.profile.first (D.profile.last - 2) (by
          rw [hfirst]
          omega) (by
            have hbound := D.profile.lastDifference.bound
            omega) hpreviousEven
    have hearlier :
        a.orderSequence.entryOrZero (D.profile.last - 2) <
          b.orderSequence.entryOrZero (D.profile.last - 2) := by
      calc
        a.orderSequence.entryOrZero (D.profile.last - 2) =
            a.orderSequence.entryOrZero D.profile.first := hsourceEarlier
        _ < b.orderSequence.entryOrZero D.profile.first := hleft.2.1
        _ ≤ b.orderSequence.entryOrZero (D.profile.last - 2) :=
          htargetMonotone
    have hpair := D.profile.leftPairEq (D.profile.last - 2)
      (by omega) (by
        refine ⟨1, ?_⟩
        omega)
    rw [show D.profile.last - 2 + 1 = D.profile.last - 1 by omega]
      at hpair
    omega
  · have hanchorLast : D.anchor < D.profile.last :=
      lt_of_le_of_ne D.profile.anchor_le_last hanchor
    have hlastDistance := (D.profile.rightProfile hanchorLast).1
    rcases hlastDistance with ⟨d, hd⟩
    have hanchorTwo : D.anchor + 2 ≤ D.profile.last := by omega
    have hpairParity :
        Even ((D.profile.last - 1) - (D.anchor + 1)) := by
      refine ⟨d - 1, ?_⟩
      omega
    have hpair := D.profile.rightPairEq (D.profile.last - 1)
      (by omega) (by
        have hbound := D.profile.lastDifference.bound
        omega) hpairParity
    rw [show D.profile.last - 1 + 1 = D.profile.last by omega] at hpair
    omega

/-- The two cross-order inequalities and the strict positive coefficient
needed by the Section 2.9 secondary-candidate reduction at `u`. -/
theorem beli2019Lemma79_typeI_caseEight_boundaryCrossAndShift
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hi : 1 < (caseEightTypeIBoundaryIndex D hlast).val ∧
      (caseEightTypeIBoundaryIndex D hlast).val + 1 < n + 2) :
    b.order ⟨(caseEightTypeIBoundaryIndex D hlast).val - 2, by omega⟩ <
        a.order ⟨(caseEightTypeIBoundaryIndex D hlast).val,
          (caseEightTypeIBoundaryIndex D hlast).lt_large⟩ ∧
      b.order ⟨(caseEightTypeIBoundaryIndex D hlast).val - 1, by omega⟩ ≤
        a.order ⟨(caseEightTypeIBoundaryIndex D hlast).val + 1, hi.2⟩ ∧
      0 <
        a.order ⟨(caseEightTypeIBoundaryIndex D hlast).val,
            (caseEightTypeIBoundaryIndex D hlast).lt_large⟩ +
          a.order ⟨(caseEightTypeIBoundaryIndex D hlast).val + 1, hi.2⟩ -
          b.order ⟨(caseEightTypeIBoundaryIndex D hlast).val - 2,
            by omega⟩ -
          b.order ⟨(caseEightTypeIBoundaryIndex D hlast).val - 1,
            by omega⟩ := by
  let i := caseEightTypeIBoundaryIndex D hlast
  have hilast : i.val = D.profile.last + 1 := rfl
  have hiFirst := hi.1
  have hiSecond := hi.2
  change 1 < D.profile.last + 1 at hiFirst
  change D.profile.last + 1 + 1 < n + 2 at hiSecond
  have hlastPos : 0 < D.profile.last := by omega
  have hpreviousEntry :=
    beli2019Lemma79_typeI_caseEight_previousTarget_lt_source
      a b D hfirst hgapTwo hlastPos
  have hsourceMonotone :=
    a.orderSequence.entryOrZero_le_of_evenGap
      (D.profile.last - 1) (D.profile.last + 1) (by omega) (by omega)
      (by refine ⟨1, by omega⟩)
  have hpreviousOrder :
      b.order ⟨D.profile.last - 1, by omega⟩ <
        a.order ⟨D.profile.last + 1, by omega⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hpreviousEntry.trans_le hsourceMonotone
  have htargetMonotone :=
    b.orderSequence.entryOrZero_le_of_evenGap
      D.profile.last (D.profile.last + 2) (by omega) hiSecond
      (by refine ⟨1, by omega⟩)
  have hsuffix := D.profile.lastDifference.after
    (D.profile.last + 2) (by omega) hiSecond
  have hcurrentOrder :
      b.order ⟨D.profile.last, by omega⟩ ≤
        a.order ⟨D.profile.last + 2, by omega⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact htargetMonotone.trans_eq hsuffix.symm
  have hshift :
      0 < a.order ⟨D.profile.last + 1, by omega⟩ +
          a.order ⟨D.profile.last + 2, by omega⟩ -
          b.order ⟨D.profile.last - 1, by omega⟩ -
          b.order ⟨D.profile.last, by omega⟩ := by
    omega
  simpa only [caseEightTypeIBoundaryIndex,
    show D.profile.last + 1 - 2 = D.profile.last - 1 by omega,
    show D.profile.last + 1 - 1 = D.profile.last by omega,
    show D.profile.last + 1 + 1 = D.profile.last + 2 by omega] using
      And.intro hpreviousOrder (And.intro hcurrentOrder hshift)

set_option maxHeartbeats 1000000 in
-- The primary-candidate reduction expands several dependent finite-index
-- witnesses before the final finite-defect calculation; allow that normalization.
/-- The gap-two calculation at the paper index `u`:
`d[-a_{1,u+1} b_{1,u-1}] = S_u - S_{u+1} + beta_u`. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_centralDefect_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast) :
    a.truncatedPrefixDefect b (-1)
        (D.profile.last + 2) D.profile.last =
      ((((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
          b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) : Rat) +
        b.alphaValue ⟨D.profile.last, hlast⟩ : Rat) : WithTop Rat) := by
  let i := caseEightTypeIBoundaryIndex D hlast
  let first : Fin (n + 1) := ⟨D.profile.last, hlast⟩
  have hvalue := beli2019Lemma79_typeI_caseEight_boundaryAlpha_eq
    a b D hdefect hlast
  have hhalf := beli2019Lemma79_typeI_caseEight_boundaryAlpha_lt_halfGap
    a b D hlast H hfirstTail
  have hcomparison : (b.alphaValue first : WithTop Rat) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    have h := hdefect i
    simpa only [first, i] using hvalue ▸ h
  have hcross (hi : 1 < i.val ∧ i.val + 1 < n + 2) :=
    beli2019Lemma79_typeI_caseEight_boundaryCrossAndShift
      a b D hfirst hgapTwo hlast hi
  have hprimaryLe : a.representationPrimaryDefect b i ≤
      (b.alphaValue first : WithTop Rat) := by
    apply a.representationPrimaryDefect_le_of_alphaValue_eq_of_lt_halfGap
      b i (b.alphaValue first)
      (hsmall := fun _ ↦ i.lt_large)
      (hpreviousCross := fun hi ↦ by
        simpa only [i] using (hcross hi).1.le)
      (hcurrentCross := fun hi ↦ by
        simpa only [i] using (hcross hi).2.1)
      (hshift := fun hi ↦ by
        simpa only [i] using (hcross hi).2.2)
    · simpa only [i, first] using hvalue
    · simpa only [i, first] using hhalf
    · exact hcomparison
  have hAlpha : a.representationAlpha b i =
      (b.alphaValue first : WithTop Rat) := by
    calc
      a.representationAlpha b i =
          (a.representationAlphaValue b i : WithTop Rat) :=
        (a.coe_representationAlphaValue b i).symm
      _ = (b.alphaValue first : WithTop Rat) := by
        exact_mod_cast (by simpa only [i, first] using hvalue)
  have hprimaryEq : a.representationPrimaryDefect b i =
      (b.alphaValue first : WithTop Rat) :=
    le_antisymm hprimaryLe (by
      rw [← hAlpha]
      exact a.representationAlpha_le_primary b i)
  let z := a.truncatedPrefixDefect b (-1)
    (D.profile.last + 2) D.profile.last
  have hprimaryEq' :
      ((((a.order ⟨D.profile.last + 1, by omega⟩ -
          b.order ⟨D.profile.last, by omega⟩ : Int) : Rat) : WithTop Rat) + z) =
        (b.alphaValue first : WithTop Rat) := by
    unfold representationPrimaryDefect at hprimaryEq
    simpa only [i, caseEightTypeIBoundaryIndex, first, z,
      show D.profile.last + 1 + 1 = D.profile.last + 2 by omega,
      show D.profile.last + 1 - 1 = D.profile.last by omega] using hprimaryEq
  have hz : z ≠ ⊤ := by
    intro htop
    apply (WithTop.coe_ne_top :
      (b.alphaValue first : WithTop Rat) ≠ ⊤)
    calc
      (b.alphaValue first : WithTop Rat) =
          ((((a.order ⟨D.profile.last + 1, by omega⟩ -
            b.order ⟨D.profile.last, by omega⟩ : Int) : Rat) :
              WithTop Rat) + z) := hprimaryEq'.symm
      _ = ⊤ := by rw [htop, add_top]
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hz
  have hnextEntry := D.profile.lastDifference.after
    (D.profile.last + 1) (by omega) (by omega)
  have hnextOrder :
      a.order ⟨D.profile.last + 1, by omega⟩ =
        b.order ⟨D.profile.last + 1, by omega⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hnextEntry
  rw [← hd] at hprimaryEq'
  rw [show a.truncatedPrefixDefect b (-1)
      (D.profile.last + 2) D.profile.last = z by rfl, ← hd]
  norm_cast at hprimaryEq' ⊢
  push_cast at hprimaryEq' ⊢
  rw [hnextOrder] at hprimaryEq'
  have hfirstCast :
      (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc =
        (⟨D.profile.last, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hfirstSucc :
      (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ =
        (⟨D.profile.last + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  rw [hfirstCast, hfirstSucc]
  simp only [first] at hprimaryEq'
  linarith

end BONG.GoodBONG

end Bong
