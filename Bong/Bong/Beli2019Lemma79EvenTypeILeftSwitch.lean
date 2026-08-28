/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeIBoundaryLower
import Bong.Bong.Beli2019Lemma79EvenAssembly
import Bong.Bong.Beli2019Lemma79EvenTypeICentralBeta
import Bong.Bong.Beli2019Lemma79EvenTypeITargetCentral

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the first central type-I switch

At the first canonical switch the ordinary central alpha-shift proof is
replaced by the dedicated switch-alpha comparison.  The candidate estimates
then give the scalar beta bound.  Lemma 7.6's boundary alternative supplies
the source self-prefix, while the completed central target theorem supplies
the target self-prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- The exact small-gap formula unfolds the two alpha arithmetic laws.
/-- In the small-gap branch, the target alpha at the first switch is exactly
the source alpha plus two. -/
theorem beli2019Lemma79_typeI_leftSwitch_alphaShift_of_gap_lt_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hleftTwo : 2 ≤ C.leftSwitch)
    (hsmall : b.orderGap ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ < 2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ =
      a.alphaValue ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ + 2 := by
  have hleftPos : 0 < C.leftSwitch := by omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let p : Fin (n + 1) := ⟨C.leftSwitch - 1, by omega⟩
  let switchIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨C.leftSwitch, hleftPos, hleftBound, hleftBound.le⟩
  have hpCast : p.castSucc =
      (⟨C.leftSwitch - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨C.leftSwitch, hleftBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hsourceFormulaRaw := lemma69_typeI_left_alpha_formula
    a b D C hfirst hdefect switchIdx (by
      simp only [switchIdx]
      omega) (by simp only [switchIdx]; exact le_rfl) (by
        simpa only [switchIdx] using C.left_even)
  have hsourceFormula : a.alphaValue p =
      (a.orderGap p : ℚ) + 1 := by
    unfold orderGap
    rw [hpSucc, hpCast]
    simpa only [switchIdx, p] using hsourceFormulaRaw
  have htargetPrevious := lemma69_v_typeI_previous_target_order
    a b D C hfirst hleftPos
  have hsourceLeft := C.source_to_anchor C.leftSwitch
    C.left_le_anchor C.left_even
  have htargetLeft := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have hleftShift : b.order ⟨C.leftSwitch, hleftBound⟩ =
      a.order ⟨C.leftSwitch, hleftBound⟩ + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero C.leftSwitch =
      a.orderSequence.entryOrZero C.leftSwitch + 2
    omega
  have hgapShift : b.orderGap p = a.orderGap p + 3 := by
    unfold orderGap
    rw [hpSucc, hpCast, hleftShift]
    have htargetPrevious' :
        b.order ⟨C.leftSwitch - 1, by omega⟩ =
          a.order ⟨C.leftSwitch - 1, by omega⟩ - 1 := by
      simpa only using htargetPrevious
    rw [htargetPrevious']
    ring
  have hodd : Odd (b.orderGap p) := by
    simpa only [p] using
      lemma76_leftSwitch_gap_odd a b D C hfirst hleftPos
  have hsmall' : b.orderGap p ≤ 2 * (ramificationIndex K : Int) := by
    simpa only [p] using hsmall.le
  have htargetFormula :=
    (b.beli2009Lemma27_iii p hsmall').2.mpr (Or.inr hodd)
  have hgapShiftQ : (b.orderGap p : ℚ) =
      (a.orderGap p : ℚ) + 3 := by
    exact_mod_cast hgapShift
  simpa only [p] using (show b.alphaValue p = a.alphaValue p + 2 by
    rw [htargetFormula, hsourceFormula, hgapShiftQ]
    ring)

set_option maxHeartbeats 5000000 in
-- Candidate comparison at the switch carries several dependent indices.
/-- The scalar beta bound at the first central type-I switch. -/
theorem beli2019Lemma79_typeI_leftSwitch_even_beta
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hleftEq : i.val = C.leftSwitch)
    (hfarRight : i.val + 2 ≤ C.rightSwitch)
    (hgapSmall : b.orderGap ⟨i.val - 1, by omega⟩ <
      2 * (ramificationIndex K : Int)) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
  have hleftTwo : 2 ≤ C.leftSwitch := by omega
  have halphaRaw :=
    beli2019Lemma79_typeI_leftSwitch_alphaShift_of_gap_lt_twoE
      a b D C hfirst hdefectAB hleftTwo (by
        simpa only [← hleftEq] using hgapSmall)
  have halpha : b.alphaValue ⟨i.val - 1, by omega⟩ =
      a.alphaValue ⟨i.val - 1, by omega⟩ + 2 := by
    simpa only [← hleftEq] using halphaRaw
  have hhalf := lemma79_typeI_central_even_halfGap_le_add_two
    a b c D C hfirst i hiEven (by omega) (by omega)
  have hprimary := beli2019Lemma79_typeI_central_even_primary
    a b c D C hfirst hrightLast horderAB hdefectAB i hi.2
      hiEven (by omega) (by omega)
  have hsecondary : ∀
      (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
      b.representationSecondaryDefect c i hi' ≤
        a.representationSecondaryDefect c i hi' +
          ((2 : ℚ) : WithTop ℚ) := by
    intro hi'
    exact beli2019Lemma79_typeI_central_even_secondary
      a b c D C hfirst hrightLast horderAB hdefectAB i hi'
        hiEven (by omega) hfarRight
  exact lemma79_even_beta_bound_of_candidate_shifts
    a b c hdefectAC i halpha hhalf hprimary hsecondary

/-- The source self-prefix bound at the first central type-I switch. -/
theorem beli2019Lemma79_typeI_leftSwitch_even_sourceCapped
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hleftEq : i.val = C.leftSwitch)
    (hfarRight : i.val + 2 ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  have htwoE := representationAlphaValue_le_twoE_of_crossGap_le
    b c i hcross
  have hleftPos : 0 < C.leftSwitch := by omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let current : Fin (n + 1) := ⟨C.leftSwitch - 1, by omega⟩
  have hupper : b.orderGap current ≤
      2 * (ramificationIndex K : Int) + 1 := by
    simpa only [current] using
      lemma79_typeI_leftSwitch_gap_le_twoE_add_one a b D C hleftPos
  by_cases hgap : b.orderGap current ≤
      2 * (ramificationIndex K : Int)
  · have hodd : Odd (b.orderGap current) := by
      simpa only [current] using
        lemma76_leftSwitch_gap_odd a b D C hfirst hleftPos
    rcases hodd with ⟨z, hz⟩
    have hgapSmall : b.orderGap current <
        2 * (ramificationIndex K : Int) := by
      omega
    have hbeta := beli2019Lemma79_typeI_leftSwitch_even_beta
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        i hi hiEven hleftEq hfarRight (by
          simpa only [current, ← hleftEq] using hgapSmall)
    have hbetaTop : (b.representationAlphaValue c i : WithTop ℚ) ≤
        (b.alphaValue ⟨C.leftSwitch - 1, by omega⟩ : WithTop ℚ) := by
      exact_mod_cast (by simpa only [← hleftEq] using hbeta)
    have hboundary := beli2019Lemma76_typeI_boundary_lower
      a b D C hfirst hleftPos
        (b.representationAlphaValue c i : WithTop ℚ) hbetaTop htwoE
    simpa only [← hleftEq] using hboundary
  · have hgapEq : b.orderGap current =
        2 * (ramificationIndex K : Int) + 1 := by
      omega
    have hcases := beli2019Lemma76_typeI a b D C hfirst hleftPos
    dsimp only at hcases
    let caseCurrent : Fin (n + 1) := ⟨C.leftSwitch - 2 + 1, by omega⟩
    have hcurrentEq : caseCurrent = current := by
      apply Fin.ext
      simp only [caseCurrent, current]
      omega
    have hgapEq' : b.orderGap caseCurrent =
        2 * (ramificationIndex K : Int) + 1 := by
      rw [hcurrentEq]
      exact hgapEq
    have hlarge := htwoE.trans (hcases.2 hgapEq')
    simpa only [← hleftEq] using hlarge

/-- Lemma 7.9(ii), case 3, at the first central even type-I switch. -/
theorem beli2019Lemma79_ii_typeI_even_leftSwitch
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hleftEq : i.val = C.leftSwitch)
    (hfarRight : i.val + 2 ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hsource := beli2019Lemma79_typeI_leftSwitch_even_sourceCapped
    a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
      i hi hiEven hleftEq hfarRight hcross
  have htarget := beli2019Lemma79_typeI_central_even_target
    a b c D C hfirst hnorm i (by omega) hiEven (by omega) (by omega) hcross
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

end BONG.GoodBONG

end Bong
